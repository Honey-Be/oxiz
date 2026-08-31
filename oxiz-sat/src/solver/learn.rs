//! Clause learning, LBD computation, database reduction, inprocessing, and vivification

use super::*;
use smallvec::SmallVec;

impl Solver {
    /// Compute LBD (Literal Block Distance) of a clause
    /// LBD is the number of distinct decision levels in the clause
    pub(super) fn compute_lbd(&mut self, lits: &[Lit]) -> u32 {
        self.lbd_mark += 1;
        let mark = self.lbd_mark;

        let mut count = 0u32;
        for &lit in lits {
            let level = self.trail.level(lit.var()) as usize;
            if level < self.level_marks.len() && self.level_marks[level] != mark {
                self.level_marks[level] = mark;
                count += 1;
            }
        }

        count
    }

    /// Learn a clause and set up watches
    /// Includes on-the-fly subsumption check
    /// Tracks allocation via memory optimizer for size-class pool accounting
    pub(super) fn learn_clause(&mut self, learnt_clause: SmallVec<[Lit; 16]>) {
        // DRAT: log the learned clause once, before any of the length-specific
        // `add_learned` branches install it. No-op unless DRAT is enabled.
        self.drat_add(&learnt_clause);

        // Track allocation in memory optimizer for pool accounting
        let _pool_buf = self.memory_optimizer.allocate(learnt_clause.len());

        if learnt_clause.len() == 1 {
            // Store unit learned clause in database for persistence across backtracks
            let clause_id = self.clauses.add_learned(learnt_clause.iter().copied());
            self.stats.learned_clauses += 1;
            self.stats.unit_clauses += 1;
            self.learned_clause_ids.push(clause_id);
            // Record in the per-push undo ledger so `pop` removes it (a clause
            // learned under a pushed assertion is unsound once that scope pops).
            self.track_clause(clause_id);

            self.trail.assign_decision(learnt_clause[0]);
        } else if learnt_clause.len() == 2 {
            // Binary learned clause - add to binary implication graph
            let lbd = self.compute_lbd(&learnt_clause);
            let clause_id = self.clauses.add_learned(learnt_clause.iter().copied());
            self.stats.learned_clauses += 1;
            self.stats.binary_clauses += 1;
            self.stats.total_lbd += lbd as u64;

            if let Some(clause) = self.clauses.get_mut(clause_id) {
                clause.lbd = lbd;
            }

            self.learned_clause_ids.push(clause_id);
            self.track_clause(clause_id);

            let lit0 = learnt_clause[0];
            let lit1 = learnt_clause[1];

            // Add to binary graph
            self.binary_graph.add(lit0.negate(), lit1, clause_id);
            self.binary_graph.add(lit1.negate(), lit0, clause_id);

            self.watches
                .add(lit0.negate(), Watcher::new(clause_id, lit1));
            self.watches
                .add(lit1.negate(), Watcher::new(clause_id, lit0));

            self.trail.assign_propagation(learnt_clause[0], clause_id);
        } else {
            let lbd = self.compute_lbd(&learnt_clause);
            self.stats.total_lbd += lbd as u64;
            let clause_id = self.clauses.add_learned(learnt_clause.iter().copied());
            self.stats.learned_clauses += 1;

            if let Some(clause) = self.clauses.get_mut(clause_id) {
                clause.lbd = lbd;
            }

            self.learned_clause_ids.push(clause_id);
            self.track_clause(clause_id);

            let lit0 = learnt_clause[0];
            let lit1 = learnt_clause[1];
            self.watches
                .add(lit0.negate(), Watcher::new(clause_id, lit1));
            self.watches
                .add(lit1.negate(), Watcher::new(clause_id, lit0));

            self.trail.assign_propagation(learnt_clause[0], clause_id);

            // On-the-fly subsumption: check if this new clause subsumes existing clauses
            if learnt_clause.len() <= 5 && lbd <= 3 {
                self.check_subsumption(clause_id);
            }
        }
    }

    /// Check if the given clause subsumes any existing clauses
    /// A clause C subsumes C' if all literals of C are in C'
    pub(super) fn check_subsumption(&mut self, new_clause_id: ClauseId) {
        let new_clause = match self.clauses.get(new_clause_id) {
            Some(c) => c.lits.clone(),
            None => return,
        };

        if new_clause.len() > 10 {
            return; // Don't check subsumption for large clauses (too expensive)
        }

        // Check against learned clauses only
        let mut to_remove = Vec::new();
        let mut locked_skipped = 0usize;
        for &cid in &self.learned_clause_ids {
            if cid == new_clause_id {
                continue;
            }

            if let Some(clause) = self.clauses.get(cid) {
                if clause.deleted || clause.lits.len() < new_clause.len() {
                    continue;
                }

                // Check if new_clause subsumes clause
                if new_clause.iter().all(|&lit| clause.lits.contains(&lit)) {
                    // LOCKED-CLAUSE GUARD — defence in depth, NOT a fix for an
                    // observed bug. Read the whole note before deleting it.
                    //
                    // Deleting a clause that is a current `Reason::Propagation`
                    // would be the #428 bug class: the trail keeps holding the
                    // id, `remove` pushes it onto the free list, the next `add`
                    // recycles the slot in place, and conflict analysis then
                    // reads an unrelated clause as the antecedent — wrong learnt
                    // clause, wrong verdict. `reduce_clause_database` has
                    // guarded against exactly that all along (its `is_reason`
                    // computation); this site never did, and the asymmetry looks
                    // alarming.
                    //
                    // It is not, and the reason is worth writing down because
                    // the asymmetry will look alarming again to the next reader.
                    // The ONE caller (learn.rs, the on-the-fly subsumption call)
                    // runs immediately after
                    // `assign_propagation(learnt_clause[0], clause_id)`, so:
                    //
                    //   * `learnt_clause[0]` is TRUE, and its trail reason is
                    //     the NEW clause;
                    //   * a subsumed `C'` contains every literal of the new
                    //     clause, hence contains `learnt_clause[0]`;
                    //   * a clause is a current reason only when all of its
                    //     literals but the propagated one are FALSE.
                    //
                    // `C'` therefore cannot be a current reason: it holds a true
                    // literal that is not its own propagation. Measured to
                    // agree — 263 instances (200 random 3-SAT at the phase
                    // transition, 60 larger, 3 pigeonhole) across the default,
                    // aggressive and glucose presets fire this guard ZERO times.
                    //
                    // It stays because the invariant is the CALLER's, established
                    // four lines away in another function, and a second caller
                    // would silently invalidate it. In a solver where id
                    // recycling has produced wrong verdicts four separate times,
                    // paying a scan over the handful of clauses that already
                    // passed the subsumption test is the cheaper side of that
                    // trade. `OXIZ_SUBSUMPTION_DBG=1` reports if it ever fires;
                    // if it does, the derivation above has a hole in it.
                    let is_reason = clause.lits.iter().any(|&lit| {
                        let var = lit.var();
                        self.trail.is_assigned(var)
                            && matches!(self.trail.reason(var), Reason::Propagation(r) if r == cid)
                    });
                    if is_reason {
                        locked_skipped += 1;
                        continue;
                    }
                    to_remove.push(cid);
                }
            }
        }
        #[cfg(feature = "std")]
        if locked_skipped > 0 && std::env::var_os("OXIZ_SUBSUMPTION_DBG").is_some() {
            eprintln!(
                "[subsumption] kept {locked_skipped} locked clause(s) that would have been freed"
            );
        }

        // Remove subsumed clauses
        for cid in to_remove {
            // DRAT: log the deletion (learned clauses only) before removal.
            self.drat_delete_clause_id(cid);
            // Detach every watcher (and, for a binary clause, every
            // implication edge) that still references this clause BEFORE
            // freeing its slot: `ClauseDatabase::remove` pushes the id onto a
            // free list the next `add_*` recycles, clearing the slot's
            // `deleted` flag, so `propagate`'s "skip deleted clause" guard
            // cannot catch a stale watcher once the id is reused — the
            // recycled clause silently inherits the deleted clause's watchers
            // and mis-propagates (the exact false-`unsat` mechanism regression
            // #428 covers: `check_subsumption` was the one clause-removal site
            // in this module that never scrubbed). The scrub is no longer a
            // per-call-site ritual — it is inside `remove`, keyed off the
            // required index-sink argument (see `ClauseIndexScrub`).
            self.scrub_and_remove_clause(cid);
            self.stats.deleted_clauses += 1;
        }

        // PRUNE THE ID LIST. `reduce_clause_database` does this after its own
        // deletions; this site did not, and the omission is not cosmetic.
        //
        // Both consumers of `learned_clause_ids` — this function and
        // `reduce_clause_database` — trust it to contain only LEARNED clauses;
        // neither checks `clause.learned`. A freed id left in the list is a
        // recycled handle: the next `add` reuses the slot, the `deleted` flag
        // is cleared, and the stale entry now names whatever clause moved in.
        // If that is an ORIGINAL clause — which is what an incremental
        // `(assert)` after a solve produces, the shape adsmt's delegation
        // uses — it can then be deleted as if it were learned, dropping an
        // input constraint and with it the `unsat` that constraint carried.
        //
        // HONESTLY: unmeasured. `check_subsumption` deleted NOTHING across
        // every workload I could build for it (263 random 3-SAT and pigeonhole
        // instances, and 5 larger solves accumulating 13,014 learned clauses,
        // all report `deleted_clauses == 0`), so I have no instance where the
        // stale entry is created in the first place, let alone one where it
        // aliases an original. The fix lands on the strength of the invariant,
        // not of a repro — and the unit test below drives the path directly
        // because the search would not.
        self.learned_clause_ids
            .retain(|&cid| self.clauses.get(cid).is_some_and(|c| !c.deleted));
    }

    /// Add a theory reason clause
    /// The clause is: reason_lits[0] OR reason_lits[1] OR ... OR propagated_lit
    pub(super) fn add_theory_reason_clause(
        &mut self,
        reason_lits: &[Lit],
        propagated_lit: Lit,
    ) -> ClauseId {
        let mut clause_lits: SmallVec<[Lit; 8]> = SmallVec::new();
        clause_lits.push(propagated_lit);
        for &lit in reason_lits {
            clause_lits.push(lit.negate());
        }

        // NOTE: deliberately NOT logged to DRAT. A theory reason clause is a
        // theory lemma, not a propositional (RUP/RAT) consequence of the CNF, so
        // emitting it would produce a clause drat-trim cannot justify. DRAT proof
        // emission is supported for the pure Boolean `solve()` loop only; the
        // CDCL(T) (`solve_with_theory`) path is out of scope for DRAT.
        let clause_id = self.clauses.add_learned(clause_lits.iter().copied());
        // Record in the per-push undo ledger: a theory-reason lemma asserted under
        // a pushed assertion must not survive the `pop` that drops that scope.
        self.track_clause(clause_id);

        // Set up watches
        if clause_lits.len() >= 2 {
            let lit0 = clause_lits[0];
            let lit1 = clause_lits[1];
            self.watches
                .add(lit0.negate(), Watcher::new(clause_id, lit1));
            self.watches
                .add(lit1.negate(), Watcher::new(clause_id, lit0));
        }

        clause_id
    }

    /// Memory-pool bookkeeping for a clause that is about to be removed:
    /// round-trip a buffer of its size through the size-class pool so the
    /// optimizer's occupancy statistics see the free. Must be called while the
    /// clause is still in the database (it reads the literal count from it).
    /// No-op if the slot is gone — matching the `if let Some(clause)` guard the
    /// three tier loops used to spell out inline.
    #[inline]
    fn account_pool_free(&mut self, cid: ClauseId) {
        if let Some(clause) = self.clauses.get(cid) {
            let num_lits = clause.lits.len();
            let buf = self.memory_optimizer.allocate(num_lits);
            self.memory_optimizer.free(buf, num_lits);
        }
    }

    /// Reduce the learned clause database using tier-based deletion strategy
    /// - Core tier (Tier 1): Rarely deleted, only if very inactive
    /// - Mid tier (Tier 2): Delete ~30% based on activity
    /// - Local tier (Tier 3): Delete ~75% based on activity
    pub(super) fn reduce_clause_database(&mut self) {
        use crate::clause::ClauseTier;

        let mut core_candidates: Vec<(ClauseId, f64)> = Vec::new();
        let mut mid_candidates: Vec<(ClauseId, f64)> = Vec::new();
        let mut local_candidates: Vec<(ClauseId, f64)> = Vec::new();

        for &cid in &self.learned_clause_ids {
            if let Some(clause) = self.clauses.get(cid) {
                if clause.deleted {
                    continue;
                }

                // Don't delete binary clauses (very useful)
                if clause.lits.len() <= 2 {
                    continue;
                }

                // Check if clause is currently a reason for any assignment
                // (We can't delete reason clauses)
                let is_reason = clause.lits.iter().any(|&lit| {
                    let var = lit.var();
                    if self.trail.is_assigned(var) {
                        matches!(self.trail.reason(var), Reason::Propagation(r) if r == cid)
                    } else {
                        false
                    }
                });

                if !is_reason {
                    match clause.tier {
                        ClauseTier::Core => core_candidates.push((cid, clause.activity)),
                        ClauseTier::Mid => mid_candidates.push((cid, clause.activity)),
                        ClauseTier::Local => local_candidates.push((cid, clause.activity)),
                    }
                }
            }
        }

        // Sort by activity (ascending) - delete low-activity clauses first
        core_candidates.sort_by(|a, b| a.1.partial_cmp(&b.1).unwrap_or(core::cmp::Ordering::Equal));
        mid_candidates.sort_by(|a, b| a.1.partial_cmp(&b.1).unwrap_or(core::cmp::Ordering::Equal));
        local_candidates
            .sort_by(|a, b| a.1.partial_cmp(&b.1).unwrap_or(core::cmp::Ordering::Equal));

        // Delete different percentages from each tier
        // Core: Delete bottom 10% (very conservative)
        let num_core_delete = core_candidates.len() / 10;
        // Mid: Delete bottom 30%
        let num_mid_delete = (mid_candidates.len() * 3) / 10;
        // Local: Delete bottom 75% (very aggressive)
        let num_local_delete = (local_candidates.len() * 3) / 4;

        // Detaching a deleted clause's watchers BEFORE freeing its slot is the
        // whole ballgame here: `ClauseDatabase::remove` pushes the id onto a
        // free list the next `add_*` recycles, clearing the slot's `deleted`
        // flag, so `propagate`'s "skip deleted clause" guard cannot catch a
        // stale watcher once the id is reused — the recycled clause silently
        // inherits the deleted clause's watchers and mis-propagates (the exact
        // spurious-SAT mechanism `reduce_clause_database_soundness` covers).
        // That scrub now lives inside `remove` itself (see `ClauseIndexScrub`);
        // all this loop still owns is the memory-pool size accounting, which
        // must read the clause while it is still there.
        for (cid, _) in core_candidates.iter().take(num_core_delete) {
            self.account_pool_free(*cid);
            // DRAT: log the deletion (learned clauses only) before removal.
            self.drat_delete_clause_id(*cid);
            self.scrub_and_remove_clause(*cid);
            self.stats.deleted_clauses += 1;
        }

        for (cid, _) in mid_candidates.iter().take(num_mid_delete) {
            self.account_pool_free(*cid);
            self.drat_delete_clause_id(*cid);
            self.scrub_and_remove_clause(*cid);
            self.stats.deleted_clauses += 1;
        }

        for (cid, _) in local_candidates.iter().take(num_local_delete) {
            self.account_pool_free(*cid);
            self.drat_delete_clause_id(*cid);
            self.scrub_and_remove_clause(*cid);
            self.stats.deleted_clauses += 1;
        }

        // Clean up learned_clause_ids (remove deleted clauses)
        self.learned_clause_ids
            .retain(|&cid| self.clauses.get(cid).is_some_and(|c| !c.deleted));

        // Apply memory optimizer recommendations after deletion
        match self.memory_optimizer.recommend_action() {
            MemoryAction::Compact => {
                self.memory_optimizer.compact();
                self.clauses.compact();
            }
            MemoryAction::ReduceClauseDatabase => {
                // Already reduced; just compact the pool
                self.memory_optimizer.compact();
            }
            MemoryAction::ExpandPools | MemoryAction::None => {
                // No action needed
            }
        }
    }

    /// Handle clause deletion check and restart check.
    ///
    /// Returns `true` if a restart fired (the trail was backtracked to level 0).
    /// In the theory-aware loop the caller MUST then notify the theory with
    /// `theory.on_backtrack(0)` — otherwise the theory's frame stack keeps the
    /// (now-stale) level-1.. frames while the SAT trail is at level 0, and the
    /// next `on_new_level` reuses those stale frames (their bounds linger) —
    /// the restart sibling of the stale-bound desync, which can yield a spurious
    /// theory conflict (and, unlike the single-atom case, may span several atoms
    /// so the `last_conflict_is_stale_bound` guard would NOT catch it).
    #[must_use]
    pub(super) fn handle_clause_deletion_and_restart(&mut self) -> bool {
        self.conflicts_since_deletion += 1;

        if self.conflicts_since_deletion >= self.config.clause_deletion_threshold as u64 {
            self.reduce_clause_database();
            self.conflicts_since_deletion = 0;
        }

        if self.stats.conflicts >= self.restart_threshold {
            self.restart();
            return true;
        }
        false
    }

    /// Handle clause deletion and restart, but don't backtrack past assumptions
    pub(super) fn handle_clause_deletion_and_restart_limited(&mut self, min_level: u32) {
        self.conflicts_since_deletion += 1;

        if self.conflicts_since_deletion >= self.config.clause_deletion_threshold as u64 {
            self.reduce_clause_database();
            self.conflicts_since_deletion = 0;
        }

        if self.stats.conflicts >= self.restart_threshold {
            // Limited restart - don't backtrack past assumptions
            self.backtrack(min_level);
            self.stats.restarts += 1;
            self.luby_index += 1;
            self.restart_threshold =
                self.stats.conflicts + self.config.restart_interval * Self::luby(self.luby_index);
        }
    }

    /// Save the model
    pub(super) fn save_model(&mut self) {
        self.model.resize(self.num_vars, LBool::Undef);
        for i in 0..self.num_vars {
            self.model[i] = self.trail.value(Var::new(i as u32));
        }
    }

    /// Delete the literal at `drop_idx` from clause `clause_id` **in place**,
    /// keeping the two-watched-literal index consistent.
    ///
    /// This is the mutating sibling of [`Solver::scrub_and_remove_clause`], and
    /// it exists for the same reason (see [`crate::ClauseIndexScrub`]): a
    /// `ClauseId` is a handle into structures that live *outside* the clause,
    /// so any edit that changes which literals a clause is watched on has to
    /// repair those structures. Deleting a **watched** literal in place leaves
    /// a watcher parked in `watches[l.negate()]` for a clause that no longer
    /// contains `l` — and that is not merely untidy:
    ///
    /// * `propagate` assumes the triggering literal is at index 0 or 1 and only
    ///   rescans from index 2, so it can miss the one remaining non-false
    ///   literal and unit-propagate a literal that is not actually implied; and
    /// * the leftover watcher's *blocker* names the deleted literal, so
    ///   `propagate`'s "blocker is true ⇒ clause satisfied" shortcut can skip a
    ///   clause that is in fact unit or falsified.
    ///
    /// Both fabricate propagations, i.e. both can fabricate a verdict.
    ///
    /// Returns `Some((old_lits, new_lits))` on success (callers need both for
    /// DRAT's delete-old + add-new encoding of an in-place strengthening), or
    /// `None` if the request was **declined**, in which case the clause is left
    /// exactly as it was. Declining is always sound — it just keeps a longer
    /// clause — and happens when the strengthened clause has fewer than two
    /// literals that are non-false at the current (level-0) assignment, i.e.
    /// when no legal watch pair exists.
    pub(super) fn strengthen_clause_in_place(
        &mut self,
        clause_id: ClauseId,
        drop_idx: usize,
    ) -> Option<(SmallVec<[Lit; 16]>, SmallVec<[Lit; 16]>)> {
        let old_lits: SmallVec<[Lit; 16]> = match self.clauses.get(clause_id) {
            Some(c) if !c.deleted && c.lits.len() > 2 && drop_idx < c.lits.len() => {
                c.lits.iter().copied().collect()
            }
            _ => return None,
        };

        // Case A: the dropped literal is not one of the two WATCHED ones
        // (indices 0 and 1). Both watchers keep pointing at literals the clause
        // still contains, and their blockers — which are each other — are
        // likewise untouched, so the index stays exact. Plain in-place removal,
        // identical to what this code always did.
        if drop_idx >= 2 {
            let clause = self.clauses.get_mut(clause_id)?;
            clause.lits.remove(drop_idx);
            let new_lits: SmallVec<[Lit; 16]> = clause.lits.iter().copied().collect();
            return Some((old_lits, new_lits));
        }

        // Case B: a watched literal is going away. Detach → mutate → re-attach.
        let mut new_lits: SmallVec<[Lit; 16]> = old_lits.clone();
        new_lits.remove(drop_idx);

        // The *other* old watched literal survives and, after the shift, sits
        // at index 0 either way (drop 0 ⇒ old[1] shifts down; drop 1 ⇒ old[0]
        // stays). Keep watching it, and find it a partner. Both watched
        // literals must be non-false, which at level 0 is a stable property.
        if self.trail.lit_value(new_lits[0]).is_false() {
            return None;
        }
        let partner = (1..new_lits.len()).find(|&j| !self.trail.lit_value(new_lits[j]).is_false())?;
        new_lits.swap(1, partner);

        // Detach against the OLD literal set — that is where the watchers are
        // keyed. (`old_lits.len() > 2`, so this clause is not in the binary
        // implication graph and the sink's binary branch is a no-op.)
        let mut indexes = Self::clause_indexes(&mut self.watches, &mut self.binary_graph);
        indexes.scrub_clause(clause_id, &old_lits);

        let clause = self.clauses.get_mut(clause_id)?;
        clause.lits = new_lits.iter().copied().collect();

        // Re-attach on the new watch pair.
        let (w0, w1) = (new_lits[0], new_lits[1]);
        self.watches.add(w0.negate(), Watcher::new(clause_id, w1));
        self.watches.add(w1.negate(), Watcher::new(clause_id, w0));

        Some((old_lits, new_lits))
    }

    /// Vivification: try to strengthen clauses by checking if some literals are redundant
    /// This is an inprocessing technique that should be called periodically
    pub(super) fn vivify_clauses(&mut self) {
        if self.trail.decision_level() != 0 {
            return; // Only vivify at decision level 0
        }

        let mut vivified_count = 0;
        let max_vivifications = 100; // Limit to avoid too much overhead

        // Try to vivify some learned clauses
        let clause_ids: Vec<ClauseId> = self
            .learned_clause_ids
            .iter()
            .copied()
            .take(max_vivifications)
            .collect();

        for clause_id in clause_ids {
            if vivified_count >= max_vivifications {
                break;
            }

            let clause_lits = match self.clauses.get(clause_id) {
                Some(c) if !c.deleted && c.lits.len() > 2 => c.lits.clone(),
                _ => continue,
            };

            // Try to find redundant literals in the clause
            // Assign all literals except one to false and see if we can derive the last one
            for skip_idx in 0..clause_lits.len() {
                // Save current state
                let saved_level = self.trail.decision_level();

                // Assign all literals except skip_idx to false
                self.trail.new_decision_level();
                let mut conflict = false;

                for (i, &lit) in clause_lits.iter().enumerate() {
                    if i == skip_idx {
                        continue;
                    }

                    let value = self.trail.lit_value(lit);
                    if value.is_true() {
                        // Clause is already satisfied
                        conflict = false;
                        break;
                    } else if value.is_false() {
                        // Already false
                        continue;
                    } else {
                        // Assign to false
                        self.trail.assign_decision(lit.negate());

                        // Propagate
                        if self.propagate().is_some() {
                            conflict = true;
                            break;
                        }
                    }
                }

                // Backtrack
                self.backtrack(saved_level);

                // The literal at skip_idx is implied by the rest, so it can be
                // dropped from the clause (vivification succeeded). The removal
                // goes through `strengthen_clause_in_place`, which repairs the
                // watch index when the dropped literal is a watched one — doing
                // it by hand here is what left `propagate` chasing a watcher for
                // a literal the clause no longer contained.
                if conflict
                    && let Some((old_lits, new_lits)) =
                        self.strengthen_clause_in_place(clause_id, skip_idx)
                {
                    vivified_count += 1;
                    if self.drat.is_some() {
                        // DRAT models an in-place strengthening as delete-old +
                        // add-new. Add the strengthened clause first, then delete
                        // the original: ordering does not matter for drat-trim's
                        // backward check, but add-then-delete keeps the active set
                        // consistent at every prefix. The DRAT helpers no-op unless
                        // DRAT is enabled, so this is free in the default build.
                        self.drat_add(&new_lits);
                        self.drat_delete(&old_lits);
                    }
                    break; // Done with this clause
                }
            }
        }
    }

    /// Perform inprocessing (apply preprocessing during search)
    pub(super) fn inprocess(&mut self) {
        use crate::Preprocessor;

        // Only inprocess at decision level 0
        if self.trail.decision_level() != 0 {
            return;
        }

        // Create preprocessor with current number of variables
        let mut preprocessor = Preprocessor::new(self.num_vars);

        // Apply lightweight preprocessing techniques
        let _pure_elim = preprocessor.pure_literal_elimination(&mut self.clauses);
        let _subsumption = preprocessor.subsumption_elimination(&mut self.clauses);

        // On-the-fly clause strengthening
        self.strengthen_clauses_inprocessing();

        // Rebuild watch lists for any modified clauses
        // This is a simplified approach - in a full implementation,
        // we would track which clauses were removed and update watches incrementally
    }

    /// On-the-fly clause strengthening during inprocessing
    ///
    /// Try to remove literals from clauses by checking if they're redundant.
    /// A literal is redundant if the clause is satisfied when it's assigned to false.
    pub(super) fn strengthen_clauses_inprocessing(&mut self) {
        if self.trail.decision_level() != 0 {
            return;
        }

        let max_clauses_to_strengthen = 50; // Limit to avoid overhead
        let mut strengthened_count = 0;

        // Collect candidate clauses (learned clauses with LBD > 2)
        let mut candidates: Vec<(ClauseId, u32)> = Vec::new();

        for &clause_id in &self.learned_clause_ids {
            if let Some(clause) = self.clauses.get(clause_id)
                && !clause.deleted
                && clause.lits.len() > 3
                && clause.lbd > 2
            {
                candidates.push((clause_id, clause.lbd));
            }
        }

        // Sort by LBD (prioritize higher LBD clauses for strengthening)
        candidates.sort_by_key(|(_, lbd)| core::cmp::Reverse(*lbd));

        for (clause_id, _) in candidates.iter().take(max_clauses_to_strengthen) {
            if strengthened_count >= max_clauses_to_strengthen {
                break;
            }

            let clause_lits = match self.clauses.get(*clause_id) {
                Some(c) if !c.deleted && c.lits.len() > 3 => c.lits.clone(),
                _ => continue,
            };

            // Try to remove each literal by checking if the remaining clause is still valid
            let mut literals_to_remove = Vec::new();

            for (i, &lit) in clause_lits.iter().enumerate() {
                // Save current trail state
                let saved_level = self.trail.decision_level();

                // Try assigning this literal to false
                self.trail.new_decision_level();
                self.trail.assign_decision(lit.negate());

                // Propagate
                let conflict = self.propagate();

                // Backtrack
                self.backtrack(saved_level);

                if conflict.is_some() {
                    // Assigning this literal to false causes a conflict
                    // This means the rest of the clause implies this literal
                    // So this literal can potentially be removed (strengthening)

                    // But we need to be careful: only remove if the remaining clause
                    // is still non-tautological and non-empty
                    let mut remaining: Vec<Lit> = clause_lits
                        .iter()
                        .enumerate()
                        .filter(|(j, _)| *j != i)
                        .map(|(_, &l)| l)
                        .collect();

                    // Check if remaining clause is still valid (at least 2 literals)
                    if remaining.len() >= 2 {
                        // Check it's not a tautology
                        remaining.sort_by_key(|l| l.code());
                        let mut is_tautology = false;
                        for k in 0..remaining.len() - 1 {
                            if remaining[k] == remaining[k + 1].negate() {
                                is_tautology = true;
                                break;
                            }
                        }

                        if !is_tautology {
                            literals_to_remove.push(i);
                            break; // Only remove one literal at a time
                        }
                    }
                }
            }

            // Apply strengthening if we found a literal to remove. The loop
            // above `break`s after the first candidate, so there is at most one
            // — and the removal goes through `strengthen_clause_in_place`, which
            // repairs the watch index when the dropped literal is a watched one
            // (see that function; deleting a watched literal in place is the
            // same broken-index class as freeing a clause id without scrubbing).
            if let Some(&drop_idx) = literals_to_remove.first()
                && let Some((old_lits, new_lits)) =
                    self.strengthen_clause_in_place(*clause_id, drop_idx)
            {
                // DRAT: emit the strengthened clause, then delete the original.
                if self.drat.is_some() {
                    self.drat_add(&new_lits);
                    self.drat_delete(&old_lits);
                }

                // Recompute LBD for the shortened clause.
                let new_lbd = self.compute_lbd(&new_lits);
                if let Some(clause) = self.clauses.get_mut(*clause_id) {
                    clause.lbd = new_lbd;
                }

                strengthened_count += 1;
            }
        }
    }
}

#[cfg(test)]
mod ledger_tests {
    use super::*;
    use crate::literal::{Lit, Var};

    /// Regression: a clause learned *inside* a `push` scope must be removed by
    /// the matching `pop`. The theory-driver learn paths (`learn_clause`,
    /// `add_theory_reason_clause`, the on-the-fly binary in `propagate`) once
    /// added the clause to the DB + `learned_clause_ids` but forgot the per-push
    /// undo ledger, so it survived the `pop` and an unsound conflict on the next
    /// solve reported a spurious `unsat` (verus-fork 2026-06-17: a prior
    /// `(check-sat)` in a pushed scope poisoned a later `(abduce)`). Routing every
    /// add through `track_clause` (recorded in `clause_ledger`, drained on `pop`)
    /// makes the omission unrepresentable; this pins it on the exact bug path.
    #[test]
    fn pop_removes_theory_reason_clause_learned_in_scope() {
        let mut s = Solver::new();
        s.ensure_vars(4);
        // A permanent base clause at level 0.
        assert!(s.add_clause([Lit::pos(Var::new(0)), Lit::pos(Var::new(1))]));
        let base = s.num_clauses();

        s.push();
        // A theory-reason lemma added during an in-scope solve — the path that
        // dropped its ledger record before this fix.
        let _ = s.add_theory_reason_clause(&[Lit::pos(Var::new(2))], Lit::pos(Var::new(3)));
        assert!(
            s.num_clauses() > base,
            "the in-scope theory-reason clause should be in the DB"
        );

        s.pop();
        assert_eq!(
            s.num_clauses(),
            base,
            "pop MUST remove the theory-reason clause learned in the scope; \
             leaving it live poisons the next solve (spurious unsat)"
        );
    }

    /// The base level (no active push) keeps its clauses: `pop` only drains
    /// pushed scopes, never the permanent level-0 prefix.
    #[test]
    fn base_level_clauses_survive() {
        let mut s = Solver::new();
        s.ensure_vars(2);
        assert!(s.add_clause([Lit::pos(Var::new(0)), Lit::neg(Var::new(1))]));
        let base = s.num_clauses();
        // A pop with no matching push is a no-op (guarded by assertion depth).
        s.pop();
        assert_eq!(s.num_clauses(), base, "level-0 clauses are permanent");
    }
}

/// "Would this device have caught the four historical recurrences?"
///
/// Each of the four clause-id-recycle soundness bugs
/// (`reduce_clause_database`, `forget_learned_since`, the assertion-scope
/// `pop` handler, and `check_subsumption` / issue #428) was the same mistake:
/// free a clause id, let the next `add_*` recycle it, and leave the old
/// clause's entry in an id-keyed index behind. Each was fixed by hand, at one
/// call site, four separate times.
///
/// Since [`crate::ClauseIndexScrub`] landed, *writing* that mistake at a
/// solver call site no longer compiles — `ClauseDatabase::remove` will not
/// accept a call that does not name an index sink (there is a `compile_fail`
/// doctest on the trait pinning that). The one way left to express it is to
/// hand the solver's database [`NoClauseIndex`], i.e. to claim in writing that
/// the solver has no watch lists. These tests do exactly that, on the exact
/// shapes the four bugs had, and pin that the runtime backstop in `propagate`
/// catches it at the first use of the corrupted entry — so the escape hatch is
/// covered too, not just the compiler-enforced path.
#[cfg(test)]
mod clause_index_scrub_regressions {
    use super::*;
    use crate::clause::NoClauseIndex;
    use crate::literal::{Lit, Var};

    /// Shape of #428 (`check_subsumption`) and of `reduce_clause_database`:
    /// a **long** clause's id is freed without scrubbing the watch lists, then
    /// recycled by the next add. The recycled clause inherits watchers keyed on
    /// literals it does not contain, and `propagate`'s `!c.deleted` guard waves
    /// them through because the slot is a live clause again — just a different
    /// one.
    #[cfg(debug_assertions)] // the backstop is a `debug_assert!`
    #[test]
    #[should_panic(expected = "stale watcher")]
    fn unscrubbed_long_clause_recycle_is_caught() {
        let mut s = Solver::new();
        s.ensure_vars(6);
        let (a, b, c) = (Var::new(0), Var::new(1), Var::new(2));
        let (d, e) = (Var::new(3), Var::new(4));

        // (a ∨ b ∨ c): watched on `a` and `b`, i.e. watchers parked in
        // watches[¬a] and watches[¬b].
        assert!(s.add_clause([Lit::pos(a), Lit::pos(b), Lit::pos(c)]));
        let victim = ClauseId::new(0);

        // THE BUG, verbatim: free the id, scrub nothing. This is what
        // `check_subsumption` did until #428 — and the only way left to say it.
        s.clauses.remove(victim, &mut NoClauseIndex);

        // The next add pops that id off the free list and overwrites the slot,
        // clearing `deleted`. Now watches[¬a] points at (d ∨ e).
        assert!(s.add_clause([Lit::pos(d), Lit::pos(e)]));

        // Falsify `a` and let propagation walk watches[¬a].
        assert!(s.add_clause([Lit::neg(a)]));
        let _ = s.solve();
    }

    /// Shape of the assertion-scope `pop` handler and of
    /// `forget_learned_since`: a **binary** clause's id is freed without
    /// scrubbing. Worse than the watcher case — `propagate` reads the binary
    /// implication graph with no deleted-clause guard whatsoever, so the leaked
    /// edge fires unconditionally under whatever clause lands on the id.
    #[cfg(debug_assertions)] // the backstop is a `debug_assert!`
    #[test]
    #[should_panic(expected = "stale binary-implication edge")]
    fn unscrubbed_binary_clause_recycle_is_caught() {
        let mut s = Solver::new();
        s.ensure_vars(6);
        let (x, y) = (Var::new(0), Var::new(1));
        let (p, q) = (Var::new(2), Var::new(3));

        // (¬x ∨ y): records the implication x ⇒ y in the binary graph.
        assert!(s.add_clause([Lit::neg(x), Lit::pos(y)]));
        let victim = ClauseId::new(0);

        // THE BUG: free the id, scrub neither the watch lists nor the graph.
        s.clauses.remove(victim, &mut NoClauseIndex);

        // Recycle the id with an unrelated clause ...
        assert!(s.add_clause([Lit::pos(p), Lit::pos(q)]));
        // ... then make `x` true so the leaked x ⇒ y edge is consulted.
        assert!(s.add_clause([Lit::pos(x)]));
        let _ = s.solve();
    }

    /// The same three scenarios, scrubbed properly through the sanctioned path,
    /// must be quiet *and* give the right answer. Without this the two
    /// `should_panic` tests above would also pass if `propagate` panicked
    /// unconditionally.
    #[test]
    fn scrubbed_recycle_is_silent_and_sound() {
        let mut s = Solver::new();
        s.ensure_vars(6);
        let (x, y) = (Var::new(0), Var::new(1));
        let (p, q) = (Var::new(2), Var::new(3));

        assert!(s.add_clause([Lit::neg(x), Lit::pos(y)]));
        // The sanctioned path: scrub + free, in one operation.
        s.scrub_and_remove_clause(ClauseId::new(0));

        assert!(s.add_clause([Lit::pos(p), Lit::pos(q)]));
        assert!(s.add_clause([Lit::pos(x)]));
        assert!(s.add_clause([Lit::neg(y)]));

        // (¬x ∨ y) is gone, so x ∧ ¬y ∧ (p ∨ q) is satisfiable. A leaked edge
        // would have propagated y and fabricated a conflict — spurious UNSAT.
        assert_eq!(s.solve(), SolverResult::Sat);
    }

    /// The fifth instance of the class, found by the new backstop rather than
    /// by a downstream wrong answer: `vivify_clauses` deleted literals from a
    /// clause **in place**, and when the deleted literal was one of the two
    /// watched ones the watcher stayed parked under a literal the clause no
    /// longer contained. `strengthen_clause_in_place` now detaches, mutates and
    /// re-attaches; this pins the repair directly.
    #[test]
    fn in_place_strengthening_repairs_the_watch_index() {
        let mut s = Solver::new();
        s.ensure_vars(4);
        let lits = [
            Lit::pos(Var::new(0)),
            Lit::pos(Var::new(1)),
            Lit::pos(Var::new(2)),
            Lit::pos(Var::new(3)),
        ];
        assert!(s.add_clause(lits));
        let cid = ClauseId::new(0);

        // Drop lits[0] — a WATCHED literal. The old watcher in watches[¬lits[0]]
        // must not survive.
        let (old, new) = s
            .strengthen_clause_in_place(cid, 0)
            .expect("three non-false literals remain, so a legal watch pair exists");
        assert_eq!(old.len(), 4);
        assert_eq!(new.len(), 3);
        assert!(!new.contains(&lits[0]));

        for &l in &old {
            for w in s.watches.get(l.negate()) {
                if w.clause == cid {
                    let held = &s.clauses.get(cid).expect("clause is live").lits;
                    assert!(
                        held.contains(&l.negate().negate()),
                        "watcher for {cid:?} parked in watches[{:?}], but the clause no longer \
                         contains {:?} — the in-place edit left the index dangling",
                        l.negate(),
                        l
                    );
                }
            }
        }

        // And the surviving watchers must be exactly the new lits[0]/lits[1].
        for (i, &l) in new.iter().enumerate() {
            let watched = s
                .watches
                .get(l.negate())
                .iter()
                .any(|w| w.clause == cid);
            assert_eq!(
                watched,
                i < 2,
                "literal {l:?} at index {i} should {}be watched",
                if i < 2 { "" } else { "not " }
            );
        }
    }

    /// Dropping a literal at index ≥ 2 leaves the watched pair untouched, so it
    /// must take the cheap path and change nothing about the index. (This is
    /// the case the original in-place removal always got right; the repair must
    /// not regress it.)
    #[test]
    fn in_place_strengthening_of_an_unwatched_literal_is_cheap_and_correct() {
        let mut s = Solver::new();
        s.ensure_vars(4);
        let lits = [
            Lit::pos(Var::new(0)),
            Lit::pos(Var::new(1)),
            Lit::pos(Var::new(2)),
            Lit::pos(Var::new(3)),
        ];
        assert!(s.add_clause(lits));
        let cid = ClauseId::new(0);

        let (_, new) = s
            .strengthen_clause_in_place(cid, 3)
            .expect("dropping an unwatched literal always succeeds");
        assert_eq!(&new[..2], &lits[..2], "the watched pair is unchanged");
        for &l in &lits[..2] {
            assert!(s.watches.get(l.negate()).iter().any(|w| w.clause == cid));
        }
    }
}

#[cfg(test)]
mod stale_learned_ids {
    use crate::{ClauseId, Lit, Solver, Var};

    fn l(d: i32) -> Lit {
        let v = Var::new(d.unsigned_abs() - 1);
        if d > 0 { Lit::pos(v) } else { Lit::neg(v) }
    }

    /// `check_subsumption` must leave `learned_clause_ids` free of the ids it
    /// just freed.
    ///
    /// Both consumers of that list trust it to name only LEARNED clauses and
    /// neither checks `clause.learned`, so a stale entry that a later `add`
    /// recycles can point the deletion loop at an ORIGINAL clause.
    ///
    /// The path is driven DIRECTLY rather than through the search, because the
    /// search does not reach it: across 263 random 3-SAT and pigeonhole
    /// instances, and 5 larger solves accumulating 13,014 learned clauses,
    /// `deleted_clauses` stayed at 0 — `check_subsumption` never found a
    /// subsumed clause at all. A test that went through `solve()` would pass
    /// while exercising nothing, which is what the first version of this test
    /// did before the counter was added.
    #[test]
    fn check_subsumption_prunes_the_ids_it_frees() {
        let mut s = Solver::new();
        for v in 0..4 {
            let _ = s.new_var();
            let _ = v;
        }
        // A long learned clause, and a short one that subsumes it.
        let long_id = s.clauses.add_learned([l(1), l(2), l(3)]);
        s.learned_clause_ids.push(long_id);
        let short_id = s.clauses.add_learned([l(1), l(2)]);
        s.learned_clause_ids.push(short_id);

        s.check_subsumption(short_id);

        assert!(
            s.clauses.get(long_id).is_some_and(|c| c.deleted),
            "precondition: the subsuming clause should have removed the longer one"
        );
        assert!(
            !s.learned_clause_ids.contains(&long_id),
            "the freed id must not survive in learned_clause_ids: {:?}",
            s.learned_clause_ids
        );
        assert!(
            s.learned_clause_ids.contains(&short_id),
            "the surviving clause must stay listed"
        );
    }

    /// ANTI-VACUITY for the test above: pin that the setup really does drive a
    /// removal, so a future change that stops `check_subsumption` from firing
    /// turns this red instead of leaving a green test that checks nothing.
    #[test]
    fn the_subsumption_path_is_actually_reached() {
        let mut s = Solver::new();
        for _ in 0..4 {
            let _ = s.new_var();
        }
        let long_id = s.clauses.add_learned([l(1), l(2), l(3)]);
        s.learned_clause_ids.push(long_id);
        let short_id = s.clauses.add_learned([l(1), l(2)]);
        s.learned_clause_ids.push(short_id);
        let before = s.stats.deleted_clauses;
        s.check_subsumption(short_id);
        assert!(
            s.stats.deleted_clauses > before,
            "the fixture must exercise a deletion, else the prune test is vacuous"
        );
        let _: ClauseId = long_id;
    }
}

#[cfg(test)]
mod reset_clears_every_id_keyed_structure {
    use crate::{ClauseId, Lit, Solver, Var};

    fn l(d: i32) -> Lit {
        let v = Var::new(d.unsigned_abs() - 1);
        if d > 0 { Lit::pos(v) } else { Lit::neg(v) }
    }

    /// `Solver::reset` re-issues every `ClauseId` from 0 WITHOUT going through
    /// `ClauseDatabase::remove`, so the `ClauseIndexScrub` invariant — which is
    /// what stops a freed id from aliasing — does not apply to it. Its
    /// correctness rests instead on a hand-written list of `.clear()` calls,
    /// and a structure added to the solver but forgotten there would leave
    /// stale ids pointing into a database whose slot 0 is about to be handed to
    /// a completely different clause.
    ///
    /// This pins that list. It cannot enumerate fields automatically, so the
    /// value it adds is a single place where the id-keyed structures are named
    /// together: a sixth one gets registered here, or the omission is invisible
    /// again.
    #[test]
    fn reset_leaves_no_id_keyed_state_behind() {
        let mut s = Solver::new();
        for _ in 0..6 {
            let _ = s.new_var();
        }
        s.add_clause([l(1), l(2), l(3)]);
        s.add_clause([l(-1), l(2), l(4)]);
        s.add_clause([l(-2), l(-3), l(5)]);
        let _ = s.solve();
        // Give the id-keyed structures something to hold.
        let learned = s.clauses.add_learned([l(1), l(-4)]);
        s.learned_clause_ids.push(learned);

        s.reset();

        // (1) the database itself
        assert_eq!(s.clauses.iter_ids().count(), 0, "clause database not emptied");
        // (2) watch lists  (3) binary implication graph
        //     — both are only observable through a re-add, checked below.
        // (4) the trail, which holds `Reason::Propagation(ClauseId)`
        assert_eq!(s.trail.size(), 0, "trail still holds assignments (and their reasons)");
        // (5) the learned-clause id list
        assert!(s.learned_clause_ids.is_empty(), "learned_clause_ids survived reset");
        // (6) the per-push undo ledger
        assert_eq!(s.clause_ledger.as_slice().len(), 0, "clause_ledger survived reset");

        // Ids really do restart, which is what makes a survivor dangerous
        // rather than merely untidy.
        for _ in 0..6 {
            let _ = s.new_var();
        }
        let fresh: ClauseId = s.clauses.add_learned([l(6)]);
        assert_eq!(fresh.index(), 0, "ids must re-issue from 0 after reset");
        // A watcher left over from before would now be attached to THIS clause.
        assert!(
            s.watches.get(l(1).negate()).is_empty() && s.watches.get(l(2).negate()).is_empty(),
            "a stale watcher survived reset and now aliases a recycled id"
        );
    }
}

#[cfg(test)]
mod vivification_switch {
    use crate::{ConfigPreset, SolverConfig};

    /// `enable_vivification` defaults to the behaviour that shipped before the
    /// flag existed, so adding the knob moved no verdict.
    #[test]
    fn the_default_preserves_the_previous_behaviour() {
        assert!(SolverConfig::default().enable_vivification);
    }

    /// And every preset keeps it, so selecting a preset is not a silent way to
    /// turn clause surgery off (or on).
    #[test]
    fn every_preset_keeps_vivification_on() {
        for preset in ConfigPreset::all_presets() {
            assert!(
                preset.config().enable_vivification,
                "{preset:?} preset turned vivification off"
            );
        }
    }

    /// THE POINT OF THE FLAG. Vivification is NOT part of `inprocess()`, so
    /// `enable_inprocessing` does not reach it — which is what made "turn
    /// inprocessing off and no clause surgery happens" false. The two switches
    /// are independent and this pins that they stay so.
    #[test]
    fn inprocessing_and_vivification_are_independent_switches() {
        let d = SolverConfig::default();
        assert!(!d.enable_inprocessing, "inprocessing is off by default");
        assert!(
            d.enable_vivification,
            "yet vivification runs — that is the asymmetry the flag exists to expose"
        );
    }
}
