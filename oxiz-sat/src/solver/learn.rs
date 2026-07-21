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
                    to_remove.push(cid);
                }
            }
        }

        // Remove subsumed clauses
        for cid in to_remove {
            // Detach every watcher that still references this clause BEFORE
            // freeing its slot — see the identical scrub in
            // `reduce_clause_database`/`forget_learned_since`/the assertion-
            // pop handler for the full mechanism: `ClauseDatabase::remove`
            // pushes the id onto a free list the next `add_*` recycles,
            // clearing the slot's `deleted` flag, so `propagate`'s "skip
            // deleted clause" guard cannot catch a stale watcher once the id
            // is reused — the recycled clause silently inherits the deleted
            // clause's watchers and mis-propagates (the exact false-`unsat`
            // mechanism regression #428 covers: `check_subsumption` was the
            // one clause-removal site in this module that never scrubbed).
            // A subsumed candidate here always has `lits.len() >= 3` (the
            // `clause.lits.len() < new_clause.len()` guard above combined
            // with `check_subsumption` only being called for `learnt_clause.
            // len() >= 3` learned clauses rules out binary candidates), so a
            // `binary_graph` scrub is currently unreachable dead weight —
            // included anyway, mirroring the sibling call sites' `is_binary`
            // guard, so this stays correct if that invariant ever changes.
            if let Some(clause) = self.clauses.get(cid) {
                let is_binary = clause.lits.len() == 2;
                for &lit in &clause.lits {
                    self.watches.remove_clause(lit.negate(), cid);
                    if is_binary {
                        self.binary_graph.remove(lit.negate(), cid);
                    }
                }
            }
            // DRAT: log the deletion (learned clauses only) before removal.
            self.drat_delete_clause_id(cid);
            self.clauses.remove(cid);
            self.stats.deleted_clauses += 1;
        }
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

        for (cid, _) in core_candidates.iter().take(num_core_delete) {
            // Detach every watcher that still references this clause BEFORE
            // freeing its slot — see the identical scrub in
            // `forget_learned_since` for the full mechanism: `ClauseDatabase::
            // remove` pushes the id onto a free list the next `add_*` recycles,
            // clearing the slot's `deleted` flag, so `propagate`'s "skip deleted
            // clause" guard cannot catch a stale watcher once the id is reused —
            // the recycled clause silently inherits the deleted clause's
            // watchers and mis-propagates (the exact spurious-SAT mechanism
            // that regression covers, reachable here too since this ordinary
            // GC path recycles ids the same way). Track clause size for memory
            // pool accounting before removal.
            if let Some(clause) = self.clauses.get(*cid) {
                let num_lits = clause.lits.len();
                for &lit in &clause.lits {
                    self.watches.remove_clause(lit.negate(), *cid);
                }
                let buf = self.memory_optimizer.allocate(num_lits);
                self.memory_optimizer.free(buf, num_lits);
            }
            // DRAT: log the deletion (learned clauses only) before removal.
            self.drat_delete_clause_id(*cid);
            self.clauses.remove(*cid);
            self.stats.deleted_clauses += 1;
        }

        for (cid, _) in mid_candidates.iter().take(num_mid_delete) {
            if let Some(clause) = self.clauses.get(*cid) {
                let num_lits = clause.lits.len();
                for &lit in &clause.lits {
                    self.watches.remove_clause(lit.negate(), *cid);
                }
                let buf = self.memory_optimizer.allocate(num_lits);
                self.memory_optimizer.free(buf, num_lits);
            }
            self.drat_delete_clause_id(*cid);
            self.clauses.remove(*cid);
            self.stats.deleted_clauses += 1;
        }

        for (cid, _) in local_candidates.iter().take(num_local_delete) {
            if let Some(clause) = self.clauses.get(*cid) {
                let num_lits = clause.lits.len();
                for &lit in &clause.lits {
                    self.watches.remove_clause(lit.negate(), *cid);
                }
                let buf = self.memory_optimizer.allocate(num_lits);
                self.memory_optimizer.free(buf, num_lits);
            }
            self.drat_delete_clause_id(*cid);
            self.clauses.remove(*cid);
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

                if conflict
                    && let Some(clause) = self.clauses.get_mut(clause_id)
                    && clause.lits.len() > 2
                {
                    // The literal at skip_idx is implied by the rest
                    // We can remove it from the clause (vivification succeeded).
                    // DRAT models an in-place strengthening as delete-old +
                    // add-new: capture both literal sets, then (after the mutable
                    // borrow ends) emit `d old` followed by `new`. The DRAT
                    // helpers no-op unless DRAT is enabled, so this is free in
                    // the default build.
                    let old_lits: SmallVec<[Lit; 16]> = clause.lits.iter().copied().collect();
                    clause.lits.remove(skip_idx);
                    let new_lits: SmallVec<[Lit; 16]> = clause.lits.iter().copied().collect();
                    vivified_count += 1;
                    if self.drat.is_some() {
                        // Add the strengthened clause first, then delete the
                        // original. Ordering does not matter for drat-trim's
                        // backward check, but add-then-delete keeps the active
                        // set consistent at every prefix.
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

            // Apply strengthening if we found literals to remove
            if !literals_to_remove.is_empty() {
                // First, remove literals
                let mut old_lits: SmallVec<[Lit; 16]> = SmallVec::new();
                if let Some(clause) = self.clauses.get_mut(*clause_id) {
                    // DRAT: capture the pre-mutation literal set so we can emit
                    // delete-old + add-new (an in-place strengthening).
                    old_lits = clause.lits.iter().copied().collect();
                    // Remove literals in reverse order to preserve indices
                    for &idx in literals_to_remove.iter().rev() {
                        if idx < clause.lits.len() {
                            clause.lits.remove(idx);
                        }
                    }
                }

                // DRAT: emit the strengthened clause, then delete the original.
                if self.drat.is_some() {
                    let new_lits: SmallVec<[Lit; 16]> = match self.clauses.get(*clause_id) {
                        Some(c) => c.lits.iter().copied().collect(),
                        None => SmallVec::new(),
                    };
                    self.drat_add(&new_lits);
                    self.drat_delete(&old_lits);
                }

                // Then, recompute LBD (after the mutable borrow ends)
                if let Some(clause) = self.clauses.get(*clause_id) {
                    let lits_clone = clause.lits.clone();
                    let new_lbd = self.compute_lbd(&lits_clone);

                    // Now update the LBD
                    if let Some(clause) = self.clauses.get_mut(*clause_id) {
                        clause.lbd = new_lbd;
                    }

                    strengthened_count += 1;
                }
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
