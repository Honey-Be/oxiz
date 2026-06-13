//! Conflict analysis, clause minimization, and assumption handling

use super::*;
use smallvec::SmallVec;

/// Instrumentation for the theory-conflict placeholder leak (feature `theory-probe`).
///
/// `analyze_theory_conflict` initialises `learnt[0]` to `Lit::from_code(0)` (the
/// positive literal of variable 0) as a placeholder, and only overwrites it when a
/// UIP `p` is found. If the trail-walk ends with `p == None` the placeholder leaks
/// into the returned learned clause. This module counts how often that happens so a
/// fuzz harness can decide whether the leak is reachable in practice.
#[cfg(feature = "theory-probe")]
pub mod theory_probe {
    use core::cell::Cell;

    thread_local! {
        /// Number of analyze_theory_conflict calls.
        static CALLS: Cell<u64> = const { Cell::new(0) };
        /// Number of calls that reached the `p == None` (no-UIP) branch — the
        /// structural precondition for the placeholder leak (some conflict lit at
        /// 0 < lvl < cur, none at cur, and not all at level 0).
        static NO_UIP: Cell<u64> = const { Cell::new(0) };
        /// Number of calls whose RETURNED learned clause still contained the var-0
        /// placeholder `Lit::from_code(0)`. This is the actual leak. Post-fix: 0.
        static PLACEHOLDER_IN_CLAUSE: Cell<u64> = const { Cell::new(0) };
        /// Number of calls that took neither the all-level-0 early return nor the
        /// UIP loop because the current-level conflict-literal count was zero.
        static ZERO_COUNTER_NONROOT: Cell<u64> = const { Cell::new(0) };
    }

    /// Reset all counters to zero.
    pub fn reset() {
        CALLS.with(|c| c.set(0));
        NO_UIP.with(|c| c.set(0));
        PLACEHOLDER_IN_CLAUSE.with(|c| c.set(0));
        ZERO_COUNTER_NONROOT.with(|c| c.set(0));
    }

    pub(super) fn note_call() {
        CALLS.with(|c| c.set(c.get() + 1));
    }

    pub(super) fn note_no_uip() {
        NO_UIP.with(|c| c.set(c.get() + 1));
    }

    pub(super) fn note_placeholder_in_clause() {
        PLACEHOLDER_IN_CLAUSE.with(|c| c.set(c.get() + 1));
    }

    pub(super) fn note_zero_counter_nonroot() {
        ZERO_COUNTER_NONROOT.with(|c| c.set(c.get() + 1));
    }

    /// Snapshot of all counters.
    #[must_use]
    pub fn snapshot() -> Snapshot {
        Snapshot {
            calls: CALLS.with(Cell::get),
            no_uip: NO_UIP.with(Cell::get),
            placeholder_in_clause: PLACEHOLDER_IN_CLAUSE.with(Cell::get),
            zero_counter_nonroot: ZERO_COUNTER_NONROOT.with(Cell::get),
        }
    }

    /// Counters captured by [`snapshot`].
    #[derive(Debug, Clone, Copy)]
    pub struct Snapshot {
        /// Total `analyze_theory_conflict` calls.
        pub calls: u64,
        /// Calls that hit the no-UIP (`p == None`) branch.
        pub no_uip: u64,
        /// Calls whose returned clause still held the var-0 placeholder (the leak).
        pub placeholder_in_clause: u64,
        /// Calls with zero current-level conflict literals (leak precondition).
        pub zero_counter_nonroot: u64,
    }
}

/// Compute LBD (Literals per Block Distance / "glue" score) from a set of clause literals.
///
/// LBD = number of distinct decision levels among the literals, excluding level 0.
/// Level-0 literals are excluded because they are consequences of unit propagation at the
/// root level and are always true — they do not contribute to the "block distance" that
/// measures how spread across the search tree a learned clause is.
///
/// This is an O(n) computation with no heap allocation in the common case
/// (`SmallVec<[u32; 32]>` avoids a heap allocation for clauses up to 32 distinct decision
/// levels, which covers the overwhelming majority of real CDCL learned clauses).
///
/// This is the standard Glucose/MiniSat LBD definition applied to the **actual learned
/// (1-UIP) clause literals**, so the value it returns satisfies `lbd <= literals.len()`.
/// It is a pure function (no shared scratch state) so it can be called at sites where a
/// `&mut self` borrow of the solver is unavailable — in particular after `self.learnt`
/// has been finalized but while `&self.trail` is borrowed to fire the external hook.
fn compute_lbd_from_literals(literals: &[Lit], trail: &Trail) -> u32 {
    let mut levels: SmallVec<[u32; 32]> = SmallVec::new();
    for &lit in literals {
        let level = trail.level(lit.var());
        if level > 0 && !levels.contains(&level) {
            levels.push(level);
        }
    }
    levels.len() as u32
}

impl Solver {
    /// Analyze conflict and learn clause
    pub(super) fn analyze(&mut self, conflict: ClauseId) -> (u32, SmallVec<[Lit; 16]>) {
        // Debug: print conflict info (only with analyze-debug feature)
        #[cfg(feature = "analyze-debug")]
        if self.num_vars <= 5 {
            eprintln!("[ANALYZE] Conflict clause id={:?}", conflict);
            if let Some(c) = self.clauses.get(conflict) {
                let lits_str: Vec<String> = c
                    .lits
                    .iter()
                    .map(|lit| {
                        let val = self.trail.lit_value(*lit);
                        let level = self.trail.level(lit.var());
                        let sign = if lit.is_pos() { "" } else { "~" };
                        format!("{}v{}@{}={:?}", sign, lit.var().index(), level, val)
                    })
                    .collect();
                eprintln!("[ANALYZE] Conflict clause: ({})", lits_str.join(" | "));
            }
            eprintln!("[ANALYZE] Trail:");
            for &lit in self.trail.assignments() {
                let var = lit.var();
                let level = self.trail.level(var);
                let reason = self.trail.reason(var);
                let sign = if lit.is_pos() { "" } else { "~" };
                eprintln!("  {}v{}@{} reason={:?}", sign, var.index(), level, reason);
            }
        }

        let current_level = self.trail.decision_level();

        // SOUNDNESS GUARD for a DEGENERATE conflict — one with NO literal at the
        // current decision level. The textbook 1-UIP analysis below assumes the
        // standard CDCL invariant "every conflict has ≥1 literal at the current
        // level" (that is how the conflicting propagation arose). In CDCL(T) that
        // invariant can be broken: theory propagation/learning installs assignments
        // at lower levels that falsify an original clause, and the conflict only
        // surfaces (via watched-literal propagation) once the engine is already at a
        // higher decision level. Running the UIP walk on such a conflict fabricates
        // garbage — an arbitrary `p`, duplicated literals (e.g. `[-1, -1]`), or a
        // unit contradicting a level-0 unit — and yields an UNSOUND verdict
        // (spurious SAT/UNSAT, with the returned model violating an input clause).
        //
        // Handle it directly and soundly. The conflict clause C is fully falsified.
        // The learned clause is exactly C (its literals, deduplicated); it is
        // trivially entailed (C is an original/learned clause of the formula). We
        // backtrack to one below the highest level present in C so that the
        // highest-level literal becomes the single unassigned (asserting) literal.
        // See the regression test `theory_callback_fuzz::regress_bool_analyze_all_level0_sat`.
        if let Some(c) = self.clauses.get(conflict) {
            let no_current_level = c
                .lits
                .iter()
                .all(|&lit| self.trail.level(lit.var()) != current_level);
            if !c.lits.is_empty() && no_current_level {
                // Deduplicate while preserving the clause literals.
                let mut uniq: SmallVec<[Lit; 16]> = SmallVec::new();
                for &lit in &c.lits {
                    if !uniq.contains(&lit) {
                        uniq.push(lit);
                    }
                }
                // All literals at level 0 ⇒ a level-0 contradiction ⇒ UNSAT.
                if uniq.iter().all(|&lit| self.trail.level(lit.var()) == 0) {
                    self.learnt.clear();
                    return (0, SmallVec::new());
                }
                // Otherwise: put the highest-level literal at index 0 (asserting),
                // and backtrack to the SECOND-highest level so it goes unit there.
                let mut hi_idx = 0;
                let mut hi_lvl = self.trail.level(uniq[0].var());
                for i in 1..uniq.len() {
                    let lvl = self.trail.level(uniq[i].var());
                    if lvl > hi_lvl {
                        hi_lvl = lvl;
                        hi_idx = i;
                    }
                }
                uniq.swap(0, hi_idx);
                // Put the SECOND-highest-level literal at index 1. `learn_clause`
                // watches lits[0]/lits[1] and asserts lits[0]; for the two-watched-
                // literal invariant to survive future backtracks the second watch
                // must be the highest-level literal among the rest — exactly the
                // `swap(1, max_idx)` the normal 1-UIP path performs. Without this the
                // clause could later be fully falsified without a watch firing (a
                // missed conflict ⇒ unsound SAT), so we arrange it explicitly here.
                let mut second = 0;
                let mut second_idx = 1;
                for i in 1..uniq.len() {
                    let lvl = self.trail.level(uniq[i].var());
                    if lvl > second {
                        second = lvl;
                        second_idx = i;
                    }
                }
                if uniq.len() >= 2 {
                    uniq.swap(1, second_idx);
                }
                self.learnt.clear();
                self.learnt.extend(uniq.iter().copied());
                return (second, self.learnt.clone());
            }
        }

        self.learnt.clear();
        self.learnt.push(Lit::from_code(0)); // Placeholder for asserting literal

        let mut counter = 0;
        let mut p = None;
        let mut index = self.trail.assignments().len();

        // Reset seen flags
        for s in &mut self.seen {
            *s = false;
        }

        // Collect variables to bump in batch (avoids repeated heap sift-ups)
        let mut vars_to_bump: SmallVec<[Var; 32]> = SmallVec::new();

        let mut reason_clause = conflict;

        while let Some(clause) = self.clauses.get(reason_clause) {
            // Process reason clause (must exist, as it's either conflict or a propagation reason)
            let is_learned = clause.learned;

            // Record clause usage for tier promotion and bump activity (if it's a learned clause)
            if is_learned && let Some(clause_mut) = self.clauses.get_mut(reason_clause) {
                clause_mut.record_usage();
                // Promote to Core if LBD ≤ 2 (GLUE clause)
                if clause_mut.lbd <= 2 {
                    clause_mut.promote_to_core();
                }
                // Bump clause activity (MapleSAT-style)
                clause_mut.activity += self.clause_bump_increment;
            }

            let Some(clause) = self.clauses.get(reason_clause) else {
                break;
            };
            // Process EVERY literal of the reason clause; the pivot `p` being
            // resolved is already `seen` (it was selected off the trail because
            // `seen[p]` is true), so the `!seen` guard below skips it.  We must
            // NOT skip `lits[0]` by index: oxiz does not guarantee a propagation
            // reason clause keeps its implied literal at index 0, so skipping
            // index 0 dropped a current-level antecedent → undercounted
            // `counter` → the trail walk stopped at a non-dominating literal and
            // learned an unsound unit clause (spurious UNSAT). See the regression
            // test `soundness_repro::minimal_spurious_unsat_default_config`.
            for &lit in &clause.lits {
                let var = lit.var();
                let level = self.trail.level(var);

                if !self.seen[var.index()] && level > 0 {
                    self.seen[var.index()] = true;
                    // Collect variable for batch bumping instead of individual bumps
                    vars_to_bump.push(var);

                    if level == current_level {
                        counter += 1;
                    } else {
                        // Add the literal itself (not negated) to the learned clause.
                        // The conflict clause has all literals FALSE. To prevent this
                        // conflict, we need at least one of these literals to become TRUE.
                        self.learnt.push(lit);
                    }
                }
            }

            // Find next literal to analyze
            let mut current_lit = Lit::from_code(0); // sentinel default
            let mut found_next = false;
            loop {
                if index == 0 {
                    // Guard against underflow: this should not happen in a
                    // well-formed conflict, but theory-conflict injection can
                    // occasionally produce a degenerate state.  Break out to
                    // avoid a usize overflow panic.
                    break;
                }
                index -= 1;
                current_lit = self.trail.assignments()[index];
                p = Some(current_lit);
                if self.seen[current_lit.var().index()] {
                    found_next = true;
                    break;
                }
            }
            if !found_next {
                break;
            }

            counter -= 1;
            if counter == 0 {
                break;
            }

            let var = current_lit.var();
            match self.trail.reason(var) {
                Reason::Propagation(c) => reason_clause = c,
                _ => break,
            }
        }

        // Batch bump all collected variables at once (single heap rebuild)
        self.vsids.bump_batch(&vars_to_bump);
        self.chb.bump_batch(&vars_to_bump);
        self.lrb.on_reason_batch(&vars_to_bump);

        // Set asserting literal (p is guaranteed to be Some at this point)
        if let Some(lit) = p {
            self.learnt[0] = lit.negate();
        }

        // Minimize learnt clause using recursive resolution
        self.minimize_learnt_clause();

        // Compute the real LBD from the FINAL learned (1-UIP) clause literals.
        // This is the standard Glucose definition: the number of distinct decision
        // levels in the learned clause itself (level 0 excluded), not the larger
        // `vars_to_bump` set. It is computed AFTER minimization so it reflects the
        // exact clause that will be stored, and therefore satisfies lbd <= clause len.
        let lbd = compute_lbd_from_literals(&self.learnt, &self.trail);

        // Notify external heuristic of each conflict-involved variable with the
        // learned-clause LBD score.
        if let Some(ref ext) = self.config.external_branching
            && let Ok(mut h) = ext.lock()
        {
            for &var in &vars_to_bump {
                h.on_conflict_var_with_lbd(var, lbd);
            }
        }

        // Calculate assertion level (traditional backtrack level)
        let assertion_level = if self.learnt.len() == 1 {
            0
        } else {
            // Find second highest level
            let mut max_level = 0;
            let mut max_idx = 1;
            for (i, &lit) in self.learnt.iter().enumerate().skip(1) {
                let level = self.trail.level(lit.var());
                if level > max_level {
                    max_level = level;
                    max_idx = i;
                }
            }
            // Move second watch to position 1
            self.learnt.swap(1, max_idx);
            max_level
        };

        // Apply chronological backtracking if enabled
        let backtrack_level = self.chrono_backtrack.compute_backtrack_level(
            &self.trail,
            &self.learnt,
            assertion_level,
        );

        // Track chronological vs non-chronological backtracks
        if backtrack_level != assertion_level {
            self.stats.chrono_backtracks += 1;
        } else {
            self.stats.non_chrono_backtracks += 1;
        }

        // Debug: print learned clause (only with analyze-debug feature)
        #[cfg(feature = "analyze-debug")]
        if self.num_vars <= 5 {
            let lits_str: Vec<String> = self
                .learnt
                .iter()
                .map(|lit| {
                    let sign = if lit.is_pos() { "" } else { "~" };
                    format!("{}v{}", sign, lit.var().index())
                })
                .collect();
            eprintln!(
                "[ANALYZE] Learned clause: ({}), backtrack_level={}",
                lits_str.join(" | "),
                backtrack_level
            );
        }

        (backtrack_level, self.learnt.clone())
    }

    /// Minimize the learned clause by removing redundant literals
    ///
    /// A literal can be removed if it is implied by the remaining literals.
    /// We use a recursive check: a literal l is redundant if its reason clause
    /// contains only literals that are either:
    /// - Already in the learnt clause (marked as seen)
    /// - At decision level 0 (always true in the learned clause context)
    /// - Themselves redundant (recursive check)
    ///
    /// This also performs clause strengthening by checking for stronger implications
    pub(super) fn minimize_learnt_clause(&mut self) {
        if self.learnt.len() <= 2 {
            // Don't minimize very small clauses
            return;
        }

        let original_len = self.learnt.len();

        // Mark all literals in the learned clause as "in clause"
        // We use analyze_stack to track literals to check
        self.analyze_stack.clear();

        // Phase 1: Basic minimization - remove redundant literals
        let mut j = 1; // Write position
        for i in 1..self.learnt.len() {
            let lit = self.learnt[i];
            if self.lit_is_redundant(lit) {
                // Skip this literal (it's redundant)
            } else {
                // Keep this literal
                self.learnt[j] = lit;
                j += 1;
            }
        }
        self.learnt.truncate(j);

        // Phase 2: Clause strengthening - check for self-subsuming resolution
        // If the clause contains both l and ~l' where l' is in a reason clause,
        // we might be able to strengthen the clause
        self.strengthen_learnt_clause();

        // Track minimization statistics
        let final_len = self.learnt.len();
        if final_len < original_len {
            self.stats.minimizations += 1;
            self.stats.literals_removed += (original_len - final_len) as u64;
        }
    }

    /// Strengthen the learned clause using on-the-fly self-subsuming resolution
    pub(super) fn strengthen_learnt_clause(&mut self) {
        if self.learnt.len() <= 2 {
            return;
        }

        // Check each literal to see if we can strengthen by resolution
        let mut j = 1;
        for i in 1..self.learnt.len() {
            let lit = self.learnt[i];
            let var = lit.var();

            // Check if this literal can be strengthened
            if let Reason::Propagation(reason_id) = self.trail.reason(var)
                && let Some(reason_clause) = self.clauses.get(reason_id)
                && reason_clause.lits.len() == 2
            {
                // Binary reason: one literal is lit, the other is the implied literal
                let other_lit = if reason_clause.lits[0] == lit.negate() {
                    reason_clause.lits[1]
                } else if reason_clause.lits[1] == lit.negate() {
                    reason_clause.lits[0]
                } else {
                    // Keep the literal
                    self.learnt[j] = lit;
                    j += 1;
                    continue;
                };

                // If other_lit is already in the learned clause at level 0,
                // we can remove lit
                if self.trail.level(other_lit.var()) == 0 && self.seen[other_lit.var().index()] {
                    // Skip this literal (strengthened)
                    continue;
                }
            }

            // Keep this literal
            self.learnt[j] = lit;
            j += 1;
        }
        self.learnt.truncate(j);
    }

    /// Check if a literal is redundant in the learned clause
    ///
    /// A literal is redundant if its reason clause only contains:
    /// - Literals marked as seen (in the learned clause)
    /// - Literals at decision level 0
    /// - Literals that are themselves redundant (recursive)
    pub(super) fn lit_is_redundant(&mut self, lit: Lit) -> bool {
        let var = lit.var();

        // Decision variables and theory propagations are not redundant
        let reason = match self.trail.reason(var) {
            Reason::Decision => return false,
            Reason::Theory => return false, // Theory propagations can't be minimized
            Reason::TheoryLemma(_) => return false, // typed theory reason — same
            Reason::Propagation(c) => c,
        };

        let reason_clause = match self.clauses.get(reason) {
            Some(c) => c,
            None => return false,
        };

        // Check all literals in the reason clause
        for &reason_lit in &reason_clause.lits {
            if reason_lit == lit.negate() {
                // Skip the literal we're analyzing
                continue;
            }

            let reason_var = reason_lit.var();

            // Level 0 literals are always OK
            if self.trail.level(reason_var) == 0 {
                continue;
            }

            // If the literal is in the learned clause (seen), it's OK
            if self.seen[reason_var.index()] {
                continue;
            }

            // Otherwise, this literal prevents minimization
            // (A full recursive check would be more powerful but more expensive)
            return false;
        }

        true
    }

    /// Analyze a theory conflict (given as a list of literals that are all false)
    pub(super) fn analyze_theory_conflict(
        &mut self,
        conflict_lits: &[Lit],
    ) -> (u32, SmallVec<[Lit; 16]>) {
        #[cfg(feature = "theory-probe")]
        theory_probe::note_call();

        self.learnt.clear();
        self.learnt.push(Lit::from_code(0)); // Placeholder

        let mut counter = 0;
        let current_level = self.trail.decision_level();

        // Reset seen flags
        for s in &mut self.seen {
            *s = false;
        }

        // Collect variables for batch bumping
        let mut vars_to_bump: SmallVec<[Var; 32]> = SmallVec::new();

        // Process conflict literals
        let mut all_level_zero = true;
        for &lit in conflict_lits {
            let var = lit.var();
            let level = self.trail.level(var);

            if !self.seen[var.index()] && level > 0 {
                all_level_zero = false;
                self.seen[var.index()] = true;
                vars_to_bump.push(var);

                if level == current_level {
                    counter += 1;
                } else {
                    // Add the literal itself (not negated) to the learned clause.
                    // The conflict clause has all literals FALSE. To prevent this
                    // conflict, we need at least one of these literals to become TRUE.
                    // So we add the literal directly to the learned clause.
                    self.learnt.push(lit);
                }
            }
        }

        // If ALL conflict literals are at level 0, this is a fundamental UNSAT
        // that cannot be resolved by backtracking. Return an empty learned clause
        // with backtrack_level=0 as a signal.
        if !conflict_lits.is_empty() && all_level_zero {
            return (0, SmallVec::new());
        }

        // Instrumentation: counter == 0 here (with not-all-level-0) is the exact
        // structural precondition for the placeholder leak — the UIP loop below is
        // skipped, so `p` stays None and learnt[0] keeps Lit::from_code(0).
        #[cfg(feature = "theory-probe")]
        if counter == 0 {
            theory_probe::note_zero_counter_nonroot();
        }

        // Find UIP by walking back through trail
        let mut index = self.trail.assignments().len();
        let mut p = None;

        while counter > 0 {
            if index == 0 {
                break; // Avoid underflow — no more trail entries
            }
            index -= 1;
            if index >= self.trail.assignments().len() {
                break; // Guard against stale length
            }
            let current_lit = self.trail.assignments()[index];
            p = Some(current_lit);
            let var = current_lit.var();

            if self.seen[var.index()] {
                counter -= 1;

                if counter > 0
                    && let Reason::Propagation(reason_clause) = self.trail.reason(var)
                    && let Some(clause) = self.clauses.get(reason_clause)
                {
                    // Get reason and process EVERY literal: the pivot `var` is
                    // already `seen` so the guard below skips it.  Do NOT skip
                    // `lits[0]` by index — oxiz does not guarantee a propagation
                    // reason keeps its implied literal at index 0 (the same
                    // defect just fixed in the Boolean `analyze`); skipping it
                    // dropped a current-level antecedent → undercounted
                    // `counter` → an unsound theory-conflict learned clause.
                    for &lit in &clause.lits {
                        let reason_var = lit.var();
                        let level = self.trail.level(reason_var);

                        if !self.seen[reason_var.index()] && level > 0 {
                            self.seen[reason_var.index()] = true;
                            vars_to_bump.push(reason_var);

                            if level == current_level {
                                counter += 1;
                            } else {
                                // Add the literal itself to the learned clause
                                self.learnt.push(lit);
                            }
                        }
                    }
                }
            }
        }

        // Batch bump all collected variables
        self.vsids.bump_batch(&vars_to_bump);
        self.chb.bump_batch(&vars_to_bump);
        self.lrb.on_reason_batch(&vars_to_bump);

        // Set asserting literal.
        //
        // If a UIP `p` was found, slot 0 becomes its negation (the asserting
        // literal). If NO UIP was found (`p == None`), the `while counter > 0`
        // loop never ran — this happens when no conflict literal is at the current
        // decision level (yet not all are at level 0, which returned early above).
        // In that case slot 0 still holds the `Lit::from_code(0)` placeholder; it
        // is NOT a real literal of the conflict and MUST NOT survive: leaving it
        // would (a) put a bogus var-0 literal into the learned clause and (b) make
        // learn_clause assign it as a spurious propagation. Drop the placeholder
        // slot; the genuine learned clause is exactly the below-current-level
        // conflict literals already collected in `learnt[1..]`.
        if let Some(uip) = p {
            self.learnt[0] = uip.negate();
        } else {
            #[cfg(feature = "theory-probe")]
            theory_probe::note_no_uip();
            // Remove the placeholder at index 0 (cheap: swap with last then pop).
            if !self.learnt.is_empty() {
                let last = self.learnt.len() - 1;
                self.learnt.swap(0, last);
                self.learnt.pop();
            }
            // If that emptied the clause, every conflict literal was filtered out
            // (all level 0) — signal fundamental UNSAT, matching the early return.
            if self.learnt.is_empty() {
                return (0, SmallVec::new());
            }
            // Make slot 0 the HIGHEST-level literal of the clause so it becomes the
            // asserting literal after backtracking. (With no current-level UIP,
            // every literal is below the current level; the highest of them is the
            // one to flip — the clause goes unit on it once we backtrack below its
            // level, which the backtrack-level computation below arranges.)
            let mut hi_idx = 0;
            let mut hi_lvl = self.trail.level(self.learnt[0].var());
            for i in 1..self.learnt.len() {
                let lvl = self.trail.level(self.learnt[i].var());
                if lvl > hi_lvl {
                    hi_lvl = lvl;
                    hi_idx = i;
                }
            }
            self.learnt.swap(0, hi_idx);
        }

        // Minimize
        self.minimize_learnt_clause();

        // Compute the real LBD from the FINAL learned clause literals (post-minimization),
        // matching the standard Glucose definition rather than using the larger
        // `vars_to_bump` proxy. For theory conflicts the learned clause shape may differ
        // from Boolean conflicts, but the distinct-decision-level count of the actual
        // learned clause is the correct glue score and never exceeds the clause length.
        let lbd = compute_lbd_from_literals(&self.learnt, &self.trail);

        // Notify external heuristic of each conflict-involved variable with the
        // learned-clause LBD score.
        if let Some(ref ext) = self.config.external_branching
            && let Ok(mut h) = ext.lock()
        {
            for &var in &vars_to_bump {
                h.on_conflict_var_with_lbd(var, lbd);
            }
        }

        // Calculate backtrack level
        let backtrack_level = if self.learnt.len() == 1 {
            0
        } else {
            let mut max_level = 0;
            let mut max_idx = 1;
            for (i, &lit) in self.learnt.iter().enumerate().skip(1) {
                let level = self.trail.level(lit.var());
                if level > max_level {
                    max_level = level;
                    max_idx = i;
                }
            }
            self.learnt.swap(1, max_idx);
            max_level
        };

        // True-leak detector: does the var-0 placeholder `Lit::from_code(0)` still
        // appear in the clause we are about to return? Post-fix this must be 0 (the
        // placeholder is removed). Pre-fix it fired whenever p == None. This is the
        // metric that distinguishes "no-UIP path taken" from "placeholder leaked".
        #[cfg(feature = "theory-probe")]
        if self.learnt.iter().any(|&l| l == Lit::from_code(0)) {
            theory_probe::note_placeholder_in_clause();
        }

        (backtrack_level, self.learnt.clone())
    }

    /// Extract a core of assumptions that caused a conflict
    pub(super) fn extract_assumption_core(
        &self,
        assumptions: &[Lit],
        conflict_idx: usize,
    ) -> Vec<Lit> {
        // The conflicting assumption and any assumptions it depends on
        let mut core = Vec::new();
        let conflict_lit = assumptions[conflict_idx];

        // Find assumptions that led to this conflict
        for &lit in &assumptions[..=conflict_idx] {
            if self.seen.get(lit.var().index()).copied().unwrap_or(false) || lit == conflict_lit {
                core.push(lit);
            }
        }

        // If core is empty, just return the conflicting assumption
        if core.is_empty() {
            core.push(conflict_lit);
        }

        core
    }

    /// Analyze conflict to find assumptions in the unsat core
    pub(super) fn analyze_assumption_conflict(&mut self, assumptions: &[Lit]) -> Vec<Lit> {
        // Use seen flags to mark which assumptions are in the conflict
        let mut core = Vec::new();

        // Walk back through the trail to find conflicting assumptions
        for &lit in assumptions {
            let var = lit.var();
            if var.index() < self.trail.assignments().len() {
                let value = self.trail.lit_value(lit);
                // If the negation of an assumption is implied, it's in the core
                if value.is_false() || self.seen.get(var.index()).copied().unwrap_or(false) {
                    core.push(lit);
                }
            }
        }

        // If no specific core found, return all assumptions
        if core.is_empty() {
            core.extend(assumptions.iter().copied());
        }

        core
    }

    /// Get the minimum backtrack level for a conflict
    pub(super) fn analyze_conflict_level(&self, conflict: ClauseId) -> u32 {
        let clause = match self.clauses.get(conflict) {
            Some(c) => c,
            None => return 0,
        };

        let mut min_level = u32::MAX;
        for lit in clause.lits.iter().copied() {
            let level = self.trail.level(lit.var());
            if level > 0 && level < min_level {
                min_level = level;
            }
        }

        if min_level == u32::MAX { 0 } else { min_level }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::trail::Trail;

    // ---------------------------------------------------------------------------
    // Tests for compute_lbd_from_literals
    // ---------------------------------------------------------------------------

    #[test]
    fn test_compute_lbd_all_same_level() {
        // Three literals whose vars are all assigned at level 3 → LBD = 1.
        let n = 4;
        let mut trail = Trail::new(n);
        // Level 0 is implicit; push 3 levels.
        trail.new_decision_level(); // → level 1
        trail.new_decision_level(); // → level 2
        trail.new_decision_level(); // → level 3

        let v0 = Var::new(0);
        let v1 = Var::new(1);
        let v2 = Var::new(2);
        trail.assign_decision(Lit::pos(v0));
        trail.assign_decision(Lit::pos(v1));
        trail.assign_decision(Lit::pos(v2));

        let lits = [Lit::pos(v0), Lit::neg(v1), Lit::pos(v2)];
        let lbd = compute_lbd_from_literals(&lits, &trail);
        assert_eq!(lbd, 1, "all literals at same level → LBD should be 1");
    }

    #[test]
    fn test_compute_lbd_distinct_levels() {
        // Three literals at levels 1, 2, 3 → LBD = 3.
        let n = 4;
        let mut trail = Trail::new(n);

        let v0 = Var::new(0);
        let v1 = Var::new(1);
        let v2 = Var::new(2);

        trail.new_decision_level(); // → level 1
        trail.assign_decision(Lit::pos(v0));

        trail.new_decision_level(); // → level 2
        trail.assign_decision(Lit::pos(v1));

        trail.new_decision_level(); // → level 3
        trail.assign_decision(Lit::pos(v2));

        let lits = [Lit::pos(v0), Lit::pos(v1), Lit::neg(v2)];
        let lbd = compute_lbd_from_literals(&lits, &trail);
        assert_eq!(lbd, 3, "literals at levels 1, 2, 3 → LBD should be 3");
    }

    #[test]
    fn test_compute_lbd_excludes_level_zero() {
        // Literals: one var at level 0 (unit prop), two at level 2 → LBD = 1.
        // Level-0 variables must not be counted.
        let n = 4;
        let mut trail = Trail::new(n);

        let v0 = Var::new(0); // Will be at level 0
        let v1 = Var::new(1); // Will be at level 2
        let v2 = Var::new(2); // Will be at level 2

        // Assign v0 at level 0 (root decision level, no new_decision_level call).
        trail.assign_decision(Lit::pos(v0));

        trail.new_decision_level(); // → level 1 (unused)
        trail.new_decision_level(); // → level 2
        trail.assign_decision(Lit::pos(v1));
        trail.assign_decision(Lit::pos(v2));

        let lits = [Lit::pos(v0), Lit::pos(v1), Lit::pos(v2)];
        let lbd = compute_lbd_from_literals(&lits, &trail);
        assert_eq!(
            lbd, 1,
            "level-0 var must be excluded; only level-2 vars count → LBD = 1"
        );
    }

    #[test]
    fn test_compute_lbd_mixed_duplicates_and_zero() {
        // v0 @ level 0 (excluded), v1 @ level 2, v2 @ level 4, v3 @ level 2 (duplicate)
        // → distinct non-zero levels: {2, 4} → LBD = 2.
        let n = 5;
        let mut trail = Trail::new(n);

        let v0 = Var::new(0);
        let v1 = Var::new(1);
        let v2 = Var::new(2);
        let v3 = Var::new(3);

        trail.assign_decision(Lit::pos(v0)); // level 0

        trail.new_decision_level(); // → 1
        trail.new_decision_level(); // → 2
        trail.assign_decision(Lit::pos(v1));
        trail.assign_decision(Lit::pos(v3));

        trail.new_decision_level(); // → 3
        trail.new_decision_level(); // → 4
        trail.assign_decision(Lit::pos(v2));

        let lits = [Lit::pos(v0), Lit::pos(v1), Lit::neg(v2), Lit::pos(v3)];
        let lbd = compute_lbd_from_literals(&lits, &trail);
        assert_eq!(lbd, 2, "levels {{2, 4}} → LBD = 2");
    }

    #[test]
    fn test_compute_lbd_empty_literals() {
        // Empty literal set → LBD = 0.
        let trail = Trail::new(0);
        let lits: [Lit; 0] = [];
        let lbd = compute_lbd_from_literals(&lits, &trail);
        assert_eq!(lbd, 0, "empty literal set → LBD = 0");
    }

    // ---------------------------------------------------------------------------
    // Integration test: conflict analysis passes LBD to the external hook
    // ---------------------------------------------------------------------------

    #[test]
    fn test_conflict_analysis_passes_lbd_to_hook() {
        // Solve PHP(3,2) — the same UNSAT formula used in the external_branching tests.
        // A ConflictLbdRecordingHeuristic records all LBD values received via
        // on_conflict_var_with_lbd.  After solving, assert:
        //   1. at least one call was made (conflicts happened)
        //   2. all recorded LBD values are > 0 (no degenerate LBD-0 passed through)
        use crate::solver::heuristic::BranchingHeuristic;
        use crate::{Solver, SolverConfig, SolverResult};
        use std::sync::{Arc, Mutex};

        struct ConflictLbdRecordingHeuristic {
            lbd_values: Arc<Mutex<Vec<u32>>>,
        }

        impl BranchingHeuristic for ConflictLbdRecordingHeuristic {
            fn select(&mut self, _candidates: &[Var], _scores: &[f64]) -> Option<Var> {
                None // always defer — VSIDS drives the solve
            }

            fn on_conflict_var_with_lbd(&mut self, _var: Var, lbd: u32) {
                self.lbd_values
                    .lock()
                    .unwrap_or_else(|e| e.into_inner())
                    .push(lbd);
            }
        }

        let lbd_values: Arc<Mutex<Vec<u32>>> = Arc::new(Mutex::new(Vec::new()));
        let heuristic = Arc::new(Mutex::new(ConflictLbdRecordingHeuristic {
            lbd_values: Arc::clone(&lbd_values),
        }));

        let config = SolverConfig {
            external_branching: Some(heuristic),
            ..SolverConfig::default()
        };
        let mut solver = Solver::with_config(config);

        // PHP(3,2): 6 variables
        for _ in 0..6 {
            solver.new_var();
        }
        // Each pigeon must be in at least one hole
        solver.add_clause_dimacs(&[1, 2]);
        solver.add_clause_dimacs(&[3, 4]);
        solver.add_clause_dimacs(&[5, 6]);
        // At most one pigeon per hole
        solver.add_clause_dimacs(&[-1, -3]);
        solver.add_clause_dimacs(&[-1, -5]);
        solver.add_clause_dimacs(&[-3, -5]);
        solver.add_clause_dimacs(&[-2, -4]);
        solver.add_clause_dimacs(&[-2, -6]);
        solver.add_clause_dimacs(&[-4, -6]);

        let result = solver.solve();
        assert_eq!(result, SolverResult::Unsat, "PHP(3,2) must be UNSAT");

        let values = lbd_values.lock().unwrap_or_else(|e| e.into_inner());
        assert!(
            !values.is_empty(),
            "on_conflict_var_with_lbd must have been called at least once"
        );
        for &lbd in values.iter() {
            assert!(
                lbd > 0,
                "LBD passed to hook must be > 0 (got {lbd}); level-0 vars should be excluded"
            );
        }
    }

    #[test]
    fn test_lbd_matches_learned_clause_glue() {
        // The LBD passed to the hook must be the glue score of the ACTUAL learned
        // (1-UIP) clause — i.e. the distinct decision-level count of `self.learnt` —
        // NOT the distinct-level count of the larger `vars_to_bump` union.
        //
        // We solve a crafted UNSAT instance with clause deletion effectively disabled
        // so every learned clause persists. The hook records the set of LBD values it
        // receives; the solver stores `clause.lbd` (computed independently in
        // learn.rs::compute_lbd from the same final clause). Since a 1-UIP learned
        // clause never contains level-0 literals, the two definitions coincide, so the
        // set of hook LBDs must be a SUBSET of the stored learned-clause LBD set
        // (plus 1 for unit learned clauses, whose single literal sits at the current
        // decision level). The old `vars_to_bump` proxy would routinely report values
        // ABSENT from any stored clause's LBD, so a subset relation is decisive.
        use crate::solver::heuristic::BranchingHeuristic;
        use crate::{Solver, SolverConfig, SolverResult};
        use std::collections::BTreeSet;
        use std::sync::{Arc, Mutex};

        struct SetRecordingHeuristic {
            lbd_set: Arc<Mutex<BTreeSet<u32>>>,
        }

        impl BranchingHeuristic for SetRecordingHeuristic {
            fn select(&mut self, _candidates: &[Var], _scores: &[f64]) -> Option<Var> {
                None
            }

            fn on_conflict_var_with_lbd(&mut self, _var: Var, lbd: u32) {
                self.lbd_set
                    .lock()
                    .unwrap_or_else(|e| e.into_inner())
                    .insert(lbd);
            }
        }

        let lbd_set: Arc<Mutex<BTreeSet<u32>>> = Arc::new(Mutex::new(BTreeSet::new()));
        let heuristic = Arc::new(Mutex::new(SetRecordingHeuristic {
            lbd_set: Arc::clone(&lbd_set),
        }));

        let config = SolverConfig {
            external_branching: Some(heuristic),
            // Disable clause deletion so every learned clause survives for inspection.
            clause_deletion_threshold: usize::MAX,
            ..SolverConfig::default()
        };
        let mut solver = Solver::with_config(config);

        // PHP(3,2): 6 variables, UNSAT, produces multi-level conflicts.
        for _ in 0..6 {
            solver.new_var();
        }
        solver.add_clause_dimacs(&[1, 2]);
        solver.add_clause_dimacs(&[3, 4]);
        solver.add_clause_dimacs(&[5, 6]);
        solver.add_clause_dimacs(&[-1, -3]);
        solver.add_clause_dimacs(&[-1, -5]);
        solver.add_clause_dimacs(&[-3, -5]);
        solver.add_clause_dimacs(&[-2, -4]);
        solver.add_clause_dimacs(&[-2, -6]);
        solver.add_clause_dimacs(&[-4, -6]);

        let result = solver.solve();
        assert_eq!(result, SolverResult::Unsat, "PHP(3,2) must be UNSAT");

        // Gather the LBD of every surviving learned clause from the solver's
        // internal database (these fields are crate-visible). Unit learned clauses
        // (len == 1) keep the default lbd 0 but their hook LBD is 1, so we add 1 for
        // every unit clause to the allowed set.
        let mut stored_lbds: BTreeSet<u32> = BTreeSet::new();
        for &cid in &solver.learned_clause_ids {
            if let Some(clause) = solver.clauses.get(cid) {
                if clause.lits.len() == 1 {
                    stored_lbds.insert(1);
                } else {
                    stored_lbds.insert(clause.lbd);
                }
            }
        }

        let hook_lbds = lbd_set.lock().unwrap_or_else(|e| e.into_inner());
        assert!(!hook_lbds.is_empty(), "hook must have received LBD values");

        // Decisive check: every LBD the hook reported is the glue score of a real
        // learned clause (subset relation). With the old vars_to_bump proxy this
        // would fail because vars_to_bump-derived LBDs exceed any stored clause's LBD.
        for &lbd in hook_lbds.iter() {
            assert!(
                stored_lbds.contains(&lbd),
                "hook LBD {lbd} must match the glue score of an actual learned clause; \
                 stored learned-clause LBDs = {stored_lbds:?}"
            );
        }
    }

    #[test]
    fn test_lbd_le_clause_size() {
        // The LBD of a learned clause can never exceed its literal count: each literal
        // contributes at most one distinct decision level. The fix computes LBD from
        // the actual learned clause, so this invariant must hold for the value handed
        // to the hook (unlike the old vars_to_bump proxy, which could exceed the clause
        // length). We verify it on every surviving learned clause and also confirm the
        // hook never reported an LBD larger than the largest learned clause.
        use crate::solver::heuristic::BranchingHeuristic;
        use crate::{Solver, SolverConfig, SolverResult};
        use std::sync::{Arc, Mutex};

        struct MaxRecordingHeuristic {
            max_lbd: Arc<Mutex<u32>>,
        }

        impl BranchingHeuristic for MaxRecordingHeuristic {
            fn select(&mut self, _candidates: &[Var], _scores: &[f64]) -> Option<Var> {
                None
            }

            fn on_conflict_var_with_lbd(&mut self, _var: Var, lbd: u32) {
                let mut m = self.max_lbd.lock().unwrap_or_else(|e| e.into_inner());
                if lbd > *m {
                    *m = lbd;
                }
            }
        }

        let max_lbd: Arc<Mutex<u32>> = Arc::new(Mutex::new(0));
        let heuristic = Arc::new(Mutex::new(MaxRecordingHeuristic {
            max_lbd: Arc::clone(&max_lbd),
        }));

        let config = SolverConfig {
            external_branching: Some(heuristic),
            clause_deletion_threshold: usize::MAX,
            ..SolverConfig::default()
        };
        let mut solver = Solver::with_config(config);

        // PHP(4,3): 12 variables, UNSAT, deeper search → larger learned clauses.
        for _ in 0..12 {
            solver.new_var();
        }
        // Each of 4 pigeons in at least one of 3 holes (pigeon p, hole h → var 3*(p-1)+h).
        solver.add_clause_dimacs(&[1, 2, 3]);
        solver.add_clause_dimacs(&[4, 5, 6]);
        solver.add_clause_dimacs(&[7, 8, 9]);
        solver.add_clause_dimacs(&[10, 11, 12]);
        // At most one pigeon per hole (for each hole h, no two pigeons share it).
        for hole in 0..3 {
            let h = hole + 1;
            let occupants = [h, h + 3, h + 6, h + 9];
            for i in 0..occupants.len() {
                for j in (i + 1)..occupants.len() {
                    solver.add_clause_dimacs(&[-occupants[i], -occupants[j]]);
                }
            }
        }

        let result = solver.solve();
        assert_eq!(result, SolverResult::Unsat, "PHP(4,3) must be UNSAT");

        // Invariant on every surviving learned clause: lbd <= number of literals.
        let mut max_learnt_len: usize = 0;
        for &cid in &solver.learned_clause_ids {
            if let Some(clause) = solver.clauses.get(cid) {
                let len = clause.lits.len();
                max_learnt_len = max_learnt_len.max(len);
                // Unit clauses store the default lbd 0; the invariant lbd <= len is
                // trivially satisfied. For len >= 2 the stored lbd was computed from
                // the clause literals and must not exceed the literal count.
                assert!(
                    clause.lbd as usize <= len,
                    "learned clause LBD {} exceeds its literal count {len}",
                    clause.lbd
                );
            }
        }

        let observed_max = *max_lbd.lock().unwrap_or_else(|e| e.into_inner());
        assert!(observed_max > 0, "hook must have received a positive LBD");
        assert!(
            observed_max as usize <= max_learnt_len,
            "max hook LBD {observed_max} must not exceed the largest learned clause length \
             {max_learnt_len} — proves LBD is computed from the learned clause, not vars_to_bump"
        );
    }
}
