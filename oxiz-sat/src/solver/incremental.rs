//! Incremental-probe state management.
//!
//! These helpers let a caller that drives the solver *incrementally* — asserting
//! more clauses and calling [`Solver::solve`] repeatedly — roll the search state
//! back to the committed (asserted) prefix after each probe.  They exist for the
//! bit-vector theory's embedded solver (`BvSolver::check`), whose probe pattern
//! exposes two ways a probe's residue can otherwise stay behind and turn a
//! genuinely-satisfiable formula into a false `Unsat`: the satisfying model left
//! on the trail (see [`Solver::restore_to_trail_size`]) and clauses learned while
//! an unjustified level-0 unit constraint was on the trail (see
//! [`Solver::forget_learned_since`]).

use super::*;

impl Solver {
    /// Number of learned clauses currently tracked.
    ///
    /// Paired with [`Self::forget_learned_since`] to let an incremental caller
    /// drop exactly the clauses a single [`Self::solve`] added.
    #[must_use]
    pub fn learned_clause_count(&self) -> usize {
        self.learned_clause_ids.len()
    }

    /// Forget every learned clause recorded after `checkpoint`
    /// (a value previously returned by [`Self::learned_clause_count`]).
    ///
    /// Clause learning in CDCL is normally a sound optimisation, but the
    /// bit-vector theory drives this SAT solver *incrementally* in a way that
    /// breaks that invariant: `assert_const` / `assert_eq` install their unit
    /// constraints as level-0 trail assignments with `reason = Decision` and
    /// **no backing clause**.  Conflict analysis treats such a level-0 literal
    /// as an unjustified decision, so a clause learned while it is on the trail
    /// silently depends on it; once [`Self::restore_to_trail_size`] rolls that
    /// assignment off the trail at the end of a probe, the retained learned
    /// clause is missing a hypothesis and can spuriously force `Unsat` on the
    /// next probe.  `BvSolver::check()` therefore discards each probe's learned
    /// clauses, keeping only the asserted (original) clauses as the sound,
    /// reusable core.
    pub fn forget_learned_since(&mut self, checkpoint: usize) {
        if checkpoint >= self.learned_clause_ids.len() {
            return;
        }
        let to_remove: Vec<ClauseId> = self.learned_clause_ids.split_off(checkpoint);
        for id in to_remove {
            // Detach every watcher that still references this clause BEFORE freeing
            // its slot.  `ClauseDatabase::remove` pushes the id onto a free list
            // that the next `add_*` recycles, and recycling clears the slot's
            // `deleted` flag — so `propagate`'s "skip deleted clause" guard cannot
            // catch a stale watcher once the id is reused.  Here the id is freed
            // and then *immediately* reused by the next incremental `add_clause`
            // (e.g. the bit-vector theory asserting the next constraint) with no
            // intervening propagation to lazily clean the stale watchers, so the
            // recycled clause would inherit the forgotten clause's watchers and
            // mis-propagate — a spurious conflict that turns a SAT query UNSAT
            // (regression: `bv_mul_aux_disjunction_const_is_sat_8bit`).  A clause's
            // (at most two) watchers live in the watch lists of the negations of
            // its own literals, so scrubbing `~l` for every literal `l` removes
            // them regardless of which pair is currently watched.
            // `self.clauses` and `self.watches` are DISJOINT fields, so the
            // immutable borrow of the clause (to read its literals) and the
            // mutable borrow of the watch lists coexist without copying the
            // literals out — `Lit` is `Copy`, so `negate()` is itself free.
            if let Some(clause) = self.clauses.get(id) {
                for &lit in &clause.lits {
                    self.watches.remove_clause(lit.negate(), id);
                }
            }
            // DRAT: log the deletion (learned clauses only) before removal.
            self.drat_delete_clause_id(id);
            self.clauses.remove(id);
        }
    }

    /// Current trail size (number of assigned literals across all levels).
    ///
    /// Combined with [`Self::restore_to_trail_size`] this lets an incremental
    /// caller (e.g. the bit-vector theory's embedded solver) snapshot the
    /// committed assignment prefix before a [`Self::solve`] call and roll the
    /// trail back to it afterwards, discarding every search-derived assignment
    /// the solve added (decisions, propagations, learned-unit assignments).
    #[must_use]
    pub fn trail_size(&self) -> usize {
        self.trail.size()
    }

    /// Roll the trail back to a previously captured [`Self::trail_size`].
    ///
    /// This unassigns every literal added after `trail_size` (re-inserting the
    /// freed variables into the decision heaps so a later solve can branch on
    /// them again) and resets the decision level to 0.  It does **not** touch
    /// the clause database, so all originally-asserted constraints — and any
    /// clauses learned so far — remain in force; only the working assignment is
    /// reset to the committed prefix.
    ///
    /// Crucially this is how `BvSolver::check()` avoids letting one
    /// satisfiability probe leave a *model-specific* (and therefore unsound for
    /// the next, augmented, probe) assignment pinned at decision level 0:
    /// `solve()` does not reset the persisted trail on entry, so without this
    /// rollback the model chosen for probe *k* (including its level-0 decisions)
    /// would survive into probe *k+1* and could spuriously contradict a freshly
    /// asserted constraint, yielding a false `Unsat`.
    pub fn restore_to_trail_size(&mut self, trail_size: usize) {
        let current_size = self.trail.size();
        if current_size <= trail_size {
            // Nothing search-derived to discard; just make sure we are at the
            // root decision level so the next solve starts cleanly.
            self.backtrack_with_phase_saving(0);
            return;
        }

        // Collect the variables that will be unassigned so they can be put back
        // into the decision heaps (mirrors the bookkeeping in `pop`).
        let mut unassigned_vars: Vec<Var> = Vec::with_capacity(current_size - trail_size);
        let assignments = self.trail.assignments();
        for &lit in &assignments[trail_size..current_size] {
            unassigned_vars.push(lit.var());
        }

        // `backtrack_to_size` clears the values and resets the level to 0 but
        // does not re-insert the freed variables into the decision heaps.
        self.trail.backtrack_to_size(trail_size);

        for var in unassigned_vars {
            if !self.vsids.contains(var) {
                self.vsids.insert(var);
            }
            if !self.chb.contains(var) {
                self.chb.insert(var);
            }
            self.lrb.unassign(var);
        }
    }
}
