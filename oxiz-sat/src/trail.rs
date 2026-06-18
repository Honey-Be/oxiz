//! Assignment trail for CDCL solver

use crate::clause::ClauseId;
use crate::literal::{LBool, Lit, Var};
#[allow(unused_imports)]
use crate::prelude::*;
use crate::solver::theory_hooks::TheoryHooks;
use smallvec::SmallVec;

/// A stable handle into the trail's theory-reason store (§4.3 redesign). It indexes
/// a `TheoryReason`; the handle itself is `Copy` so it can live inside the `Copy`
/// `Reason` enum, while the explanation it points at is carried out-of-band.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TheoryReasonId(pub u32);

/// A first-class theory-propagation reason (§4.3). The **asserting** literal is an
/// INPUT carried by value, never a discovered output — so the `Lit::from_code(0)`
/// placeholder leak is unrepresentable. `explanation` is the false-literal set that
/// justifies asserting `asserting`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TheoryReason {
    /// The implied/asserting literal (always present — that is the whole point).
    pub asserting: Lit,
    /// The false literals justifying the propagation/conflict.
    pub explanation: SmallVec<[Lit; 8]>,
}

/// Reason for an assignment
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Reason {
    /// Decision (no antecedent)
    Decision,
    /// Unit propagation from a clause
    Propagation(ClauseId),
    /// Theory propagation (legacy opaque reason; kept for the old `solve_with_theory`
    /// path until Phase 2. The §4.3 redesign uses `TheoryLemma` instead).
    Theory,
    /// Theory propagation with a first-class, typed reason (§4.3): the handle indexes
    /// the trail's theory-reason store, where the asserting literal + explanation live.
    TheoryLemma(TheoryReasonId),
}

/// Information about a variable assignment
#[derive(Debug, Clone, Copy)]
pub struct VarInfo {
    /// Current value
    pub value: LBool,
    /// Decision level at which assigned
    pub level: u32,
    /// Reason for assignment
    pub reason: Reason,
    /// Position in trail
    #[allow(dead_code)]
    pub trail_idx: u32,
}

impl Default for VarInfo {
    fn default() -> Self {
        Self {
            value: LBool::Undef,
            level: 0,
            reason: Reason::Decision,
            trail_idx: 0,
        }
    }
}

/// The assignment trail
pub struct Trail {
    /// Sequence of assigned literals
    assignments: Vec<Lit>,
    /// Information for each variable
    var_info: Vec<VarInfo>,
    /// Indices marking the start of each decision level
    level_starts: Vec<usize>,
    /// Current decision level
    current_level: u32,
    /// Propagation queue head
    prop_head: usize,
    /// Theory-reason store (§4.3): `TheoryLemma(id)` reasons index here. Append-only
    /// within a solve; cleared on `clear`/`reset`.
    theory_reasons: Vec<TheoryReason>,
    /// §4.1 the theory lives ON the trail. When `Some`, the trail fires its hooks
    /// (`push_frame`/`pop_frame`/`assign_hook`/`unassign_hook`) atomically with the
    /// corresponding trail mutation, so the lock-step invariant holds by construction.
    /// `None` (the pure-SAT and legacy `solve_with_theory` paths) ⇒ every hook site
    /// is a no-op and behaviour is unchanged.
    theory: Option<Box<dyn TheoryHooks>>,
}

// `dyn TheoryHooks` is not `Debug`, so `Trail` cannot derive it (mirrors the
// hand-written `Debug` for `SolverConfig`'s boxed `external_branching`).
impl core::fmt::Debug for Trail {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("Trail")
            .field("assignments", &self.assignments)
            .field("var_info", &self.var_info)
            .field("level_starts", &self.level_starts)
            .field("current_level", &self.current_level)
            .field("prop_head", &self.prop_head)
            .field("theory_reasons", &self.theory_reasons)
            .field("theory", &self.theory.as_ref().map(|_| "<dyn TheoryHooks>"))
            .finish()
    }
}

impl Trail {
    /// Create a new trail for n variables
    #[must_use]
    pub fn new(num_vars: usize) -> Self {
        Self {
            assignments: Vec::with_capacity(num_vars),
            var_info: vec![VarInfo::default(); num_vars],
            level_starts: vec![0],
            current_level: 0,
            prop_head: 0,
            theory_reasons: Vec::new(),
            theory: None,
        }
    }

    /// Install a theory on the trail (§4.1). Subsequent level/assignment mutations
    /// fire its hooks atomically. The freshly-installed theory is SYNCED with the
    /// current trail state first — every live decision level is replayed as a
    /// `push_frame` and every existing assignment as an `assign_hook` (in trail
    /// order) — so assignments made before installation (e.g. level-0 units enqueued
    /// while building the formula) are not invisible to the theory.
    pub fn set_theory(&mut self, theory: Box<dyn TheoryHooks>) {
        // Precompute (lit, level) pairs before borrowing `self.theory` mutably.
        let cur = self.current_level;
        let pairs: Vec<(Lit, u32)> = self
            .assignments
            .iter()
            .map(|&lit| (lit, self.var_info[lit.var().index()].level))
            .collect();
        self.theory = Some(theory);
        if let Some(t) = self.theory.as_mut() {
            for lvl in 1..=cur {
                t.push_frame(lvl);
            }
            for (lit, lvl) in pairs {
                let _ = t.assign_hook(lit, lvl);
            }
        }
    }

    /// Borrow the installed theory mutably (for loop-driven calls — `final_check`,
    /// `eval` — that are NOT trail mutations).
    pub fn theory_mut(&mut self) -> Option<&mut (dyn TheoryHooks + 'static)> {
        self.theory.as_deref_mut()
    }

    /// Remove and return the installed theory (e.g. to hand ownership back).
    pub fn take_theory(&mut self) -> Option<Box<dyn TheoryHooks>> {
        self.theory.take()
    }

    /// Record a typed theory reason (§4.3) and return its stable handle.
    pub fn add_theory_reason(&mut self, reason: TheoryReason) -> TheoryReasonId {
        let id = TheoryReasonId(self.theory_reasons.len() as u32);
        self.theory_reasons.push(reason);
        id
    }

    /// Resolve a theory-reason handle to its `TheoryReason`.
    #[must_use]
    pub fn theory_reason(&self, id: TheoryReasonId) -> &TheoryReason {
        &self.theory_reasons[id.0 as usize]
    }

    /// Get the current decision level
    #[must_use]
    pub fn decision_level(&self) -> u32 {
        self.current_level
    }

    /// Get the value of a variable
    #[must_use]
    pub fn value(&self, var: Var) -> LBool {
        self.var_info
            .get(var.index())
            .map_or(LBool::Undef, |v| v.value)
    }

    /// Get the value of a literal
    #[must_use]
    pub fn lit_value(&self, lit: Lit) -> LBool {
        let val = self.value(lit.var());
        if lit.is_pos() { val } else { val.negate() }
    }

    /// Check if a variable is assigned
    #[must_use]
    pub fn is_assigned(&self, var: Var) -> bool {
        self.value(var).is_defined()
    }

    /// Get the level at which a variable was assigned
    #[must_use]
    pub fn level(&self, var: Var) -> u32 {
        self.var_info.get(var.index()).map_or(0, |v| v.level)
    }

    /// Get the reason for a variable's assignment
    #[must_use]
    pub fn reason(&self, var: Var) -> Reason {
        self.var_info
            .get(var.index())
            .map_or(Reason::Decision, |v| v.reason)
    }

    /// Start a new decision level. §4.1: pushes a theory frame ATOMICALLY with the
    /// level bump, so `|frames| == level + 1` holds immediately after. This is the
    /// growth half of the §4 spine — the ONLY writer that pushes a frame, mirroring
    /// `retract_trail_to` which is the only writer that pops one.
    pub fn new_decision_level(&mut self) {
        self.current_level += 1;
        self.level_starts.push(self.assignments.len());
        let lvl = self.current_level;
        if let Some(t) = self.theory.as_mut() {
            t.push_frame(lvl);
        }
    }

    /// Assign a literal as a decision
    pub fn assign_decision(&mut self, lit: Lit) {
        self.assign(lit, Reason::Decision);
    }

    /// Assign a literal due to propagation
    pub fn assign_propagation(&mut self, lit: Lit, clause: ClauseId) {
        self.assign(lit, Reason::Propagation(clause));
    }

    /// Assign a literal due to theory propagation
    pub fn assign_theory(&mut self, lit: Lit) {
        self.assign(lit, Reason::Theory);
    }

    /// Assign a literal due to a typed theory propagation (§4.3). `id` indexes the
    /// theory-reason store (see `add_theory_reason`).
    pub fn assign_theory_lemma(&mut self, lit: Lit, id: TheoryReasonId) {
        self.assign(lit, Reason::TheoryLemma(id));
    }

    fn assign(&mut self, lit: Lit, reason: Reason) {
        let var = lit.var();
        let idx = var.index();

        // Resize if needed
        if idx >= self.var_info.len() {
            self.var_info.resize(idx + 1, VarInfo::default());
        }

        let value = if lit.is_pos() {
            LBool::True
        } else {
            LBool::False
        };

        self.var_info[idx] = VarInfo {
            value,
            level: self.current_level,
            reason,
            trail_idx: self.assignments.len() as u32,
        };

        self.assignments.push(lit);

        // §4.2: fire `assign_hook` once per assignment, in trail order. Phase 1 is
        // final-check-driven: the trail fires the hook so the theory tracks state
        // (and the lock-step invariant is maintained), but the returned `TheoryStep`
        // is not acted on here — `solve_with_hooks` obtains theory propagations and
        // conflicts via `final_check` at each propagation fixpoint. (Eager per-assign
        // theory propagation is a Phase-2 refinement.)
        let lvl = self.current_level;
        if let Some(t) = self.theory.as_mut() {
            let _ = t.assign_hook(lit, lvl);
        }
    }

    /// Get the next literal to propagate (if any)
    pub fn next_to_propagate(&mut self) -> Option<Lit> {
        if self.prop_head < self.assignments.len() {
            let lit = self.assignments[self.prop_head];
            self.prop_head += 1;
            Some(lit)
        } else {
            None
        }
    }

    /// Check if there are literals to propagate
    #[must_use]
    pub fn has_pending_propagation(&self) -> bool {
        self.prop_head < self.assignments.len()
    }

    /// Get the current size of the trail (number of assignments)
    #[must_use]
    pub fn size(&self) -> usize {
        self.assignments.len()
    }

    /// §4 anti-drift spine — the SINGLE trail-shrinking primitive.
    ///
    /// Retract every assignment newer than `target_idx`, then pop one theory frame
    /// for every decision level above `target_level`, ATOMICALLY re-basing the level
    /// bookkeeping so the §4.1 lock-step invariant `|theory frames| ==
    /// decision_level + 1` holds on return. Every shrinking level-writer
    /// (`backtrack_to_with_callback`, `backtrack_to_size`, `clear`) routes through
    /// here, so the hook-firing discipline is written ONCE and cannot drift across
    /// the writers. That is the whole point: the cross-writer desync class (the
    /// `38019b0` consistency-gate / trigger-F family, where one writer popped frames
    /// the other writers forgot — or got the level arithmetic subtly different) is
    /// made structurally unreachable rather than caught by review on each new
    /// writer. (`new_decision_level` is the symmetric growth half — the only writer
    /// that pushes a frame.)
    ///
    /// * `fire_unassign` — fire `unassign_hook` per retracted literal (incremental
    ///   retraction, the instant the literal leaves the trail). `clear` passes
    ///   `false`: a full wipe resets the theory wholesale, not literal-by-literal.
    /// * `on_lit` — the caller's per-retracted-literal callback (phase saving, the
    ///   conflict-analysis literal sink), invoked once per literal in reverse trail
    ///   order before its hook fires.
    fn retract_trail_to(
        &mut self,
        target_idx: usize,
        target_level: u32,
        fire_unassign: bool,
        mut on_lit: impl FnMut(Lit),
    ) {
        debug_assert!(target_idx <= self.assignments.len());
        debug_assert!(target_level <= self.current_level);
        // 1. Retract assignments above `target_idx`, newest-first.
        while self.assignments.len() > target_idx {
            let lit = self
                .assignments
                .pop()
                .expect("assignments non-empty in loop condition");
            let var = lit.var();
            let lvl = self.var_info[var.index()].level;
            self.var_info[var.index()].value = LBool::Undef;
            on_lit(lit);
            if fire_unassign {
                if let Some(t) = self.theory.as_mut() {
                    t.unassign_hook(lit, lvl);
                }
            }
        }
        // 2. Pop one theory frame per crossed decision level (atomic with the move).
        let mut l = self.current_level;
        while l > target_level {
            if let Some(t) = self.theory.as_mut() {
                t.pop_frame(l);
            }
            l -= 1;
        }
        // 3. Re-base the level bookkeeping to `target_level`.
        //    `level_starts[0]` is invariantly 0, so `truncate(target_level + 1)`
        //    leaves exactly the surviving levels (and `[0]` when target_level == 0).
        self.level_starts.truncate((target_level + 1) as usize);
        self.current_level = target_level;
        self.prop_head = self.assignments.len();
    }

    /// Backtrack to a specific trail size (number of assignments)
    /// This is useful for incremental solving where we want to restore
    /// the exact state at a push point. Resets to decision level 0 (the push
    /// baseline); routes through the `retract_trail_to` spine so the
    /// frame-pop / unassign discipline is the same one every writer uses.
    pub fn backtrack_to_size(&mut self, target_size: usize) {
        self.retract_trail_to(target_size, 0, true, |_| {});
    }

    /// Backtrack to a given decision level
    pub fn backtrack_to(&mut self, level: u32) {
        self.backtrack_to_with_callback(level, |_| {});
    }

    /// Backtrack to a given decision level, calling the callback for each unassigned
    /// literal. Routes through the `retract_trail_to` spine (fires `unassign_hook`
    /// per retracted literal + one `pop_frame` per crossed level).
    pub fn backtrack_to_with_callback<F>(&mut self, level: u32, callback: F)
    where
        F: FnMut(Lit),
    {
        if level >= self.current_level {
            return;
        }
        let target_idx = self.level_starts[(level + 1) as usize];
        self.retract_trail_to(target_idx, level, true, callback);
    }

    /// Get the number of assigned variables
    #[must_use]
    pub fn num_assigned(&self) -> usize {
        self.assignments.len()
    }

    /// Get all assignments
    #[must_use]
    pub fn assignments(&self) -> &[Lit] {
        &self.assignments
    }

    /// Get assignments at current level
    #[must_use]
    pub fn level_assignments(&self) -> &[Lit] {
        let start = *self.level_starts.last().unwrap_or(&0);
        &self.assignments[start..]
    }

    /// Resize to support more variables
    pub fn resize(&mut self, num_vars: usize) {
        if num_vars > self.var_info.len() {
            self.var_info.resize(num_vars, VarInfo::default());
        }
    }

    /// Clear the trail completely. Full reset to decision level 0; routes through
    /// the `retract_trail_to` spine with `fire_unassign = false` — a wipe resets the
    /// theory wholesale (every frame popped to the root) rather than retracting
    /// literal-by-literal. The theory-reason store is cleared too (it is owned by
    /// the trail and meaningless once the trail is empty).
    pub fn clear(&mut self) {
        self.retract_trail_to(0, 0, false, |_| {});
        self.theory_reasons.clear();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::solver::theory_hooks::TheoryStep;

    /// A counting toy theory that maintains its own frame stack + assign/unassign
    /// counters, so a test can assert the §4.1 lock-step invariant directly.
    #[derive(Default)]
    struct CountingTheory {
        frames: u32,         // number of frames currently on the toy stack
        assigns: u32,
        unassigns: u32,
        pushes: u32,
        pops: u32,
    }

    impl TheoryHooks for CountingTheory {
        fn assign_hook(&mut self, _lit: Lit, _level: u32) -> TheoryStep {
            self.assigns += 1;
            TheoryStep::Ok
        }
        fn unassign_hook(&mut self, _lit: Lit, _level: u32) {
            self.unassigns += 1;
        }
        fn push_frame(&mut self, _level: u32) {
            self.frames += 1;
            self.pushes += 1;
        }
        fn pop_frame(&mut self, _level: u32) {
            self.frames -= 1;
            self.pops += 1;
        }
        fn final_check(&mut self) -> TheoryStep {
            TheoryStep::Ok
        }
        fn eval(&mut self, _atom: Var) -> Option<bool> {
            None
        }
    }

    /// The §4.1 lock-step invariant `|theory frames| == decision_level + 1` holds
    /// after EVERY level mutation — including the two hook-bypassing writers
    /// (`backtrack_to_size`, `clear`) that the Verus model proves desync an
    /// un-hooked trail. The toy theory starts with one root frame (matching the
    /// trail's initial level 0).
    #[test]
    fn test_lockstep_invariant_all_writers() {
        let mut trail = Trail::new(8);
        // Seed the toy frame count to 1 so it mirrors `level 0 ⇒ 1 frame`. From here
        // the invariant `frames == level + 1` is witnessed by the ABSENCE of a
        // `pop_frame` underflow: `CountingTheory::pop_frame` does `self.frames -= 1`,
        // which panics in debug if ever called more often than `push_frame` — i.e.
        // exactly when the frame stack desyncs from the decision level.
        let mut theory = Box::new(CountingTheory::default());
        theory.frames = 1; // root frame for level 0
        trail.set_theory(theory);

        for _ in 0..4 {
            trail.new_decision_level();
        }
        assert_eq!(trail.decision_level(), 4);
        trail.assign_decision(Lit::from_dimacs(1));
        trail.new_decision_level();
        trail.assign_decision(Lit::from_dimacs(2));
        assert_eq!(trail.decision_level(), 5);

        trail.backtrack_to(2); // pops levels 5,4,3 → frames must follow
        assert_eq!(trail.decision_level(), 2);

        trail.new_decision_level();
        trail.assign_decision(Lit::from_dimacs(3));
        trail.backtrack_to_size(0); // the bypass writer → must pop frames to root
        assert_eq!(trail.decision_level(), 0);

        trail.new_decision_level();
        trail.clear(); // the other bypass writer → must pop frames to root
        assert_eq!(trail.decision_level(), 0);
        // Reaching here without a debug `pop_frame` underflow panic witnesses that
        // the toy theory's frame count stayed == level + 1 throughout.
    }

    /// Stronger than the underflow check above: assert `|frames| == decision_level
    /// + 1` EXPLICITLY after each writer. `CountingTheory::pop_frame`'s `frames -= 1`
    /// underflow only catches OVER-popping; an UNDER-pop (a writer that forgets to
    /// pop a crossed frame — exactly the 38019b0 / trigger-F desync, where stale
    /// frames linger above the new level) leaves `frames > level + 1` and slips past
    /// it. Routing every shrinking writer through the single `retract_trail_to`
    /// spine makes both directions impossible; this witnesses it for all four.
    #[test]
    fn test_lockstep_frames_equal_level_plus_one() {
        use core::any::Any;
        let mut trail = Trail::new(8);
        let mut theory = Box::new(CountingTheory::default());
        theory.frames = 1; // root frame for level 0
        trail.set_theory(theory);

        fn frames(trail: &mut Trail) -> u32 {
            let any: &mut dyn Any = trail.theory_mut().expect("theory installed");
            any.downcast_mut::<CountingTheory>()
                .expect("CountingTheory")
                .frames
        }
        macro_rules! check {
            () => {{
                let lvl = trail.decision_level();
                assert_eq!(frames(&mut trail), lvl + 1, "frames must equal level + 1");
            }};
        }

        check!(); // level 0 → 1 frame
        for _ in 0..3 {
            trail.new_decision_level();
        }
        trail.assign_decision(Lit::from_dimacs(1));
        check!(); // level 3 → 4 frames

        // backtrack_to_with_callback: pop exactly the crossed frames.
        trail.backtrack_to_with_callback(1, |_| {});
        check!(); // level 1 → 2 frames

        // backtrack_to_size: the incremental-restore bypass writer.
        trail.new_decision_level();
        trail.assign_decision(Lit::from_dimacs(2));
        trail.backtrack_to_size(0);
        check!(); // level 0 → 1 frame

        // clear: the wholesale-wipe bypass writer.
        trail.new_decision_level();
        trail.new_decision_level();
        trail.clear();
        check!(); // level 0 → 1 frame
    }

    #[test]
    fn test_typed_theory_reason_roundtrip() {
        let mut trail = Trail::new(4);
        let r = TheoryReason {
            asserting: Lit::from_dimacs(3),
            explanation: smallvec::smallvec![Lit::from_dimacs(-1), Lit::from_dimacs(2)],
        };
        let id = trail.add_theory_reason(r.clone());
        assert_eq!(trail.theory_reason(id), &r);
        assert_eq!(trail.theory_reason(id).asserting, Lit::from_dimacs(3));
    }

    #[test]
    fn test_trail_basic() {
        let mut trail = Trail::new(5);

        assert_eq!(trail.decision_level(), 0);
        assert!(!trail.is_assigned(Var::new(0)));

        trail.new_decision_level();
        trail.assign_decision(Lit::pos(Var::new(0)));

        assert_eq!(trail.decision_level(), 1);
        assert!(trail.is_assigned(Var::new(0)));
        assert!(trail.lit_value(Lit::pos(Var::new(0))).is_true());
        assert!(trail.lit_value(Lit::neg(Var::new(0))).is_false());
    }

    #[test]
    fn test_trail_backtrack() {
        let mut trail = Trail::new(5);

        trail.new_decision_level();
        trail.assign_decision(Lit::pos(Var::new(0)));

        trail.new_decision_level();
        trail.assign_decision(Lit::neg(Var::new(1)));

        assert_eq!(trail.decision_level(), 2);
        assert_eq!(trail.num_assigned(), 2);

        trail.backtrack_to(1);

        assert_eq!(trail.decision_level(), 1);
        assert_eq!(trail.num_assigned(), 1);
        assert!(trail.is_assigned(Var::new(0)));
        assert!(!trail.is_assigned(Var::new(1)));
    }

    #[test]
    fn test_trail_propagation() {
        let mut trail = Trail::new(5);

        trail.new_decision_level();
        trail.assign_decision(Lit::pos(Var::new(0)));
        trail.assign_propagation(Lit::neg(Var::new(1)), ClauseId::new(0));

        assert!(trail.has_pending_propagation());
        assert_eq!(trail.next_to_propagate(), Some(Lit::pos(Var::new(0))));
        assert_eq!(trail.next_to_propagate(), Some(Lit::neg(Var::new(1))));
        assert!(!trail.has_pending_propagation());
    }
}
