//! §4.2 the mandatory, trail-driven `TheoryHooks` contract.
//!
//! This replaces (in the new `solve_with_hooks` path) the advisory `TheoryCallback`
//! (`on_assignment`/`final_check`/`on_new_level`[default-empty]/`on_backtrack`),
//! whose desync failure mode the redesign eliminates by construction. The two
//! "level" hooks (`push_frame`/`pop_frame`) and the two "assignment" hooks
//! (`assign_hook`/`unassign_hook`) are fired BY THE TRAIL from inside its level- and
//! assignment-mutators (see `trail.rs`), not by the solve loop — so:
//!
//!   * `|theory frames| == decision_level + 1` holds after every trail mutation
//!     (the §4.1 lock-step invariant the Verus model proves), and
//!   * each assign/unassign is delivered exactly once, in trail order, so the old
//!     `theory_processed` re-scan/dedup index is unnecessary.
//!
//! All hook methods take `Lit`/`level` by value (Copy), so a theory implementation
//! never borrows the trail — that is what lets the trail own the theory and still
//! call its hooks without aliasing.
use crate::literal::{Lit, Var};
use crate::trail::TheoryReason;
use smallvec::SmallVec;

/// The only ways a theory can respond to a hook. A `Propagate` always carries a
/// first-class `TheoryReason` whose asserting literal is non-null by construction
/// (§4.3); a `Conflict` carries the (non-empty) false-literal set directly — the
/// shape `analyze_theory_conflict` consumes.
pub enum TheoryStep {
    /// Nothing to report.
    Ok,
    /// Force `lit` true, justified by `reason` (a unit-implying explanation;
    /// `reason.asserting == lit`).
    Propagate { lit: Lit, reason: TheoryReason },
    /// The current partial assignment is theory-inconsistent; the literals are the
    /// (currently all-false) conflict clause to learn from.
    Conflict { explanation: SmallVec<[Lit; 8]> },
}

/// The trait a theory implements. The ENGINE owns the calling discipline.
///
/// `Send + Sync` so that a `Trail` (and therefore a `Solver`) carrying an installed
/// theory stays `Send + Sync` — the `oxiz-theories` `Theory` trait and the parallel
/// engine require it. Every concrete theory is single-threaded data, so this is free.
/// `Any` so `solve_with_hooks` can hand the CONCRETE theory back to the caller
/// (downcast the returned `Box<dyn TheoryHooks>`) — used by the SMT path to recover
/// its owned EUF/arith/bv solvers after a solve.
pub trait TheoryHooks: Send + Sync + core::any::Any {
    /// Fired once per newly-assigned trail literal, in trail order, by `Trail::assign`.
    fn assign_hook(&mut self, lit: Lit, level: u32) -> TheoryStep;

    /// Fired once per retracted literal, in reverse trail order, by the trail's
    /// backtracking mutators — so a retracted atom's theory state is dropped the
    /// instant its literal leaves the trail (a stale bound becomes unrepresentable).
    fn unassign_hook(&mut self, lit: Lit, level: u32);

    /// Fired atomically with a level-up, from inside `Trail::new_decision_level`.
    fn push_frame(&mut self, level: u32);

    /// Fired atomically with a level-down, from inside the trail's backtracking
    /// mutators (`backtrack_to_with_callback`, and — closing the §4.1 four-writer
    /// gap — `backtrack_to_size`/`clear`).
    fn pop_frame(&mut self, level: u32);

    /// A full theory check at a propagation fixpoint (the completeness oracle).
    fn final_check(&mut self) -> TheoryStep;

    /// Model-evaluation oracle: the theory's value for `atom`, if determined.
    fn eval(&mut self, atom: Var) -> Option<bool>;
}

/// An in-crate TOY theory for Phase-1 testing of the `TheoryHooks` contract.
///
/// It enforces a fixed set of binary implications `premise ⇒ conclusion` (each a
/// clause `conclusion ∨ ¬premise`). It is *sound* (it only ever asserts these
/// clauses) and exercises BOTH response paths: when a premise is true and its
/// conclusion is undecided it `Propagate`s the conclusion; when the conclusion is
/// already false it reports a `Conflict`. It maintains its own asserted-literal set
/// (driven entirely by `assign_hook`/`unassign_hook`) and a frame counter so the
/// §4.5 lock-step invariant `frame_depth() == decision_level()+1` can be checked.
pub struct ToyImplTheory {
    /// `(premise, conclusion)` implications.
    axioms: Vec<(Lit, Lit)>,
    /// Currently-asserted literals, in assignment order.
    asserted: Vec<Lit>,
    /// Number of theory frames currently live (starts at 1 for the root level 0).
    frames: u32,
}

impl ToyImplTheory {
    /// Build a toy theory from `(premise, conclusion)` implications.
    #[must_use]
    pub fn new(axioms: Vec<(Lit, Lit)>) -> Self {
        Self { axioms, asserted: Vec::new(), frames: 1 }
    }

    /// The current frame depth — for the §4.5 invariant assertion.
    #[must_use]
    pub fn frame_depth(&self) -> u32 {
        self.frames
    }

    /// The theory's current truth value for `lit` (from the asserted set).
    fn val(&self, lit: Lit) -> Option<bool> {
        if self.asserted.contains(&lit) {
            Some(true)
        } else if self.asserted.contains(&lit.negate()) {
            Some(false)
        } else {
            None
        }
    }
}

impl TheoryHooks for ToyImplTheory {
    fn assign_hook(&mut self, lit: Lit, _level: u32) -> TheoryStep {
        self.asserted.push(lit);
        // Final-check-driven: the trail fires this for state tracking; propagations
        // and conflicts are reported from `final_check`.
        TheoryStep::Ok
    }

    fn unassign_hook(&mut self, lit: Lit, _level: u32) {
        // Retract the literal the instant it leaves the trail (no stale state).
        if let Some(pos) = self.asserted.iter().rposition(|&l| l == lit) {
            self.asserted.remove(pos);
        }
    }

    fn push_frame(&mut self, _level: u32) {
        self.frames += 1;
    }

    fn pop_frame(&mut self, _level: u32) {
        self.frames -= 1;
    }

    fn final_check(&mut self) -> TheoryStep {
        for &(premise, conclusion) in &self.axioms {
            if self.val(premise) == Some(true) {
                match self.val(conclusion) {
                    Some(true) => {} // implication satisfied
                    Some(false) => {
                        // premise true, conclusion false ⇒ the clause (conclusion ∨
                        // ¬premise) is violated; its literals are currently all false.
                        let mut explanation: SmallVec<[Lit; 8]> = SmallVec::new();
                        explanation.push(conclusion);
                        explanation.push(premise.negate());
                        return TheoryStep::Conflict { explanation };
                    }
                    None => {
                        // premise true, conclusion undecided ⇒ propagate the
                        // conclusion, justified by the unit clause (conclusion ∨
                        // ¬premise) whose only non-conclusion literal `¬premise` is
                        // false (premise is true).
                        let mut explanation: SmallVec<[Lit; 8]> = SmallVec::new();
                        explanation.push(premise.negate());
                        return TheoryStep::Propagate {
                            lit: conclusion,
                            reason: TheoryReason { asserting: conclusion, explanation },
                        };
                    }
                }
            }
        }
        TheoryStep::Ok
    }

    fn eval(&mut self, atom: Var) -> Option<bool> {
        self.val(Lit::pos(atom))
    }
}
