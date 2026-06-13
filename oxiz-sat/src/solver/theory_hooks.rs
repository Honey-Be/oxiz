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

/// The only ways a theory can respond to a hook. There is no sentinel and no empty
/// conflict: a `Propagate`/`Conflict` always carries a first-class `TheoryReason`
/// whose asserting literal is non-null by construction (§4.3).
pub enum TheoryStep {
    /// Nothing to report.
    Ok,
    /// Force `lit` true, justified by `reason` (a unit-implying explanation).
    Propagate { lit: Lit, reason: TheoryReason },
    /// The current partial assignment is theory-inconsistent; `reason` is the
    /// (non-empty, level-tagged) false-literal set.
    Conflict { reason: TheoryReason },
}

/// The trait a theory implements. The ENGINE owns the calling discipline.
///
/// `Send + Sync` so that a `Trail` (and therefore a `Solver`) carrying an installed
/// theory stays `Send + Sync` — the `oxiz-theories` `Theory` trait and the parallel
/// engine require it. Every concrete theory is single-threaded data, so this is free.
pub trait TheoryHooks: Send + Sync {
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
