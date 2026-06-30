//! The soundness seam: the [`Explainer`] trait.
//!
//! `explain` is **the only path to an `unsat`** in `oxiz-nl2`. Its contract is
//! the whole soundness obligation of the explainer ladder:
//!
//! > Given a conflict (an empty feasible region for some variable under the
//! > current partial assignment), return a [`Clause`] that is **valid over ℝ**
//! > (true in every real model) and **falsified by the current trail** (so it
//! > prunes). Or [`ExplainResult::GiveUp`] — the loop treats that subproblem as
//! > `Unknown`.
//!
//! Soundness of the whole solver reduces to: every clause returned here is
//! ℝ-valid. The two runtime gates (G-SAT, G-UNSAT) re-check verdicts so that
//! even a *buggy* explainer downgrades to `Unknown` rather than producing a
//! false verdict (DESIGN.md §1, §2).

use crate::atom::PolyAtom;

/// A learned clause: a disjunction of polynomial atoms, asserted to be valid
/// over ℝ. (At M1 these are interval-exclusion clauses; the ladder enriches the
/// shape over M2→M4.)
#[derive(Clone, Debug, Default)]
pub struct Clause {
    pub literals: Vec<PolyAtom>,
}

impl Clause {
    #[must_use]
    pub fn new(literals: Vec<PolyAtom>) -> Self {
        Self { literals }
    }
}

/// A conflict handed to the explainer: the variable whose feasible region went
/// empty, and the atoms that jointly emptied it. (Fleshed out with the trail at
/// M1; the shape is fixed here so the seam is stable.)
#[derive(Clone, Debug)]
pub struct Conflict {
    pub var: crate::atom::Var,
    pub culprits: Vec<PolyAtom>,
}

/// Why an explainer declined to explain a conflict. All variants are sound (→
/// `Unknown`); none is a verdict.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum GiveUpReason {
    /// A separating root/bound is algebraic and the algebraic primitives are
    /// not wired yet (M1/M2 rational-only).
    AlgebraicBound,
    /// This tier does not handle this conflict shape; a higher tier should try.
    OutOfScope,
    /// A per-tier budget was hit.
    Budget,
}

/// The result of an `explain` call.
#[derive(Clone, Debug)]
pub enum ExplainResult {
    Clause(Clause),
    GiveUp(GiveUpReason),
}

/// The single soundness seam. Implementors are the *tiers* of the explainer
/// ladder; the MCSAT loop is frozen and never changes (DESIGN.md §5).
pub trait Explainer {
    /// Contract: the returned clause is valid over ℝ and falsified by the
    /// current trail. See module docs.
    fn explain(&self, conflict: &Conflict) -> ExplainResult;

    /// A short tier label for differential telemetry / debugging.
    fn name(&self) -> &'static str;
}
