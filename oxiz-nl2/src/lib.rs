//! # oxiz-nl2 — clean-room nonlinear-arithmetic solver for OxiZ
//!
//! A sound-first replacement for OxiZ's `NlsatSolver` (real) and `NiaSolver`
//! (integer), which a z3-differential proved broadly unsound on nonlinear
//! `unsat`. The full design is in `DESIGN.md`; the one-paragraph version:
//!
//! `oxiz-nl2` is a **model-constructing MCSAT trail** whose loop and data
//! structures are *frozen*, with a **monotone-strength explainer ladder** as
//! the only growing part. The entire soundness obligation reduces to one
//! contract on one function ([`explain`](explain::Explainer::explain)): the
//! clauses it learns are valid over ℝ. Two runtime gates — **G-SAT** (exact
//! model re-check, [`value::Model::checks`]) and **G-UNSAT** (covering
//! re-verification) — make `FALSE_UNSAT = 0` / `FALSE_SAT = 0` hold *regardless
//! of explainer correctness*: a buggy tier downgrades to `Unknown`, never to a
//! false verdict.
//!
//! ## Status: M0
//!
//! This crate is at **milestone M0** (DESIGN.md §10): the type skeleton, the
//! G-SAT model re-check, the `Explainer` seam, and the z3-differential gate are
//! in place. [`check`] is the trivially-sound solver — it returns `Unknown` for
//! every input. M1 wires the MCSAT spine + interval/§G explainer behind this
//! same signature; nothing above changes.
//!
//! ## Priority order (non-negotiable)
//!
//! `soundness ≫ completeness ≫ latency`. `Unknown` is always an acceptable
//! verdict; a false `Unsat` never is.

pub mod atom;
pub mod cac;
pub mod cdcac;
pub mod corpus;
pub mod differential;
pub mod explain;
pub mod fdlcg;
pub mod layer0;
pub mod project;
pub mod spine;
pub mod univariate;
pub mod value;
pub mod verdict;

pub use atom::{AtomCmp, OriginId, PolyAtom, Polynomial, Var, VarSort};
pub use explain::{Clause, Conflict, ExplainResult, Explainer, GiveUpReason};
pub use value::{Model, Value};
pub use verdict::{Cause, Cell, UnsatReason, Verdict};

/// Decide a conjunction of polynomial atoms.
///
/// The single public entry point and the one the M4-port wires into OxiZ's
/// `dispatch_nl_solver`. Sound by the priority order: it returns `Sat` only
/// with a G-SAT-verified model, `Unsat` only from a sound source (Layer-0
/// §G/§G-SOS or a single-variable exactly-empty feasible region), and `Unknown`
/// for everything else.
///
/// **M1:** routes to the MCSAT spine ([`spine::solve`]) with the interval/§G
/// explainer. Decides the documented single-atom false-unsat shapes; harder
/// problems return `Unknown` until later milestones enrich the explainer.
#[must_use]
pub fn check(atoms: &[PolyAtom]) -> Verdict {
    spine::solve(atoms)
}
