//! The solver verdict and its certificates.
//!
//! `Unsat` carries a covering certificate that **G-UNSAT** re-verifies before
//! the verdict leaves the solver (DESIGN.md §2). `Unknown` carries a cause so
//! the differential's telemetry can attribute incompleteness.

use crate::atom::OriginId;
use crate::value::Model;

/// The three sound verdicts. There is no fourth — every uncertainty is
/// `Unknown`.
#[derive(Clone, Debug)]
pub enum Verdict {
    /// Witnessed by an exact model that passed G-SAT.
    Sat(Model),
    /// Backed by a covering certificate that passed G-UNSAT.
    Unsat(UnsatReason),
    /// The sound fallback. Always acceptable.
    Unknown(Cause),
}

impl Verdict {
    #[must_use]
    pub fn is_sat(&self) -> bool {
        matches!(self, Verdict::Sat(_))
    }
    #[must_use]
    pub fn is_unsat(&self) -> bool {
        matches!(self, Verdict::Unsat(_))
    }
    #[must_use]
    pub fn is_unknown(&self) -> bool {
        matches!(self, Verdict::Unknown(_))
    }
}

/// Why the solver returned `Unknown`. Non-soundness-bearing; pure telemetry.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Cause {
    /// No verdict-producing tier is wired yet (M0).
    NotImplemented,
    /// A per-tier budget was exhausted (DESIGN.md §12).
    Budget,
    /// The explainer ladder produced no ℝ-valid clause for a conflict.
    NoExplanation,
    /// A separating bound would be algebraic before the algebraic primitives
    /// are wired (M1/M2 rational-only).
    AlgebraicBound,
    /// G-SAT re-check failed — a candidate model did not verify exactly.
    GSatFailed,
    /// G-UNSAT re-check failed — a covering did not re-verify.
    GUnsatFailed,
}

/// An unsat certificate: a covering of the space by cells, each falsifying a
/// named origin atom, plus the infeasible subset of origins. G-UNSAT samples
/// each cell and checks the union before trusting the verdict.
#[derive(Clone, Debug, Default)]
pub struct UnsatReason {
    pub covering: Vec<Cell>,
    pub infeasible_subset: Vec<OriginId>,
}

/// One cell of an unsat covering: a region on which `falsifies` is everywhere
/// false. (The region representation lands with the interval explainer at M1;
/// M0 keeps the certificate shape so the wire/type surface is fixed early.)
#[derive(Clone, Debug)]
pub struct Cell {
    pub falsifies: OriginId,
}
