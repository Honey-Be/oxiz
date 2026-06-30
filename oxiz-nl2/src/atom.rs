//! Normalised polynomial atoms — the input the solver reasons over.
//!
//! A [`PolyAtom`] is a single comparison `p ⋈ 0` with `p ∈ ℚ[x₁..xₙ]`, plus a
//! provenance id so an unsat reason can name the originating assertion. This
//! mirrors what OxiZ's `TermPolyTranslator` already produces; at the M4-port we
//! consume the translator's output directly (DESIGN.md §11).

pub use oxiz_math::polynomial::{Polynomial, Var};

/// Variable sort. Drives NIA layering (DESIGN.md §6) — a `Real` var is never
/// integerized.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum VarSort {
    Real,
    Integer,
}

/// Comparison operator of a normalised atom `p ⋈ 0`.
///
/// Kept independent of `oxiz-nlsat::discriminant::AtomCmp` for clean-room
/// isolation; mapped at the port.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum AtomCmp {
    Lt,
    Le,
    Gt,
    Ge,
    Eq,
    Ne,
}

impl AtomCmp {
    /// Does `sign(p)` (one of -1, 0, +1) satisfy `p ⋈ 0`?
    ///
    /// This is the kernel of the G-SAT model re-check: evaluate the polynomial
    /// at the model to an exact sign, then ask whether that sign honours the
    /// comparison.
    #[must_use]
    pub fn holds_for_sign(self, sign: i32) -> bool {
        match self {
            AtomCmp::Lt => sign < 0,
            AtomCmp::Le => sign <= 0,
            AtomCmp::Gt => sign > 0,
            AtomCmp::Ge => sign >= 0,
            AtomCmp::Eq => sign == 0,
            AtomCmp::Ne => sign != 0,
        }
    }

    /// The SMT-LIB relation symbol for this comparison (used by the
    /// differential harness when it serialises `(op p 0)`).
    #[must_use]
    pub fn smtlib_op(self) -> &'static str {
        match self {
            AtomCmp::Lt => "<",
            AtomCmp::Le => "<=",
            AtomCmp::Gt => ">",
            AtomCmp::Ge => ">=",
            AtomCmp::Eq => "=",
            AtomCmp::Ne => "distinct",
        }
    }
}

/// Opaque handle back to the asserted term that produced this atom. Lets an
/// unsat reason report an infeasible *subset* of the original assertions.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct OriginId(pub u32);

/// A normalised polynomial atom `poly ⋈ 0`.
#[derive(Clone, Debug)]
pub struct PolyAtom {
    pub poly: Polynomial,
    pub op: AtomCmp,
    pub sort: VarSort,
    pub origin: OriginId,
}

impl PolyAtom {
    #[must_use]
    pub fn new(poly: Polynomial, op: AtomCmp, sort: VarSort, origin: OriginId) -> Self {
        Self {
            poly,
            op,
            sort,
            origin,
        }
    }

    /// Total degree of the underlying polynomial. The current OxiZ band-aid
    /// gate (`unsat_is_trustworthy = total_degree ≤ 1`) keys on exactly this;
    /// `oxiz-nl2` deletes that gate at M4/M5 once the sound core subsumes it.
    #[must_use]
    pub fn total_degree(&self) -> u32 {
        self.poly.total_degree()
    }
}
