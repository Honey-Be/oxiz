//! Exact coordinate values and the model, plus the **G-SAT** gate.
//!
//! A model coordinate is *exact*: a `BigRational` in the common case, an
//! in-house [`AlgebraicReal`] only when an equality forces an irrational. It is
//! **never** an `f64` — approximate coordinates are exactly what produced OxiZ's
//! spurious-sat verdicts.

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::Zero;
use rustc_hash::FxHashMap;

use crate::atom::{PolyAtom, Var};
use crate::univariate::AlgebraicReal;

/// An exact coordinate. Carries an [`AlgebraicReal`] losslessly so an
/// irrational-equality witness can be re-checked *exactly* (not refused).
#[derive(Clone, Debug)]
pub enum Value {
    Rational(BigRational),
    Algebraic(AlgebraicReal),
}

impl Value {
    #[must_use]
    pub fn from_i64(n: i64) -> Self {
        Value::Rational(BigRational::from(BigInt::from(n)))
    }
}

/// An exact assignment `Var → Value`, and the G-SAT re-check over it.
#[derive(Clone, Debug, Default)]
pub struct Model {
    pub vals: FxHashMap<Var, Value>,
}

impl Model {
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    pub fn insert(&mut self, v: Var, val: Value) {
        self.vals.insert(v, val);
    }

    /// **G-SAT** — re-check every atom exactly against this model.
    ///
    /// Returns `true` only if every atom is *provably* satisfied at the model's
    /// exact coordinates. This is the mandatory final gate on any `Sat`
    /// verdict: a model that does not verify here downgrades the verdict to
    /// `Unknown`, making FALSE_SAT structurally impossible (DESIGN.md §2).
    ///
    /// The **rational fast path** handles all-rational models exactly. A model
    /// with **one** algebraic coordinate is handled exactly too (M3): substitute
    /// the rational coordinates, reduce the atom to a univariate polynomial in
    /// the algebraic variable, and take its exact sign at that algebraic number
    /// ([`AlgebraicReal::sign_of`]). A model with **two or more** algebraic
    /// coordinates conservatively returns `false` (→ `Unknown`) — sound, never
    /// unsound; the multivariate `sign_at_algebraic` lands at M4.
    #[must_use]
    pub fn checks(&self, atoms: &[PolyAtom]) -> bool {
        atoms.iter().all(|atom| self.atom_holds(atom).unwrap_or(false))
    }

    /// `Some(true/false)` if the atom's truth at this model is *exactly* decided;
    /// `None` if it cannot yet be (an unassigned var, or ≥ 2 algebraic coords).
    fn atom_holds(&self, atom: &PolyAtom) -> Option<bool> {
        self.poly_sign(&atom.poly).map(|s| atom.op.holds_for_sign(s))
    }

    /// Exact **sign** of the polynomial `p` at this model's coordinates, or `None`
    /// if it cannot be decided exactly here — an unassigned variable of `p`, or
    /// ≥ 2 algebraic coordinates among its variables (the multivariate
    /// `sign_at_algebraic` is out of the single-extension fragment). The rational
    /// coordinates substitute away; with one algebraic coordinate the polynomial
    /// reduces to univariate in it and [`AlgebraicReal::sign_of`] gives the exact
    /// sign. This is the sign oracle the CAC engine evaluates constraints with.
    #[must_use]
    pub fn poly_sign(&self, p: &crate::atom::Polynomial) -> Option<i32> {
        let mut rational: FxHashMap<Var, BigRational> = FxHashMap::default();
        let mut algebraic: Option<(Var, &AlgebraicReal)> = None;
        for v in p.vars() {
            match self.vals.get(&v) {
                Some(Value::Rational(r)) => {
                    rational.insert(v, r.clone());
                }
                Some(Value::Algebraic(a)) => {
                    if algebraic.is_some() {
                        return None; // ≥ 2 algebraic coordinates ⇒ single-extension fragment exceeded
                    }
                    algebraic = Some((v, a));
                }
                None => return None, // unassigned needed var
            }
        }
        Some(match algebraic {
            None => sign_of(&p.eval(&rational)),
            Some((v, alpha)) => {
                let mut q = p.clone();
                for (var, val) in &rational {
                    q = q.eval_at(*var, val);
                }
                let deg = q.degree(v);
                let coeffs: Vec<BigRational> = (0..=deg).map(|k| q.univ_coeff(v, k)).collect();
                alpha.sign_of(&coeffs)
            }
        })
    }
}

fn sign_of(value: &BigRational) -> i32 {
    if value.is_zero() {
        0
    } else if *value < BigRational::zero() {
        -1
    } else {
        1
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::atom::{AtomCmp, OriginId, Polynomial, VarSort};

    fn atom(coeffs: &[(i64, &[(Var, u32)])], op: AtomCmp) -> PolyAtom {
        PolyAtom::new(
            Polynomial::from_coeffs_int(coeffs),
            op,
            VarSort::Real,
            OriginId(0),
        )
    }

    #[test]
    fn rational_model_satisfies_linear_atom() {
        // x - 2 = 0 at x = 2  ⇒ holds
        let a = atom(&[(1, &[(0, 1)]), (-2, &[])], AtomCmp::Eq);
        let mut m = Model::new();
        m.insert(0, Value::from_i64(2));
        assert!(m.checks(std::slice::from_ref(&a)));
    }

    #[test]
    fn rational_model_violates_atom() {
        // x^2 - 4 > 0 at x = 1  ⇒  1 - 4 = -3 ≯ 0  ⇒ fails
        let a = atom(&[(1, &[(0, 2)]), (-4, &[])], AtomCmp::Gt);
        let mut m = Model::new();
        m.insert(0, Value::from_i64(1));
        assert!(!m.checks(std::slice::from_ref(&a)));
    }

    #[test]
    fn unassigned_var_is_not_verified() {
        // y > 0 with y unassigned ⇒ conservatively unverified (false)
        let a = atom(&[(1, &[(5, 1)])], AtomCmp::Gt);
        let m = Model::new();
        assert!(!m.checks(std::slice::from_ref(&a)));
    }

    #[test]
    fn multi_atom_conjunction() {
        // x >= 0  ∧  x - 3 <= 0  at x = 2 ⇒ both hold
        let a1 = atom(&[(1, &[(0, 1)])], AtomCmp::Ge);
        let a2 = atom(&[(1, &[(0, 1)]), (-3, &[])], AtomCmp::Le);
        let mut m = Model::new();
        m.insert(0, Value::from_i64(2));
        assert!(m.checks(&[a1, a2]));
    }
}
