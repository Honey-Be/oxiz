//! Layer 0 — exact one-sided pre-deciders (DESIGN.md §5).
//!
//! These are the **permanent** fast front line: cheap, sound, one-atom (or
//! one-variable) checks that short-circuit before the MCSAT spine. They only
//! ever produce `Unsat` (never `Sat`), and only when a single atom is
//! *definitely* unsatisfiable on its own — so the conjunction is unsatisfiable.
//!
//! M1 folds in **§G** (univariate-quadratic definite sign by discriminant) and
//! **§G-SOS** (multivariate quadratic-form PSD by LDLᵀ inertia), reused verbatim
//! from `oxiz_nlsat::discriminant` (the user's "interval + §G together" call).

use num_rational::BigRational;
use num_traits::{Signed, Zero};
use oxiz_nlsat::discriminant::{self, AtomCmp as GCmp};
use rustc_hash::FxHashMap;

use crate::atom::{AtomCmp, PolyAtom, Var};

/// Map our comparison to the §G decider's. §G is defined for the five ordering
/// comparisons; `Ne` has no definite-sign refutation for a single polynomial
/// (a non-constant poly is `≠ 0` somewhere), so it never triggers §G.
fn to_g_cmp(op: AtomCmp) -> Option<GCmp> {
    match op {
        AtomCmp::Lt => Some(GCmp::Lt),
        AtomCmp::Le => Some(GCmp::Le),
        AtomCmp::Gt => Some(GCmp::Gt),
        AtomCmp::Ge => Some(GCmp::Ge),
        AtomCmp::Eq => Some(GCmp::Eq),
        AtomCmp::Ne => None,
    }
}

/// Is some single atom **definitely unsatisfiable** by §G / §G-SOS? If so the
/// whole conjunction is unsat. Returns the index of the refuting atom.
///
/// Sound by construction: §G concludes `unsat` only when the polynomial's value
/// has a fixed sign incompatible with the comparison over *all* reals (e.g.
/// `x² < 0`, `(x−1)² < 0`, `(x−y)² < 0`).
#[must_use]
pub fn definite_sign_unsat(atoms: &[PolyAtom]) -> Option<usize> {
    for (i, atom) in atoms.iter().enumerate() {
        // §G / §G-SOS (quadratic + quadratic-form) — needs the mapped comparison.
        if let Some(g) = to_g_cmp(atom.op)
            && (discriminant::quadratic_atom_is_unsat(&atom.poly, g)
                || discriminant::quadratic_form_is_unsat(&atom.poly, g))
        {
            return Some(i);
        }
        // Even-monomial definite sign (generalises §G to any degree).
        if even_monomial_atom_is_unsat(atom) {
            return Some(i);
        }
    }
    None
}

/// The definite sign of a polynomial that is a sum of **all-even-exponent**
/// monomials (each such monomial is `≥ 0` everywhere), or `None` if it has any
/// odd-exponent monomial or mixed coefficient signs (sign not determined here).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[allow(clippy::enum_variant_names)] // names mirror §G's DefiniteSign on purpose
enum DefSign {
    AllPositive,
    AllNonNegative,
    AllNegative,
    AllNonPositive,
}

fn even_monomial_definite_sign(poly: &crate::atom::Polynomial) -> Option<DefSign> {
    let mut has_const = false; // a nonzero constant term
    let mut const_pos = false;
    let mut saw_pos = false;
    let mut saw_neg = false;
    let mut nonconst_terms = false;
    for term in poly.terms() {
        if term.coeff.is_zero() {
            continue;
        }
        let is_const = term.monomial.vars().is_empty();
        if is_const {
            has_const = true;
            const_pos = term.coeff.is_positive();
        } else {
            // every variable's exponent must be even for the monomial to be ≥ 0
            if term.monomial.vars().iter().any(|vp| vp.power % 2 != 0) {
                return None;
            }
            nonconst_terms = true;
        }
        if term.coeff.is_positive() {
            saw_pos = true;
        } else {
            saw_neg = true;
        }
    }
    if !nonconst_terms {
        return None; // pure constant: handled by the constant-atom check
    }
    match (saw_pos, saw_neg) {
        (true, false) => Some(if has_const && const_pos {
            DefSign::AllPositive
        } else {
            DefSign::AllNonNegative
        }),
        (false, true) => Some(if has_const && !const_pos {
            DefSign::AllNegative
        } else {
            DefSign::AllNonPositive
        }),
        _ => None, // mixed signs ⇒ not definite by this structural test
    }
}

/// Is a single atom `p ⋈ 0` unsatisfiable because `p` is an even-monomial sum
/// of definite sign incompatible with `⋈`? (e.g. `3x⁴ < 0`, `−3y⁴ > 0`,
/// `x²+y²+1 = 0`.) Sound — the sign classification holds over all reals.
fn even_monomial_atom_is_unsat(atom: &PolyAtom) -> bool {
    let Some(s) = even_monomial_definite_sign(&atom.poly) else {
        return false;
    };
    match s {
        DefSign::AllPositive => matches!(atom.op, AtomCmp::Lt | AtomCmp::Le | AtomCmp::Eq),
        DefSign::AllNegative => matches!(atom.op, AtomCmp::Gt | AtomCmp::Ge | AtomCmp::Eq),
        DefSign::AllNonNegative => matches!(atom.op, AtomCmp::Lt),
        DefSign::AllNonPositive => matches!(atom.op, AtomCmp::Gt),
    }
}

/// Is some atom a **constant** (no variables) that is false? Then the whole
/// conjunction is unsat. Returns the refuting atom's index.
#[must_use]
pub fn constant_false_atom(atoms: &[PolyAtom]) -> Option<usize> {
    let empty: FxHashMap<Var, BigRational> = FxHashMap::default();
    for (i, atom) in atoms.iter().enumerate() {
        if atom.poly.vars().is_empty() {
            let val = atom.poly.eval(&empty);
            let sign = if val.is_zero() {
                0
            } else if val.is_negative() {
                -1
            } else {
                1
            };
            if !atom.op.holds_for_sign(sign) {
                return Some(i);
            }
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::atom::{OriginId, Polynomial, VarSort};

    fn atom(coeffs: &[(i64, &[(u32, u32)])], op: AtomCmp) -> PolyAtom {
        PolyAtom::new(Polynomial::from_coeffs_int(coeffs), op, VarSort::Real, OriginId(0))
    }

    #[test]
    fn x2_lt_0_is_definite_unsat() {
        // x² < 0
        let a = atom(&[(1, &[(0, 2)])], AtomCmp::Lt);
        assert_eq!(definite_sign_unsat(std::slice::from_ref(&a)), Some(0));
    }

    #[test]
    fn perfect_square_lt_0_is_definite_unsat() {
        // x² - 2x + 1 < 0  ==  (x-1)² < 0
        let a = atom(&[(1, &[(0, 2)]), (-2, &[(0, 1)]), (1, &[])], AtomCmp::Lt);
        assert_eq!(definite_sign_unsat(std::slice::from_ref(&a)), Some(0));
    }

    #[test]
    fn sos_lt_0_is_definite_unsat() {
        // x² - 2xy + y² < 0  ==  (x-y)² < 0
        let a = atom(
            &[(1, &[(0, 2)]), (-2, &[(0, 1), (1, 1)]), (1, &[(1, 2)])],
            AtomCmp::Lt,
        );
        assert_eq!(definite_sign_unsat(std::slice::from_ref(&a)), Some(0));
    }

    #[test]
    fn satisfiable_atom_is_not_flagged() {
        // 3x² - 5 < 0 is satisfiable (x small) — must NOT be flagged unsat
        let a = atom(&[(3, &[(0, 2)]), (-5, &[])], AtomCmp::Lt);
        assert_eq!(definite_sign_unsat(std::slice::from_ref(&a)), None);
    }

    #[test]
    fn even_monomial_quartic_definite_unsat() {
        // 3x⁴ < 0 → unsat (AllNonNegative); degree 4, beyond §G's quadratic reach
        let a = atom(&[(3, &[(0, 4)])], AtomCmp::Lt);
        assert_eq!(definite_sign_unsat(std::slice::from_ref(&a)), Some(0));
        // -3y⁴ > 0 → unsat (AllNonPositive)
        let b = atom(&[(-3, &[(1, 4)])], AtomCmp::Gt);
        assert_eq!(definite_sign_unsat(std::slice::from_ref(&b)), Some(0));
        // x² + y² + 1 = 0 → unsat (AllPositive)
        let c = atom(&[(1, &[(0, 2)]), (1, &[(1, 2)]), (1, &[])], AtomCmp::Eq);
        assert_eq!(definite_sign_unsat(std::slice::from_ref(&c)), Some(0));
    }

    #[test]
    fn even_monomial_with_odd_term_declines() {
        // x⁴ + x  has an odd-exponent term ⇒ not definite ⇒ not flagged
        let a = atom(&[(1, &[(0, 4)]), (1, &[(0, 1)])], AtomCmp::Lt);
        assert_eq!(definite_sign_unsat(std::slice::from_ref(&a)), None);
        // x²+y² = 0 is SAT (x=y=0): AllNonNegative + Eq must NOT be flagged
        let b = atom(&[(1, &[(0, 2)]), (1, &[(1, 2)])], AtomCmp::Eq);
        assert_eq!(definite_sign_unsat(std::slice::from_ref(&b)), None);
    }

    #[test]
    fn constant_false_detected() {
        // 5 = 0 → false constant
        let a = atom(&[(5, &[])], AtomCmp::Eq);
        assert_eq!(constant_false_atom(std::slice::from_ref(&a)), Some(0));
        // 3 < 0 → false constant
        let b = atom(&[(3, &[])], AtomCmp::Lt);
        assert_eq!(constant_false_atom(std::slice::from_ref(&b)), Some(0));
        // 0 = 0 → true, not flagged
        let c = atom(&[], AtomCmp::Eq);
        assert_eq!(constant_false_atom(std::slice::from_ref(&c)), None);
    }
}
