//! McCallum projection — M4 step A of the CDCAC implementation.
//!
//! Eliminating the top variable `var` from a set of polynomials, the McCallum
//! projection produces polynomials in the *remaining* variables whose real roots
//! delineate the cylindrical cells: where leading coefficients vanish (the
//! degree drops), where discriminants vanish (roots collide), and where
//! resultants vanish (two polynomials share a root).
//!
//! Built on `oxiz_math`'s `resultant`/`discriminant`/`leading_coeff_wrt`. Those
//! two were rewritten in-house (Sylvester-matrix determinant; the old
//! subresultant-PRS was unsound on the multivariate case — e.g.
//! `res_x(x-y,x-2y)` returned `x` instead of `±y`), so they are now the single
//! correct source; oxiz-nl2 no longer keeps a duplicate.
//!
//! Per the Verus-proven `covering_implies_unsat` (in `~/oxiz-nl2-verification`),
//! the eventual `Unsat` is sound regardless of projection correctness — the
//! runtime G-UNSAT gate re-checks the covering — so even a projection bug only
//! costs completeness. The unit tests below confirm the primitives on
//! hand-computed examples regardless.

use oxiz_math::polynomial::{Polynomial, Var};

/// The McCallum projection of `polys`, eliminating `var`: the leading
/// coefficients and discriminant factors (`res(p, ∂p/∂var)`) of each polynomial
/// of positive degree in `var`, plus the pairwise resultants. Zero and
/// pure-constant results (no lower-dimensional information) are dropped;
/// duplicates are removed.
#[must_use]
pub fn mccallum_project(polys: &[Polynomial], var: Var) -> Vec<Polynomial> {
    let active: Vec<&Polynomial> = polys.iter().filter(|p| p.degree(var) >= 1).collect();
    let mut out: Vec<Polynomial> = Vec::new();
    for p in &active {
        push_informative(&mut out, p.leading_coeff_wrt(var));
        if p.degree(var) >= 2 {
            // discriminant factor: res(p, ∂p/∂var) — vanishes on the
            // double-root locus (and where lc vanishes, already included).
            push_informative(&mut out, p.discriminant(var));
        }
    }
    for i in 0..active.len() {
        for j in (i + 1)..active.len() {
            push_informative(&mut out, active[i].resultant(active[j], var));
        }
    }
    out
}

/// Keep `p` only if it carries lower-dimensional structure (non-zero, not a
/// pure numeric constant) and is new.
fn push_informative(out: &mut Vec<Polynomial>, p: Polynomial) {
    if p.is_zero() || p.is_constant() {
        return;
    }
    if !out.contains(&p) {
        out.push(p);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_bigint::BigInt;
    use num_rational::BigRational;

    fn p(coeffs: &[(i64, &[(Var, u32)])]) -> Polynomial {
        Polynomial::from_coeffs_int(coeffs)
    }
    fn at(poly: &Polynomial, var: Var, val: i64) -> Polynomial {
        poly.eval_at(var, &BigRational::from_integer(BigInt::from(val)))
    }

    // ── confirm the (now in-house) oxiz-math primitives on hand-computed cases ──
    #[test]
    fn resultant_vanishes_iff_common_root() {
        // res_x(x-1, x-2): no common root ⇒ non-zero constant
        let r = p(&[(1, &[(0, 1)]), (-1, &[])]).resultant(&p(&[(1, &[(0, 1)]), (-2, &[])]), 0);
        assert!(!r.is_zero() && r.is_constant());
        // res_x(x-1, x-1): common root ⇒ zero
        let r0 = p(&[(1, &[(0, 1)]), (-1, &[])]).resultant(&p(&[(1, &[(0, 1)]), (-1, &[])]), 0);
        assert!(r0.is_zero());
    }

    #[test]
    fn resultant_two_lines_is_y() {
        // res_x(x-y, x-2y) = ±y : vanishes at y=0, non-zero at y=1, no x left.
        let r = p(&[(1, &[(0, 1)]), (-1, &[(1, 1)])]).resultant(&p(&[(1, &[(0, 1)]), (-2, &[(1, 1)])]), 0);
        assert!(at(&r, 1, 0).is_zero(), "res = {r:?}");
        assert!(!at(&r, 1, 1).is_zero());
        assert_eq!(r.degree(0), 0); // x eliminated
        assert_eq!(r.degree(1), 1); // linear in y
    }

    #[test]
    fn project_bivariate_quadratic_yields_discriminant_curve() {
        // eliminate x from { x² - y } : disc factor = res(x²-y, 2x) = ±4y,
        // vanishing exactly at y=0 (double root x=0).
        let proj = mccallum_project(&[p(&[(1, &[(0, 2)]), (-1, &[(1, 1)])])], 0);
        assert_eq!(proj.len(), 1, "got {proj:?}");
        assert!(at(&proj[0], 1, 0).is_zero());
        assert!(!at(&proj[0], 1, 1).is_zero());
        assert_eq!(proj[0].degree(0), 0); // contains no x
    }

    #[test]
    fn project_resultant_of_two_lines() {
        let proj = mccallum_project(
            &[p(&[(1, &[(0, 1)]), (-1, &[(1, 1)])]), p(&[(1, &[(0, 1)]), (-2, &[(1, 1)])])],
            0,
        );
        assert_eq!(proj.len(), 1, "got {proj:?}");
        assert!(at(&proj[0], 1, 0).is_zero());
        assert!(!at(&proj[0], 1, 1).is_zero());
    }

    #[test]
    fn project_univariate_is_empty() {
        let proj = mccallum_project(&[p(&[(1, &[(0, 2)]), (-3, &[])])], 0);
        assert!(proj.is_empty(), "got {proj:?}");
    }
}
