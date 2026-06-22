//! Algebraic reduction knowledge base (KB).
//!
//! This module implements a *leveled* "reduction knowledge base" that recognizes
//! polynomial-equality systems whose only satisfying assignment is **irrational**
//! (and therefore cannot be represented by the solver's rational-only
//! `arith_values`). The canonical example is the circle/line system
//!
//! ```text
//!   x^2 + y^2 - 25 = 0      (circle of radius 5)
//!   y - x = 0               (line y = x)
//! ```
//!
//! whose real solutions are `x = y = ±sqrt(12.5)`, irrational. The base NLSAT
//! search picks a rational value for the first "free" variable, after which the
//! second variable's feasible region becomes empty, and the solver spuriously
//! reports `Unsat`.
//!
//! ## Strategy (mirrors the leveled-KB pattern in `oxiz-solver/src/calculus.rs`)
//!
//! - **Level 0 (primitive reductions).** Use asserted equality atoms (`p = 0`)
//!   to eliminate variables. A linear-in-some-variable equality (e.g. `y - x = 0
//!   ⇒ y = x`) is *exactly* substituted into the other equalities, repeating to
//!   triangularize the system toward a single **univariate** polynomial `q(x)`.
//!   When no equality is linear in a shared variable, fall to a resultant-based
//!   elimination (Level 1).
//! - **Level 1+ (derived/composite forms).** Recognized conic ∩ line / conic ∩
//!   conic patterns built *on top of* the Level-0 primitives (the linear
//!   substitution above, or `Polynomial::resultant` for two genuine conics).
//!   Every derived rule is re-verified from the level below by the final
//!   back-substitution check.
//! - **Confirmation.** Once reduced to a univariate `q(x)`, the crate's Sturm
//!   machinery (`crate::cad::SturmSequence`) isolates a real root; if one exists,
//!   we build an exact [`AlgebraicNumber`] for it (its constructor re-validates
//!   single-root isolation via Sturm — a built-in soundness gate).
//! - **Verification.** Before concluding SAT, the candidate algebraic assignment
//!   is verified to satisfy **every** original equality atom *exactly* (symbolic
//!   divisibility `q | p_reduced`, never a numeric midpoint eval).
//!
//! ## Soundness
//!
//! This KB is a purely **additive recognizer**: it can only turn a spurious
//! `Unsat` into a *verified* `Sat`. Its failure path is side-effect-free — when
//! anything is uncertain (system not all-equalities, not reducible by exact
//! substitution, no real root, or the verification fails), it returns `None` and
//! the existing CDCL+CAD search runs verbatim, unchanged. It NEVER concludes
//! `Unsat` (an inexact resultant could otherwise fabricate one) and NEVER writes
//! to the assignment unless the exact verification has passed.

use crate::assignment::Assignment;
use crate::cad::SturmSequence;
use crate::types::{Atom, AtomKind};
use num_rational::BigRational;
use num_traits::Zero;
use oxiz_math::algebraic::AlgebraicNumber;
use oxiz_math::polynomial::root_counting::Polynomial as UniPolynomial;
use oxiz_math::polynomial::{Polynomial, Var};

/// A solved algebraic system, ready to be written into the assignment.
///
/// Holds the exact algebraic value for every arithmetic variable that appears
/// in the recognized equality system. Construction of this struct already
/// implies the full back-substitution verification succeeded.
#[derive(Debug, Clone)]
pub struct AlgebraicSolution {
    /// Exact algebraic value for each solved variable.
    pub values: Vec<(Var, AlgebraicNumber)>,
}

/// An asserted equality `p = 0`, the Level-0 KB input.
#[derive(Debug, Clone)]
struct EqConstraint {
    poly: Polynomial,
}

/// Try to recognize and solve an all-equality polynomial system algebraically.
///
/// `equalities` are the polynomials `p` of asserted (`bool_value == true`),
/// single-factor equality atoms, with the semantics `p = 0`.
///
/// Returns `Some(solution)` only when:
///   1. the system reduces (by exact substitution and/or resultant elimination)
///      to a single univariate polynomial `q` of degree ≥ 1,
///   2. `q` has a real root (confirmed by Sturm), an exact [`AlgebraicNumber`] is
///      built for it, and
///   3. the resulting assignment satisfies **every** original equality exactly.
///
/// Otherwise returns `None` (fall back to the existing solver). This function is
/// pure: it has no observable side effects.
pub fn try_solve_equalities(equalities: &[Polynomial]) -> Option<AlgebraicSolution> {
    if equalities.is_empty() {
        return None;
    }

    // Collect the active constraints, dropping trivial (constant) ones. A
    // non-zero constant equality means the system is inconsistent — but we do
    // NOT conclude Unsat from the KB (soundness asymmetry), we just fall back.
    let mut constraints: Vec<EqConstraint> = Vec::new();
    for p in equalities {
        if p.is_constant() {
            if !p.constant_value().is_zero() {
                // 0 = c with c != 0 — genuinely unsat, but leave the verdict to
                // the existing path. The KB never reports Unsat.
                return None;
            }
            // 0 = 0 is trivially true; ignore it.
            continue;
        }
        constraints.push(EqConstraint { poly: p.clone() });
    }

    if constraints.is_empty() {
        return None;
    }

    // The set of variables that the system constrains.
    let mut all_vars: Vec<Var> = Vec::new();
    for c in &constraints {
        for v in c.poly.vars() {
            if !all_vars.contains(&v) {
                all_vars.push(v);
            }
        }
    }
    all_vars.sort_unstable();

    // ---- Level 0: linear-equality elimination + triangularization. ----
    //
    // `subs` records the elimination chain `var := replacement(remaining vars)`,
    // in the order performed. `active` holds the equalities not yet consumed as
    // an elimination pivot (with prior substitutions already applied).
    let mut active: Vec<Polynomial> = constraints.iter().map(|c| c.poly.clone()).collect();
    let mut subs: Vec<(Var, Polynomial)> = Vec::new();

    // Repeatedly find an equality that is linear in some variable still present
    // in other equalities, isolate that variable, and substitute it away.
    loop {
        let mut progressed = false;

        'find_pivot: for i in 0..active.len() {
            // Skip equalities that have collapsed to constants.
            if active[i].is_constant() {
                continue;
            }
            let vars_i = active[i].vars();
            for &v in &vars_i {
                if active[i].degree(v) != 1 {
                    continue;
                }
                // Only eliminate a variable that *couples* this equation to at
                // least one OTHER active equation. Eliminating a variable that
                // appears nowhere else would simply consume the equation without
                // reducing coupling, and could leave the system with no
                // univariate eliminant to confirm (e.g. a pure `2x - 6 = 0`).
                let appears_elsewhere = active
                    .iter()
                    .enumerate()
                    .any(|(j, eq)| j != i && eq.vars().contains(&v));
                if !appears_elsewhere {
                    continue;
                }
                // Isolate `v = f(other vars)` from this (degree-1-in-v) equality.
                let Some(replacement) = isolate_linear_var(&active[i], v) else {
                    continue;
                };
                // The replacement must not itself depend on `v` (it can't, since
                // we removed the v-term) — guaranteed by `isolate_linear_var`.

                // Substitute `v := replacement` into all OTHER active equalities.
                for (j, eq) in active.iter_mut().enumerate() {
                    if j == i {
                        continue;
                    }
                    if eq.vars().contains(&v) {
                        *eq = eq.substitute(v, &replacement);
                    }
                }
                // Record the elimination and drop the pivot equation.
                subs.push((v, replacement));
                active.remove(i);
                progressed = true;
                break 'find_pivot;
            }
        }

        if !progressed {
            break;
        }
    }

    // Gate: the KB only intervenes on genuinely *coupled* multivariate systems,
    // i.e. ones where at least one variable was eliminated by substitution. A
    // single-equation problem (e.g. `x^3 - x = 0`, `x - 1 = 0`) does no
    // elimination — the base CDCL+CAD search already solves it (and, for NIA,
    // applies the integer-domain constraint the KB is unaware of). Falling back
    // here keeps the KB strictly additive: it cannot change any verdict the
    // existing path already produces.
    if subs.is_empty() {
        return None;
    }

    // Drop any equalities that became `0 = 0`. A non-zero constant means unsat —
    // again, fall back rather than report Unsat.
    let mut remaining: Vec<Polynomial> = Vec::new();
    for eq in active {
        if eq.is_constant() {
            if !eq.constant_value().is_zero() {
                return None;
            }
            continue;
        }
        remaining.push(eq);
    }

    // Find the eliminant: a single univariate polynomial of degree ≥ 1. If
    // Level-0 substitution did not already leave one, fall to the Level-1
    // resultant elimination for a 2-equation conic system.
    let (q, root_var) = match find_univariate_eliminant(&remaining) {
        Some(qr) => qr,
        None => try_resultant_eliminant(&remaining)?,
    };

    // ---- Confirmation: isolate a real root of q via Sturm. ----
    let sturm = SturmSequence::new(&q, root_var);
    let roots = sturm.isolate_roots();
    let (lower, upper) = roots.into_iter().next()?; // no real root ⇒ fall back

    // Build the exact algebraic number for the root variable. Its constructor
    // re-validates (via its own Sturm sequence on the univariate type) that the
    // interval isolates exactly one root — a built-in soundness gate. Any error
    // means we cannot certify ⇒ fall back.
    let uni_q = to_univariate(&q, root_var)?;
    let root = AlgebraicNumber::new(uni_q, lower, upper).ok()?;

    // Gate: the KB is the *irrational-solution* recognizer. If the isolated root
    // is rational, the base CDCL+CAD search already represents and finds it
    // exactly (and a rational `arith_value` would otherwise need to be written,
    // duplicating that path). Fall back so the KB only ever supplies the value
    // type the base path *cannot* (an irrational algebraic number). This keeps
    // the change strictly additive and avoids the midpoint-vs-exact mismatch a
    // rational root would introduce in the rational `arith_values` map.
    if root.is_rational() {
        return None;
    }

    // ---- Back-substitution: assign every system variable. ----
    //
    // The root variable takes `root`. Each eliminated `v := f` must reduce, under
    // the full substitution chain, to an expression in `root_var` only; we only
    // support the case where that reduced expression is itself univariate in
    // `root_var` so the value is exactly representable. For the canonical
    // circle/line system this is `y = x` (the identity in `root_var`).
    let assignment = build_assignment(&q, root_var, &root, &subs, &all_vars)?;

    // ---- Verification: every original equality must hold exactly. ----
    //
    // For an equality `p = 0`, we reduce `p` through the recorded substitution
    // chain to a polynomial `p_reduced` in `root_var` only, then confirm
    // `q | p_reduced` (pseudo-remainder is zero). Because `root_var = root` is a
    // root of `q`, divisibility guarantees `p_reduced(root) = 0` exactly. This is
    // a symbolic check — never a numeric/interval approximation.
    for c in &constraints {
        let reduced = apply_subs(&c.poly, &subs);

        // The substituted polynomial reduced to identically zero ⇒ this equality
        // holds for *every* value of the root variable (e.g. the eliminated
        // `y - x = 0` becomes `0` after `y := x`). Trivially satisfied.
        if reduced.is_zero() {
            continue;
        }
        // A non-zero *constant* residue means `c = 0` for some non-zero `c` ⇒ the
        // equality is unsatisfiable under the substitution ⇒ fall back (the KB
        // never reports Unsat).
        if reduced.is_constant() {
            return None;
        }
        // Otherwise the residue must be univariate in the root variable; any
        // other variable means the elimination was incomplete ⇒ fall back.
        let rvars = reduced.vars();
        if rvars.len() != 1 || rvars[0] != root_var {
            return None;
        }
        // q | reduced ?  (exact, via pseudo-remainder over Q). Because the root
        // variable equals a root of `q`, divisibility guarantees `reduced` is
        // exactly zero at the model point.
        let rem = reduced.pseudo_remainder(&q, root_var);
        if !rem.is_zero() {
            return None;
        }
    }

    Some(AlgebraicSolution {
        values: assignment,
    })
}

/// Isolate a degree-1 variable `v` from `p = 0`, returning `f` with `v = f`.
///
/// `p` must be exactly degree 1 in `v`. Returns `None` if `v`'s coefficient is
/// not a non-zero constant (e.g. `x*y` makes `v=x`'s coefficient `y`, which is
/// not a constant — substituting then would not be an equivalence we can later
/// represent), keeping the substitution exact and one variable lighter.
fn isolate_linear_var(p: &Polynomial, v: Var) -> Option<Polynomial> {
    // Coefficient of v^1 must be a non-zero rational constant.
    let lead = p.coeff(v, 1);
    if !lead.is_constant() {
        return None;
    }
    let a = lead.constant_value();
    if a.is_zero() {
        return None;
    }
    // p must have no higher powers of v.
    if p.degree(v) != 1 {
        return None;
    }
    // rest = p - a*v  (the v^0 coefficient polynomial in the other variables).
    let rest = p.coeff(v, 0);
    // v = -rest / a
    let inv_neg = -BigRational::from_integer(num_bigint::BigInt::from(1)) / a;
    Some(rest.scale(&inv_neg))
}

/// Among the remaining equalities, find one that is univariate of degree ≥ 1.
fn find_univariate_eliminant(remaining: &[Polynomial]) -> Option<(Polynomial, Var)> {
    for eq in remaining {
        if eq.is_constant() {
            continue;
        }
        let vars = eq.vars();
        if vars.len() == 1 {
            let v = vars[0];
            if eq.degree(v) >= 1 {
                return Some((eq.clone(), v));
            }
        }
    }
    None
}

/// Level-1 resultant elimination for a (conic ∩ conic) two-equation system.
///
/// Picks a shared variable, eliminates it via `Polynomial::resultant`, and
/// returns the eliminant if it is univariate of degree ≥ 1. The eliminant from
/// the in-crate resultant is documented as approximate; soundness is preserved
/// because the final per-atom back-substitution verification gates every SAT —
/// an inexact resultant can only fail to find a model, never fabricate one.
fn try_resultant_eliminant(remaining: &[Polynomial]) -> Option<(Polynomial, Var)> {
    if remaining.len() != 2 {
        return None;
    }
    let p = &remaining[0];
    let r = &remaining[1];

    // Find a variable shared by both, to eliminate.
    let pv = p.vars();
    let rv = r.vars();
    let shared: Vec<Var> = pv.iter().copied().filter(|v| rv.contains(v)).collect();
    if shared.is_empty() {
        return None;
    }

    // Eliminate one shared var; the eliminant should be univariate in the other.
    for &elim in &shared {
        let res = p.resultant(r, elim);
        if res.is_zero() || res.is_constant() {
            continue;
        }
        let vars = res.vars();
        if vars.len() == 1 && res.degree(vars[0]) >= 1 {
            return Some((res, vars[0]));
        }
    }
    None
}

/// Build the exact assignment for every system variable.
///
/// `root_var` takes `root`. Each elimination `v := f` (newest last) is resolved
/// back to a value in `root_var` only. We only accept the case where the chained
/// substitution leaves a polynomial univariate in `root_var` whose value we can
/// realise exactly:
///   - a rational constant (representable as a rational AlgebraicNumber), or
///   - exactly `root_var` itself (reuse `root`).
///
/// Anything more complex (a non-trivial polynomial of `root_var`) is conservative
/// territory we do not yet model exactly ⇒ return `None` (fall back).
fn build_assignment(
    _q: &Polynomial,
    root_var: Var,
    root: &AlgebraicNumber,
    subs: &[(Var, Polynomial)],
    all_vars: &[Var],
) -> Option<Vec<(Var, AlgebraicNumber)>> {
    let mut out: Vec<(Var, AlgebraicNumber)> = Vec::new();
    out.push((root_var, root.clone()));

    // Resolve each eliminated variable. Apply the *later* substitutions to each
    // `f` so it is expressed purely in terms of variables that are themselves
    // resolved (ultimately root_var).
    for idx in 0..subs.len() {
        let (v, f) = &subs[idx];
        // Apply all substitutions recorded AFTER this one (which eliminate the
        // vars that `f` may still mention).
        let mut resolved = f.clone();
        for (lv, lf) in subs.iter().skip(idx + 1) {
            if resolved.vars().contains(lv) {
                resolved = resolved.substitute(*lv, lf);
            }
        }

        let value = realise_in_root(&resolved, root_var, root)?;
        out.push((*v, value));
    }

    // Sanity: every variable of the system must now have a value.
    for &v in all_vars {
        if !out.iter().any(|(w, _)| *w == v) {
            return None;
        }
    }

    Some(out)
}

/// Realise a polynomial `expr` (in `root_var` only, or constant) as an exact
/// algebraic value, given `root_var = root`.
fn realise_in_root(
    expr: &Polynomial,
    root_var: Var,
    root: &AlgebraicNumber,
) -> Option<AlgebraicNumber> {
    if expr.is_constant() {
        return Some(AlgebraicNumber::from_rational(expr.constant_value()));
    }
    let vars = expr.vars();
    if vars.len() != 1 || vars[0] != root_var {
        return None;
    }
    // expr == c1 * root_var + c0 ?  (affine in root_var) — the c1*x + c0 case.
    if expr.degree(root_var) == 1 {
        let c1 = expr.univ_coeff(root_var, 1);
        let c0 = expr.univ_coeff(root_var, 0);
        // Pure identity `root_var` (c1 == 1, c0 == 0): reuse the root exactly.
        if c1 == BigRational::from_integer(num_bigint::BigInt::from(1)) && c0.is_zero() {
            return Some(root.clone());
        }
        // Other affine forms are not realised exactly here (would need algebraic
        // arithmetic); be conservative and fall back.
        return None;
    }
    None
}

/// Apply the full substitution chain to a polynomial.
fn apply_subs(p: &Polynomial, subs: &[(Var, Polynomial)]) -> Polynomial {
    let mut out = p.clone();
    for (v, f) in subs {
        if out.vars().contains(v) {
            out = out.substitute(*v, f);
        }
    }
    out
}

/// Convert a multivariate polynomial that is univariate in `var` into the
/// dense `root_counting::Polynomial` (low-to-high coefficients) required by
/// [`AlgebraicNumber::new`]. Returns `None` if `p` mentions any other variable.
fn to_univariate(p: &Polynomial, var: Var) -> Option<UniPolynomial> {
    let vars = p.vars();
    if vars.len() > 1 {
        return None;
    }
    if vars.len() == 1 && vars[0] != var {
        return None;
    }
    let deg = p.degree(var) as usize;
    let mut coeffs = Vec::with_capacity(deg + 1);
    for k in 0..=deg {
        coeffs.push(p.univ_coeff(var, k as u32));
    }
    Some(UniPolynomial::new(coeffs))
}

/// Gather the asserted single-factor equality polynomials from a solver's atoms.
///
/// An atom contributes iff it is an `Atom::Ineq` with `kind == Eq`, exactly one
/// factor, and its boolean variable is currently assigned **true** (asserted at
/// the top level). This respects the boolean structure: a negated equality is
/// not eligible for elimination.
pub(crate) fn collect_asserted_equalities(
    atoms: &[Atom],
    assignment: &Assignment,
) -> Vec<Polynomial> {
    let mut out = Vec::new();
    for atom in atoms {
        if let Atom::Ineq(ineq) = atom {
            if ineq.kind != AtomKind::Eq {
                continue;
            }
            if ineq.factors.len() != 1 {
                continue;
            }
            if !assignment.bool_value(ineq.bool_var).is_true() {
                continue;
            }
            out.push(ineq.factors[0].poly.clone());
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_traits::Signed;

    fn rat(n: i64) -> BigRational {
        BigRational::from_integer(num_bigint::BigInt::from(n))
    }

    #[test]
    fn test_circle_and_line_algebraic() {
        // x^2 + y^2 - 25 = 0  and  y - x = 0
        let x = Polynomial::from_var(0);
        let y = Polynomial::from_var(1);
        let x2 = Polynomial::mul(&x, &x);
        let y2 = Polynomial::mul(&y, &y);
        let circle = Polynomial::sub(&Polynomial::add(&x2, &y2), &Polynomial::constant(rat(25)));
        let line = Polynomial::sub(&y, &x);

        let sol = try_solve_equalities(&[circle, line]).expect("should solve circle/line");
        assert_eq!(sol.values.len(), 2);

        // x must satisfy 2x^2 - 25 = 0 (i.e. its minimal polynomial divides it).
        let xnum = &sol
            .values
            .iter()
            .find(|(v, _)| *v == 0)
            .expect("x present")
            .1;
        // The defining polynomial should have a real root in the isolating interval,
        // and 2x^2 - 25 should be a multiple of the minimal polynomial.
        let lo = xnum.lower.clone();
        let hi = xnum.upper.clone();
        // 2x^2 - 25 changes sign across the isolating interval.
        let f = |t: &BigRational| rat(2) * t * t - rat(25);
        assert!(
            f(&lo).signum() != f(&hi).signum() || f(&lo).is_zero() || f(&hi).is_zero(),
            "2x^2-25 must straddle a root in the isolating interval"
        );

        // y must equal x (same algebraic number representation).
        let ynum = &sol
            .values
            .iter()
            .find(|(v, _)| *v == 1)
            .expect("y present")
            .1;
        assert_eq!(xnum.lower, ynum.lower);
        assert_eq!(xnum.upper, ynum.upper);
        assert_eq!(xnum.minimal_poly, ynum.minimal_poly);
    }

    #[test]
    fn test_falls_back_on_non_reducible() {
        // A single bivariate equality with no linear variable: x^2 + y^2 - 1 = 0.
        // Not reducible to univariate by linear substitution and only one eq, so
        // resultant elimination (needs 2 eqs) does not apply ⇒ None (fall back).
        let x = Polynomial::from_var(0);
        let y = Polynomial::from_var(1);
        let x2 = Polynomial::mul(&x, &x);
        let y2 = Polynomial::mul(&y, &y);
        let circle = Polynomial::sub(&Polynomial::add(&x2, &y2), &Polynomial::constant(rat(1)));
        assert!(try_solve_equalities(&[circle]).is_none());
    }

    #[test]
    fn test_no_real_root_falls_back() {
        // x^2 + 1 = 0 (no real root) AND y - x = 0 — eliminant x^2+1 has no real
        // root, so the KB returns None (never reports Unsat).
        let x = Polynomial::from_var(0);
        let y = Polynomial::from_var(1);
        let x2 = Polynomial::mul(&x, &x);
        let eq = Polynomial::add(&x2, &Polynomial::constant(rat(1)));
        let line = Polynomial::sub(&y, &x);
        assert!(try_solve_equalities(&[eq, line]).is_none());
    }

    #[test]
    fn test_rational_solution_falls_back() {
        // 2x - 6 = 0 (x = 3) AND y - x = 0 (y = 3). Linear, RATIONAL solution.
        // The system is reducible (y:=x, then 2x-6=0), but the root is rational
        // and therefore representable by the base CDCL+CAD search. The KB is the
        // irrational-solution recognizer, so it falls back here (returns None) to
        // stay strictly additive.
        let x = Polynomial::from_var(0);
        let y = Polynomial::from_var(1);
        let eq = Polynomial::sub(&Polynomial::scale(&x, &rat(2)), &Polynomial::constant(rat(6)));
        let line = Polynomial::sub(&y, &x);
        assert!(try_solve_equalities(&[eq, line]).is_none());
    }
}
