//! CDCAC — Conflict-Driven Cylindrical Algebraic Coverings (M4 step B).
//!
//! This is the multivariate decision tier. For a **two-variable** problem it
//! realises a covering of the outer axis: the McCallum projection (eliminating
//! the inner variable) gives polynomials in the outer variable whose roots are
//! the *only* places the inner-feasibility structure can change. So between
//! consecutive projection roots — a "cell" of the outer axis — the inner
//! problem is satisfiable-or-not *uniformly*, and a single rational
//! representative decides the whole cell. Sampling one point per cell, plus
//! each breakpoint, then either finds a model (some outer value admits an inner
//! value) or proves every outer value infeasible (UNSAT).
//!
//! Soundness rests on (a) the covering lemma proven in Verus
//! (`covering_implies_unsat`: cells that each rule out the problem and cover ℝ
//! ⟹ UNSAT) and (b) the McCallum cell-invariance; the z3-differential is the
//! empirical backstop. A `Sat` is always a concrete model passed through G-SAT,
//! so it can never be wrong regardless of projection correctness.
//!
//! **Scope (step B):** the *rational-breakpoint* case — projection roots all
//! rational, so the cells partition the outer axis at rational points. When a
//! projection root is irrational the decision is deferred (`Unknown`); the
//! algebraic-breakpoint case is step B2 (multivariate `sign_at_algebraic`).

use num_rational::BigRational;
use rustc_hash::FxHashMap;

use crate::atom::{AtomCmp, PolyAtom, Polynomial, Var, VarSort};
use crate::univariate::{self, UniResult};
use crate::value::{Model, Value};

/// Keep `p` as a breakpoint polynomial only if it carries structure on the outer
/// axis (non-zero, not a pure numeric constant) and is new.
fn push_informative(out: &mut Vec<Polynomial>, p: Polynomial) {
    if p.is_zero() || p.is_constant() {
        return;
    }
    if !out.contains(&p) {
        out.push(p);
    }
}

/// The outcome of the CDCAC tier.
pub enum Decision {
    Unsat,
    Sat(Model),
    /// Could not decide (irrational breakpoint, or a model that did not verify);
    /// the caller falls back to the search.
    Unknown,
}

/// Decide a two-variable problem over `{va, vb}`. Tries eliminating each
/// variable in turn (one order may have rational breakpoints when the other
/// does not); the first conclusive order wins.
#[must_use]
pub fn decide_2var(atoms: &[PolyAtom], va: Var, vb: Var, sort: VarSort) -> Decision {
    match decide_oriented(atoms, va, vb, sort) {
        Decision::Unknown => decide_oriented(atoms, vb, va, sort),
        decided => decided,
    }
}

/// Decide with `outer` as the axis we cover and `inner` as the eliminated
/// variable.
fn decide_oriented(atoms: &[PolyAtom], outer: Var, inner: Var, sort: VarSort) -> Decision {
    // Breakpoint polynomials on the outer axis: the McCallum projection
    // (eliminating `inner`) plus any constraint that is already univariate in
    // `outer` (its own sign-changes are breakpoints too).
    let active: Vec<crate::atom::Polynomial> =
        atoms.iter().filter(|a| a.poly.degree(inner) >= 1).map(|a| a.poly.clone()).collect();

    // Cost guard: the projection's pairwise resultants are Sylvester
    // determinants of size up to 2·(max inner degree); cofactor expansion is
    // super-polynomial, so cap the size and the constraint count. Beyond the cap
    // we decline (Unknown → the search handles it) rather than stall — sound.
    let max_inner_deg = active.iter().map(|p| p.degree(inner)).max().unwrap_or(0);
    if max_inner_deg > 4 || active.len() > 5 {
        return Decision::Unknown;
    }

    // McCallum projection WITH well-orientedness detection. A discriminant or
    // resultant that is identically zero means the input is not square-free /
    // shares a factor in `inner` — the projection is then degenerate and
    // cell-invariance can FAIL (e.g. `x³(4x+3y)<0`: the x³ factor makes the
    // discriminant ≡ 0, dropping the y=0 breakpoint → a false unsat). In that
    // case McCallum is not well-oriented, so we bail to Unknown (sound).
    let mut breakpoint_polys: Vec<crate::atom::Polynomial> = Vec::new();
    for p in &active {
        push_informative(&mut breakpoint_polys, p.leading_coeff_wrt(inner));
        if p.degree(inner) >= 2 {
            let disc = p.discriminant(inner);
            if disc.is_zero() {
                return Decision::Unknown; // not square-free in `inner`
            }
            push_informative(&mut breakpoint_polys, disc);
        }
    }
    for i in 0..active.len() {
        for j in (i + 1)..active.len() {
            let res = active[i].resultant(&active[j], inner);
            if res.is_zero() {
                return Decision::Unknown; // common factor in `inner`
            }
            push_informative(&mut breakpoint_polys, res);
        }
    }
    for a in atoms {
        if a.poly.degree(inner) == 0 && a.poly.degree(outer) >= 1 {
            push_informative(&mut breakpoint_polys, a.poly.clone());
        }
    }

    // ── Fast path: all breakpoints rational ──────────────────────────────
    // `real_roots_rational` is cheap (Sturm count + rational-root candidates,
    // no bisection). If every breakpoint polynomial has only rational roots,
    // sample one rep per open cell + each breakpoint and decide directly.
    let mut breaks: Vec<BigRational> = Vec::new();
    let mut all_rational = true;
    for bp in &breakpoint_polys {
        let coeffs: Vec<BigRational> = (0..=bp.degree(outer)).map(|k| bp.univ_coeff(outer, k)).collect();
        match univariate::real_roots_rational(&coeffs) {
            Some(roots) => breaks.extend(roots),
            None => {
                all_rational = false;
                break;
            }
        }
    }
    if all_rational {
        breaks.sort();
        breaks.dedup();
        for r in cell_and_breakpoint_samples(&breaks) {
            match decide_inner_at(atoms, outer, inner, &r, sort) {
                InnerResult::SatModel(m) => return Decision::Sat(m),
                InnerResult::Unsat => {}
                InnerResult::Indeterminate => return Decision::Unknown,
            }
        }
        return Decision::Unsat;
    }

    // ── Irrational breakpoints: strict-only open-cell path (step B2a) ─────
    // For STRICT-only constraints the feasible set is open, so it intersects a
    // full-dimensional cell iff nonempty — the measure-zero breakpoints cannot
    // add feasibility. So sampling one rational point per OPEN cell (between the
    // isolating intervals — no algebraic arithmetic) decides it. Non-strict
    // constraints (a feasible piece can live exactly on an algebraic breakpoint)
    // are deferred to step B2b (multivariate sign_at_algebraic).
    let strict_only = atoms.iter().all(|a| matches!(a.op, AtomCmp::Lt | AtomCmp::Gt | AtomCmp::Ne));
    if !strict_only {
        return Decision::Unknown;
    }
    let mut product = crate::atom::Polynomial::one();
    for bp in &breakpoint_polys {
        product = &product * bp;
    }
    // Isolating high-degree polynomials (bisection) is expensive; cap it.
    if product.degree(outer) > 8 {
        return Decision::Unknown;
    }
    let prod_coeffs: Vec<BigRational> = (0..=product.degree(outer)).map(|k| product.univ_coeff(outer, k)).collect();
    for r in univariate::cell_sample_points(&prod_coeffs) {
        match decide_inner_at(atoms, outer, inner, &r, sort) {
            InnerResult::SatModel(m) => return Decision::Sat(m),
            InnerResult::Unsat => {}
            InnerResult::Indeterminate => return Decision::Unknown,
        }
    }
    Decision::Unsat
}

/// One rational representative per open cell of the axis partitioned by sorted
/// distinct rational `breaks`, plus each breakpoint itself.
fn cell_and_breakpoint_samples(breaks: &[BigRational]) -> Vec<BigRational> {
    use num_bigint::BigInt;
    let one = BigRational::from_integer(BigInt::from(1));
    if breaks.is_empty() {
        return vec![BigRational::from_integer(BigInt::from(0))];
    }
    let two = BigRational::from_integer(BigInt::from(2));
    let mut pts = Vec::with_capacity(2 * breaks.len() + 1);
    pts.push(&breaks[0] - &one);
    for (i, b) in breaks.iter().enumerate() {
        pts.push(b.clone());
        if i + 1 < breaks.len() {
            pts.push((b + &breaks[i + 1]) / &two);
        }
    }
    pts.push(&breaks[breaks.len() - 1] + &one);
    pts
}

enum InnerResult {
    SatModel(Model),
    Unsat,
    Indeterminate,
}

/// Substitute `outer = r` and decide the resulting univariate problem in
/// `inner`; on Sat, build and G-SAT-verify the full 2-D model.
fn decide_inner_at(
    atoms: &[PolyAtom],
    outer: Var,
    inner: Var,
    r: &BigRational,
    sort: VarSort,
) -> InnerResult {
    let uni: Vec<(Vec<BigRational>, crate::atom::AtomCmp)> = atoms
        .iter()
        .map(|a| {
            let p = a.poly.eval_at(outer, r); // poly in `inner` (or constant)
            let coeffs: Vec<BigRational> = (0..=p.degree(inner)).map(|k| p.univ_coeff(inner, k)).collect();
            (coeffs, a.op)
        })
        .collect();

    let inner_val = match univariate::decide(&uni) {
        UniResult::Unsat => return InnerResult::Unsat,
        UniResult::Sat(w) => {
            // integer sort: a non-integer inner witness is no integer model
            if sort == VarSort::Integer && !w.is_integer() {
                return InnerResult::Indeterminate;
            }
            Value::Rational(w)
        }
        UniResult::SatAlgebraic(alpha) => {
            if sort == VarSort::Integer {
                return InnerResult::Indeterminate; // algebraic ⇒ no integer
            }
            Value::Algebraic(alpha)
        }
    };
    // integer sort: the outer coordinate must be an integer too
    if sort == VarSort::Integer && !r.is_integer() {
        return InnerResult::Indeterminate;
    }

    let mut m = Model::new();
    m.insert(outer, Value::Rational(r.clone()));
    m.insert(inner, inner_val);
    if m.checks(atoms) {
        InnerResult::SatModel(m)
    } else {
        InnerResult::Indeterminate // model did not verify ⇒ don't trust this slice
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// n-variable CDCAC (≥ 3 variables) — recursive CAD sample-point decision
// ─────────────────────────────────────────────────────────────────────────────

/// Decide an **n-variable** (n ≥ 3) real problem by sampling one rational point
/// per cell of the cylindrical algebraic decomposition and checking the
/// conjunction at each. A satisfying sample ⇒ `Sat` (G-SAT-verified, always
/// sound). For STRICT-only constraints the feasible set is open, so every cell
/// representative failing ⇒ `Unsat` (the open set must meet a full-dimensional
/// cell). Non-strict or any degeneracy/cost-cap ⇒ `Unknown`. Integer sort is
/// not handled here (⇒ Unknown). Soundness of the `Unsat` rests on McCallum
/// cell-invariance at every projection level (Verus `cdcac::…`,
/// differential-guarded; degenerate levels bail).
#[must_use]
pub fn decide_nvar(atoms: &[PolyAtom], vars: &[Var], sort: VarSort) -> Decision {
    if sort == VarSort::Integer {
        return Decision::Unknown; // n-var integer feasibility is M5+ territory
    }
    let polys: Vec<Polynomial> = atoms.iter().map(|a| a.poly.clone()).collect();

    // (1) Complete rational CAD. When every projection breakpoint is rational we
    // can sample *every* cell — sectors and sections — so all-reps-infeasible is
    // UNSAT for any mix of strict/non-strict atoms (a closed feasible set would
    // still occupy some sampled cell). This also sidesteps the projection-product
    // blowup (it unions per-polynomial rational roots instead).
    if let Some(cells) = rational_cad_cells(&polys, vars) {
        for s in &cells {
            if let Some(m) = sat_model(s, atoms) {
                return Decision::Sat(m);
            }
        }
        return Decision::Unsat;
    }

    // (2) Open-cell fallback. An irrational breakpoint means we only sample full-
    // dimensional cells, so we can conclude UNSAT only for a strict-only
    // conjunction (its open feasible set, if non-empty, must meet a full-dim
    // cell). A `Sat` is a G-SAT-verified model, always sound.
    let samples = match cad_sample_points(&polys, vars) {
        Some(s) => s,
        None => return Decision::Unknown,
    };
    for s in &samples {
        if let Some(m) = sat_model(s, atoms) {
            return Decision::Sat(m);
        }
    }
    if atoms.iter().all(|a| matches!(a.op, AtomCmp::Lt | AtomCmp::Gt | AtomCmp::Ne)) {
        Decision::Unsat
    } else {
        Decision::Unknown // a lower-dimensional feasible piece may live on a boundary
    }
}

/// Build the rational model from a cell sample assignment and return it iff it
/// satisfies every atom (G-SAT). A returned `Sat` model is thus always sound.
fn sat_model(s: &FxHashMap<Var, BigRational>, atoms: &[PolyAtom]) -> Option<Model> {
    let mut m = Model::new();
    for (&v, r) in s {
        m.insert(v, Value::Rational(r.clone()));
    }
    if m.checks(atoms) {
        Some(m)
    } else {
        None
    }
}

/// Maximum CAD sample points produced before giving up (`None`).
const MAX_CAD_SAMPLES: usize = 4000;

/// Sample points of the CAD of `polys` over `vars`: one rational full assignment
/// per cell. `None` on degeneracy (a discriminant/resultant ≡ 0 — not
/// well-oriented) or if the count/degree exceeds the caps.
fn cad_sample_points(polys: &[Polynomial], vars: &[Var]) -> Option<Vec<FxHashMap<Var, BigRational>>> {
    if vars.is_empty() {
        return Some(vec![FxHashMap::default()]);
    }
    if vars.len() == 1 {
        let v = vars[0];
        let coeffs = univariate_product_coeffs(polys, v)?;
        return Some(
            univariate::cell_sample_points(&coeffs)
                .into_iter()
                .map(|r| {
                    let mut m = FxHashMap::default();
                    m.insert(v, r);
                    m
                })
                .collect(),
        );
    }

    let last = *vars.last().unwrap();
    let lower_vars = &vars[..vars.len() - 1];

    // McCallum projection eliminating `last`, with cost cap + degeneracy guard.
    let proj = mccallum_project(polys, last, lower_vars.len())?;

    // Recurse for the lower-dimensional arrangement, then lift each sample.
    let lower_samples = cad_sample_points(&proj, lower_vars)?;
    let mut out: Vec<FxHashMap<Var, BigRational>> = Vec::new();
    for s in &lower_samples {
        // substitute the lower sample into the originals → univariate in `last`
        let substituted: Vec<Polynomial> = polys
            .iter()
            .map(|p| {
                let mut q = p.clone();
                for (&var, val) in s {
                    q = q.eval_at(var, val);
                }
                q
            })
            .collect();
        let coeffs = univariate_product_coeffs(&substituted, last)?;
        for r in univariate::cell_sample_points(&coeffs) {
            let mut full = s.clone();
            full.insert(last, r);
            out.push(full);
            if out.len() > MAX_CAD_SAMPLES {
                return None;
            }
        }
    }
    Some(out)
}

/// Largest degree of the product polynomial whose real roots are the cell
/// boundaries on one axis. The product of the projection polynomials can reach
/// degree ≈ Σ degrees (≈100 for a dense 3-variable arrangement), and the Sturm
/// real-root isolation on such a high-degree polynomial with the attendant
/// coefficient blowup is intractable. Capping the product degree keeps the
/// base-case/lift root isolation cheap; exceeding it bails the whole CAD to
/// `Unknown` (always sound — the downstream search still looks for a model).
const MAX_PRODUCT_DEGREE: u32 = 20;

/// Coefficient vector (low-degree-first, in `v`) of the **product** of the
/// `polys` that have positive degree in `v` — the polynomial whose roots are all
/// the cell boundaries on `v`'s axis. `None` if the product degree would exceed
/// [`MAX_PRODUCT_DEGREE`] (cost cap — bails the CAD to `Unknown`).
fn univariate_product_coeffs(polys: &[Polynomial], v: Var) -> Option<Vec<BigRational>> {
    let total_degree: u32 = polys.iter().map(|p| p.degree(v)).filter(|&d| d >= 1).sum();
    if total_degree > MAX_PRODUCT_DEGREE {
        return None;
    }
    let mut product = Polynomial::one();
    for p in polys {
        if p.degree(v) >= 1 {
            product = &product * p;
        }
    }
    Some((0..=product.degree(v)).map(|k| product.univ_coeff(v, k)).collect())
}

/// McCallum projection eliminating `last` from `polys`: leading coefficients +
/// discriminants (for the degree-≥2 ones) + pairwise resultants of the active
/// polynomials, plus the `last`-free polynomials carried down verbatim. Returns
/// `None` on a **cost-cap** breach or a **well-orientedness** failure (a
/// discriminant or resultant identically zero ⇒ non-square-free / shared factor,
/// so the projection is not delineable). `remaining` is the number of variables
/// left after `last`, used to size the cost cap.
///
/// Cost cap: a resultant/discriminant is a Sylvester determinant of dimension
/// `deg_p + deg_q` whose *entries* are polynomials in the `remaining` variables.
/// (The determinant itself is now `O(n³)` fraction-free Bareiss, but the
/// *result*'s degree — and the downstream root isolation — still grows with the
/// entry arity.) So cap the per-variable degree tighter when ≥2 variables remain
/// (multivariate entries) than when one remains. Bailing is always sound: it only
/// yields `Unknown`.
pub(crate) fn mccallum_project(
    polys: &[Polynomial],
    last: Var,
    remaining: usize,
) -> Option<Vec<Polynomial>> {
    // McCallum projection is only valid on a *square-free basis*. Reduce each
    // input to its monomial-free primitive part (re-adding the divided-out
    // variable factors) so a shared/repeated **monomial** factor — the dominant
    // nullification source (e.g. `x0³·x1`, `4x0·x1³`) — no longer zeroes a
    // discriminant or resultant. A residual non-monomial repeated factor still
    // bails to `Unknown` (sound).
    let basis = square_free_basis(polys);
    let active: Vec<&Polynomial> = basis.iter().filter(|p| p.degree(last) >= 1).collect();
    let deg_cap = if remaining >= 2 { 2 } else { 4 };
    if active.iter().any(|p| p.degree(last) > deg_cap) || active.len() > 5 {
        return None; // cost cap (projection would blow up)
    }

    let mut proj: Vec<Polynomial> = Vec::new();
    for p in &active {
        push_informative(&mut proj, p.leading_coeff_wrt(last));
        if p.degree(last) >= 2 {
            let disc = p.discriminant(last);
            if disc.is_zero() {
                return None; // not square-free in `last`
            }
            push_informative(&mut proj, disc);
        }
    }
    for i in 0..active.len() {
        for j in (i + 1)..active.len() {
            let res = active[i].resultant(active[j], last);
            if res.is_zero() {
                return None; // common factor in `last`
            }
            push_informative(&mut proj, res);
        }
    }
    // constraints with no `last` carry their own lower-dimensional structure
    for p in &basis {
        if p.degree(last) == 0 {
            push_informative(&mut proj, p.clone());
        }
    }
    Some(proj)
}

/// Reduce projection inputs toward a **square-free basis** (the precondition of
/// McCallum projection): divide out each polynomial's monomial content (the
/// largest monomial dividing every term) and re-add the divided-out variables as
/// their own degree-1 boundary polynomials `{xᵥ}`. The variety is preserved
/// (`p = content · primitive`, and `{content = 0} = ⋃ {xᵥ = 0}`), but a shared or
/// repeated **monomial** factor no longer nullifies a discriminant/resultant — the
/// dominant nullification source in practice. A residual *non-monomial* repeated
/// factor is not removed (full square-free factorisation / Lazard is a later
/// milestone), so such a case still bails to `Unknown` (sound).
fn square_free_basis(polys: &[Polynomial]) -> Vec<Polynomial> {
    use oxiz_math::polynomial::{Monomial, MonomialOrder, Term};
    let mut out: Vec<Polynomial> = Vec::new();
    for p in polys {
        if p.is_zero() {
            continue;
        }
        let content: Vec<(Var, u32)> = p
            .vars()
            .into_iter()
            .filter_map(|v| {
                let m = p.terms().iter().map(|t| t.monomial.degree(v)).min().unwrap_or(0);
                (m >= 1).then_some((v, m))
            })
            .collect();
        if content.is_empty() {
            push_informative(&mut out, p.clone());
            continue;
        }
        let cm = Monomial::from_powers(content.iter().copied());
        let terms = p
            .terms()
            .iter()
            .filter_map(|t| t.monomial.div(&cm).map(|m| Term::new(t.coeff.clone(), m)));
        push_informative(&mut out, Polynomial::from_terms(terms, MonomialOrder::default()));
        for (v, _) in content {
            push_informative(&mut out, Polynomial::from_var_power(v, 1));
        }
    }
    out
}

/// The **distinct rational breakpoints** of `polys` on `v`'s axis: the union of
/// every polynomial's real roots in `v`, sorted. `None` if *any* active
/// polynomial has an irrational real root — the signal that the cells on this
/// axis cannot all be sampled at rational points, so the complete (boundary-
/// inclusive) rational CAD does not apply (the caller falls back to the open-cell
/// path). Unlike [`univariate_product_coeffs`] this never forms the product, so
/// it stays cheap regardless of how many polynomials there are.
fn rational_breakpoints(polys: &[Polynomial], v: Var) -> Option<Vec<BigRational>> {
    let mut roots: std::collections::BTreeSet<BigRational> = std::collections::BTreeSet::new();
    for p in polys {
        if p.degree(v) >= 1 {
            let coeffs: Vec<BigRational> = (0..=p.degree(v)).map(|k| p.univ_coeff(v, k)).collect();
            let rs = univariate::real_roots_rational(&coeffs)?; // irrational root ⇒ None
            roots.extend(rs);
        }
    }
    Some(roots.into_iter().collect())
}

/// One sample point per cell of `ℝ` cut at the (sorted, distinct) `roots`:
/// **both** the open sectors (below the least root, the gap midpoints, above the
/// greatest) **and** the section points (the roots themselves). Sampling the
/// boundaries — not just the interiors — is what lets the rational CAD decide
/// non-strict (closed) conjunctions soundly. A root-free axis yields `[0]`.
fn cell_points_with_boundaries(roots: &[BigRational]) -> Vec<BigRational> {
    use num_bigint::BigInt;
    if roots.is_empty() {
        return vec![BigRational::from_integer(BigInt::from(0))];
    }
    let one = BigRational::from_integer(BigInt::from(1));
    let two = BigRational::from_integer(BigInt::from(2));
    let mut pts = Vec::with_capacity(2 * roots.len() + 1);
    pts.push(&roots[0] - &one); // below the least root
    pts.push(roots[0].clone()); // the least root (section)
    for w in roots.windows(2) {
        pts.push((&w[0] + &w[1]) / &two); // interior of the gap (sector)
        pts.push(w[1].clone()); // the next root (section)
    }
    pts.push(roots.last().unwrap() + &one); // above the greatest root
    pts
}

/// Sample points of the **complete rational CAD** of `polys` over `vars` — one
/// representative for *every* cell of all dimensions (sectors and sections) —
/// returned **only** when every projection breakpoint at every level is rational
/// (so all cell boundaries have rational coordinates). `None` as soon as an
/// irrational breakpoint appears (the caller falls back to the open-cell, strict-
/// only path) or a cost/degeneracy guard trips. Because it covers boundary cells
/// too, infeasibility of all representatives is UNSAT for *any* mix of
/// strict/non-strict atoms (the closed feasible set, if any, would occupy some
/// cell we sampled).
fn rational_cad_cells(polys: &[Polynomial], vars: &[Var]) -> Option<Vec<FxHashMap<Var, BigRational>>> {
    if vars.is_empty() {
        return Some(vec![FxHashMap::default()]);
    }
    if vars.len() == 1 {
        let v = vars[0];
        let roots = rational_breakpoints(polys, v)?;
        return Some(
            cell_points_with_boundaries(&roots)
                .into_iter()
                .map(|r| {
                    let mut m = FxHashMap::default();
                    m.insert(v, r);
                    m
                })
                .collect(),
        );
    }

    let last = *vars.last().unwrap();
    let lower_vars = &vars[..vars.len() - 1];
    let proj = mccallum_project(polys, last, lower_vars.len())?;
    let lower_samples = rational_cad_cells(&proj, lower_vars)?;
    let mut out: Vec<FxHashMap<Var, BigRational>> = Vec::new();
    for s in &lower_samples {
        let substituted: Vec<Polynomial> = polys
            .iter()
            .map(|p| {
                let mut q = p.clone();
                for (&var, val) in s {
                    q = q.eval_at(var, val);
                }
                q
            })
            .collect();
        let roots = rational_breakpoints(&substituted, last)?;
        for r in cell_points_with_boundaries(&roots) {
            let mut full = s.clone();
            full.insert(last, r);
            out.push(full);
            if out.len() > MAX_CAD_SAMPLES {
                return None;
            }
        }
    }
    Some(out)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::atom::{AtomCmp, OriginId, Polynomial};

    fn at(coeffs: &[(i64, &[(Var, u32)])], op: AtomCmp) -> PolyAtom {
        PolyAtom::new(Polynomial::from_coeffs_int(coeffs), op, VarSort::Real, OriginId(0))
    }
    fn is_unsat(d: Decision) -> bool {
        matches!(d, Decision::Unsat)
    }
    fn is_sat(d: Decision) -> bool {
        matches!(d, Decision::Sat(_))
    }

    #[test]
    fn two_var_sat() {
        // x·y = 1 ∧ x = 2  → y = 1/2 : sat (rational breakpoints)
        let v = decide_2var(
            &[
                at(&[(1, &[(0, 1), (1, 1)]), (-1, &[])], AtomCmp::Eq),
                at(&[(1, &[(0, 1)]), (-2, &[])], AtomCmp::Eq),
            ],
            0,
            1,
            VarSort::Real,
        );
        assert!(is_sat(v));
    }

    #[test]
    fn two_var_unsat_linear() {
        // y > x ∧ y < x - 1  → unsat (no y between x and x-1)
        let v = decide_2var(
            &[
                at(&[(1, &[(1, 1)]), (-1, &[(0, 1)])], AtomCmp::Gt), // y - x > 0
                at(&[(1, &[(1, 1)]), (-1, &[(0, 1)]), (1, &[])], AtomCmp::Lt), // y - x + 1 < 0
            ],
            0,
            1,
            VarSort::Real,
        );
        assert!(is_unsat(v), "expected unsat");
    }

    #[test]
    fn strict_irrational_breakpoint_unsat() {
        // y > x ∧ y < x - 1 (unsatisfiable, strict) together with x² < 2, which
        // contributes the IRRATIONAL breakpoints x = ±√2. The strict-only
        // open-cell path (step B2a) decides UNSAT without any algebraic
        // arithmetic — it samples the open cells between the isolating intervals.
        let v = decide_2var(
            &[
                at(&[(1, &[(1, 1)]), (-1, &[(0, 1)])], AtomCmp::Gt), // y - x > 0
                at(&[(1, &[(1, 1)]), (-1, &[(0, 1)]), (1, &[])], AtomCmp::Lt), // y - x + 1 < 0
                at(&[(1, &[(0, 2)]), (-2, &[])], AtomCmp::Lt),       // x² - 2 < 0
            ],
            0,
            1,
            VarSort::Real,
        );
        assert!(matches!(v, Decision::Unsat), "B2a strict-only irrational-breakpoint path");
    }

    #[test]
    fn degenerate_not_square_free_bails_unknown() {
        // 4x⁴ + 3x³y < 0  =  x³(4x+3y) < 0 : NOT square-free in x (the x³ factor),
        // so the McCallum projection degenerates (disc ≡ 0). Decided over ℝ it is
        // SAT (e.g. x=1,y=-2). CDCAC must bail to Unknown, never report unsat.
        let v = decide_2var(
            &[at(&[(4, &[(0, 4)]), (3, &[(0, 3), (1, 1)])], AtomCmp::Lt)],
            0,
            1,
            VarSort::Integer,
        );
        assert!(matches!(v, Decision::Unknown), "must not decide a degenerate case");
    }

    #[test]
    fn two_var_unsat_product_sign() {
        // x ≥ 1 ∧ y ≥ 1 ∧ x·y < 0  → unsat (both positive ⇒ product positive)
        let v = decide_2var(
            &[
                at(&[(1, &[(0, 1)]), (-1, &[])], AtomCmp::Ge),
                at(&[(1, &[(1, 1)]), (-1, &[])], AtomCmp::Ge),
                at(&[(1, &[(0, 1), (1, 1)])], AtomCmp::Lt),
            ],
            0,
            1,
            VarSort::Real,
        );
        assert!(is_unsat(v), "expected unsat");
    }

    #[test]
    fn nvar_rational_nonstrict_unsat() {
        // 3 variables, all-rational breakpoints, NON-strict atoms: x ≥ 1 ∧ x ≤ 0
        // (∧ y ≥ 0 ∧ z ≥ 0 to make it genuinely 3-variable). The x part is
        // unsatisfiable. Only the complete rational CAD (which samples cell
        // *boundaries*) can decide this — the strict-only open-cell path would
        // leave it `Unknown` since the atoms are `Ge`/`Le`, not strict.
        let v = decide_nvar(
            &[
                at(&[(1, &[(0, 1)]), (-1, &[])], AtomCmp::Ge), // x - 1 ≥ 0
                at(&[(-1, &[(0, 1)])], AtomCmp::Le),           // -x ≤ 0  (x ≥ 0)
                at(&[(1, &[(0, 1)]), (-2, &[])], AtomCmp::Le), // x - 2 ≤ 0  (x ≤ 2)
                at(&[(1, &[(1, 1)])], AtomCmp::Ge),            // y ≥ 0
                at(&[(1, &[(2, 1)])], AtomCmp::Ge),            // z ≥ 0
            ],
            &[0, 1, 2],
            VarSort::Real,
        );
        // x ≥ 1 is consistent with x ≥ 0 ∧ x ≤ 2, so this is actually SAT — fix
        // the constraints to be genuinely unsat: x ≥ 1 ∧ x ≤ 0.
        let _ = v;
        let v = decide_nvar(
            &[
                at(&[(1, &[(0, 1)]), (-1, &[])], AtomCmp::Ge), // x - 1 ≥ 0  (x ≥ 1)
                at(&[(-1, &[(0, 1)])], AtomCmp::Ge),           // -x ≥ 0     (x ≤ 0)
                at(&[(1, &[(1, 1)])], AtomCmp::Ge),            // y ≥ 0
                at(&[(1, &[(2, 1)])], AtomCmp::Ge),            // z ≥ 0
            ],
            &[0, 1, 2],
            VarSort::Real,
        );
        assert!(is_unsat(v), "rational-CAD must decide non-strict 3-var unsat");
    }

    #[test]
    fn nvar_rational_nonstrict_sat() {
        // 3 variables, rational breakpoints, non-strict, SATISFIABLE: x ≥ 1 ∧
        // x ≤ 2 ∧ y ≥ 0 ∧ z ≤ 5. A boundary/interior sample (e.g. x=1,y=0,z=0)
        // satisfies it; the G-SAT check makes the `Sat` sound regardless.
        let v = decide_nvar(
            &[
                at(&[(1, &[(0, 1)]), (-1, &[])], AtomCmp::Ge), // x ≥ 1
                at(&[(1, &[(0, 1)]), (-2, &[])], AtomCmp::Le), // x ≤ 2
                at(&[(1, &[(1, 1)])], AtomCmp::Ge),            // y ≥ 0
                at(&[(1, &[(2, 1)]), (-5, &[])], AtomCmp::Le), // z ≤ 5
            ],
            &[0, 1, 2],
            VarSort::Real,
        );
        assert!(is_sat(v), "rational-CAD must find a 3-var model");
    }

    #[test]
    fn nvar_irrational_nonstrict_not_false_unsat() {
        // x² = 2 (irrational breakpoints ±√2), non-strict, with y,z present. This
        // is SAT over ℝ (x=√2, any y,z). The rational CAD must DECLINE (irrational
        // breakpoint ⇒ `rational_breakpoints` returns None), and the open-cell
        // path must NOT report unsat for a non-strict atom. So: never `Unsat`.
        let v = decide_nvar(
            &[
                at(&[(1, &[(0, 2)]), (-2, &[])], AtomCmp::Eq), // x² - 2 = 0
                at(&[(1, &[(1, 1)])], AtomCmp::Ge),            // y ≥ 0
                at(&[(1, &[(2, 1)])], AtomCmp::Ge),            // z ≥ 0
            ],
            &[0, 1, 2],
            VarSort::Real,
        );
        assert!(!is_unsat(v), "must never falsely report unsat on a SAT irrational case");
    }
}
