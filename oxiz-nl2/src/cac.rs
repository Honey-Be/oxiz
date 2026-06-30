//! CAC — the model-driven **Conflict-Driven Cylindrical Algebraic Covering**
//! engine (Ábrahám–Davenport–England–Kremer 2020, Algorithm `get_unsat_cover`).
//!
//! Unlike the [`crate::cdcac`] full-CAD tier (which decomposes a whole axis at
//! once and so cannot reach the *irrational-breakpoint, non-strict* frontier),
//! CAC works **top-down with concrete sample points**: it fixes `x₁`, then `x₂`,
//! …; if a partial sample cannot be extended it computes a *covering* of the
//! current axis by unsat intervals — each interval generalised from a conflicting
//! sample via a McCallum projection (so it is genuinely infeasible, not just the
//! point) — until the intervals cover ℝ, concluding the sample is infeasible and
//! projecting that conflict down a dimension. Soundness is the per-dimension
//! covering lemma pre-verified in Verus
//! (`oxiz-nl2-verification::cdcac_covering::interval_covering_refutes`): unsat
//! intervals covering an axis, each certified infeasible, ⟹ the partial sample
//! is inextensible; chained down the dimensions ⟹ global UNSAT.
//!
//! **Algebraic samples.** A boundary (section) sample point is an exact real root
//! — possibly irrational ([`RealRoot::Algebraic`]). Evaluating a constraint at a
//! sample with **one** algebraic coordinate is exact (substitute the rationals,
//! reduce to univariate in the algebraic variable, take [`AlgebraicReal::sign_of`],
//! via [`Model::poly_sign`]); root isolation over such a sample eliminates the
//! algebraic coordinate by a resultant with its defining polynomial, leaving a
//! polynomial over ℚ (the candidate boundaries — a sign-invariance-preserving
//! superset is harmless). A **second** algebraic coordinate leaves the
//! single-extension fragment, so the engine bails to `Unknown` (sound). Any
//! degeneracy (nullification in the projection, a resultant that vanishes, the
//! node budget) likewise yields `Unknown` — never a wrong verdict. Every `Sat` is
//! a concrete model passed through G-SAT, so it can never be wrong.

use core::cmp::Ordering;

use num_rational::BigRational;
use num_traits::Zero;

use crate::atom::{PolyAtom, Polynomial, Var, VarSort};
use crate::cdcac::{mccallum_project, Decision};
use crate::univariate::{self, AlgebraicReal, RealRoot};
use crate::value::{Model, Value};

/// Node budget for the covering search (each `sample_outside` iteration). Hitting
/// it yields `Unknown` — sound.
const NODE_BUDGET: u64 = 50_000;

thread_local! {
    static REASON: std::cell::Cell<&'static str> = const { std::cell::Cell::new("") };
}
/// Record (debug) why the engine could not decide. Read with
/// [`last_unknown_reason`]. Returns `Cover::Unknown` for convenient `?`-free use.
fn bail(reason: &'static str) -> Cover {
    REASON.with(|r| r.set(reason));
    Cover::Unknown
}
/// The reason the most recent [`decide_cac`] returned `Unknown` (debug/telemetry).
#[must_use]
pub fn last_unknown_reason() -> &'static str {
    REASON.with(std::cell::Cell::get)
}

/// A bound of an unsat interval on the current axis.
#[derive(Clone)]
enum Bound {
    NegInf,
    PosInf,
    At(RealRoot),
}

/// An unsat interval on the current axis: an open sector `(lo, hi)`, or — when
/// `point` is set — the single section point `lo (= hi)`. Both kinds are
/// **certified infeasible** for the partial sample.
#[derive(Clone)]
struct Interval {
    lo: Bound,
    hi: Bound,
    point: bool,
}

/// A sampled value on the current axis: a rational interior (sector) point, or an
/// exact boundary (section) root.
enum SamplePoint {
    Sector(BigRational),
    Section(RealRoot),
}

impl SamplePoint {
    fn to_value(&self) -> Value {
        match self {
            SamplePoint::Sector(q) => Value::Rational(q.clone()),
            SamplePoint::Section(RealRoot::Rational(r)) => Value::Rational(r.clone()),
            SamplePoint::Section(RealRoot::Algebraic(a)) => Value::Algebraic(a.clone()),
        }
    }
}

/// The result of covering one dimension's axis.
enum Cover {
    /// A full satisfying assignment was found.
    Sat(Model),
    /// The partial sample is infeasible; the polynomials whose roots/signs the
    /// covering rests on are returned for the caller to project down a dimension.
    Unsat(Vec<Polynomial>),
    /// Could not decide exactly (degeneracy / fragment limit / budget).
    Unknown,
}

/// Decide a conjunction of polynomial atoms by CAC (DESIGN.md §4, the algebraic-
/// breakpoint tier). `vars` are the variables present; `sort` must be real.
#[must_use]
pub fn decide_cac(atoms: &[PolyAtom], vars: &[Var], sort: VarSort) -> Decision {
    if sort == VarSort::Integer {
        REASON.with(|r| r.set("integer-sort"));
        return Decision::Unknown; // integer feasibility is the NIA tier
    }
    let mut order: Vec<Var> = vars.to_vec();
    order.sort_unstable(); // x₁ ≺ x₂ ≺ … by variable index
    let mut budget = NODE_BUDGET;
    match get_unsat_cover(atoms, &order, &Model::new(), 0, &mut budget) {
        Cover::Sat(m) => {
            if m.checks(atoms) {
                Decision::Sat(m)
            } else {
                Decision::Unknown // G-SAT failed (e.g. a coordinate we could not verify)
            }
        }
        Cover::Unsat(_) => Decision::Unsat,
        Cover::Unknown => Decision::Unknown,
    }
}

/// The main recursion (Algorithm 2). `sample` fixes `order[0..i]`; we explore
/// `order[i]`.
fn get_unsat_cover(
    atoms: &[PolyAtom],
    order: &[Var],
    sample: &Model,
    i: usize,
    budget: &mut u64,
) -> Cover {
    let xi = order[i];
    let last_dim = i + 1 == order.len();

    // constraints whose highest variable is exactly `xi` (lower ones already hold
    // by construction; higher ones are handled at deeper levels).
    let here: Vec<&PolyAtom> =
        atoms.iter().filter(|a| main_var(a, order) == Some(xi)).collect();

    // (Algorithm 3) the unsat intervals on the xᵢ axis from the direct conflicts.
    let (mut intervals, mut cover_polys) = match unsat_intervals(&here, sample, xi) {
        Some(x) => x,
        None => return Cover::Unknown, // `eliminate_over_sample` already set the reason
    };

    loop {
        if *budget == 0 {
            return bail("budget");
        }
        *budget -= 1;

        match sample_outside(&intervals, &cover_polys, sample, xi) {
            Outside::Covered => break, // intervals cover ℝ ⇒ sample infeasible
            Outside::Cant => return bail("two-algebraic-sample"),
            Outside::Point(sp) => {
                let mut ext = sample.clone();
                ext.insert(xi, sp.to_value());
                if last_dim {
                    // a full assignment outside every unsat interval satisfies all
                    // `here` constraints; the lower ones hold by construction.
                    return if ext.checks(atoms) {
                        Cover::Sat(ext)
                    } else {
                        bail("gsat-two-algebraic") // could not verify (≥2 algebraic coords)
                    };
                }
                match get_unsat_cover(atoms, order, &ext, i + 1, budget) {
                    Cover::Sat(m) => return Cover::Sat(m),
                    Cover::Unknown => return Cover::Unknown, // child already recorded its reason
                    Cover::Unsat(child_polys) => {
                        match generalize(&child_polys, sample, order, i, &sp) {
                            Some((interval, projected)) => {
                                intervals.push(interval);
                                cover_polys.extend(projected);
                            }
                            None => return bail("nullification"),
                        }
                    }
                }
            }
        }
    }

    Cover::Unsat(cover_polys)
}

/// Algorithm 3: for each constraint with main variable `xi`, the cells of the
/// `xi` axis (over `sample`) on which it is **false** become unsat intervals.
/// Returns the intervals and the constraints' defining polynomials. `None` if a
/// constraint cannot be reduced exactly over the sample.
type Intervals = (Vec<Interval>, Vec<Polynomial>);
fn unsat_intervals(here: &[&PolyAtom], sample: &Model, xi: Var) -> Option<Intervals> {
    let mut intervals = Vec::new();
    let mut polys = Vec::new();
    for atom in here {
        polys.push(atom.poly.clone());
        // boundaries of this constraint on the xi axis, over the sample
        let coeffs = eliminate_over_sample(&atom.poly, sample, xi)?;
        let roots = univariate::real_roots(&coeffs);
        // walk the cells: (-∞,r0) r0 (r0,r1) r1 … (rk,∞); a cell is unsat for this
        // constraint iff the atom is false at a sample point in it.
        for (cell_lo, cell_hi, test) in cells(&roots) {
            let mut ext = sample.clone();
            ext.insert(xi, test.to_value());
            match ext.poly_sign(&atom.poly) {
                Some(sign) => {
                    if !atom.op.holds_for_sign(sign) {
                        let point = matches!(test, SamplePoint::Section(_))
                            && matches!((&cell_lo, &cell_hi), (Bound::At(_), Bound::At(_)))
                            && cell_is_point(&cell_lo, &cell_hi);
                        intervals.push(Interval { lo: cell_lo, hi: cell_hi, point });
                    }
                }
                None => return None,
            }
        }
    }
    Some((intervals, polys))
}

/// Whether the two bounds denote the *same* section point (a degenerate `[r,r]`
/// cell). Used to tag a point interval.
fn cell_is_point(lo: &Bound, hi: &Bound) -> bool {
    match (lo, hi) {
        (Bound::At(a), Bound::At(b)) => a.cmp(b) == Ordering::Equal,
        _ => false,
    }
}

/// The cells of `ℝ` cut at the sorted distinct `roots`, as
/// `(lo_bound, hi_bound, test_point)`: the open sectors below/between/above the
/// roots (a rational interior test point) and the section points (the root
/// itself).
fn cells(roots: &[RealRoot]) -> Vec<(Bound, Bound, SamplePoint)> {
    let mut out = Vec::new();
    if roots.is_empty() {
        out.push((Bound::NegInf, Bound::PosInf, SamplePoint::Sector(BigRational::zero())));
        return out;
    }
    // sector below the least root
    out.push((
        Bound::NegInf,
        Bound::At(roots[0].clone()),
        SamplePoint::Sector(roots[0].rational_below()),
    ));
    for (j, r) in roots.iter().enumerate() {
        // the section point r itself
        out.push((Bound::At(r.clone()), Bound::At(r.clone()), SamplePoint::Section(r.clone())));
        // the sector above r (up to the next root, or +∞)
        let (hi, test) = match roots.get(j + 1) {
            Some(next) => (Bound::At(next.clone()), univariate::rational_between(r, next)),
            None => (Bound::PosInf, r.rational_above()),
        };
        out.push((Bound::At(r.clone()), hi, SamplePoint::Sector(test)));
    }
    out
}

/// Where to sample next on the `xi` axis.
enum Outside {
    /// A point not covered by any unsat interval.
    Point(SamplePoint),
    /// The intervals cover ℝ.
    Covered,
    /// An uncovered point exists but cannot be sampled exactly (a second
    /// algebraic coordinate would be required).
    Cant,
}

/// Pick a point on the `xi` axis outside every unsat interval, or report the axis
/// covered. Enumerates the cells of the arrangement of all `cover_polys` (over
/// the sample) and returns the first whose representative no interval covers.
fn sample_outside(
    intervals: &[Interval],
    cover_polys: &[Polynomial],
    sample: &Model,
    xi: Var,
) -> Outside {
    // all boundary roots of the covering's polynomials, over the sample
    let mut roots: Vec<RealRoot> = Vec::new();
    for p in cover_polys {
        match eliminate_over_sample(p, sample, xi) {
            Some(coeffs) => roots.extend(univariate::real_roots(&coeffs)),
            None => return Outside::Cant,
        }
    }
    sort_dedup_roots(&mut roots);

    let has_algebraic = sample.vals.values().any(|v| matches!(v, Value::Algebraic(_)));

    for (_, _, test) in cells(&roots) {
        let covered = intervals.iter().any(|iv| covers(iv, &test));
        if !covered {
            // an uncovered cell: try to sample it. An algebraic section here would
            // be a *second* algebraic coordinate — outside the exact fragment.
            if has_algebraic && matches!(&test, SamplePoint::Section(RealRoot::Algebraic(_))) {
                return Outside::Cant;
            }
            return Outside::Point(test);
        }
    }
    Outside::Covered
}

/// Sort the roots ascending and remove duplicates (exact, via [`RealRoot::cmp`]).
fn sort_dedup_roots(roots: &mut Vec<RealRoot>) {
    roots.sort_by(|a, b| a.cmp(b));
    roots.dedup_by(|a, b| a.cmp(b) == Ordering::Equal);
}

/// Whether the unsat `interval` covers the test point.
fn covers(iv: &Interval, test: &SamplePoint) -> bool {
    if iv.point {
        // a section [r,r] covers only the exact root r
        return match (&iv.lo, test) {
            (Bound::At(r), SamplePoint::Section(s)) => r.cmp(s) == Ordering::Equal,
            (Bound::At(r), SamplePoint::Sector(q)) => r.cmp_rational(q) == Ordering::Equal,
            _ => false,
        };
    }
    // open (lo, hi): strictly inside
    let above_lo = match (&iv.lo, test) {
        (Bound::NegInf, _) => true,
        (Bound::At(r), SamplePoint::Sector(q)) => r.cmp_rational(q) == Ordering::Less,
        (Bound::At(r), SamplePoint::Section(s)) => r.cmp(s) == Ordering::Less,
        (Bound::PosInf, _) => false,
    };
    let below_hi = match (&iv.hi, test) {
        (Bound::PosInf, _) => true,
        (Bound::At(r), SamplePoint::Sector(q)) => r.cmp_rational(q) == Ordering::Greater,
        (Bound::At(r), SamplePoint::Section(s)) => r.cmp(s) == Ordering::Greater,
        (Bound::NegInf, _) => false,
    };
    above_lo && below_hi
}

/// Algorithms 4 + 5: generalise the conflicting sample `sp` (a value for
/// `order[i]`) to an unsat interval, by McCallum-projecting the child covering's
/// polynomials (`child_polys`, in `order[0..=i+1]`) down to `order[0..=i]` and
/// taking the cell of `sp` in their arrangement over the lower sample. Returns
/// the interval and the projected polynomials (for the parent's own projection).
/// `None` on nullification / fragment limit (⇒ `Unknown`).
fn generalize(
    child_polys: &[Polynomial],
    sample: &Model,
    order: &[Var],
    i: usize,
    sp: &SamplePoint,
) -> Option<(Interval, Vec<Polynomial>)> {
    let q = match sp {
        // A section conflict holds *exactly* at the point — its constraint vanishes
        // there, so moving off it changes that constraint's sign. Generalise to the
        // single point: sound on its own (the child proved this exact point
        // infeasible) and terminating (sections are finitely many). No projection
        // is needed — and crucially none is *attempted*, so a nullifying resultant
        // among the child polynomials cannot force `Unknown` here.
        SamplePoint::Section(r) => {
            return Some((
                Interval { lo: Bound::At(r.clone()), hi: Bound::At(r.clone()), point: true },
                Vec::new(),
            ));
        }
        SamplePoint::Sector(q) => q,
    };

    // A sector conflict generalises to the open cell of `q` in the arrangement of
    // the McCallum projection of the child covering's polynomials (Algorithms 4+5):
    // over that cell every projection polynomial is sign-invariant, so the child's
    // reasons — hence its infeasibility — persist across the whole interval.
    let xi = order[i];
    let elim = order[i + 1];
    let projected = match mccallum_project(child_polys, elim, i + 1) {
        Some(p) => p,
        None => {
            REASON.with(|r| r.set("nullification"));
            return None;
        }
    };
    let mut boundary_roots: Vec<RealRoot> = Vec::new();
    for p in &projected {
        if main_var_of(p, order) == Some(xi) {
            let coeffs = eliminate_over_sample(p, sample, xi)?;
            boundary_roots.extend(univariate::real_roots(&coeffs));
        }
    }
    sort_dedup_roots(&mut boundary_roots);

    // The sample point `q` was chosen before the child's projection existed, so it
    // can coincide with a *new* boundary root (e.g. a leading coefficient that
    // vanishes there). When it does, `q` is really a SECTION of the refined
    // arrangement — the conflict holds only at that point (the open cells either
    // side may be feasible). Generalise to the point `[q,q]`, never the open cell,
    // or we would unsoundly exclude the neighbouring feasible region.
    if let Some(r) = boundary_roots.iter().find(|r| r.cmp_rational(q) == Ordering::Equal) {
        return Some((
            Interval { lo: Bound::At(r.clone()), hi: Bound::At(r.clone()), point: true },
            projected,
        ));
    }

    let lo = boundary_roots
        .iter()
        .filter(|r| r.cmp_rational(q) == Ordering::Less)
        .max_by(|a, b| a.cmp(b))
        .map_or(Bound::NegInf, |r| Bound::At(r.clone()));
    let hi = boundary_roots
        .iter()
        .filter(|r| r.cmp_rational(q) == Ordering::Greater)
        .min_by(|a, b| a.cmp(b))
        .map_or(Bound::PosInf, |r| Bound::At(r.clone()));
    Some((Interval { lo, hi, point: false }, projected))
}

/// The coefficient vector (low-degree-first, in `xi`) of `p` after fixing the
/// sample's coordinates: the rational coordinates substitute away; a single
/// algebraic coordinate `α` (root of `d`) is eliminated by `Resₐ(p, d)`, leaving
/// a polynomial over ℚ in `xi` whose real roots **superset** `p`'s roots over the
/// sample (extra roots only over-refine cells — harmless for sign-invariance).
/// `None` if `p` has an unassigned variable other than `xi`, ≥2 algebraic
/// coordinates, or the elimination degenerates.
fn eliminate_over_sample(p: &Polynomial, sample: &Model, xi: Var) -> Option<Vec<BigRational>> {
    let mut q = p.clone();
    let mut algebraic: Option<(Var, &AlgebraicReal)> = None;
    for v in p.vars() {
        if v == xi {
            continue;
        }
        match sample.vals.get(&v) {
            Some(Value::Rational(r)) => {
                q = q.eval_at(v, r);
            }
            Some(Value::Algebraic(a)) => {
                if algebraic.is_some() {
                    REASON.with(|r| r.set("elim:two-algebraic"));
                    return None; // ≥2 algebraic coordinates
                }
                algebraic = Some((v, a));
            }
            None => {
                REASON.with(|r| r.set("elim:unassigned"));
                return None; // unassigned non-`xi` variable
            }
        }
    }
    let univ = match algebraic {
        None => q,
        Some((v, a)) => {
            let d = build_poly_in_var(&a.defining, v);
            let r = q.resultant(&d, v);
            if r.is_zero() {
                REASON.with(|r| r.set("elim:zero-resultant"));
                return None; // degenerate elimination
            }
            r
        }
    };
    let deg = univ.degree(xi);
    Some((0..=deg).map(|k| univ.univ_coeff(xi, k)).collect())
}

/// Build the polynomial `Σ coeffs[k]·vᵏ` in variable `v` from low-degree-first
/// rational coefficients.
fn build_poly_in_var(coeffs: &[BigRational], v: Var) -> Polynomial {
    let mut acc = Polynomial::zero();
    for (k, c) in coeffs.iter().enumerate() {
        if c.is_zero() {
            continue;
        }
        acc = acc.add(&Polynomial::from_var_power(v, k as u32).scale(c));
    }
    acc
}

/// The highest variable of an atom's polynomial in the `order` (its CAC main
/// variable), or `None` for a constant.
fn main_var(atom: &PolyAtom, order: &[Var]) -> Option<Var> {
    main_var_of(&atom.poly, order)
}

fn main_var_of(p: &Polynomial, order: &[Var]) -> Option<Var> {
    p.vars().into_iter().filter(|v| order.contains(v)).max()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::atom::{AtomCmp, OriginId};

    fn at(coeffs: &[(i64, &[(Var, u32)])], op: AtomCmp) -> PolyAtom {
        PolyAtom::new(Polynomial::from_coeffs_int(coeffs), op, VarSort::Real, OriginId(0))
    }
    fn is_unsat(d: &Decision) -> bool {
        matches!(d, Decision::Unsat)
    }
    fn is_sat(d: &Decision) -> bool {
        matches!(d, Decision::Sat(_))
    }

    #[test]
    fn single_var_irrational_unsat() {
        // x² < 2 ∧ x² > 2  : unsat. Boundaries ±√2 are irrational (sections).
        let v = decide_cac(
            &[
                at(&[(1, &[(0, 2)]), (-2, &[])], AtomCmp::Lt),
                at(&[(1, &[(0, 2)]), (-2, &[])], AtomCmp::Gt),
            ],
            &[0],
            VarSort::Real,
        );
        assert!(is_unsat(&v), "x²<2 ∧ x²>2 is unsat");
    }

    #[test]
    fn two_var_irrational_nonstrict_unsat() {
        // x² = 2 ∧ x ≤ 0 ∧ x ≥ 1  : unsat (x = ±√2 contradicts 0 ≤ x ≤ 1... actually
        // x ≤ 0 ∧ x ≥ 1 is already unsat). Make it genuinely use the irrational
        // section: x² = 2 ∧ x·y > 0 ∧ y < 0 ∧ x > 0  ⇒ x = √2 > 0 ⇒ need y<0 and
        // x·y>0 ⇒ y>0, contradiction. The feasible x is the irrational √2.
        let v = decide_cac(
            &[
                at(&[(1, &[(0, 2)]), (-2, &[])], AtomCmp::Eq), // x² = 2
                at(&[(1, &[(0, 1)])], AtomCmp::Gt),            // x > 0  (picks +√2)
                at(&[(1, &[(0, 1), (1, 1)])], AtomCmp::Gt),    // x·y > 0
                at(&[(1, &[(1, 1)])], AtomCmp::Lt),            // y < 0
            ],
            &[0, 1],
            VarSort::Real,
        );
        assert!(is_unsat(&v), "x=√2>0 forces y>0, contradicting y<0");
    }

    #[test]
    fn two_var_irrational_sat() {
        // x² = 2 ∧ x > 0 ∧ y = x + 1 : sat, with x = √2 (algebraic), y = √2 + 1.
        let v = decide_cac(
            &[
                at(&[(1, &[(0, 2)]), (-2, &[])], AtomCmp::Eq), // x² = 2
                at(&[(1, &[(0, 1)])], AtomCmp::Gt),            // x > 0
                at(&[(1, &[(1, 1)]), (-1, &[(0, 1)]), (-1, &[])], AtomCmp::Eq), // y - x - 1 = 0
            ],
            &[0, 1],
            VarSort::Real,
        );
        // y has TWO algebraic-linked coords; G-SAT with ≥2 algebraic may be
        // unverifiable ⇒ Unknown is acceptable, but it must NOT be unsat.
        assert!(!is_unsat(&v), "must never report unsat on a satisfiable system");
    }

    #[test]
    fn rational_unsat_still_works() {
        // y > x + 1 ∧ y > 1 - x ∧ y < 0 : the paper's worked example, unsat.
        let v = decide_cac(
            &[
                at(&[(1, &[(1, 1)]), (-1, &[(0, 1)]), (-1, &[])], AtomCmp::Gt), // y - x - 1 > 0
                at(&[(1, &[(1, 1)]), (1, &[(0, 1)]), (-1, &[])], AtomCmp::Gt),  // y + x - 1 > 0
                at(&[(1, &[(1, 1)])], AtomCmp::Lt),                            // y < 0
            ],
            &[0, 1],
            VarSort::Real,
        );
        assert!(is_unsat(&v), "the CDCAC worked example is unsat");
    }

    #[test]
    fn simple_sat() {
        // x > 0 ∧ y > 0 : trivially sat.
        let v = decide_cac(
            &[at(&[(1, &[(0, 1)])], AtomCmp::Gt), at(&[(1, &[(1, 1)])], AtomCmp::Gt)],
            &[0, 1],
            VarSort::Real,
        );
        assert!(is_sat(&v), "x>0 ∧ y>0 is sat");
    }
}
