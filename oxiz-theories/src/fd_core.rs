//! `fd_core` — the pure finite-domain integer decision core (the `oxiz-nl2`
//! `fdlcg` engine), over `oxiz-math`'s `Polynomial`.
//!
//! This is the **single, shared** sound add-on for nonlinear-integer (QF_NIA)
//! conjunctions. It has two consumers:
//!   * the live SMT dispatch ([`dispatch_nia_constraints`](crate::nlsat)), which
//!     consults [`decide`] as a sound `Unsat`/`Sat` tier the legacy `NiaSolver`
//!     cannot trust on nonlinear shapes; and
//!   * the `oxiz-solver` `FdPropagator` `TheoryHooks` bus citizen, which wraps it.
//!
//! Both reuse this one verified core (a single funnel), so the soundness argument
//! is made once, here.
//!
//! ## Soundness (FALSE_UNSAT = 0, FALSE_SAT = 0)
//! - Domains are single closed integer intervals (`None` = ±∞) — the type cannot
//!   express a hole, so a disequality is never a one-sided write (closes the
//!   classic NEQ-collapse unsoundness structurally).
//! - Every domain shrink removes only **proven**-infeasible points; an atom's range
//!   over the box is a sound interval over-approximation (monomial-wise). An empty
//!   box is therefore a genuine conflict.
//! - [`FdDecision::Unsat`] is returned only when a finite box is exhausted with no
//!   integer solution **and** a second, independent G-UNSAT re-run confirms it; any
//!   open axis / budget exhaustion ⇒ [`FdDecision::Open`].
//! - [`FdDecision::Sat`] always carries a concrete integer model that exactly
//!   satisfies every atom (G-SAT). Real-domain reasoning is sound for the integer
//!   domain (ℤ ⊆ ℝ), and `Unsat` over a sub-conjunction stays sound for any
//!   super-conjunction (adding constraints only shrinks feasibility) — the two
//!   facts the live dispatch relies on.
//!
//! ## Scope
//! A deliberately soundness-complete **subset** of `fdlcg`: interval
//! over-approximation, linear bound-consistency, finite branch-and-prune, exact
//! integer model checking. The univariate-root tier (`cauchy_bound` /
//! `univ_int_status`, which converts some open-tail nonlinear cases to `Unsat`) is
//! a completeness add-on for a later increment — dropping it only turns some
//! `Unsat` into `Open`, never a sound verdict into a false one.

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, ToPrimitive, Zero};
use rustc_hash::FxHashMap;

use oxiz_math::polynomial::{Polynomial, Var};

/// Node budget for the branch-and-prune search. Exhaustion ⇒ `Open`.
const NODE_BUDGET: u64 = 40_000;
/// Largest finite integer domain we enumerate / bisect across. Beyond this ⇒
/// treat as effectively open ⇒ `Open` (never enumerate unboundedly).
const MAX_ENUM: i64 = 4096;

/// A polynomial comparison `p ⋈ 0`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FdCmp {
    /// `p < 0`.
    Lt,
    /// `p ≤ 0`.
    Le,
    /// `p > 0`.
    Gt,
    /// `p ≥ 0`.
    Ge,
    /// `p = 0`.
    Eq,
    /// `p ≠ 0`.
    Ne,
}

impl FdCmp {
    /// Does `sign(p)` (one of -1, 0, +1) satisfy `p ⋈ 0`? The kernel of the exact
    /// model re-check (G-SAT).
    #[must_use]
    pub fn holds_for_sign(self, sign: i32) -> bool {
        match self {
            FdCmp::Lt => sign < 0,
            FdCmp::Le => sign <= 0,
            FdCmp::Gt => sign > 0,
            FdCmp::Ge => sign >= 0,
            FdCmp::Eq => sign == 0,
            FdCmp::Ne => sign != 0,
        }
    }

    /// The exact negation of `p ⋈ 0` over an ordered field (an atom asserted
    /// *false*): `¬(p<0) = (p≥0)`, etc.
    #[must_use]
    pub fn negate(self) -> FdCmp {
        match self {
            FdCmp::Lt => FdCmp::Ge,
            FdCmp::Le => FdCmp::Gt,
            FdCmp::Gt => FdCmp::Le,
            FdCmp::Ge => FdCmp::Lt,
            FdCmp::Eq => FdCmp::Ne,
            FdCmp::Ne => FdCmp::Eq,
        }
    }
}

/// The verdict on a conjunction of atoms, sound by the priority order
/// `soundness ≫ completeness`.
#[derive(Clone, Debug)]
pub enum FdDecision {
    /// Integer-UNSAT (G-UNSAT re-verified).
    Unsat,
    /// Satisfiable; the witness is a concrete integer model that exactly satisfies
    /// every atom (G-SAT-checked). Keyed by polynomial `Var`.
    Sat(FxHashMap<Var, BigRational>),
    /// Could not decide soundly (open axis / budget). Always an acceptable verdict.
    Open,
}

// ── integer domains ─────────────────────────────────────────────────────────

/// An integer domain: one closed interval, `None` = ±∞. **Cannot** express a hole.
#[derive(Clone, Debug, PartialEq, Eq)]
struct IntDom {
    lo: Option<BigInt>,
    hi: Option<BigInt>,
}

impl IntDom {
    fn full() -> Self {
        IntDom { lo: None, hi: None }
    }
    fn is_empty(&self) -> bool {
        matches!((&self.lo, &self.hi), (Some(l), Some(h)) if l > h)
    }
    fn is_finite(&self) -> bool {
        self.lo.is_some() && self.hi.is_some()
    }
    fn singleton(&self) -> Option<&BigInt> {
        match (&self.lo, &self.hi) {
            (Some(l), Some(h)) if l == h => Some(l),
            _ => None,
        }
    }
    fn count(&self) -> Option<BigInt> {
        match (&self.lo, &self.hi) {
            (Some(l), Some(h)) => Some(h - l + BigInt::one()),
            _ => None,
        }
    }
}

type DomBox = FxHashMap<Var, IntDom>;

// ── rational interval enclosures ────────────────────────────────────────────

/// A rational interval enclosure of a polynomial's range, `None` = ±∞.
#[derive(Clone)]
struct RatIv {
    lo: Option<BigRational>,
    hi: Option<BigRational>,
}

impl RatIv {
    fn point(r: BigRational) -> Self {
        RatIv { lo: Some(r.clone()), hi: Some(r) }
    }
    fn full() -> Self {
        RatIv { lo: None, hi: None }
    }
}

fn riv_add(a: &RatIv, b: &RatIv) -> RatIv {
    let lo = match (&a.lo, &b.lo) {
        (Some(x), Some(y)) => Some(x + y),
        _ => None,
    };
    let hi = match (&a.hi, &b.hi) {
        (Some(x), Some(y)) => Some(x + y),
        _ => None,
    };
    RatIv { lo, hi }
}

/// Sound interval multiplication, handling ±∞ conservatively.
fn riv_mul(a: &RatIv, b: &RatIv) -> RatIv {
    let (Some(al), Some(ah), Some(bl), Some(bh)) = (&a.lo, &a.hi, &b.lo, &b.hi) else {
        if is_zero_iv(a) || is_zero_iv(b) {
            return RatIv::point(BigRational::zero());
        }
        return RatIv::full();
    };
    let prods = [al * bl, al * bh, ah * bl, ah * bh];
    let mut lo = prods[0].clone();
    let mut hi = prods[0].clone();
    for p in &prods[1..] {
        if *p < lo {
            lo = p.clone();
        }
        if *p > hi {
            hi = p.clone();
        }
    }
    RatIv { lo: Some(lo), hi: Some(hi) }
}

fn is_zero_iv(a: &RatIv) -> bool {
    matches!((&a.lo, &a.hi), (Some(l), Some(h)) if l.is_zero() && h.is_zero())
}

fn riv_pow(a: &RatIv, k: u32) -> RatIv {
    let mut acc = RatIv::point(BigRational::one());
    for _ in 0..k {
        acc = riv_mul(&acc, a);
    }
    acc
}

fn idom_to_riv(d: &IntDom) -> RatIv {
    RatIv {
        lo: d.lo.as_ref().map(|x| BigRational::from(x.clone())),
        hi: d.hi.as_ref().map(|x| BigRational::from(x.clone())),
    }
}

/// A **sound over-approximation** of the range of `p` over the box (monomial-wise
/// interval arithmetic; the dependency problem only loosens the enclosure).
fn interval_eval(p: &Polynomial, box_: &DomBox) -> RatIv {
    let mut acc = RatIv::point(BigRational::zero());
    for term in p.terms() {
        let mut m = RatIv::point(term.coeff.clone());
        for vp in term.monomial.vars() {
            let d = box_.get(&vp.var).cloned().unwrap_or_else(IntDom::full);
            m = riv_mul(&m, &riv_pow(&idom_to_riv(&d), vp.power));
        }
        acc = riv_add(&acc, &m);
    }
    acc
}

/// Whether an atom is **provably violated everywhere** on the box (a conflict),
/// using the sound range enclosure. Only returns `true` when certain.
fn atom_conflicts(poly: &Polynomial, op: FdCmp, box_: &DomBox) -> bool {
    let iv = interval_eval(poly, box_);
    match op {
        FdCmp::Gt => iv.hi.is_some_and(|h| h <= BigRational::zero()),
        FdCmp::Lt => iv.lo.is_some_and(|l| l >= BigRational::zero()),
        FdCmp::Ge => iv.hi.is_some_and(|h| h < BigRational::zero()),
        FdCmp::Le => iv.lo.is_some_and(|l| l > BigRational::zero()),
        FdCmp::Eq => {
            iv.lo.is_some_and(|l| l > BigRational::zero())
                || iv.hi.is_some_and(|h| h < BigRational::zero())
        }
        FdCmp::Ne => is_zero_iv(&iv),
    }
}

fn sign_of(r: &BigRational) -> i32 {
    if r.is_zero() {
        0
    } else if r.is_negative() {
        -1
    } else {
        1
    }
}

// ── propagation + search ────────────────────────────────────────────────────

fn collect_vars(atoms: &[(Polynomial, FdCmp)]) -> Vec<Var> {
    let mut set: Vec<Var> = Vec::new();
    for (poly, _) in atoms {
        for v in poly.vars() {
            if !set.contains(&v) {
                set.push(v);
            }
        }
    }
    set.sort_unstable();
    set
}

fn initial_box(vars: &[Var]) -> DomBox {
    vars.iter().map(|&v| (v, IntDom::full())).collect()
}

fn free_vars(vars: &[Var], box_: &DomBox) -> Vec<Var> {
    vars.iter()
        .copied()
        .filter(|v| box_.get(v).and_then(IntDom::singleton).is_none())
        .collect()
}

fn singleton_map(box_: &DomBox) -> FxHashMap<Var, BigRational> {
    box_.iter()
        .filter_map(|(&v, d)| d.singleton().map(|s| (v, BigRational::from(s.clone()))))
        .collect()
}

/// The **sound** univariate-in-`v` coefficient vector (low-degree-first) of `p`
/// once every *other* variable is fixed by `fixed`. Uses `coeff(v,k)` (keeps mixed
/// monomials). `None` if some other var of `p` is not fixed.
fn univ_coeffs_in(
    p: &Polynomial,
    v: Var,
    fixed: &FxHashMap<Var, BigRational>,
) -> Option<Vec<BigRational>> {
    let deg = p.degree(v);
    let mut out = Vec::with_capacity(deg as usize + 1);
    for k in 0..=deg {
        let ck = p.coeff(v, k);
        if !ck.vars().iter().all(|x| *x == v || fixed.contains_key(x)) {
            return None;
        }
        out.push(ck.eval(fixed));
    }
    Some(out)
}

/// The single free (non-singleton) variable of `poly` under `fixed`, or `None` if
/// it has zero or ≥2 free vars.
fn lone_free_var(poly: &Polynomial, fixed: &FxHashMap<Var, BigRational>) -> Option<Var> {
    let mut cand = None;
    for v in poly.vars() {
        if fixed.contains_key(&v) {
            continue;
        }
        if cand.is_some() {
            return None;
        }
        cand = Some(v);
    }
    cand
}

fn raise_lo(dom: &mut IntDom, val: BigInt) {
    dom.lo = Some(match dom.lo.take() {
        Some(cur) if cur > val => cur,
        _ => val,
    });
}
fn lower_hi(dom: &mut IntDom, val: BigInt) {
    dom.hi = Some(match dom.hi.take() {
        Some(cur) if cur < val => cur,
        _ => val,
    });
}

/// Bound-consistency on a **linear-in-`v`** atom `c1·v + c0 ⋈ 0`. `Err(())` ⇒
/// conflict. Sound: removes only integers that provably violate the atom. `Ne`
/// does not tighten (a hole the single interval cannot express).
fn linear_tighten(coeffs: &[BigRational], op: FdCmp, dom: &mut IntDom) -> Result<(), ()> {
    let (c0, c1) = (&coeffs[0], &coeffs[1]);
    let r = -c0 / c1;
    let flip = c1.is_negative();
    let eff = match (op, flip) {
        (FdCmp::Gt, false) | (FdCmp::Lt, true) => FdCmp::Gt,
        (FdCmp::Lt, false) | (FdCmp::Gt, true) => FdCmp::Lt,
        (FdCmp::Ge, false) | (FdCmp::Le, true) => FdCmp::Ge,
        (FdCmp::Le, false) | (FdCmp::Ge, true) => FdCmp::Le,
        (FdCmp::Eq, _) => FdCmp::Eq,
        (FdCmp::Ne, _) => return Ok(()),
    };
    let is_int = r.is_integer();
    match eff {
        FdCmp::Gt => raise_lo(
            dom,
            if is_int { r.to_integer() + BigInt::one() } else { r.ceil().to_integer() },
        ),
        FdCmp::Ge => raise_lo(dom, r.ceil().to_integer()),
        FdCmp::Lt => lower_hi(
            dom,
            if is_int { r.to_integer() - BigInt::one() } else { r.floor().to_integer() },
        ),
        FdCmp::Le => lower_hi(dom, r.floor().to_integer()),
        FdCmp::Eq => {
            if is_int {
                let n = r.to_integer();
                raise_lo(dom, n.clone());
                lower_hi(dom, n);
            } else {
                return Err(());
            }
        }
        FdCmp::Ne => unreachable!(),
    }
    if dom.is_empty() {
        return Err(());
    }
    Ok(())
}

/// Bound-consistency propagation fixpoint: tighten every linear-in-one-free-var
/// atom until no domain changes. Returns `false` on conflict. Sound — only
/// provably-infeasible integers removed.
fn propagate(atoms: &[(Polynomial, FdCmp)], box_: &mut DomBox) -> bool {
    for _ in 0..1000 {
        let mut changed = false;
        let fixed = singleton_map(box_);
        for (poly, op) in atoms {
            let Some(v) = lone_free_var(poly, &fixed) else { continue };
            let Some(coeffs) = univ_coeffs_in(poly, v, &fixed) else { continue };
            if coeffs.len() != 2 || coeffs[1].is_zero() {
                continue;
            }
            let mut dom = box_.get(&v).cloned().unwrap_or_else(IntDom::full);
            let before = dom.clone();
            if linear_tighten(&coeffs, *op, &mut dom).is_err() {
                return false;
            }
            if dom != before {
                box_.insert(v, dom);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    true
}

/// Exact integer model check (G-SAT): every atom must hold at the assignment.
fn model_checks(atoms: &[(Polynomial, FdCmp)], model: &FxHashMap<Var, BigRational>) -> bool {
    atoms.iter().all(|(poly, op)| op.holds_for_sign(sign_of(&poly.eval(model))))
}

enum BoxResult {
    Unsat,
    Sat(FxHashMap<Var, BigRational>),
    Open,
}

fn solve(
    atoms: &[(Polynomial, FdCmp)],
    vars: &[Var],
    box_: &mut DomBox,
    budget: &mut u64,
) -> BoxResult {
    if *budget == 0 {
        return BoxResult::Open;
    }
    *budget -= 1;

    if !propagate(atoms, box_) {
        return BoxResult::Unsat;
    }
    if atoms.iter().any(|(poly, op)| atom_conflicts(poly, *op, box_)) {
        return BoxResult::Unsat;
    }
    if vars.iter().any(|v| box_.get(v).is_some_and(IntDom::is_empty)) {
        return BoxResult::Unsat;
    }
    let frees = free_vars(vars, box_);
    if frees.is_empty() {
        let model = singleton_map(box_);
        return if model_checks(atoms, &model) {
            BoxResult::Sat(model)
        } else {
            BoxResult::Unsat
        };
    }
    let pick = frees
        .iter()
        .copied()
        .filter(|v| box_.get(v).is_some_and(IntDom::is_finite))
        .min_by_key(|v| {
            box_.get(v).and_then(IntDom::count).and_then(|c| c.to_i64()).unwrap_or(i64::MAX)
        });
    let Some(v) = pick else {
        return BoxResult::Open;
    };
    let dom = box_.get(&v).cloned().unwrap();
    let (lo, hi) = (dom.lo.clone().unwrap(), dom.hi.clone().unwrap());
    if (&hi - &lo).to_i64().is_none_or(|c| c > MAX_ENUM) {
        return BoxResult::Open;
    }
    let mid = &lo + (&hi - &lo) / BigInt::from(2u32);
    let mut any_open = false;
    for (nlo, nhi) in [(lo.clone(), mid.clone()), (&mid + BigInt::one(), hi.clone())] {
        if nlo > nhi {
            continue;
        }
        // SOUNDNESS: each branch explores an INDEPENDENT copy of the box.
        // `propagate` (called at the child node) tightens *other* variables' domains
        // under this branch's bound on `v`, and those tightenings are valid ONLY
        // under that bound — restoring just `v` between siblings would leak them into
        // the next branch, wrongly excluding feasible points (the classic
        // branch-and-prune state-restoration bug; a leak here produced a false UNSAT
        // the randomized ground-truth differential caught). Cloning the box per child
        // confines every tightening to its own subtree.
        let mut child = box_.clone();
        child.insert(v, IntDom { lo: Some(nlo), hi: Some(nhi) });
        match solve(atoms, vars, &mut child, budget) {
            BoxResult::Sat(m) => return BoxResult::Sat(m),
            BoxResult::Open => any_open = true,
            BoxResult::Unsat => {}
        }
    }
    if any_open {
        BoxResult::Open
    } else {
        BoxResult::Unsat
    }
}

/// Independent **G-UNSAT** re-verification: re-run the search from a fresh box and
/// require `Unsat` again (mirrors G-SAT's re-check) before an `Unsat` is trusted.
fn g_unsat_reverify(atoms: &[(Polynomial, FdCmp)], vars: &[Var]) -> bool {
    let mut box_ = initial_box(vars);
    let mut budget = NODE_BUDGET;
    matches!(solve(atoms, vars, &mut box_, &mut budget), BoxResult::Unsat)
}

/// Decide a conjunction of integer polynomial atoms `pᵢ ⋈ᵢ 0`.
///
/// Sound by the priority order: `Unsat` only when re-verified, `Sat` only with an
/// exact integer model, else `Open`. Callers may soundly:
///   * trust `Unsat` for **any super-conjunction** (more atoms ⟹ still unsat); and
///   * trust `Sat` only when the atoms are the **whole** problem (no constraint
///     dropped) — the live dispatch enforces this with its `sat_is_trustworthy`.
#[must_use]
pub fn decide(atoms: &[(Polynomial, FdCmp)]) -> FdDecision {
    if atoms.is_empty() {
        return FdDecision::Open;
    }
    let vars = collect_vars(atoms);
    let mut box_ = initial_box(&vars);
    let mut budget = NODE_BUDGET;
    match solve(atoms, &vars, &mut box_, &mut budget) {
        BoxResult::Sat(m) => {
            if model_checks(atoms, &m) {
                FdDecision::Sat(m)
            } else {
                FdDecision::Open
            }
        }
        BoxResult::Unsat => {
            if g_unsat_reverify(atoms, &vars) {
                FdDecision::Unsat
            } else {
                FdDecision::Open
            }
        }
        BoxResult::Open => FdDecision::Open,
    }
}

/// A **cheap** refutation check: linear bound-propagation + interval conflict over
/// a fresh box (no integer-variable search). `true` ⇒ the conjunction is provably
/// integer-UNSAT. Used by the `TheoryHooks` bus citizen's per-fixpoint
/// `final_check`. Sound: a `true` is a genuine conflict (the empty-box keystone).
#[must_use]
pub fn cheap_refute(atoms: &[(Polynomial, FdCmp)]) -> bool {
    if atoms.is_empty() {
        return false;
    }
    let vars = collect_vars(atoms);
    let mut box_ = initial_box(&vars);
    !propagate(atoms, &mut box_) || atoms.iter().any(|(poly, op)| atom_conflicts(poly, *op, &box_))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn poly(coeffs: &[(i64, &[(Var, u32)])]) -> Polynomial {
        Polynomial::from_coeffs_int(coeffs)
    }
    fn is_unsat(d: &FdDecision) -> bool {
        matches!(d, FdDecision::Unsat)
    }
    fn is_sat(d: &FdDecision) -> bool {
        matches!(d, FdDecision::Sat(_))
    }

    #[test]
    fn linear_no_integer_between_0_and_1() {
        // x > 0 ∧ x < 1  (integer) ⇒ unsat.
        let d = decide(&[
            (poly(&[(1, &[(0, 1)])]), FdCmp::Gt),
            (poly(&[(1, &[(0, 1)]), (-1, &[])]), FdCmp::Lt),
        ]);
        assert!(is_unsat(&d));
    }

    #[test]
    fn nonlinear_x_squared_eq_3_is_unsat() {
        // x² = 3 has no integer solution — the NiaSolver gap fdlcg closes.
        // bound it so the finite search can exhaust: -3 ≤ x ≤ 3.
        let d = decide(&[
            (poly(&[(1, &[(0, 2)]), (-3, &[])]), FdCmp::Eq),
            (poly(&[(1, &[(0, 1)]), (3, &[])]), FdCmp::Ge),
            (poly(&[(1, &[(0, 1)]), (-3, &[])]), FdCmp::Le),
        ]);
        assert!(is_unsat(&d), "x²=3 has no integer root");
    }

    #[test]
    fn nonlinear_sat_has_model() {
        // x*y = 6 ∧ 1 ≤ x ≤ 6 ∧ 1 ≤ y ≤ 6 : sat (e.g. 2,3).
        let d = decide(&[
            (poly(&[(1, &[(0, 1), (1, 1)]), (-6, &[])]), FdCmp::Eq),
            (poly(&[(1, &[(0, 1)]), (-1, &[])]), FdCmp::Ge),
            (poly(&[(1, &[(0, 1)]), (-6, &[])]), FdCmp::Le),
            (poly(&[(1, &[(1, 1)]), (-1, &[])]), FdCmp::Ge),
            (poly(&[(1, &[(1, 1)]), (-6, &[])]), FdCmp::Le),
        ]);
        assert!(is_sat(&d));
    }

    #[test]
    fn open_axis_is_open_not_unsat() {
        // x > 0 alone — satisfiable but unbounded ⇒ Open, NEVER Unsat.
        let d = decide(&[(poly(&[(1, &[(0, 1)])]), FdCmp::Gt)]);
        assert!(!is_unsat(&d));
    }

    #[test]
    fn cheap_refute_catches_linear_empty() {
        assert!(cheap_refute(&[
            (poly(&[(1, &[(0, 1)])]), FdCmp::Gt),
            (poly(&[(1, &[(0, 1)]), (-1, &[])]), FdCmp::Lt),
        ]));
        assert!(!cheap_refute(&[(poly(&[(1, &[(0, 1)])]), FdCmp::Gt)]));
    }
}
