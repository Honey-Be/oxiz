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

/// An extended-real interval endpoint (`±∞` first-class) for sound interval
/// multiplication across unbounded domains.
#[derive(Clone)]
enum Ext {
    NegInf,
    Fin(BigRational),
    PosInf,
}

fn ext_sign(e: &Ext) -> i32 {
    match e {
        Ext::NegInf => -1,
        Ext::PosInf => 1,
        Ext::Fin(r) => sign_of(r),
    }
}

/// Extended-real product. `0 · ∞` is taken as `0` — sound for the corner-product
/// min/max method (the other corners carry any genuine `±∞`).
fn ext_mul(x: &Ext, y: &Ext) -> Ext {
    match (x, y) {
        (Ext::Fin(a), Ext::Fin(b)) => Ext::Fin(a * b),
        _ => match ext_sign(x) * ext_sign(y) {
            s if s > 0 => Ext::PosInf,
            s if s < 0 => Ext::NegInf,
            _ => Ext::Fin(BigRational::zero()),
        },
    }
}

fn ext_lt(a: &Ext, b: &Ext) -> bool {
    match (a, b) {
        (Ext::NegInf, Ext::NegInf) | (Ext::PosInf, Ext::PosInf) => false,
        (Ext::NegInf, _) | (_, Ext::PosInf) => true,
        (_, Ext::NegInf) | (Ext::PosInf, _) => false,
        (Ext::Fin(x), Ext::Fin(y)) => x < y,
    }
}

/// **Sound** interval multiplication with proper `±∞` handling (the four extended
/// corner products, then min/max). Tighter than a blanket "unbounded ⇒ ⊤" bailout —
/// e.g. `[1,1] · [5,∞) = [5,∞)` instead of `(−∞,∞)` — which is what lets the
/// propagation forced-literal check (and conflict detection) see half-unbounded
/// domains. Remains a sound OVER-approximation.
fn riv_mul(a: &RatIv, b: &RatIv) -> RatIv {
    if is_zero_iv(a) || is_zero_iv(b) {
        return RatIv::point(BigRational::zero());
    }
    let al = a.lo.as_ref().map_or(Ext::NegInf, |r| Ext::Fin(r.clone()));
    let ah = a.hi.as_ref().map_or(Ext::PosInf, |r| Ext::Fin(r.clone()));
    let bl = b.lo.as_ref().map_or(Ext::NegInf, |r| Ext::Fin(r.clone()));
    let bh = b.hi.as_ref().map_or(Ext::PosInf, |r| Ext::Fin(r.clone()));
    let corners = [ext_mul(&al, &bl), ext_mul(&al, &bh), ext_mul(&ah, &bl), ext_mul(&ah, &bh)];
    let mut lo = corners[0].clone();
    let mut hi = corners[0].clone();
    for c in &corners[1..] {
        if ext_lt(c, &lo) {
            lo = c.clone();
        }
        if ext_lt(&hi, c) {
            hi = c.clone();
        }
    }
    let to_opt = |e: Ext| match e {
        Ext::Fin(r) => Some(r),
        _ => None, // ±∞
    };
    RatIv { lo: to_opt(lo), hi: to_opt(hi) }
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

// ── univariate-root tier (open-tail completeness) ───────────────────────────

/// Cauchy's bound `B ≥ 0`: every real root of the univariate polynomial with
/// coefficients `coeffs` (low-degree-first) satisfies `|root| < B`. For a constant
/// (or zero) polynomial there are no roots ⇒ `0` (the sign is constant on all of ℝ).
/// `B = 1 + maxᵢ |cᵢ / c_d|` over `i < d`, `c_d` the leading (highest-degree
/// nonzero) coefficient — the standard bound, sound by construction.
fn cauchy_bound(coeffs: &[BigRational]) -> BigRational {
    let mut deg = None;
    for (i, c) in coeffs.iter().enumerate() {
        if !c.is_zero() {
            deg = Some(i);
        }
    }
    let Some(d) = deg else { return BigRational::zero() }; // zero polynomial
    if d == 0 {
        return BigRational::zero(); // constant ⇒ no roots
    }
    let cd = coeffs[d].abs();
    let mut maxr = BigRational::zero();
    for c in &coeffs[..d] {
        let r = c.abs() / &cd;
        if r > maxr {
            maxr = r;
        }
    }
    BigRational::one() + maxr
}

/// Integer feasibility of one univariate atom `(coeffs) ⋈ 0` over `dom`.
enum UniInt {
    /// No integer in `dom` satisfies it — a sound conflict.
    Unsat,
    /// Some integer satisfies it, or an unbounded feasible tail exists — feasible.
    SatOrOpen,
    /// Could not conclude soundly (scan window too large) — treat as open.
    Open,
}

/// Decide integer feasibility of a univariate atom over `dom`, EXACTLY where it
/// can. **Sound on `Unsat`**: returned only when every integer that *could* satisfy
/// the atom is exhausted — the real-feasible region restricted to `dom` is bounded
/// (finite `dom`, or the feasible region ends before `dom`'s open side via the
/// Cauchy bound) and contains no integer. This is the open-tail completeness tier
/// the bounded branch-and-prune cannot reach. Ported from `oxiz-nl2`'s `fdlcg`.
fn univ_int_status(coeffs: &[BigRational], op: FdCmp, dom: &IntDom) -> UniInt {
    let sat_at = |n: &BigInt| -> bool {
        let x = BigRational::from(n.clone());
        let mut acc = BigRational::zero();
        for c in coeffs.iter().rev() {
            acc = acc * &x + c; // Horner
        }
        op.holds_for_sign(sign_of(&acc))
    };
    // Beyond ±B every real root is excluded, so the sign — and hence feasibility —
    // is the constant leading-term behaviour. The only place the sign can vary is
    // the window [-bi, bi]; `bi` rounds the bound up and adds 1 to enclose it.
    let b = cauchy_bound(coeffs);
    let bi = b.ceil().to_integer() + BigInt::one();
    let lo = dom.lo.clone().unwrap_or_else(|| -bi.clone());
    let hi = dom.hi.clone().unwrap_or_else(|| bi.clone());
    let scan_lo = if lo < -bi.clone() { -bi.clone() } else { lo.clone() };
    let scan_hi = if hi > bi { bi.clone() } else { hi.clone() };
    match (&scan_hi - &scan_lo).to_i64() {
        Some(diff) if diff <= MAX_ENUM => {}
        _ => return UniInt::Open, // window too large to scan soundly
    }
    let mut k = scan_lo.clone();
    while k <= scan_hi {
        if sat_at(&k) {
            return UniInt::SatOrOpen;
        }
        k += BigInt::one();
    }
    // The window has no solution. The only remaining integers of `dom` are those
    // BEYOND ±bi, where the sign is the constant leading-term behaviour. `dom` may
    // reach there whether its bound is OPEN (`None`) or merely FINITE-BUT-PAST-`bi`
    // (e.g. `dom = [2,8]`, `bi = 6` leaves `{7,8}` un-scanned) — in BOTH cases the
    // representative `±(bi+1)` (which then lies inside `dom`) decides the whole
    // constant-sign tail. Testing only the `None` case is unsound (it drops the
    // finite over-`bi` integers — a false UNSAT the differential caught).
    let neg_bi = -bi.clone();
    let extends_above = dom.hi.as_ref().is_none_or(|h| *h > bi);
    let extends_below = dom.lo.as_ref().is_none_or(|l| *l < neg_bi);
    let tail_above_sat = extends_above && sat_at(&(&bi + BigInt::one()));
    let tail_below_sat = extends_below && sat_at(&(&neg_bi - BigInt::one()));
    if tail_above_sat || tail_below_sat {
        return UniInt::SatOrOpen;
    }
    // Bounded everywhere relevant and no integer satisfied ⇒ a genuine conflict.
    UniInt::Unsat
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
    // Univariate-at-a-leaf: any atom whose ONLY free var is `v` (all others fixed)
    // is decided EXACTLY over `v`'s domain — closing open-tail nonlinear univariate
    // cases the finite branch-and-prune would otherwise leave Open (e.g. `x² > 4`
    // over an unbounded axis). Sound on Unsat (an atom with no integer solution over
    // its var's domain makes the whole conjunction unsat).
    {
        let fixed = singleton_map(box_);
        for (poly, op) in atoms {
            let Some(v) = lone_free_var(poly, &fixed) else { continue };
            let Some(coeffs) = univ_coeffs_in(poly, v, &fixed) else { continue };
            let dom = box_.get(&v).cloned().unwrap_or_else(IntDom::full);
            if matches!(univ_int_status(&coeffs, *op, &dom), UniInt::Unsat) {
                return BoxResult::Unsat;
            }
        }
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

/// For each `candidate` atom, whether the `asserted` conjunction FORCES its truth
/// value over the cheap (propagate-derived) domain box. Returns `(candidate_index,
/// forced_truth)` for each forced candidate.
///
/// **Sound** (the keystone `box_forced_lit_is_valid_propagation`): `propagate`
/// yields a box that OVER-approximates the feasible set of `asserted` (every
/// integer solution of `asserted` lies in it). If the candidate's atom holds on the
/// WHOLE box (its negation is interval-refuted everywhere), it holds on every
/// feasible point ⇒ `asserted` entails it (force TRUE); symmetrically for FALSE.
/// So a `TheoryHooks` propagation built from this has a theory-valid reason. Used
/// by the bus citizen's `final_check` to propagate forced literals. The check is a
/// sound over-approximation, so it only ever MISSES forced literals (completeness),
/// never reports a wrong one.
#[must_use]
pub fn forced_literals(
    asserted: &[(Polynomial, FdCmp)],
    candidates: &[(Polynomial, FdCmp)],
) -> Vec<(usize, bool)> {
    let mut out = Vec::new();
    if asserted.is_empty() {
        return out;
    }
    let vars = collect_vars(asserted);
    let mut box_ = initial_box(&vars);
    if !propagate(asserted, &mut box_) {
        return out; // `asserted` is already conflicting — the conflict path owns it
    }
    for (i, (poly, op)) in candidates.iter().enumerate() {
        if atom_conflicts(poly, *op, &box_) {
            out.push((i, false)); // refuted everywhere ⇒ forced FALSE
        } else if atom_conflicts(poly, op.negate(), &box_) {
            out.push((i, true)); // negation refuted everywhere ⇒ forced TRUE
        }
    }
    out
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
        // x > 0 alone — satisfiable but unbounded ⇒ NEVER Unsat (univ_int_status
        // finds x=1 in the scan window ⇒ SatOrOpen).
        let d = decide(&[(poly(&[(1, &[(0, 1)])]), FdCmp::Gt)]);
        assert!(!is_unsat(&d));
    }

    #[test]
    fn unbounded_x_squared_eq_2_is_unsat() {
        // x² = 2 over the WHOLE integer axis (no bounds): real roots ±√2, beyond
        // which x² > 2, so no integer anywhere satisfies it. The univariate-root
        // tier decides this UNSAT where the finite branch-and-prune leaves it Open.
        let d = decide(&[(poly(&[(1, &[(0, 2)]), (-2, &[])]), FdCmp::Eq)]);
        assert!(is_unsat(&d), "x²=2 has no integer root (and is bounded-feasible-free)");
    }

    #[test]
    fn unbounded_x_squared_ge_4_is_sat() {
        // x² ≥ 4 over the whole axis — x=2 (or -2) satisfies it ⇒ NOT Unsat.
        let d = decide(&[(poly(&[(1, &[(0, 2)]), (-4, &[])]), FdCmp::Ge)]);
        assert!(!is_unsat(&d), "x²≥4 is satisfiable (x=2)");
    }

    #[test]
    fn unbounded_x_cubed_eq_5_is_unsat() {
        // x³ = 5 over the whole axis — 5 is not a perfect cube ⇒ no integer root.
        let d = decide(&[(poly(&[(1, &[(0, 3)]), (-5, &[])]), FdCmp::Eq)]);
        assert!(is_unsat(&d), "x³=5 has no integer root");
    }

    #[test]
    fn unbounded_neg_quadratic_le_minus_one_is_unsat() {
        // -x² ≥ 1  ⟺  x² ≤ -1 — no real (hence no integer) solution anywhere.
        let d = decide(&[(poly(&[(-1, &[(0, 2)]), (-1, &[])]), FdCmp::Ge)]);
        assert!(is_unsat(&d), "x² ≤ -1 is unsatisfiable");
    }

    #[test]
    fn half_bounded_tail_sat_not_unsat() {
        // x² ≥ 9 with x ≥ 0 (bounded BELOW only) — x=3 in the upper tail ⇒ NOT
        // Unsat (exercises the finite-lo / open-hi tail path).
        let d = decide(&[
            (poly(&[(1, &[(0, 2)]), (-9, &[])]), FdCmp::Ge),
            (poly(&[(1, &[(0, 1)])]), FdCmp::Ge),
        ]);
        assert!(!is_unsat(&d), "x²≥9 ∧ x≥0 is satisfiable (x=3)");
    }

    #[test]
    fn riv_mul_is_sound_over_approximation_with_infinities() {
        // riv_mul must NEVER under-approximate: for every a ∈ A, b ∈ B (including
        // points in unbounded tails), a·b must lie in riv_mul(A, B). An
        // under-approximation would let atom_conflicts fire wrongly ⇒ a false UNSAT.
        // This exercises the new ±∞ corner-product path the bounded differential
        // (all-finite domains) never reaches.
        let vals = [Some(-3i64), Some(-1), Some(0), Some(1), Some(3), None];
        let mk = |lo: Option<i64>, hi: Option<i64>| RatIv {
            lo: lo.map(|x| BigRational::from(BigInt::from(x))),
            hi: hi.map(|x| BigRational::from(BigInt::from(x))),
        };
        let inside = |iv: &RatIv, x: &BigRational| {
            iv.lo.as_ref().is_none_or(|l| l <= x) && iv.hi.as_ref().is_none_or(|h| x <= h)
        };
        // Representative integer points of an interval, including beyond open ends.
        let pts = |lo: Option<i64>, hi: Option<i64>| -> Vec<i64> {
            match (lo, hi) {
                (Some(l), Some(h)) => vec![l, h, (l + h) / 2],
                (None, Some(h)) => vec![h, h - 1, h - 7, h - 60],
                (Some(l), None) => vec![l, l + 1, l + 7, l + 60],
                (None, None) => vec![-60, -1, 0, 1, 60],
            }
        };
        for &alo in &vals {
            for &ahi in &vals {
                if let (Some(l), Some(h)) = (alo, ahi) {
                    if l > h {
                        continue;
                    }
                }
                for &blo in &vals {
                    for &bhi in &vals {
                        if let (Some(l), Some(h)) = (blo, bhi) {
                            if l > h {
                                continue;
                            }
                        }
                        let (a, b) = (mk(alo, ahi), mk(blo, bhi));
                        let prod = riv_mul(&a, &b);
                        for &pa in &pts(alo, ahi) {
                            for &pb in &pts(blo, bhi) {
                                let p = BigRational::from(BigInt::from(pa))
                                    * BigRational::from(BigInt::from(pb));
                                assert!(
                                    inside(&prod, &p),
                                    "riv_mul under-approximated: {alo:?}..{ahi:?} * {blo:?}..{bhi:?} ∌ {pa}*{pb}={p}"
                                );
                            }
                        }
                    }
                }
            }
        }
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
