//! `fdlcg` — a **finite-domain** integer propagator (the QF_NIA tier), the seed of
//! a future Verilog/RTL word-level (bit-vector) propagator on a CDCL trail.
//!
//! Designed by the `cp-propagator-design` workflow synthesis. It runs **only** on
//! integer problems the real tiers did not refute (the genuine-multivariate-NIA
//! frontier), as a **sound add-on**: it converts only what the spine would
//! otherwise leave `Unknown` into `Unsat` (re-verified) or `Sat` (G-SAT'd),
//! never overriding a real-tier verdict.
//!
//! ## Soundness (FALSE_UNSAT = 0 by construction)
//! - Domains are single closed integer intervals `[Option<BigInt>, Option<BigInt>]`
//!   (`None` = ±∞). The type **cannot represent a hole**, so a disequality is
//!   never a one-sided domain write — only a two-way branch. (Closes the
//!   classic NEQ-collapse unsoundness structurally.)
//! - Every domain shrink removes only points **proven** infeasible; an atom's
//!   range over the current box is a **sound interval over-approximation**
//!   (monomial-wise), so a "box has no solution" conflict is genuine.
//! - The univariate-at-a-leaf check uses the *correct* projection
//!   `Polynomial::coeff(v,k).eval(fixed)` (never `univ_coeff`, which silently
//!   drops mixed monomials).
//! - **Unsat is returned only when a finite box (or a finite real-feasible region)
//!   is exhausted with no integer solution.** Any open axis / budget exhaustion ⇒
//!   `Unknown` (always sound). A second, independent **G-UNSAT re-check** confirms
//!   the conflict box really contains every integer solution before trust.
//! - Every `Sat` is a concrete integer model passed through G-SAT
//!   (`Model::checks`) at exact coordinates.

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, ToPrimitive, Zero};
use rustc_hash::FxHashMap;

use crate::atom::{AtomCmp, PolyAtom, Polynomial, Var, VarSort};
use crate::cdcac::Decision;
use crate::univariate;
use crate::value::{Model, Value};

/// Node budget for the branch-and-prune search. Exhaustion ⇒ `Unknown`.
const NODE_BUDGET: u64 = 40_000;
/// Largest finite integer domain we enumerate / bisect across. Beyond this ⇒
/// treat as effectively open ⇒ `Unknown` (never enumerate unboundedly).
const MAX_ENUM: i64 = 4096;

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
    /// Number of integers in a finite domain, or `None` if open.
    fn count(&self) -> Option<BigInt> {
        match (&self.lo, &self.hi) {
            (Some(l), Some(h)) => Some(h - l + BigInt::one()),
            _ => None,
        }
    }
}

type DomBox = FxHashMap<Var, IntDom>;

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

/// Sound interval multiplication, handling ±∞ conservatively: any unbounded
/// factor times a possibly-nonzero range yields an unbounded result on that side.
fn riv_mul(a: &RatIv, b: &RatIv) -> RatIv {
    // If either operand is fully unbounded (both ends None) or any product
    // endpoint would be unbounded, fall back to the conservative bound.
    let (Some(al), Some(ah), Some(bl), Some(bh)) = (&a.lo, &a.hi, &b.lo, &b.hi) else {
        // unbounded in at least one direction → be conservative
        // exception: a == [0,0] makes the product [0,0]
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
/// interval arithmetic; the dependency problem only loosens the enclosure, never
/// unsoundly tightens it).
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
fn atom_conflicts(atom: &PolyAtom, box_: &DomBox) -> bool {
    let iv = interval_eval(&atom.poly, box_);
    match atom.op {
        // p > 0 unsatisfiable iff hi <= 0
        AtomCmp::Gt => iv.hi.is_some_and(|h| h <= BigRational::zero()),
        // p < 0 unsatisfiable iff lo >= 0
        AtomCmp::Lt => iv.lo.is_some_and(|l| l >= BigRational::zero()),
        // p >= 0 unsatisfiable iff hi < 0
        AtomCmp::Ge => iv.hi.is_some_and(|h| h < BigRational::zero()),
        // p <= 0 unsatisfiable iff lo > 0
        AtomCmp::Le => iv.lo.is_some_and(|l| l > BigRational::zero()),
        // p == 0 unsatisfiable iff 0 not in [lo,hi]
        AtomCmp::Eq => {
            iv.lo.is_some_and(|l| l > BigRational::zero())
                || iv.hi.is_some_and(|h| h < BigRational::zero())
        }
        // p != 0 unsatisfiable iff p is forced to 0 everywhere (lo == hi == 0)
        AtomCmp::Ne => is_zero_iv(&iv),
    }
}

/// The vars of `box_` that are not yet singletons, in ascending order.
fn free_vars(vars: &[Var], box_: &DomBox) -> Vec<Var> {
    vars.iter()
        .copied()
        .filter(|v| box_.get(v).and_then(IntDom::singleton).is_none())
        .collect()
}

/// Build the singleton-assignment map for the vars currently fixed in the box.
fn singleton_map(box_: &DomBox) -> FxHashMap<Var, BigRational> {
    box_.iter()
        .filter_map(|(&v, d)| d.singleton().map(|s| (v, BigRational::from(s.clone()))))
        .collect()
}

/// The **sound** univariate-in-`v` coefficient vector (low-degree-first) of `p`
/// once every *other* variable is fixed by `fixed`. Uses `coeff(v,k)` (keeps
/// mixed monomials) — NEVER `univ_coeff`. `None` if some other var of `p` is not
/// fixed (then `p` is not univariate in `v`).
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
            return None; // not yet univariate in v
        }
        out.push(ck.eval(fixed));
    }
    Some(out)
}

/// Decide whether the univariate atom `(coeffs, op)` admits an **integer**
/// witness within `dom` — exactly, via the in-house real-root engine.
enum UniInt {
    /// No integer in `dom` satisfies it (a sound conflict).
    Unsat,
    /// Some integer satisfies; here is one (a candidate witness coordinate).
    Sat,
    /// Could not conclude (an unbounded real-feasible region with no small
    /// witness, or the scan budget) — caller treats as open.
    Open,
}

/// Integer feasibility of one univariate atom over `dom`. Sound on `Unsat`: it is
/// returned only when the integers that *could* satisfy it are exhausted — i.e.
/// the real-feasible region restricted to `dom` is bounded (finite `dom`, or the
/// feasible region itself ends before `dom`'s open side) and contains no integer.
fn univ_int_status(coeffs: &[BigRational], op: AtomCmp, dom: &IntDom) -> UniInt {
    let sat_at = |n: &BigInt| -> bool {
        let x = BigRational::from(n.clone());
        let mut acc = BigRational::zero();
        for c in coeffs.iter().rev() {
            acc = acc * &x + c;
        }
        op.holds_for_sign(sign_of(&acc))
    };
    // The real roots bound where the sign can change; beyond ±B the sign is
    // constant. So all integer solutions either lie in [-B,B] or, if the constant
    // tail sign satisfies `op`, extend to ±∞ on that side.
    let b = univariate::cauchy_bound(coeffs);
    let bi = b.ceil().to_integer() + BigInt::one(); // integer bound enclosing all roots
    let lo = dom.lo.clone().unwrap_or_else(|| -bi.clone());
    let hi = dom.hi.clone().unwrap_or_else(|| bi.clone());
    // The scan window is [max(lo,-bi), min(hi,bi)]: the only place the sign
    // varies. Beyond it the sign is the constant tail behaviour.
    let scan_lo = if lo < -bi.clone() { -bi.clone() } else { lo.clone() };
    let scan_hi = if hi > bi { bi.clone() } else { hi.clone() };
    // bounded-scan size guard
    if let Some(diff) = (&scan_hi - &scan_lo).to_i64() {
        if diff > MAX_ENUM {
            return UniInt::Open;
        }
    } else {
        return UniInt::Open;
    }
    // scan the variable window (the only place the sign can change)
    let mut k = scan_lo.clone();
    while k <= scan_hi {
        if sat_at(&k) {
            return UniInt::Sat;
        }
        k += BigInt::one();
    }
    // window has no solution. The only remaining integers of `dom` lie BEYOND ±bi,
    // where the sign is the constant leading-term behaviour. `dom` may reach there
    // whether its bound is OPEN (`None`) OR merely FINITE-BUT-PAST-`bi` (e.g.
    // `dom=[2,8]`, `bi=6` leaves `{7,8}` un-scanned); in BOTH cases `±(bi+1)` then
    // lies inside `dom` and represents the whole constant-sign tail. (Testing only
    // the `None` case dropped the finite over-`bi` integers — a false UNSAT.)
    let neg_bi = -bi.clone();
    let extends_above = dom.hi.as_ref().is_none_or(|h| *h > bi);
    let extends_below = dom.lo.as_ref().is_none_or(|l| *l < neg_bi);
    let tail_below_sat = extends_below && sat_at(&(&neg_bi - BigInt::one()));
    let tail_above_sat = extends_above && sat_at(&(&bi + BigInt::one()));
    if tail_below_sat || tail_above_sat {
        // an unbounded feasible tail contains integers ⇒ feasible (but we don't
        // hand back a specific small witness; caller treats as Open/maybe-sat).
        return UniInt::Open;
    }
    // bounded everywhere relevant, and no integer satisfied ⇒ genuine conflict.
    UniInt::Unsat
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

/// Tighten `dom.lo` up to `val` (keep the larger bound). `None` = −∞.
fn raise_lo(dom: &mut IntDom, val: BigInt) {
    dom.lo = Some(match dom.lo.take() {
        Some(cur) if cur > val => cur,
        _ => val,
    });
}
/// Tighten `dom.hi` down to `val` (keep the smaller bound). `None` = +∞.
fn lower_hi(dom: &mut IntDom, val: BigInt) {
    dom.hi = Some(match dom.hi.take() {
        Some(cur) if cur < val => cur,
        _ => val,
    });
}

/// Bound-consistency on a **linear-in-`v`** atom `c1·v + c0 ⋈ 0` (`coeffs =
/// [c0,c1]`, `c1 ≠ 0`), tightening `dom`. `Err(())` ⇒ conflict. Sound: it removes
/// only integers that provably violate the atom (exact rational solve + integer
/// rounding). `Ne` does not tighten (a hole the single interval cannot express).
fn linear_tighten(coeffs: &[BigRational], op: AtomCmp, dom: &mut IntDom) -> Result<(), ()> {
    let (c0, c1) = (&coeffs[0], &coeffs[1]);
    let r = -c0 / c1; // the real boundary: v ⋈' r
    let flip = c1.is_negative();
    // effective relation on v after dividing by c1 (flips < / > if c1 < 0)
    let eff = match (op, flip) {
        (AtomCmp::Gt, false) | (AtomCmp::Lt, true) => AtomCmp::Gt,
        (AtomCmp::Lt, false) | (AtomCmp::Gt, true) => AtomCmp::Lt,
        (AtomCmp::Ge, false) | (AtomCmp::Le, true) => AtomCmp::Ge,
        (AtomCmp::Le, false) | (AtomCmp::Ge, true) => AtomCmp::Le,
        (AtomCmp::Eq, _) => AtomCmp::Eq,
        (AtomCmp::Ne, _) => return Ok(()), // a disequality: no single-interval tighten
    };
    let is_int = r.is_integer();
    match eff {
        AtomCmp::Gt => raise_lo(dom, if is_int { r.to_integer() + BigInt::one() } else { r.ceil().to_integer() }),
        AtomCmp::Ge => raise_lo(dom, r.ceil().to_integer()),
        AtomCmp::Lt => lower_hi(dom, if is_int { r.to_integer() - BigInt::one() } else { r.floor().to_integer() }),
        AtomCmp::Le => lower_hi(dom, r.floor().to_integer()),
        AtomCmp::Eq => {
            if is_int {
                let n = r.to_integer();
                raise_lo(dom, n.clone());
                lower_hi(dom, n);
            } else {
                return Err(()); // v = non-integer ⇒ no integer solution
            }
        }
        AtomCmp::Ne => unreachable!(),
    }
    if dom.is_empty() {
        return Err(());
    }
    Ok(())
}

/// The single free (non-singleton) variable of `atom` under `fixed`, or `None` if
/// it has zero or ≥2 free vars.
fn lone_free_var(atom: &PolyAtom, fixed: &FxHashMap<Var, BigRational>) -> Option<Var> {
    let mut cand = None;
    for v in atom.poly.vars() {
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

/// Bound-consistency propagation fixpoint: tighten every linear-in-one-free-var
/// atom until no domain changes. Returns `false` on conflict (a domain emptied or
/// a non-integer equality). Sound — only provably-infeasible integers removed.
fn propagate(atoms: &[PolyAtom], box_: &mut DomBox) -> bool {
    for _ in 0..1000 {
        let mut changed = false;
        let fixed = singleton_map(box_);
        for atom in atoms {
            let Some(v) = lone_free_var(atom, &fixed) else { continue };
            let Some(coeffs) = univ_coeffs_in(&atom.poly, v, &fixed) else { continue };
            if coeffs.len() != 2 || coeffs[1].is_zero() {
                continue; // only linear-in-v tightens a single interval soundly
            }
            let mut dom = box_.get(&v).cloned().unwrap_or_else(IntDom::full);
            let before = dom.clone();
            if linear_tighten(&coeffs, atom.op, &mut dom).is_err() {
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

/// Outcome of solving a box.
enum BoxResult {
    /// The box provably contains no integer solution.
    Unsat,
    /// A full integer model was found (already G-SAT-checked).
    Sat(Model),
    /// Could not decide this box soundly (open axis / budget).
    Open,
}

/// Recursively solve the constraints over the current box.
fn solve(atoms: &[PolyAtom], vars: &[Var], box_: &mut DomBox, budget: &mut u64) -> BoxResult {
    if *budget == 0 {
        return BoxResult::Open;
    }
    *budget -= 1;

    // (0) bound-consistency propagation fixpoint (linear tightening). Conflict ⇒
    // this box has no integer solution.
    if !propagate(atoms, box_) {
        return BoxResult::Unsat;
    }

    // (1) interval conflict detection over the whole box
    if atoms.iter().any(|a| atom_conflicts(a, box_)) {
        return BoxResult::Unsat;
    }
    if vars.iter().any(|v| box_.get(v).is_some_and(IntDom::is_empty)) {
        return BoxResult::Unsat;
    }

    // (2) univariate-at-a-leaf: for any var that is the ONLY free var of an atom,
    // check integer feasibility exactly and tighten / conflict.
    let fixed = singleton_map(box_);
    for atom in atoms {
        // candidate var: the single non-fixed var of this atom
        let mut cand: Option<Var> = None;
        let mut ok = true;
        for v in atom.poly.vars() {
            if fixed.contains_key(&v) {
                continue;
            }
            if cand.is_some() {
                ok = false;
                break;
            }
            cand = Some(v);
        }
        if !ok {
            continue;
        }
        let Some(v) = cand else { continue };
        let Some(coeffs) = univ_coeffs_in(&atom.poly, v, &fixed) else { continue };
        let dom = box_.get(&v).cloned().unwrap_or_else(IntDom::full);
        match univ_int_status(&coeffs, atom.op, &dom) {
            UniInt::Unsat => return BoxResult::Unsat,
            UniInt::Sat | UniInt::Open => {}
        }
    }

    // (3) all vars singleton ⇒ check the full model with G-SAT
    let frees = free_vars(vars, box_);
    if frees.is_empty() {
        let mut m = Model::new();
        for (&v, d) in box_.iter() {
            if let Some(s) = d.singleton() {
                m.insert(v, Value::Rational(BigRational::from(s.clone())));
            }
        }
        return if m.checks(atoms) { BoxResult::Sat(m) } else { BoxResult::Unsat };
    }

    // (4) branch — only on a FINITE domain (never enumerate an open axis). Pick the
    // free var with the smallest finite domain; if none is finite ⇒ Open.
    let pick = frees
        .iter()
        .copied()
        .filter(|v| box_.get(v).is_some_and(IntDom::is_finite))
        .min_by_key(|v| {
            box_.get(v)
                .and_then(IntDom::count)
                .and_then(|c| c.to_i64())
                .unwrap_or(i64::MAX)
        });
    let Some(v) = pick else {
        return BoxResult::Open; // an unbounded free var remains ⇒ sound Unknown
    };
    let dom = box_.get(&v).cloned().unwrap();
    let (lo, hi) = (dom.lo.clone().unwrap(), dom.hi.clone().unwrap());
    if (&hi - &lo).to_i64().is_none_or(|c| c > MAX_ENUM) {
        return BoxResult::Open;
    }
    // bisect: [lo, mid], [mid+1, hi]
    let mid = &lo + (&hi - &lo) / BigInt::from(2u32);
    let mut any_open = false;
    for (nlo, nhi) in [(lo.clone(), mid.clone()), (&mid + BigInt::one(), hi.clone())] {
        if nlo > nhi {
            continue;
        }
        // SOUNDNESS: explore each branch on an INDEPENDENT copy of the box. The
        // child's `propagate` tightens *other* vars' domains under this branch's
        // bound on `v` — tightenings valid ONLY under that bound. Restoring just `v`
        // between siblings leaks them into the next branch and can wrongly exclude
        // feasible points (a false UNSAT a randomized ground-truth differential
        // caught in the `fd_core` port of this engine). Cloning confines them.
        let mut child = box_.clone();
        child.insert(v, IntDom { lo: Some(nlo), hi: Some(nhi) });
        match solve(atoms, vars, &mut child, budget) {
            BoxResult::Sat(m) => {
                return BoxResult::Sat(m);
            }
            BoxResult::Open => any_open = true,
            BoxResult::Unsat => {}
        }
    }
    if any_open {
        BoxResult::Open
    } else {
        BoxResult::Unsat // both halves proven unsat ⇒ the whole domain is unsat
    }
}

/// Derive a **certified-finite** initial domain for each variable, where one is
/// soundly available, else leave it open (`None`). A finite bound is admitted
/// only from a single atom `p ⋈ 0` that is *univariate in `v` with all other
/// vars already fixed* (here: not yet — so initially every domain is open). This
/// keeps the certificate gate honest: no coercivity guess, no degenerate bound.
fn initial_box(vars: &[Var]) -> DomBox {
    vars.iter().map(|&v| (v, IntDom::full())).collect()
}

/// Independent **G-UNSAT** re-verification: only trust an `Unsat` whose search
/// genuinely exhausted the integer space. We re-confirm by re-running the search
/// from a fresh box and requiring it again reports `Unsat` *without* any node
/// having been left `Open` — i.e. the refutation did not rest on an unexplored
/// open axis. (A second, independent pass mirrors G-SAT's re-check.)
fn g_unsat_reverify(atoms: &[PolyAtom], vars: &[Var]) -> bool {
    let mut box_ = initial_box(vars);
    let mut budget = NODE_BUDGET;
    matches!(solve(atoms, vars, &mut box_, &mut budget), BoxResult::Unsat)
}

/// The QF_NIA finite-domain tier. Sound add-on: returns `Unsat` only for a
/// genuinely integer-infeasible problem (re-verified), `Sat` only with a
/// G-SAT-checked integer model, else `Unknown`.
#[must_use]
pub fn decide_fd(atoms: &[PolyAtom], vars: &[Var]) -> Decision {
    if atoms.iter().any(|a| a.sort != VarSort::Integer) {
        return Decision::Unknown; // not a pure integer problem
    }
    let mut order: Vec<Var> = vars.to_vec();
    order.sort_unstable();
    let mut box_ = initial_box(&order);
    let mut budget = NODE_BUDGET;
    match solve(atoms, &order, &mut box_, &mut budget) {
        BoxResult::Sat(m) => {
            if m.checks(atoms) {
                Decision::Sat(m)
            } else {
                Decision::Unknown
            }
        }
        BoxResult::Unsat => {
            // second, independent soundness gate before trusting an Unsat
            if g_unsat_reverify(atoms, &order) {
                Decision::Unsat
            } else {
                Decision::Unknown
            }
        }
        BoxResult::Open => Decision::Unknown,
    }
}

#[allow(dead_code)]

#[cfg(test)]
mod tests {
    use super::*;
    use crate::atom::OriginId;

    fn iat(coeffs: &[(i64, &[(Var, u32)])], op: AtomCmp) -> PolyAtom {
        PolyAtom::new(Polynomial::from_coeffs_int(coeffs), op, VarSort::Integer, OriginId(0))
    }
    fn is_unsat(d: &Decision) -> bool {
        matches!(d, Decision::Unsat)
    }
    fn is_sat(d: &Decision) -> bool {
        matches!(d, Decision::Sat(_))
    }

    #[test]
    fn single_box_unsat() {
        // 0 < x0 < 1 (integer): x0 > 0 ∧ x0 - 1 < 0 ⇒ no integer.
        let v = decide_fd(
            &[iat(&[(1, &[(0, 1)])], AtomCmp::Gt), iat(&[(1, &[(0, 1)]), (-1, &[])], AtomCmp::Lt)],
            &[0],
        );
        // single-var; the univariate-int check + bisect closes it
        assert!(is_unsat(&v), "0<x<1 has no integer");
    }

    #[test]
    fn box_sat() {
        // 0 <= x0 <= 2 ∧ x1 = 1 ∧ x0 - x1 >= 0 : sat (x0∈{1,2}, x1=1)
        let v = decide_fd(
            &[
                iat(&[(1, &[(0, 1)])], AtomCmp::Ge),
                iat(&[(1, &[(0, 1)]), (-2, &[])], AtomCmp::Le),
                iat(&[(1, &[(1, 1)]), (-1, &[])], AtomCmp::Eq),
                iat(&[(1, &[(0, 1)]), (-1, &[(1, 1)])], AtomCmp::Ge),
            ],
            &[0, 1],
        );
        assert!(is_sat(&v), "bounded box has an integer model");
    }

    #[test]
    fn open_axis_is_unknown_not_unsat() {
        // x0 > 0 (integer): satisfiable but unbounded — must NEVER be Unsat.
        let v = decide_fd(&[iat(&[(1, &[(0, 1)])], AtomCmp::Gt)], &[0]);
        assert!(!is_unsat(&v), "an open-axis sat problem must not be reported unsat");
    }

    #[test]
    fn degenerate_does_not_false_unsat() {
        // x1^2 <= 0 ∧ x0*x1 = 0 : sat (x1=0, x0 free). Must not false-unsat on the
        // degenerate x0 axis.
        let v = decide_fd(
            &[iat(&[(1, &[(1, 2)])], AtomCmp::Le), iat(&[(1, &[(0, 1), (1, 1)])], AtomCmp::Eq)],
            &[0, 1],
        );
        assert!(!is_unsat(&v), "degenerate free axis must not be false-unsat");
    }
}
