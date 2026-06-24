//! `FdPropagator` — a finite-domain integer **constraint-propagation theory** on
//! the §4.2 `TheoryHooks` bus.
//!
//! This is the bus-citizen port of the `fdlcg` prototype (clean-room `oxiz-nl2`):
//! the QF_NIA finite-domain propagator, re-expressed as a `TheoryHooks` theory so
//! it lives on the **shared CDCL(T) trail** instead of owning a private solver
//! loop. It is the constraint-programming slice of the multi-paradigm propagator
//! bus (the design doc: `AD1/docs/design/UNIFIED_VERIFICATION_GATE.md`), and the
//! reference implementation of the verified keystone
//! `oxiz-nl2-verification/src/cp_propagator.rs` (`empty_box_is_sound_conflict` /
//! `tightening_preserves_over_approx` / `box_forced_lit_is_valid_propagation`).
//!
//! ## Where the trail draws the line (CDCL(T), not MCSAT)
//! The bus trail carries Boolean `Lit`s — it decides **which polynomial atoms are
//! asserted**, not integer variable values. So:
//!   * the Boolean-structure branching (which constraints hold) is the **trail's**;
//!   * the integer-variable search (bound propagation + bisection) stays **inside
//!     this theory** — it is the theory's own decision procedure, invoked at the
//!     trail's fixpoints.
//!
//! `final_check` runs the **cheap** linear bound-propagation + interval conflict
//! detection (fired after every Boolean fixpoint). `final_check_complete` runs the
//! **complete** branch-and-prune (fired once per full assignment), authorising
//! `Sat` only with an exact integer model.
//!
//! ## Soundness (FALSE_UNSAT = 0, FALSE_SAT = 0)
//! - Domains are single closed integer intervals (`None` = ±∞) — the type cannot
//!   express a hole, so a disequality is never a one-sided write (closes the
//!   classic NEQ-collapse unsoundness structurally).
//! - Every domain shrink removes only **proven**-infeasible points; an atom's range
//!   over the box is a sound interval over-approximation (monomial-wise). An empty
//!   box is therefore a genuine conflict (the keystone's `empty_box_is_sound_conflict`).
//! - `Unsat` (⟹ `Conflict`) is returned only when a finite box is exhausted with no
//!   integer solution; any open axis / budget exhaustion ⇒ the verdict stays `Open`.
//! - **The CDCL(T) bus has no `Unknown` step.** When the theory cannot decide
//!   (`Open`), `final_check_complete` returns `Ok` (it cannot refute) but records
//!   [`FdVerdict::Open`] in [`FdPropagator::verdict`]; the caller MUST downgrade a
//!   resulting `Sat` to `Unknown` — the same `had_opaque` discipline adsmt uses for
//!   opaque asserts. Returning `Ok` on `Open` is sound ONLY under that contract.
//!
//! ## Scope of this first increment
//! A deliberately soundness-complete **subset** of `fdlcg`: interval
//! over-approximation, linear bound-consistency, finite branch-and-prune, and exact
//! integer model checking. The univariate-root tier (`cauchy_bound` /
//! `univ_int_status`, which converts some open-tail nonlinear cases to `Unsat`) is a
//! completeness add-on for a later increment — dropping it only turns some `Unsat`
//! into `Open`, never a sound verdict into a false one.

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, ToPrimitive, Zero};
use rustc_hash::FxHashMap;
use smallvec::SmallVec;

use oxiz_math::polynomial::{Polynomial, Var as PolyVar};
use oxiz_sat::{Lit, TheoryHooks, TheoryStep, Var};

/// Node budget for the branch-and-prune search. Exhaustion ⇒ `Open`.
const NODE_BUDGET: u64 = 40_000;
/// Largest finite integer domain we enumerate / bisect across. Beyond this ⇒
/// treat as effectively open ⇒ `Open` (never enumerate unboundedly).
const MAX_ENUM: i64 = 4096;

/// A polynomial comparison `p ⋈ 0` (the `oxiz-nl2` `AtomCmp`, ported locally).
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
    /// model re-check (G-SAT): evaluate `p` at the model to an exact sign, then ask
    /// whether that sign honours the comparison.
    #[must_use]
    fn holds_for_sign(self, sign: i32) -> bool {
        match self {
            FdCmp::Lt => sign < 0,
            FdCmp::Le => sign <= 0,
            FdCmp::Gt => sign > 0,
            FdCmp::Ge => sign >= 0,
            FdCmp::Eq => sign == 0,
            FdCmp::Ne => sign != 0,
        }
    }

    /// The exact negation of `p ⋈ 0` over an ordered field (used when an atom is
    /// asserted *false* on the trail): `¬(p<0) = (p≥0)`, etc.
    #[must_use]
    fn negate(self) -> FdCmp {
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

/// An asserted (polarity-resolved) atom `poly ⋈ 0` the theory currently believes.
#[derive(Clone)]
struct EffAtom {
    poly: Polynomial,
    op: FdCmp,
}

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

type DomBox = FxHashMap<PolyVar, IntDom>;

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
fn atom_conflicts(atom: &EffAtom, box_: &DomBox) -> bool {
    let iv = interval_eval(&atom.poly, box_);
    match atom.op {
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

/// The union of all variables occurring in `atoms`, sorted ascending.
fn collect_vars(atoms: &[EffAtom]) -> Vec<PolyVar> {
    let mut set: Vec<PolyVar> = Vec::new();
    for a in atoms {
        for v in a.poly.vars() {
            if !set.contains(&v) {
                set.push(v);
            }
        }
    }
    set.sort_unstable();
    set
}

fn initial_box(vars: &[PolyVar]) -> DomBox {
    vars.iter().map(|&v| (v, IntDom::full())).collect()
}

fn free_vars(vars: &[PolyVar], box_: &DomBox) -> Vec<PolyVar> {
    vars.iter()
        .copied()
        .filter(|v| box_.get(v).and_then(IntDom::singleton).is_none())
        .collect()
}

fn singleton_map(box_: &DomBox) -> FxHashMap<PolyVar, BigRational> {
    box_.iter()
        .filter_map(|(&v, d)| d.singleton().map(|s| (v, BigRational::from(s.clone()))))
        .collect()
}

/// The **sound** univariate-in-`v` coefficient vector (low-degree-first) of `p`
/// once every *other* variable is fixed by `fixed`. Uses `coeff(v,k)` (keeps mixed
/// monomials) — NEVER a mixed-monomial-dropping projection. `None` if some other
/// var of `p` is not fixed (then `p` is not univariate in `v`).
fn univ_coeffs_in(
    p: &Polynomial,
    v: PolyVar,
    fixed: &FxHashMap<PolyVar, BigRational>,
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

/// The single free (non-singleton) variable of `atom` under `fixed`, or `None` if
/// it has zero or ≥2 free vars.
fn lone_free_var(atom: &EffAtom, fixed: &FxHashMap<PolyVar, BigRational>) -> Option<PolyVar> {
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
/// [c0,c1]`, `c1 ≠ 0`), tightening `dom`. `Err(())` ⇒ conflict. Sound: removes
/// only integers that provably violate the atom (exact rational solve + integer
/// rounding). `Ne` does not tighten (a hole the single interval cannot express).
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
fn propagate(atoms: &[EffAtom], box_: &mut DomBox) -> bool {
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

/// Exact integer model check (G-SAT): every atom must hold at the assignment.
fn model_checks(atoms: &[EffAtom], model: &FxHashMap<PolyVar, BigRational>) -> bool {
    atoms.iter().all(|a| a.op.holds_for_sign(sign_of(&a.poly.eval(model))))
}

/// Outcome of solving a box.
enum BoxResult {
    Unsat,
    Sat(FxHashMap<PolyVar, BigRational>),
    Open,
}

/// Recursively solve the constraints over the current box (branch-and-prune).
fn solve(atoms: &[EffAtom], vars: &[PolyVar], box_: &mut DomBox, budget: &mut u64) -> BoxResult {
    if *budget == 0 {
        return BoxResult::Open;
    }
    *budget -= 1;

    // (0) bound-consistency propagation fixpoint (linear tightening).
    if !propagate(atoms, box_) {
        return BoxResult::Unsat;
    }
    // (1) interval conflict detection over the whole box.
    if atoms.iter().any(|a| atom_conflicts(a, box_)) {
        return BoxResult::Unsat;
    }
    if vars.iter().any(|v| box_.get(v).is_some_and(IntDom::is_empty)) {
        return BoxResult::Unsat;
    }
    // (2) all vars singleton ⇒ check the full model with G-SAT.
    let frees = free_vars(vars, box_);
    if frees.is_empty() {
        let model = singleton_map(box_);
        return if model_checks(atoms, &model) {
            BoxResult::Sat(model)
        } else {
            BoxResult::Unsat
        };
    }
    // (3) branch — only on a FINITE domain (never enumerate an open axis). Pick the
    // free var with the smallest finite domain; if none is finite ⇒ Open.
    let pick = frees
        .iter()
        .copied()
        .filter(|v| box_.get(v).is_some_and(IntDom::is_finite))
        .min_by_key(|v| {
            box_.get(v).and_then(IntDom::count).and_then(|c| c.to_i64()).unwrap_or(i64::MAX)
        });
    let Some(v) = pick else {
        return BoxResult::Open; // an unbounded free var remains ⇒ sound Open
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
        let saved = box_.get(&v).cloned();
        box_.insert(v, IntDom { lo: Some(nlo), hi: Some(nhi) });
        match solve(atoms, vars, box_, budget) {
            BoxResult::Sat(m) => return BoxResult::Sat(m),
            BoxResult::Open => any_open = true,
            BoxResult::Unsat => {}
        }
        match saved {
            Some(d) => {
                box_.insert(v, d);
            }
            None => {
                box_.remove(&v);
            }
        }
    }
    if any_open {
        BoxResult::Open
    } else {
        BoxResult::Unsat
    }
}

/// Independent **G-UNSAT** re-verification: only trust an `Unsat` whose search
/// genuinely exhausted the integer space, re-run from a fresh box (mirrors G-SAT's
/// re-check).
fn g_unsat_reverify(atoms: &[EffAtom], vars: &[PolyVar]) -> bool {
    let mut box_ = initial_box(vars);
    let mut budget = NODE_BUDGET;
    matches!(solve(atoms, vars, &mut box_, &mut budget), BoxResult::Unsat)
}

/// The theory's decision on the asserted conjunction.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FdVerdict {
    /// No assertion processed yet / nothing to decide.
    Trivial,
    /// The conjunction is integer-UNSAT (G-UNSAT re-verified).
    Unsat,
    /// A concrete integer model was found and exactly checked (G-SAT).
    Sat,
    /// Could not decide soundly (open axis / budget). The caller MUST treat a
    /// resulting solver `Sat` as `Unknown`.
    Open,
}

/// The full finite-domain decision over a polarity-resolved atom set. Sound:
/// `Unsat` only re-verified, `Sat` only with a G-SAT model, else `Open`.
fn decide_fd(atoms: &[EffAtom]) -> FdVerdict {
    let vars = collect_vars(atoms);
    let mut box_ = initial_box(&vars);
    let mut budget = NODE_BUDGET;
    match solve(atoms, &vars, &mut box_, &mut budget) {
        BoxResult::Sat(m) => {
            if model_checks(atoms, &m) {
                FdVerdict::Sat
            } else {
                FdVerdict::Open
            }
        }
        BoxResult::Unsat => {
            if g_unsat_reverify(atoms, &vars) {
                FdVerdict::Unsat
            } else {
                FdVerdict::Open
            }
        }
        BoxResult::Open => FdVerdict::Open,
    }
}

/// A finite-domain integer CP theory on the `TheoryHooks` bus.
///
/// Each input atom `poly ⋈ 0` is abstracted by a Boolean `Var`; the trail decides
/// the Var, this theory decides integer feasibility of the resulting conjunction.
pub struct FdPropagator {
    /// The atoms, indexed by the position the Boolean `Var` maps to.
    atoms: Vec<(Polynomial, FdCmp)>,
    /// Boolean atom `Var` → index into `atoms`.
    var_to_atom: FxHashMap<Var, usize>,
    /// Currently-asserted `(lit, atom index, polarity)`, in trail order.
    asserted: Vec<(Lit, usize, bool)>,
    /// `asserted.len()` checkpoints, one per live decision level (scoped rollback).
    frame_marks: Vec<usize>,
    /// The last completeness verdict (see [`FdPropagator::verdict`]).
    verdict: FdVerdict,
}

impl FdPropagator {
    /// Build a propagator from `(poly, cmp, boolean-var)` triples. The `Var` is the
    /// trail's Boolean abstraction of the atom `poly cmp 0`.
    #[must_use]
    pub fn new(atoms: Vec<(Polynomial, FdCmp, Var)>) -> Self {
        let mut polys = Vec::with_capacity(atoms.len());
        let mut var_to_atom = FxHashMap::default();
        for (poly, cmp, var) in atoms {
            var_to_atom.insert(var, polys.len());
            polys.push((poly, cmp));
        }
        FdPropagator {
            atoms: polys,
            var_to_atom,
            asserted: Vec::new(),
            frame_marks: Vec::new(),
            verdict: FdVerdict::Trivial,
        }
    }

    /// The theory's last completeness verdict. After `solve_with_hooks` returns
    /// `Sat`, the caller MUST downgrade it to `Unknown` if this is
    /// [`FdVerdict::Open`] (the CDCL(T) bus has no `Unknown` step; see the module
    /// docs — this is the `had_opaque` Sat→Unknown discipline).
    #[must_use]
    pub fn verdict(&self) -> FdVerdict {
        self.verdict
    }

    /// The polarity-resolved atoms currently asserted on the trail.
    fn active_atoms(&self) -> Vec<EffAtom> {
        self.asserted
            .iter()
            .map(|&(_, idx, polarity)| {
                let (poly, cmp) = &self.atoms[idx];
                EffAtom { poly: poly.clone(), op: if polarity { *cmp } else { cmp.negate() } }
            })
            .collect()
    }

    /// The conflict clause: the negation of the asserted literals (all currently
    /// true), so the learned clause's literals are all currently false — the shape
    /// `TheoryStep::Conflict` consumes. This is a sound (whole-set) explanation;
    /// minimisation is a later optimisation.
    fn explanation(&self) -> SmallVec<[Lit; 8]> {
        self.asserted.iter().map(|&(lit, _, _)| lit.negate()).collect()
    }
}

impl TheoryHooks for FdPropagator {
    fn assign_hook(&mut self, lit: Lit, _level: u32) -> TheoryStep {
        if let Some(&idx) = self.var_to_atom.get(&lit.var()) {
            // Final-check-driven: record the asserted atom; the work happens in
            // `final_check` / `final_check_complete` (the driver acts on their return).
            self.asserted.push((lit, idx, !lit.is_neg()));
        }
        TheoryStep::Ok
    }

    fn unassign_hook(&mut self, lit: Lit, _level: u32) {
        // Drop the atom the instant its literal leaves the trail (no stale state).
        if let Some(pos) = self.asserted.iter().rposition(|&(l, _, _)| l == lit) {
            self.asserted.remove(pos);
        }
    }

    fn push_frame(&mut self, _level: u32) {
        self.frame_marks.push(self.asserted.len());
    }

    fn pop_frame(&mut self, _level: u32) {
        // Scoped rollback: forget every atom asserted since this level opened.
        if let Some(mark) = self.frame_marks.pop() {
            self.asserted.truncate(mark);
        }
    }

    fn final_check(&mut self) -> TheoryStep {
        // CHEAP per-fixpoint check: linear bound-propagation + interval conflict
        // over a fresh box. A conflict here is a genuine refutation of the asserted
        // conjunction (the keystone's `empty_box_is_sound_conflict`).
        let active = self.active_atoms();
        if active.is_empty() {
            return TheoryStep::Ok;
        }
        let vars = collect_vars(&active);
        let mut box_ = initial_box(&vars);
        if !propagate(&active, &mut box_) || active.iter().any(|a| atom_conflicts(a, &box_)) {
            return TheoryStep::Conflict { explanation: self.explanation() };
        }
        TheoryStep::Ok
    }

    fn final_check_complete(&mut self) -> TheoryStep {
        // COMPLETE check (full assignment): the theory's own integer-variable
        // branch-and-prune. `Unsat` ⇒ a sound `Conflict`; otherwise `Ok`, with the
        // completeness verdict recorded for the caller's Sat→Unknown downgrade.
        let active = self.active_atoms();
        if active.is_empty() {
            self.verdict = FdVerdict::Trivial;
            return TheoryStep::Ok;
        }
        self.verdict = decide_fd(&active);
        match self.verdict {
            FdVerdict::Unsat => TheoryStep::Conflict { explanation: self.explanation() },
            // `Sat` authorises the verdict; `Open` returns `Ok` (cannot refute) but
            // leaves `verdict() == Open` so the caller downgrades a resulting Sat.
            FdVerdict::Sat | FdVerdict::Open | FdVerdict::Trivial => TheoryStep::Ok,
        }
    }

    fn eval(&mut self, _atom: Var) -> Option<bool> {
        // The integer model is reconstructed by the complete check, not exposed as a
        // per-atom Boolean oracle — stay conservative (as `TheoryManager::eval`).
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use oxiz_sat::{Solver, SolverResult};

    /// `coeffs` is `(int-coeff, &[(poly-var, power)])` — the `oxiz-math`
    /// `from_coeffs_int` shape.
    fn poly(coeffs: &[(i64, &[(PolyVar, u32)])]) -> Polynomial {
        Polynomial::from_coeffs_int(coeffs)
    }

    #[test]
    fn fd_conjunction_unsat_is_solver_unsat() {
        // 0 < x ∧ x - 1 < 0  (integer)  ⇒ no integer ⇒ the trail must report UNSAT.
        let mut solver = Solver::new();
        let a0 = solver.new_var(); // abstracts  x > 0
        let a1 = solver.new_var(); // abstracts  x - 1 < 0
        solver.add_clause([Lit::pos(a0)]);
        solver.add_clause([Lit::pos(a1)]);
        let theory = FdPropagator::new(vec![
            (poly(&[(1, &[(0, 1)])]), FdCmp::Gt, a0),
            (poly(&[(1, &[(0, 1)]), (-1, &[])]), FdCmp::Lt, a1),
        ]);
        let (result, theory) = solver.solve_with_hooks(theory);
        assert_eq!(result, SolverResult::Unsat, "0<x<1 has no integer");
        // The refutation came from the theory's complete check (or the cheap one).
        assert_ne!(theory.verdict(), FdVerdict::Sat);
    }

    #[test]
    fn fd_bounded_box_is_sat() {
        // 0 ≤ x ∧ x ≤ 2 ∧ y = 1 ∧ x - y ≥ 0 : sat (x∈{1,2}, y=1).
        let mut solver = Solver::new();
        let a0 = solver.new_var();
        let a1 = solver.new_var();
        let a2 = solver.new_var();
        let a3 = solver.new_var();
        for a in [a0, a1, a2, a3] {
            solver.add_clause([Lit::pos(a)]);
        }
        let theory = FdPropagator::new(vec![
            (poly(&[(1, &[(0, 1)])]), FdCmp::Ge, a0),
            (poly(&[(1, &[(0, 1)]), (-2, &[])]), FdCmp::Le, a1),
            (poly(&[(1, &[(1, 1)]), (-1, &[])]), FdCmp::Eq, a2),
            (poly(&[(1, &[(0, 1)]), (-1, &[(1, 1)])]), FdCmp::Ge, a3),
        ]);
        let (result, theory) = solver.solve_with_hooks(theory);
        assert_eq!(result, SolverResult::Sat);
        assert_eq!(theory.verdict(), FdVerdict::Sat, "a concrete integer model exists");
    }

    #[test]
    fn fd_open_axis_is_not_false_unsat() {
        // x > 0 (integer): satisfiable but unbounded. The theory must NEVER refute
        // it; the verdict is Open (the caller downgrades the solver Sat to Unknown).
        let mut solver = Solver::new();
        let a0 = solver.new_var();
        solver.add_clause([Lit::pos(a0)]);
        let theory = FdPropagator::new(vec![(poly(&[(1, &[(0, 1)])]), FdCmp::Gt, a0)]);
        let (result, theory) = solver.solve_with_hooks(theory);
        assert_ne!(result, SolverResult::Unsat, "an open-axis sat problem must not be unsat");
        assert_eq!(theory.verdict(), FdVerdict::Open, "unbounded ⇒ sound Open, not Sat");
    }

    #[test]
    fn fd_false_asserted_atom_negates() {
        // Assert ¬(x ≤ 0) i.e. x > 0, plus x - 1 < 0  ⇒ 0 < x < 1 ⇒ UNSAT, via the
        // false-polarity negation path (a0 forced FALSE).
        let mut solver = Solver::new();
        let a0 = solver.new_var(); // x ≤ 0, asserted FALSE ⇒ x > 0
        let a1 = solver.new_var(); // x - 1 < 0
        solver.add_clause([Lit::neg(a0)]);
        solver.add_clause([Lit::pos(a1)]);
        let theory = FdPropagator::new(vec![
            (poly(&[(1, &[(0, 1)])]), FdCmp::Le, a0),
            (poly(&[(1, &[(0, 1)]), (-1, &[])]), FdCmp::Lt, a1),
        ]);
        let (result, _theory) = solver.solve_with_hooks(theory);
        assert_eq!(result, SolverResult::Unsat, "¬(x≤0) ∧ x<1 has no integer");
    }
}
