//! A **correct, self-contained** univariate real-root engine (Sturm) and an
//! exact single-variable decision procedure.
//!
//! Built in-house because every univariate root tool in the vendored substrate
//! is unreliable: `cad::SturmSequence::count_roots` under-counts on a negative
//! leading coefficient, and `root_isolation::RootIsolator::isolate_roots` hangs.
//! Since `oxiz-nl2` replaces that substrate wholesale, its soundness must not
//! depend on any of it — this module touches only exact `BigRational` arithmetic.
//!
//! A polynomial is a `Vec<BigRational>` of coefficients **low-degree first**
//! (`c[i]` is the coefficient of `xⁱ`), with trailing zeros stripped (the zero
//! polynomial is the empty vector).
//!
//! Univariate real arithmetic is decidable, so [`decide`] always returns a
//! definite answer — `Unsat`, `Sat` with a *rational* witness, or
//! `SatIrrational` (satisfiable, but every witness is irrational, so a rational
//! model cannot be produced yet — the caller reports `Unknown` until the M3
//! algebraic primitives land).

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};

use crate::atom::AtomCmp;

type Poly = Vec<BigRational>;

fn r0() -> BigRational {
    BigRational::zero()
}

/// Strip trailing (high-degree) zero coefficients.
fn normalize(mut p: Poly) -> Poly {
    while p.last().is_some_and(|c| c.is_zero()) {
        p.pop();
    }
    p
}

/// Degree, or `None` for the zero polynomial.
fn degree(p: &[BigRational]) -> Option<usize> {
    if p.is_empty() { None } else { Some(p.len() - 1) }
}

/// Horner evaluation at a rational point.
fn eval(p: &[BigRational], x: &BigRational) -> BigRational {
    let mut acc = r0();
    for c in p.iter().rev() {
        acc = acc * x + c;
    }
    acc
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

/// Derivative.
fn derivative(p: &[BigRational]) -> Poly {
    if p.len() <= 1 {
        return Vec::new();
    }
    let mut d = Vec::with_capacity(p.len() - 1);
    for (i, c) in p.iter().enumerate().skip(1) {
        d.push(BigRational::from_integer(BigInt::from(i)) * c);
    }
    normalize(d)
}

/// Polynomial remainder `a mod b` over ℚ (b ≠ 0).
fn rem(a: &[BigRational], b: &[BigRational]) -> Poly {
    let mut r = normalize(a.to_vec());
    let bd = degree(b).expect("rem by zero polynomial");
    let lead_b = &b[bd];
    while let Some(rd) = degree(&r) {
        if rd < bd {
            break;
        }
        // coefficient to cancel r's leading term with b
        let factor = &r[rd] / lead_b;
        let shift = rd - bd;
        // r -= factor * x^shift * b
        for (i, bc) in b.iter().enumerate() {
            r[shift + i] -= &factor * bc;
        }
        r = normalize(r);
    }
    r
}

/// The Sturm chain of `p`: `p₀ = p`, `p₁ = p'`, `pᵢ₊₁ = −rem(pᵢ₋₁, pᵢ)`, until 0.
/// Counts **distinct** real roots regardless of multiplicity.
fn sturm_chain(p: &[BigRational]) -> Vec<Poly> {
    let p = normalize(p.to_vec());
    if degree(&p).unwrap_or(0) == 0 {
        return vec![p]; // constant (or zero): no sign changes contribute roots
    }
    let mut chain = vec![p.clone(), derivative(&p)];
    while let Some(last) = chain.last() {
        if degree(last).is_none() {
            chain.pop(); // drop the trailing zero
            break;
        }
        let n = chain.len();
        let nxt = rem(&chain[n - 2], &chain[n - 1]);
        if degree(&nxt).is_none() {
            break;
        }
        let neg: Poly = nxt.iter().map(|c| -c).collect();
        chain.push(neg);
    }
    chain
}

/// Number of sign changes of the chain evaluated at `x` (zeros skipped).
fn sign_changes_at(chain: &[Poly], x: &BigRational) -> usize {
    count_changes(chain.iter().map(|p| sign_of(&eval(p, x))))
}

/// Number of sign changes of the chain's leading behaviour at ±∞.
/// At `+∞` the sign of each poly is the sign of its leading coefficient; at
/// `−∞` it is that times `(−1)^deg`.
fn sign_changes_at_inf(chain: &[Poly], pos: bool) -> usize {
    count_changes(chain.iter().map(|p| match degree(p) {
        None => 0,
        Some(d) => {
            let s = sign_of(&p[d]);
            if pos || d % 2 == 0 { s } else { -s }
        }
    }))
}

fn count_changes(signs: impl Iterator<Item = i32>) -> usize {
    let mut prev = 0i32;
    let mut changes = 0;
    for s in signs {
        if s == 0 {
            continue;
        }
        if prev != 0 && s != prev {
            changes += 1;
        }
        prev = s;
    }
    changes
}

/// Count distinct real roots in the OPEN interval `(a, b)` — valid only when
/// neither `a` nor `b` is itself a root (Sturm's `V(a) − V(b)`). All callers
/// maintain that invariant (endpoints are kept off the roots).
fn count_open(chain: &[Poly], a: &BigRational, b: &BigRational) -> usize {
    sign_changes_at(chain, a).saturating_sub(sign_changes_at(chain, b))
}

/// Count all distinct real roots.
fn count_total(chain: &[Poly]) -> usize {
    sign_changes_at_inf(chain, false).saturating_sub(sign_changes_at_inf(chain, true))
}

/// A Cauchy bound `B` such that every real root lies in `(−B, B)`.
fn root_bound(p: &[BigRational]) -> BigRational {
    let d = match degree(p) {
        Some(d) if d >= 1 => d,
        _ => return BigRational::one(),
    };
    let lead = p[d].abs();
    let mut m = r0();
    for c in &p[..d] {
        let v = c.abs() / &lead;
        if v > m {
            m = v;
        }
    }
    m + BigRational::one()
}

/// Isolate every distinct real root of `p` into a disjoint **open** interval
/// `(lo, hi)` — with `lo` and `hi` guaranteed **not** to be roots of `p`, so the
/// Sturm count `V(lo) − V(hi)` is exact. The root-free-endpoint invariant is the
/// fix for the classic Sturm bug where a bisection midpoint lands exactly on a
/// (rational) root and the half-open count miscounts/loops. Returns the
/// intervals sorted by `lo`.
fn isolate(p: &[BigRational]) -> Vec<(BigRational, BigRational)> {
    let chain = sturm_chain(p);
    if count_total(&chain) == 0 {
        return Vec::new();
    }
    let b = root_bound(p); // ±b strictly bound all roots ⇒ non-roots
    let mut out = Vec::new();
    let mut stack = vec![(-b.clone(), b)];
    let mut guard = 0u32;
    while let Some((lo, hi)) = stack.pop() {
        guard += 1;
        if guard > 200_000 {
            break; // defensive: never spin (only costs completeness)
        }
        match count_open(&chain, &lo, &hi) {
            0 => continue,
            1 => out.push((lo, hi)),
            _ => {
                let mid = root_free_point(p, &lo, &hi);
                stack.push((lo, mid.clone()));
                stack.push((mid, hi));
            }
        }
    }
    out.sort_by(|a, b| a.0.cmp(&b.0));
    out
}

/// A bound `B > 0` such that every real root of `p` lies strictly inside
/// `(−B, B)` (Cauchy's bound). Used by the NIA tier to bound the integer search:
/// beyond `±B` the sign is constant, so the feasible set's structure is settled.
#[must_use]
pub fn cauchy_bound(p: &[BigRational]) -> BigRational {
    root_bound(&normalize(p.to_vec()))
}

/// If **every** real root of the univariate polynomial `p` (coeffs low-first)
/// is rational, return them sorted-distinct; otherwise `None` (an irrational
/// real root exists). Used by CDCAC to decide whether the projection's
/// breakpoints partition the axis at rational points (the case it handles
/// exactly) vs. algebraic points (deferred). A constant/zero polynomial has no
/// roots → `Some(empty)`.
#[must_use]
pub fn real_roots_rational(p: &[BigRational]) -> Option<Vec<BigRational>> {
    let p = normalize(p.to_vec());
    match degree(&p) {
        None | Some(0) => return Some(Vec::new()),
        _ => {}
    }
    let n_real = count_total(&sturm_chain(&p));
    let mut rats: Vec<BigRational> = rational_root_candidates(&p)
        .into_iter()
        .filter(|c| eval(&p, c).is_zero())
        .collect();
    rats.sort();
    rats.dedup();
    if rats.len() == n_real { Some(rats) } else { None }
}

/// One **rational** sample strictly inside each open interval of `ℝ ∖ {real
/// roots of p}` — below the least root, in each gap between consecutive roots,
/// and above the greatest. Works for *irrational* roots: it samples the gaps
/// between the (rational-endpoint) isolating intervals, so no algebraic
/// arithmetic is needed. A root-free `p` yields `[0]`.
#[must_use]
pub fn cell_sample_points(p: &[BigRational]) -> Vec<BigRational> {
    let iv = isolate(p); // sorted, disjoint, root-free endpoints
    if iv.is_empty() {
        return vec![r0()];
    }
    let one = BigRational::one();
    let two = BigRational::from_integer(BigInt::from(2));
    let mut pts = Vec::with_capacity(iv.len() + 1);
    pts.push(&iv[0].0 - &one); // below the least root
    for w in iv.windows(2) {
        // a rational in the gap [hi_i, lo_{i+1}] lies in the open cell between
        // the two roots (the endpoints are non-roots, the gap is root-free)
        pts.push((&w[0].1 + &w[1].0) / &two);
    }
    pts.push(&iv[iv.len() - 1].1 + &one); // above the greatest root
    pts
}

/// A rational point strictly inside `(lo, hi)` that is **not** a root of `p`.
/// Tries the midpoint, then a spread of off-centre fractions; since `p` has
/// finitely many roots, one is always non-root.
fn root_free_point(p: &[BigRational], lo: &BigRational, hi: &BigRational) -> BigRational {
    let w = hi - lo;
    let two = BigRational::from_integer(BigInt::from(2));
    let mid = lo + &w / &two;
    if !eval(p, &mid).is_zero() {
        return mid;
    }
    for (n, d) in [(1i64, 3i64), (2, 3), (1, 4), (3, 4), (1, 5), (2, 5), (3, 5), (4, 5), (3, 7), (5, 11)] {
        let cand = lo + &w * BigRational::new(BigInt::from(n), BigInt::from(d));
        if !eval(p, &cand).is_zero() {
            return cand;
        }
    }
    mid // unreachable in practice
}

/// An exact **real algebraic number**: the unique real root of `defining` in the
/// open interval `(lo, hi)`, with `lo`/`hi` non-roots of `defining`. Built
/// in-house (not `oxiz_math::AlgebraicNumber`) so the exact sign computation
/// rests only on our own Sturm machinery — see [`AlgebraicReal::sign_of`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AlgebraicReal {
    pub defining: Vec<BigRational>,
    pub lo: BigRational,
    pub hi: BigRational,
}

impl AlgebraicReal {
    /// Order this algebraic number `α` against a rational `q` (exact): the sign of
    /// `α − q`, i.e. the sign of the linear polynomial `x − q` at `α`.
    #[must_use]
    pub fn cmp_rational(&self, q: &BigRational) -> core::cmp::Ordering {
        use core::cmp::Ordering;
        match self.sign_of(&[-q.clone(), BigRational::one()]) {
            s if s < 0 => Ordering::Less,
            s if s > 0 => Ordering::Greater,
            _ => Ordering::Equal,
        }
    }

    /// Exact sign of the univariate polynomial `q` (low-degree-first) evaluated
    /// at this algebraic number `α`. Sound — no floating point.
    ///
    /// `q(α) = 0` iff `α` is a common root of `q` and `defining`, detected by
    /// `gcd(q, defining)` having a root in `(lo, hi)` (its only possible root
    /// there is `α`, since it divides `defining`). Otherwise `q(α) ≠ 0`, so the
    /// isolating interval is refined (keeping `α` isolated via `defining`'s
    /// Sturm) until `q` is root-free on it, and the sign at any interior point is
    /// `q(α)`'s sign.
    #[must_use]
    pub fn sign_of(&self, q: &[BigRational]) -> i32 {
        let q = normalize(q.to_vec());
        match degree(&q) {
            None => return 0,                       // zero polynomial
            Some(0) => return sign_of(&q[0]),       // constant
            _ => {}
        }
        // q(α) = 0 ?
        let g = poly_gcd(&q, &self.defining);
        if degree(&g).unwrap_or(0) >= 1 {
            let gchain = sturm_chain(&g);
            if count_open(&gchain, &self.lo, &self.hi) >= 1 {
                return 0;
            }
        }
        // q(α) ≠ 0: refine until q is sign-constant on the α-isolating interval.
        let dchain = sturm_chain(&self.defining);
        let qchain = sturm_chain(&q);
        let (mut lo, mut hi) = (self.lo.clone(), self.hi.clone());
        let two = BigRational::from_integer(BigInt::from(2));
        for _ in 0..2000 {
            if count_open(&qchain, &lo, &hi) == 0 {
                let mid = (&lo + &hi) / &two;
                return sign_of(&eval(&q, &mid));
            }
            // bisect, keeping the half that still contains α (per `defining`)
            let mid = root_free_point(&self.defining, &lo, &hi);
            if count_open(&dchain, &lo, &mid) == 1 {
                hi = mid;
            } else {
                lo = mid;
            }
        }
        // refinement budget hit (should not happen); conservative 0 would be
        // unsound, so signal via the interval midpoint sign (q is tiny here).
        let mid = (&lo + &hi) / &two;
        sign_of(&eval(&q, &mid))
    }
}

/// A distinct real root: an exact rational, or an in-house algebraic number.
/// Used by the CAC engine to delineate an axis into cells at exact boundary
/// points and to sample *at* a boundary (a section cell) exactly.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RealRoot {
    Rational(BigRational),
    Algebraic(AlgebraicReal),
}

impl RealRoot {
    /// Order this root against a rational `q` (exact). For an algebraic root `α`
    /// this is the sign of `α − q`, computed exactly via [`AlgebraicReal::sign_of`]
    /// on the linear polynomial `x − q`.
    #[must_use]
    pub fn cmp_rational(&self, q: &BigRational) -> core::cmp::Ordering {
        use core::cmp::Ordering;
        match self {
            RealRoot::Rational(r) => r.cmp(q),
            RealRoot::Algebraic(a) => match a.sign_of(&[-q.clone(), BigRational::one()]) {
                s if s < 0 => Ordering::Less,
                s if s > 0 => Ordering::Greater,
                _ => Ordering::Equal,
            },
        }
    }

    /// Exact total order on real roots — including two algebraic roots of
    /// *different* defining polynomials (the comparison a model-driven covering
    /// needs, and the reason it can avoid forming the boundary-polynomial
    /// product). Rational/algebraic mixes reduce to [`AlgebraicReal::cmp_rational`].
    /// Two algebraic roots are compared by refining their isolating intervals
    /// until disjoint (then ordered by position); equality is detected exactly via
    /// `gcd` of the defining polynomials (a shared root in the overlap).
    ///
    /// (An inherent method, not `Ord::cmp`: the comparison can refine isolating
    /// intervals, so it is not the cheap structural compare a trait impl implies.)
    #[must_use]
    #[allow(clippy::should_implement_trait)]
    pub fn cmp(&self, other: &RealRoot) -> core::cmp::Ordering {
        match (self, other) {
            (RealRoot::Rational(a), RealRoot::Rational(b)) => a.cmp(b),
            (RealRoot::Rational(a), RealRoot::Algebraic(b)) => b.cmp_rational(a).reverse(),
            (RealRoot::Algebraic(a), RealRoot::Rational(b)) => a.cmp_rational(b),
            (RealRoot::Algebraic(a), RealRoot::Algebraic(b)) => compare_algebraic(a, b),
        }
    }

    /// A rational strictly below this root: `r − 1` for a rational root, the
    /// isolating-interval lower bound `lo` (a non-root, `< α`) for an algebraic.
    #[must_use]
    pub fn rational_below(&self) -> BigRational {
        match self {
            RealRoot::Rational(r) => r - BigRational::one(),
            RealRoot::Algebraic(a) => a.lo.clone(),
        }
    }

    /// A rational strictly above this root (dual of [`Self::rational_below`]).
    #[must_use]
    pub fn rational_above(&self) -> BigRational {
        match self {
            RealRoot::Rational(r) => r + BigRational::one(),
            RealRoot::Algebraic(a) => a.hi.clone(),
        }
    }
}

/// All distinct real roots of `p` (low-degree-first), **sorted ascending**, each
/// classified as exactly rational or algebraic (irrational). The two classes are
/// distinguished by testing each isolating interval against the exact rational
/// roots (rational-root theorem filtered by `eval == 0`); an isolating interval
/// with no rational root inside contains an irrational algebraic root.
#[must_use]
pub fn real_roots(p: &[BigRational]) -> Vec<RealRoot> {
    let p = normalize(p.to_vec());
    match degree(&p) {
        None | Some(0) => return Vec::new(),
        _ => {}
    }
    let rats: Vec<BigRational> = rational_root_candidates(&p)
        .into_iter()
        .filter(|c| eval(&p, c).is_zero())
        .collect();
    isolate(&p) // sorted by `lo`, disjoint, each holding exactly one root
        .into_iter()
        .map(|(lo, hi)| match rats.iter().find(|r| lo < **r && **r < hi) {
            Some(r) => RealRoot::Rational(r.clone()),
            None => RealRoot::Algebraic(AlgebraicReal { defining: p.clone(), lo, hi }),
        })
        .collect()
}

/// Exact comparison of two algebraic reals, possibly roots of different defining
/// polynomials. Equality is decided exactly: `α = β` iff `α` is a root of `β`'s
/// defining polynomial *and* lies in `β`'s isolating interval. When unequal,
/// `β`'s isolating interval is refined (keeping `β`'s root) until `α` falls
/// strictly outside it, then the side decides the order. Uses only exact
/// rational Sturm reasoning via [`AlgebraicReal::cmp_rational`]/`sign_of`.
fn compare_algebraic(a: &AlgebraicReal, b: &AlgebraicReal) -> core::cmp::Ordering {
    use core::cmp::Ordering;
    // Equality (exact): α is a root of β's defining poly, inside β's interval.
    if a.sign_of(&b.defining) == 0
        && a.cmp_rational(&b.lo) == Ordering::Greater
        && a.cmp_rational(&b.hi) == Ordering::Less
    {
        return Ordering::Equal;
    }
    // α ≠ β: shrink β's isolating interval around β until α is on one side.
    let bchain = sturm_chain(&b.defining);
    let (mut blo, mut bhi) = (b.lo.clone(), b.hi.clone());
    for _ in 0..2000 {
        if a.cmp_rational(&bhi) != Ordering::Less {
            return Ordering::Greater; // α ≥ bhi > β
        }
        if a.cmp_rational(&blo) != Ordering::Greater {
            return Ordering::Less; // α ≤ blo < β
        }
        let mid = root_free_point(&b.defining, &blo, &bhi);
        if count_open(&bchain, &blo, &mid) == 1 {
            bhi = mid;
        } else {
            blo = mid;
        }
    }
    // refinement budget exhausted (α extremely close to β but proven ≠): the
    // tightened interval midpoint decides; conservative and effectively unreached.
    let two = BigRational::from_integer(BigInt::from(2));
    a.cmp_rational(&((&blo + &bhi) / &two))
}

/// A rational strictly between two distinct real roots `a < b` (the caller
/// guarantees `a < b`). Algebraic isolating intervals are refined via Sturm
/// until a separating rational is exposed. Used to pick a sector sample point
/// strictly inside an open cell of the CAC decomposition.
#[must_use]
pub fn rational_between(a: &RealRoot, b: &RealRoot) -> BigRational {
    let two = BigRational::from_integer(BigInt::from(2));
    match (a, b) {
        (RealRoot::Rational(x), RealRoot::Rational(y)) => (x + y) / &two,
        (RealRoot::Rational(x), RealRoot::Algebraic(beta)) => {
            let lo = refine_lo_above(beta, x);
            (x + &lo) / &two
        }
        (RealRoot::Algebraic(alpha), RealRoot::Rational(y)) => {
            let hi = refine_hi_below(alpha, y);
            (&hi + y) / &two
        }
        (RealRoot::Algebraic(alpha), RealRoot::Algebraic(beta)) => {
            let (mut a_lo, mut a_hi) = (alpha.lo.clone(), alpha.hi.clone());
            let (mut b_lo, mut b_hi) = (beta.lo.clone(), beta.hi.clone());
            let achain = sturm_chain(&alpha.defining);
            let bchain = sturm_chain(&beta.defining);
            for _ in 0..4000 {
                if a_hi < b_lo {
                    return (&a_hi + &b_lo) / &two;
                }
                if (&a_hi - &a_lo) >= (&b_hi - &b_lo) {
                    let mid = root_free_point(&alpha.defining, &a_lo, &a_hi);
                    if count_open(&achain, &a_lo, &mid) == 1 {
                        a_hi = mid;
                    } else {
                        a_lo = mid;
                    }
                } else {
                    let mid = root_free_point(&beta.defining, &b_lo, &b_hi);
                    if count_open(&bchain, &b_lo, &mid) == 1 {
                        b_hi = mid;
                    } else {
                        b_lo = mid;
                    }
                }
            }
            (&a_hi + &b_lo) / &two
        }
    }
}

/// Refine `β`'s isolating interval upward until its lower bound exceeds `x` (with
/// `x < β` guaranteed), returning that lower bound.
fn refine_lo_above(beta: &AlgebraicReal, x: &BigRational) -> BigRational {
    let chain = sturm_chain(&beta.defining);
    let (mut lo, mut hi) = (beta.lo.clone(), beta.hi.clone());
    for _ in 0..4000 {
        if &lo > x {
            return lo;
        }
        let mid = root_free_point(&beta.defining, &lo, &hi);
        if count_open(&chain, &lo, &mid) == 1 {
            hi = mid;
        } else {
            lo = mid;
        }
    }
    lo
}

/// Dual of [`refine_lo_above`]: refine `α` downward until its upper bound drops
/// below `y` (with `α < y` guaranteed).
fn refine_hi_below(alpha: &AlgebraicReal, y: &BigRational) -> BigRational {
    let chain = sturm_chain(&alpha.defining);
    let (mut lo, mut hi) = (alpha.lo.clone(), alpha.hi.clone());
    for _ in 0..4000 {
        if &hi < y {
            return hi;
        }
        let mid = root_free_point(&alpha.defining, &lo, &hi);
        if count_open(&chain, &lo, &mid) == 1 {
            hi = mid;
        } else {
            lo = mid;
        }
    }
    hi
}

/// Monic-free polynomial GCD over ℚ (Euclidean), low-degree-first.
fn poly_gcd(a: &[BigRational], b: &[BigRational]) -> Vec<BigRational> {
    let mut a = normalize(a.to_vec());
    let mut b = normalize(b.to_vec());
    while degree(&b).is_some() {
        let r = rem(&a, &b);
        a = b;
        b = r;
    }
    a
}

/// The verdict of the exact univariate decision procedure.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum UniResult {
    /// No real `x` satisfies the conjunction.
    Unsat,
    /// Satisfiable, with a concrete **rational** witness.
    Sat(BigRational),
    /// Satisfiable, with an exact **algebraic** (irrational) witness.
    SatAlgebraic(AlgebraicReal),
}

/// Decide a conjunction of univariate atoms `pᵢ(x) ⋈ᵢ 0` exactly over ℝ.
///
/// Each atom is `(coeffs_low_first, op)`. Always returns a definite result
/// (univariate real arithmetic is decidable). Sound by construction — uses only
/// exact rational Sturm reasoning.
pub fn decide(atoms: &[(Poly, AtomCmp)]) -> UniResult {
    // Constant atoms decide immediately.
    let mut nonconst: Vec<&(Poly, AtomCmp)> = Vec::new();
    for a in atoms {
        match degree(&a.0) {
            None => {
                // zero polynomial: 0 ⋈ 0
                if !a.1.holds_for_sign(0) {
                    return UniResult::Unsat;
                }
            }
            Some(0) => {
                if !a.1.holds_for_sign(sign_of(&a.0[0])) {
                    return UniResult::Unsat;
                }
            }
            Some(_) => nonconst.push(a),
        }
    }
    if nonconst.is_empty() {
        return UniResult::Sat(r0()); // only satisfied constants ⇒ any x works
    }

    // Breakpoints: the real roots of the product of all non-constant atoms,
    // isolated into disjoint OPEN intervals with root-free endpoints. Each open
    // cell between/outside the roots is sign-invariant for every atom, and each
    // isolating endpoint lies in an adjacent cell (a ready-made sample).
    let mut product: Poly = vec![BigRational::one()];
    for a in &nonconst {
        product = poly_mul(&product, &a.0);
    }
    let roots = isolate(&product);

    // Per-atom Sturm chains, for exact "does this atom vanish at the root in I?".
    let chains: Vec<Vec<Poly>> = nonconst.iter().map(|a| sturm_chain(&a.0)).collect();
    let holds_at = |x: &BigRational| nonconst.iter().all(|a| a.1.holds_for_sign(sign_of(&eval(&a.0, x))));

    // 1) Test one sample per open cell. Each isolating interval `(loᵢ, hiᵢ)`
    //    has root-free endpoints lying in adjacent cells: `loₒ` is in the cell
    //    left of the first root, every `hiᵢ` is in the cell right of root i.
    if roots.is_empty() {
        // no roots ⇒ all atoms have constant sign; one representative suffices.
        return if holds_at(&r0()) { UniResult::Sat(r0()) } else { UniResult::Unsat };
    }
    let mut samples: Vec<&BigRational> = vec![&roots[0].0];
    samples.extend(roots.iter().map(|(_, hi)| hi));
    for x in samples {
        if holds_at(x) {
            return UniResult::Sat(x.clone());
        }
    }

    // 2) Test each root ρ ∈ (lo, hi). Atom A's sign at ρ is 0 if A vanishes in
    //    (lo, hi) (A has its own root there), else the constant sign A carries
    //    across the cell — read at the root-free endpoint `lo`. If ρ is rational,
    //    witness it; otherwise capture it as an exact algebraic witness.
    let mut algebraic: Option<AlgebraicReal> = None;
    for (lo, hi) in &roots {
        let all = nonconst.iter().enumerate().all(|(i, a)| {
            let s = if count_open(&chains[i], lo, hi) >= 1 {
                0
            } else {
                sign_of(&eval(&a.0, lo))
            };
            a.1.holds_for_sign(s)
        });
        if all {
            if let Some(rat) = rational_root_in(&product, lo, hi) {
                return UniResult::Sat(rat);
            }
            if algebraic.is_none() {
                algebraic = Some(AlgebraicReal {
                    defining: product.clone(),
                    lo: lo.clone(),
                    hi: hi.clone(),
                });
            }
        }
    }

    match algebraic {
        Some(a) => UniResult::SatAlgebraic(a),
        None => UniResult::Unsat,
    }
}

/// Multiply two polynomials (low-degree-first).
fn poly_mul(a: &[BigRational], b: &[BigRational]) -> Poly {
    if a.is_empty() || b.is_empty() {
        return Vec::new();
    }
    let mut out = vec![r0(); a.len() + b.len() - 1];
    for (i, ca) in a.iter().enumerate() {
        if ca.is_zero() {
            continue;
        }
        for (j, cb) in b.iter().enumerate() {
            out[i + j] += ca * cb;
        }
    }
    normalize(out)
}

/// If the single root of `p` in the OPEN interval `(lo, hi)` is rational, return
/// it. Probes the rational-root-theorem candidates of `p` that fall inside.
fn rational_root_in(p: &[BigRational], lo: &BigRational, hi: &BigRational) -> Option<BigRational> {
    rational_root_candidates(p)
        .into_iter()
        .find(|cand| cand > lo && cand < hi && eval(p, cand).is_zero())
}

/// Rational-root-theorem candidates of `p` (low-degree-first): clear
/// denominators to an integer polynomial, then `± p_div / q_div` for `p_div |
/// a₀`, `q_div | aₙ`. Divisor search is capped (a missed large divisor only
/// costs completeness — the root is then reported irrational, never unsound).
fn rational_root_candidates(p: &[BigRational]) -> Vec<BigRational> {
    let d = match degree(p) {
        Some(d) if d >= 1 => d,
        _ => return Vec::new(),
    };
    // If `x` divides `p` (low-degree zero coefficients), `0` is a root; strip
    // that `xᵐ` factor and apply the rational-root theorem to the cofactor,
    // whose constant term is the first nonzero coefficient `p[m]`. (Without this
    // the theorem only ever yields `0` when `a₀ = 0` and misses the nonzero
    // rational roots — the false-unsat the differential caught on `−x³−3x²=0`.)
    let m = p.iter().position(|c| !c.is_zero()).expect("nonzero poly has a nonzero coeff");

    // The denominator-clearing scale L = lcm(all denominators) makes the whole
    // polynomial integer, but only the (shifted) constant and leading terms of
    // that integer polynomial are needed — so materialise just `a₀` and `aₙ`,
    // not the full coefficient vector.
    let mut lcm = BigInt::one();
    for c in p {
        lcm = lcm_bigint(&lcm, c.denom());
    }
    let a0 = p[m].numer() * (&lcm / p[m].denom());
    let an = p[d].numer() * (&lcm / p[d].denom());
    let (a0, an) = (&a0, &an);
    if an.is_zero() {
        return Vec::new();
    }
    let mut out = Vec::new();
    if m > 0 {
        out.push(r0()); // x = 0 is a root of p
    }
    for pd in divisors(a0) {
        for qd in divisors(an) {
            if qd.is_zero() {
                continue;
            }
            for sgn in [BigInt::one(), -BigInt::one()] {
                let cand = BigRational::new(&sgn * &pd, qd.clone());
                if !out.contains(&cand) {
                    out.push(cand);
                }
            }
        }
    }
    out
}

fn divisors(n: &BigInt) -> Vec<BigInt> {
    let m = n.magnitude();
    if m.bits() == 0 {
        return vec![BigInt::one()]; // n == 0
    }
    let n_abs = BigInt::from(m.clone());
    let cap = BigInt::from(4096);
    let mut out = Vec::new();
    let mut dd = BigInt::one();
    while dd <= n_abs && dd <= cap {
        if (&n_abs % &dd).is_zero() {
            out.push(dd.clone());
        }
        dd += BigInt::one();
    }
    out
}

fn lcm_bigint(a: &BigInt, b: &BigInt) -> BigInt {
    if a.is_zero() || b.is_zero() {
        return BigInt::one();
    }
    let g = gcd_bigint(a, b);
    BigInt::from((a / &g * b).magnitude().clone())
}

fn gcd_bigint(a: &BigInt, b: &BigInt) -> BigInt {
    let mut a = BigInt::from(a.magnitude().clone());
    let mut b = BigInt::from(b.magnitude().clone());
    while !b.is_zero() {
        let t = b.clone();
        b = &a % &b;
        a = t;
    }
    a
}

#[cfg(test)]
mod tests {
    use super::*;

    fn p(coeffs: &[i64]) -> Poly {
        normalize(coeffs.iter().map(|&c| BigRational::from_integer(BigInt::from(c))).collect())
    }

    #[test]
    fn sturm_counts_distinct_real_roots() {
        // negative leading coeff (the cad::SturmSequence bug case): -5x⁴+1 → 2
        assert_eq!(count_total(&sturm_chain(&p(&[1, 0, 0, 0, -5]))), 2);
        // x⁴+1 → 0
        assert_eq!(count_total(&sturm_chain(&p(&[1, 0, 0, 0, 1]))), 0);
        // x²-2 → 2 (irrational)
        assert_eq!(count_total(&sturm_chain(&p(&[-2, 0, 1]))), 2);
        // x² (double root) → 1 distinct
        assert_eq!(count_total(&sturm_chain(&p(&[0, 0, 1]))), 1);
        // x³-x = x(x-1)(x+1) → 3
        assert_eq!(count_total(&sturm_chain(&p(&[0, -1, 0, 1]))), 3);
        // x⁴+x²+1 → 0 (no real roots)
        assert_eq!(count_total(&sturm_chain(&p(&[1, 0, 1, 0, 1]))), 0);
    }

    fn d(atoms: &[(&[i64], AtomCmp)]) -> UniResult {
        let v: Vec<(Poly, AtomCmp)> = atoms.iter().map(|(c, op)| (p(c), *op)).collect();
        decide(&v)
    }

    #[test]
    fn decides_no_real_root_unsat() {
        // x⁴ + 1 < 0  → unsat (constant positive)
        assert_eq!(d(&[(&[1, 0, 0, 0, 1], AtomCmp::Lt)]), UniResult::Unsat);
        // x² + 1 = 0 → unsat
        assert_eq!(d(&[(&[1, 0, 1], AtomCmp::Eq)]), UniResult::Unsat);
    }

    #[test]
    fn decides_definite_unsat() {
        // x² < 0 → unsat
        assert_eq!(d(&[(&[0, 0, 1], AtomCmp::Lt)]), UniResult::Unsat);
        // -x⁴ ≥ ... actually -x⁴ > 0 → unsat
        assert_eq!(d(&[(&[0, 0, 0, 0, -1], AtomCmp::Gt)]), UniResult::Unsat);
    }

    #[test]
    fn decides_rational_sat() {
        // 3x² - 5 < 0 → sat at x=0
        assert!(matches!(d(&[(&[-5, 0, 3], AtomCmp::Lt)]), UniResult::Sat(_)));
        // x⁴ - 4 > 0 → sat at x=2
        assert!(matches!(d(&[(&[-4, 0, 0, 0, 1], AtomCmp::Gt)]), UniResult::Sat(_)));
    }

    #[test]
    fn decides_irrational_only_sat() {
        // x² = 2 → sat only at ±√2 (irrational) → an exact algebraic witness
        let v = d(&[(&[-2, 0, 1], AtomCmp::Eq)]);
        match v {
            UniResult::SatAlgebraic(a) => {
                // the witness must actually satisfy x² - 2 = 0
                assert_eq!(a.sign_of(&p(&[-2, 0, 1])), 0);
            }
            other => panic!("expected SatAlgebraic, got {other:?}"),
        }
    }

    #[test]
    fn sign_at_algebraic_is_exact() {
        // α = √2 as the root of x²-2 in (1, 2)
        let a = AlgebraicReal { defining: p(&[-2, 0, 1]), lo: r(1), hi: r(2) };
        assert_eq!(a.sign_of(&p(&[-2, 0, 1])), 0); // α² - 2 = 0
        assert_eq!(a.sign_of(&p(&[-1, 0, 1])), 1); // α² - 1 = 1 > 0
        assert_eq!(a.sign_of(&p(&[-3, 0, 1])), -1); // α² - 3 = -1 < 0
        assert_eq!(a.sign_of(&p(&[0, 1])), 1); // α > 0
        assert_eq!(a.sign_of(&p(&[-2, 1])), -1); // α - 2 < 0  (√2 ≈ 1.41)
    }

    fn r(n: i64) -> BigRational {
        BigRational::from_integer(BigInt::from(n))
    }

    #[test]
    fn finds_nonzero_rational_root_when_constant_is_zero() {
        // -x³-3x² = 0 ∧ -2x²-x+5 < 0  → sat at x = -3 (a rational root, even
        // though the product's constant term is 0). Regression for the
        // rational-root-theorem a₀=0 false-unsat.
        let v = d(&[
            (&[0, 0, -3, -1], AtomCmp::Eq), // -x³ - 3x²
            (&[5, -1, -2], AtomCmp::Lt),    // -2x² - x + 5
        ]);
        assert_eq!(v, UniResult::Sat(BigRational::from_integer(BigInt::from(-3))));
    }

    #[test]
    fn decides_conjunction_unsat() {
        // x ≥ 2 ∧ x ≤ 1 → unsat
        assert_eq!(
            d(&[(&[-2, 1], AtomCmp::Ge), (&[-1, 1], AtomCmp::Le)]),
            UniResult::Unsat
        );
        // x² < 1 ∧ x > 2  → unsat
        assert_eq!(
            d(&[(&[-1, 0, 1], AtomCmp::Lt), (&[-2, 1], AtomCmp::Gt)]),
            UniResult::Unsat
        );
    }

    #[test]
    fn decides_quartic_sat_rational() {
        // 2x⁴ - 2x² < 0  is sat on (-1,0)∪(0,1) — a rational witness exists.
        assert!(matches!(d(&[(&[0, 0, -2, 0, 2], AtomCmp::Lt)]), UniResult::Sat(_)));
    }
}
