//! A small symbolic-calculus engine and a LEVELED monotonicity knowledge base.
//!
//! Monotonicity is decided by the **first-derivative sign test**: on a CONNECTED
//! interval, `f' ≥ 0 ⇒ f` non-decreasing and `f' ≤ 0 ⇒ f` non-increasing (mean
//! value theorem). The engine therefore (1) differentiates an expression
//! symbolically, then (2) determines the sign of the derivative over the
//! function's domain. Every rule used is a theorem, so a derived monotonicity is
//! sound.
//!
//! The KB is **leveled**, not monolithic (lookups walk levels, newest first):
//!
//! * **Level 0** — *primitive* facts that cannot be derived: the derivative
//!   rules ([`diff`]), the primitive sign facts ([`Expr::sign_on`] — e.g. a
//!   positive-base exponential is always positive, `ln`'s domain is `x > 0`),
//!   and the catalogue of primitive functions ([`level0_primitives`]).
//! * **Level 1+** — facts DERIVED from lower levels and VERIFIED by the
//!   first-derivative test ([`Kb::derive_next_level`]). The first thing the
//!   engine does is run that test on the level-0 primitives themselves, so the
//!   KB is self-consistent before it is ever consulted for a composite.
//!
//! This is the calculus core behind the monotonicity recognizers in
//! `clean_mbqi`; transcendental symbols (`exp`/`ln`/`sin`/`cos`/`tan`) are not
//! OxiZ theory symbols, so they live here as KB-described uninterpreted
//! functions and only reach the solver through their certified attributes.

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};
use std::collections::HashMap;

fn rat(n: i64) -> BigRational {
    BigRational::from_integer(BigInt::from(n))
}

/// A calculus expression in a single variable `x`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Expr {
    /// The variable.
    X,
    /// A rational constant.
    Const(BigRational),
    /// Sum.
    Add(Vec<Expr>),
    /// Product.
    Mul(Vec<Expr>),
    /// Negation.
    Neg(Box<Expr>),
    /// `base ^ k` for a CONSTANT rational exponent `k` (`d(b^k) = k·b^{k-1}·b'`).
    Pow(Box<Expr>, BigRational),
    /// `a ^ inner` for a CONSTANT positive base `a` (`d(a^g)=a^g·ln a·g'`).
    ExpBase(BigRational, Box<Expr>),
    /// Natural log (`d ln g = g'/g`); domain `g > 0`.
    Ln(Box<Expr>),
    /// `sin g` (`d sin g = cos g · g'`).
    Sin(Box<Expr>),
    /// `cos g` (`d cos g = −sin g · g'`).
    Cos(Box<Expr>),
    /// `tan g` (`d tan g = (1 + tan² g) · g'`).
    Tan(Box<Expr>),
}

use Expr::*;

impl Expr {
    fn c(n: i64) -> Expr {
        Const(rat(n))
    }
    fn mul(a: Expr, b: Expr) -> Expr {
        Mul(vec![a, b])
    }
}

/// The sign of an expression over a domain (a conservative lattice — `Unknown`
/// is always sound).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Sign {
    Pos,
    Neg,
    Zero,
    NonNeg,
    NonPos,
    Unknown,
}

impl Sign {
    fn flip(self) -> Sign {
        match self {
            Sign::Pos => Sign::Neg,
            Sign::Neg => Sign::Pos,
            Sign::NonNeg => Sign::NonPos,
            Sign::NonPos => Sign::NonNeg,
            Sign::Zero => Sign::Zero,
            Sign::Unknown => Sign::Unknown,
        }
    }
    /// Sign of a product of two signs.
    fn mul(self, o: Sign) -> Sign {
        use Sign::*;
        match (self, o) {
            (Zero, _) | (_, Zero) => Zero,
            (Unknown, _) | (_, Unknown) => Unknown,
            (Pos, Pos) | (Neg, Neg) => Pos,
            (Pos, Neg) | (Neg, Pos) => Neg,
            // NonNeg / NonPos absorb the strictness.
            (Pos, NonNeg) | (NonNeg, Pos) | (Neg, NonPos) | (NonPos, Neg) | (NonNeg, NonNeg)
            | (NonPos, NonPos) => NonNeg,
            (Pos, NonPos) | (NonPos, Pos) | (Neg, NonNeg) | (NonNeg, Neg) | (NonNeg, NonPos)
            | (NonPos, NonNeg) => NonPos,
        }
    }
    /// Sign of a sum of two signs (undetermined when the two disagree).
    fn add(self, o: Sign) -> Sign {
        use Sign::*;
        match (self, o) {
            (Zero, x) | (x, Zero) => x,
            (Pos, Pos) | (Pos, NonNeg) | (NonNeg, Pos) => Pos,
            (Neg, Neg) | (Neg, NonPos) | (NonPos, Neg) => Neg,
            (NonNeg, NonNeg) => NonNeg,
            (NonPos, NonPos) => NonPos,
            _ => Unknown,
        }
    }
    fn rational(r: &BigRational) -> Sign {
        if r.is_zero() {
            Sign::Zero
        } else if r.is_positive() {
            Sign::Pos
        } else {
            Sign::Neg
        }
    }
}

/// A connected domain interval (the connectedness is what makes the
/// first-derivative test sound — `1/x` is decreasing on each of `(−∞,0)` and
/// `(0,∞)` but not across `0`). `None` bound = unbounded on that side.
#[derive(Clone, Debug)]
pub struct Domain {
    pub lo: Option<BigRational>,
    pub lo_strict: bool,
    pub hi: Option<BigRational>,
    pub hi_strict: bool,
}

impl Domain {
    pub fn all() -> Domain {
        Domain { lo: None, lo_strict: false, hi: None, hi_strict: false }
    }
    /// `x > 0`.
    pub fn positive() -> Domain {
        Domain { lo: Some(rat(0)), lo_strict: true, hi: None, hi_strict: false }
    }
    /// `x ≥ 0`.
    pub fn non_negative() -> Domain {
        Domain { lo: Some(rat(0)), lo_strict: false, hi: None, hi_strict: false }
    }
    /// `x ≤ 0`.
    pub fn non_positive() -> Domain {
        Domain { lo: None, lo_strict: false, hi: Some(rat(0)), hi_strict: false }
    }
    /// The sign the variable `x` necessarily takes over this domain.
    fn var_sign(&self) -> Sign {
        let zero = rat(0);
        let lo_nonneg = self.lo.as_ref().is_some_and(|l| *l >= zero);
        let lo_pos = self.lo.as_ref().is_some_and(|l| *l > zero || (*l == zero && self.lo_strict));
        let hi_nonpos = self.hi.as_ref().is_some_and(|h| *h <= zero);
        let hi_neg = self.hi.as_ref().is_some_and(|h| *h < zero || (*h == zero && self.hi_strict));
        if lo_pos {
            Sign::Pos
        } else if lo_nonneg {
            Sign::NonNeg
        } else if hi_neg {
            Sign::Neg
        } else if hi_nonpos {
            Sign::NonPos
        } else {
            Sign::Unknown
        }
    }
}

/// Symbolic first derivative — purely mechanical, every arm a theorem.
pub fn diff(e: &Expr) -> Expr {
    match e {
        X => Expr::c(1),
        Const(_) => Expr::c(0),
        Add(xs) => Add(xs.iter().map(diff).collect()),
        Neg(a) => Neg(Box::new(diff(a))),
        Mul(xs) => {
            // Product rule: Σ_i (Π_{j≠i} x_j) · x_i'.
            let mut terms = Vec::new();
            for i in 0..xs.len() {
                let mut factors: Vec<Expr> = Vec::new();
                for (j, xj) in xs.iter().enumerate() {
                    if j != i {
                        factors.push(xj.clone());
                    }
                }
                factors.push(diff(&xs[i]));
                terms.push(Mul(factors));
            }
            Add(terms)
        }
        Pow(b, k) => {
            // d(b^k) = k · b^{k-1} · b'.
            let km1 = k - BigRational::one();
            Mul(vec![Const(k.clone()), Pow(b.clone(), km1), diff(b)])
        }
        ExpBase(a, g) => {
            // d(a^g) = a^g · ln(a) · g'.  ln(a) is a constant — represented as
            // `Ln(Const a)`, whose SIGN the KB knows (a>1 ⇒ +, a<1 ⇒ −).
            Mul(vec![
                ExpBase(a.clone(), g.clone()),
                Ln(Box::new(Const(a.clone()))),
                diff(g),
            ])
        }
        Ln(g) => {
            // d(ln g) = g' / g = g' · g^{-1}.
            Mul(vec![diff(g), Pow(g.clone(), -BigRational::one())])
        }
        Sin(g) => Mul(vec![Cos(g.clone()), diff(g)]),
        Cos(g) => Mul(vec![Neg(Box::new(Sin(g.clone()))), diff(g)]),
        Tan(g) => {
            // d(tan g) = (1 + tan² g) · g'  (= sec² g · g').
            let sec2 = Add(vec![Expr::c(1), Pow(Box::new(Tan(g.clone())), rat(2))]);
            Mul(vec![sec2, diff(g)])
        }
    }
}

impl Expr {
    /// Determine the sign of this expression over `dom` using level-0 primitive
    /// sign facts + structural propagation. Conservative: `Unknown` is sound.
    pub fn sign_on(&self, dom: &Domain) -> Sign {
        match self {
            X => dom.var_sign(),
            Const(c) => Sign::rational(c),
            Neg(a) => a.sign_on(dom).flip(),
            Add(xs) => xs.iter().fold(Sign::Zero, |acc, x| acc.add(x.sign_on(dom))),
            Mul(xs) => xs.iter().fold(Sign::Pos, |acc, x| acc.mul(x.sign_on(dom))),
            // a^g with a > 0 is ALWAYS positive (primitive fact).
            ExpBase(a, _) if a.is_positive() => Sign::Pos,
            ExpBase(..) => Sign::Unknown,
            // `b^k`: positive base ⇒ positive; even integer power ⇒ `≥ 0`; odd
            // integer power PRESERVES the base sign (`b^1 = b`, `1/b` keeps b's
            // sign); a fractional power needs a positive base.
            Pow(b, k) => {
                let bs = b.sign_on(dom);
                if k.is_zero() {
                    Sign::Pos // b^0 = 1
                } else if bs == Sign::Pos {
                    Sign::Pos
                } else if !k.is_integer() {
                    Sign::Unknown // fractional power of a non-positive/unknown base
                } else if (k.numer() % BigInt::from(2)).is_zero() {
                    Sign::NonNeg // even integer power is ≥ 0
                } else {
                    bs // odd integer power preserves the base sign
                }
            }
            // ln g > 0 iff g > 1; the bare primitive only knows `g > 0` (its
            // domain) ⇒ sign Unknown unless `g` is a constant we can compare.
            Ln(g) => match g.as_ref() {
                Const(c) => {
                    if *c > BigRational::one() {
                        Sign::Pos
                    } else if *c == BigRational::one() {
                        Sign::Zero
                    } else if c.is_positive() {
                        Sign::Neg
                    } else {
                        Sign::Unknown // out of domain
                    }
                }
                _ => Sign::Unknown,
            },
            // Oscillating — sign is not constant over any nondegenerate interval.
            Sin(_) | Cos(_) | Tan(_) => Sign::Unknown,
        }
    }

    /// Monotonicity of this expression on `dom`, by the first-derivative sign
    /// test. `Some(Inc/Dec/Const)` is sound; `None` = the test is inconclusive.
    pub fn monotonicity(&self, dom: &Domain) -> Option<MonoDir> {
        match diff(self).sign_on(dom) {
            Sign::Pos | Sign::NonNeg => Some(MonoDir::Inc),
            Sign::Neg | Sign::NonPos => Some(MonoDir::Dec),
            Sign::Zero => Some(MonoDir::Const),
            Sign::Unknown => None,
        }
    }
}

/// Monotonicity direction (mirrors the `clean_mbqi` sign-algebra).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MonoDir {
    Inc,
    Dec,
    Const,
}

/// A primitive (level-0) function in the KB: its symbol, its body as an `Expr`
/// of `x`, its domain, and the monotonicity the level-1 derivation must confirm.
pub struct Primitive {
    pub name: &'static str,
    pub body: Expr,
    pub domain: Domain,
    pub expected: Option<MonoDir>,
}

/// The level-0 catalogue: the primitive functions whose derivative-sign test the
/// engine runs first to self-verify the KB.
pub fn level0_primitives() -> Vec<Primitive> {
    vec![
        Primitive { name: "id", body: X, domain: Domain::all(), expected: Some(MonoDir::Inc) },
        Primitive {
            name: "neg",
            body: Neg(Box::new(X)),
            domain: Domain::all(),
            expected: Some(MonoDir::Dec),
        },
        Primitive {
            name: "affine_2x+1",
            body: Add(vec![Expr::mul(Expr::c(2), X), Expr::c(1)]),
            domain: Domain::all(),
            expected: Some(MonoDir::Inc),
        },
        Primitive {
            // x² is increasing on x ≥ 0 (the derivative 2x ≥ 0 there).
            name: "x^2_on_nonneg",
            body: Pow(Box::new(X), rat(2)),
            domain: Domain::non_negative(),
            expected: Some(MonoDir::Inc),
        },
        Primitive {
            // x² is decreasing on x ≤ 0.
            name: "x^2_on_nonpos",
            body: Pow(Box::new(X), rat(2)),
            domain: Domain::non_positive(),
            expected: Some(MonoDir::Dec),
        },
        Primitive {
            // a^x for a = 2 (>1) is strictly increasing: d = 2^x·ln2 > 0.
            name: "exp_base2",
            body: ExpBase(rat(2), Box::new(X)),
            domain: Domain::all(),
            expected: Some(MonoDir::Inc),
        },
        Primitive {
            // (1/2)^x is decreasing: d = (1/2)^x·ln(1/2) < 0.
            name: "exp_base_half",
            body: ExpBase(BigRational::new(BigInt::one(), BigInt::from(2)), Box::new(X)),
            domain: Domain::all(),
            expected: Some(MonoDir::Dec),
        },
        Primitive {
            // ln x is increasing on its domain x > 0: d = 1/x > 0.
            name: "ln_on_positive",
            body: Ln(Box::new(X)),
            domain: Domain::positive(),
            expected: Some(MonoDir::Inc),
        },
    ]
}

/// A leveled knowledge base of certified monotonicity facts. Level 0 is the
/// primitive catalogue; each `derive_next_level` adds the facts the
/// first-derivative test certifies from the levels below. Lookups walk newest
/// level first (keeps each level small — no monolithic table to scan).
#[derive(Default)]
pub struct Kb {
    levels: Vec<HashMap<String, MonoDir>>,
}

impl Kb {
    /// Build the KB and self-verify: run the first-derivative monotonicity test
    /// on every level-0 primitive, confirm it matches the declared expectation,
    /// and record the certified facts as level 1. Returns the count of
    /// primitives whose derived monotonicity disagreed with the expectation
    /// (must be 0 for a sound KB).
    pub fn build_and_verify() -> (Kb, usize) {
        let mut kb = Kb::default();
        let prims = level0_primitives();
        // Level 0: the declared (axiomatic) facts.
        let mut l0 = HashMap::new();
        for p in &prims {
            if let Some(d) = p.expected {
                l0.insert(p.name.to_string(), d);
            }
        }
        kb.levels.push(l0);
        // Level 1: derive monotonicity by the first-derivative test, count
        // disagreements with the declared expectation.
        let mut l1 = HashMap::new();
        let mut mismatches = 0usize;
        for p in &prims {
            let derived = p.body.monotonicity(&p.domain);
            if let (Some(exp), Some(got)) = (p.expected, derived) {
                if exp != got {
                    mismatches += 1;
                }
            }
            if let Some(got) = derived {
                l1.insert(p.name.to_string(), got);
            }
        }
        kb.levels.push(l1);
        (kb, mismatches)
    }

    /// Look up a function's certified monotonicity, newest level first.
    pub fn monotonicity_of(&self, name: &str) -> Option<MonoDir> {
        self.levels.iter().rev().find_map(|lvl| lvl.get(name).copied())
    }

    pub fn num_levels(&self) -> usize {
        self.levels.len()
    }

    /// Derive the next level: re-run the derivative test (a placeholder for the
    /// compositional derivation that future increments will add — composing
    /// certified lower-level facts). Returns the number of newly certified facts.
    pub fn derive_next_level(&mut self) -> usize {
        // Future increment: derive monotonicity of COMPOSITES of already-certified
        // functions (sum/product/composition) and append as a new level. For now
        // this is a no-op stub keeping the leveled-growth API in place.
        self.levels.push(HashMap::new());
        0
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn kb_self_verifies_with_no_mismatch() {
        let (kb, mismatches) = Kb::build_and_verify();
        assert_eq!(mismatches, 0, "every level-0 primitive's derivative-sign test must match its declared monotonicity");
        assert_eq!(kb.num_levels(), 2);
    }

    #[test]
    fn derivative_sign_test_matches_each_primitive() {
        for p in level0_primitives() {
            let got = p.body.monotonicity(&p.domain);
            assert_eq!(
                got, p.expected,
                "first-derivative test disagreed for `{}`: got {:?}, expected {:?}",
                p.name, got, p.expected
            );
        }
    }

    #[test]
    fn exp_positive_base_is_always_positive() {
        // a^g with a > 0 is positive everywhere — the load-bearing primitive sign
        // fact behind `exp` being strictly monotone.
        let e = ExpBase(rat(2), Box::new(Neg(Box::new(X))));
        assert_eq!(e.sign_on(&Domain::all()), Sign::Pos);
    }

    #[test]
    fn ln_domain_restricted_increasing_only_on_positive() {
        // ln is increasing on x > 0; on all-reals the derivative 1/x has no
        // constant sign (the domain is not connected through 0), so the test is
        // inconclusive — never a wrong direction.
        let ln = Ln(Box::new(X));
        assert_eq!(ln.monotonicity(&Domain::positive()), Some(MonoDir::Inc));
        assert_eq!(ln.monotonicity(&Domain::all()), None);
    }

    #[test]
    fn oscillating_trig_is_not_certified_monotone() {
        // sin/cos have no constant-sign derivative over an unrestricted domain.
        assert_eq!(Sin(Box::new(X)).monotonicity(&Domain::all()), None);
        assert_eq!(Cos(Box::new(X)).monotonicity(&Domain::all()), None);
    }

    #[test]
    fn x_squared_sign_flips_with_domain() {
        let sq = Pow(Box::new(X), rat(2));
        assert_eq!(sq.monotonicity(&Domain::non_negative()), Some(MonoDir::Inc));
        assert_eq!(sq.monotonicity(&Domain::non_positive()), Some(MonoDir::Dec));
        // Across 0 the derivative 2x straddles 0 → inconclusive (sound).
        assert_eq!(sq.monotonicity(&Domain::all()), None);
    }
}
