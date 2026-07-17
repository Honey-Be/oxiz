//! Delta-rational numbers for strict inequalities
//!
//! A delta-rational represents a value of the form `r + k*δ` where:
//! - r is a rational number (the "real" part)
//! - k is a rational number (the "delta" coefficient)
//! - δ is an infinitesimally small positive value
//!
//! This allows exact representation of strict inequalities in LRA:
//! - `x < c` becomes `x <= c - δ` (represented as (c, -1))
//! - `x > c` becomes `x >= c + δ` (represented as (c, 1))

#[allow(unused_imports)]
use crate::prelude::*;
use core::cmp::Ordering;
use core::ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign};
use crate::ArithRat;
use num_traits::{One, Zero};

/// A delta-rational number: represents `real + delta * δ` where δ is infinitesimal
#[derive(Debug, Clone, Copy, Default)]
pub struct DeltaRational {
    /// The real part
    pub real: ArithRat,
    /// The delta coefficient (multiplied by infinitesimal δ)
    pub delta: ArithRat,
}

impl DeltaRational {
    /// Create a new delta-rational from components
    #[must_use]
    pub const fn new(real: ArithRat, delta: ArithRat) -> Self {
        Self { real, delta }
    }

    /// Create from a rational (delta = 0)
    #[must_use]
    pub fn from_rational(r: ArithRat) -> Self {
        Self {
            real: r,
            delta: ArithRat::zero(),
        }
    }

    /// Create zero
    #[must_use]
    pub fn zero() -> Self {
        Self {
            real: ArithRat::zero(),
            delta: ArithRat::zero(),
        }
    }

    /// Create a positive infinitesimal (0 + δ)
    #[must_use]
    pub fn epsilon() -> Self {
        Self {
            real: ArithRat::zero(),
            delta: ArithRat::one(),
        }
    }

    /// Create a negative infinitesimal (0 - δ)
    #[must_use]
    pub fn neg_epsilon() -> Self {
        Self {
            real: ArithRat::zero(),
            delta: -ArithRat::one(),
        }
    }

    /// Check if this is exactly zero
    #[must_use]
    pub fn is_zero(&self) -> bool {
        self.real.is_zero() && self.delta.is_zero()
    }

    /// Check if this is positive (greater than zero)
    #[must_use]
    pub fn is_positive(&self) -> bool {
        match self.real.cmp(&ArithRat::zero()) {
            Ordering::Greater => true,
            Ordering::Less => false,
            Ordering::Equal => self.delta > ArithRat::zero(),
        }
    }

    /// Check if this is negative (less than zero)
    #[must_use]
    pub fn is_negative(&self) -> bool {
        match self.real.cmp(&ArithRat::zero()) {
            Ordering::Less => true,
            Ordering::Greater => false,
            Ordering::Equal => self.delta < ArithRat::zero(),
        }
    }

    /// Check if this is non-negative (>= 0)
    #[must_use]
    pub fn is_non_negative(&self) -> bool {
        !self.is_negative()
    }

    /// Check if this is non-positive (<= 0)
    #[must_use]
    pub fn is_non_positive(&self) -> bool {
        !self.is_positive()
    }

    /// Get the floor (largest integer <= this value)
    ///
    /// Returns `i128` since the LRA/LIA core's rational is `Ratio<i128>`
    /// ([`crate::ArithRat`]); the integer part of a value that needs more than
    /// `i64` is preserved exactly instead of being silently truncated.
    #[must_use]
    pub fn floor(&self) -> i128 {
        let real_floor = self.real.floor().to_integer();
        // If real is exactly an integer and delta is negative, floor is real - 1
        if self.real.fract().is_zero() && self.delta < ArithRat::zero() {
            real_floor - 1
        } else {
            real_floor
        }
    }

    /// Get the ceiling (smallest integer >= this value)
    ///
    /// Returns `i128` for the same reason as [`Self::floor`].
    #[must_use]
    pub fn ceil(&self) -> i128 {
        let real_ceil = self.real.ceil().to_integer();
        // If real is exactly an integer and delta is positive, ceil is real + 1
        if self.real.fract().is_zero() && self.delta > ArithRat::zero() {
            real_ceil + 1
        } else {
            real_ceil
        }
    }

    /// Fused multiply-add: `self += x * c`, without materializing the
    /// intermediate `DeltaRational` product.
    ///
    /// Zero fast paths — each skip is BIT-IDENTICAL to the unfused
    /// `self += x * c` sequence, because `num-rational` keeps every `Ratio`
    /// in reduced form (denominator positive, gcd(numer, denom) = 1), so
    /// `a + 0/1` reproduces `a` exactly and `0/1 * c` produces exactly `0/1`:
    /// - `c == 0` or `x == 0`: the product is `0/1` in both lanes and adding
    ///   zero is the identity — skip the whole term.
    /// - `x.real == 0`: the real lane contributes `0/1` — skip its gcd/reduce.
    /// - `x.delta == 0` (the dominant case: values from non-strict bounds have
    ///   no infinitesimal part): the delta lane contributes `0/1` — skip it.
    pub fn add_mul(&mut self, x: &DeltaRational, c: &ArithRat) {
        if c.is_zero() || x.is_zero() {
            return;
        }
        if !x.real.is_zero() {
            self.real += x.real * c;
        }
        if !x.delta.is_zero() {
            self.delta += x.delta * c;
        }
    }
}

impl From<ArithRat> for DeltaRational {
    fn from(r: ArithRat) -> Self {
        Self::from_rational(r)
    }
}

impl From<i64> for DeltaRational {
    fn from(n: i64) -> Self {
        // Widen the i64 to i128 (lossless) to build the `ArithRat`.
        Self::from_rational(ArithRat::from_integer(i128::from(n)))
    }
}

impl PartialEq for DeltaRational {
    fn eq(&self, other: &Self) -> bool {
        self.real == other.real && self.delta == other.delta
    }
}

impl Eq for DeltaRational {}

impl PartialOrd for DeltaRational {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for DeltaRational {
    fn cmp(&self, other: &Self) -> Ordering {
        match self.real.cmp(&other.real) {
            Ordering::Equal => self.delta.cmp(&other.delta),
            other => other,
        }
    }
}

impl Neg for DeltaRational {
    type Output = Self;

    fn neg(self) -> Self::Output {
        Self {
            real: -self.real,
            delta: -self.delta,
        }
    }
}

impl Add for DeltaRational {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        Self {
            real: self.real + rhs.real,
            delta: self.delta + rhs.delta,
        }
    }
}

impl AddAssign for DeltaRational {
    fn add_assign(&mut self, rhs: Self) {
        // Zero fast paths: on reduced `Ratio`s, `a + 0/1` yields `a` with the
        // exact same (reduced) representation, so skipping the lane op when the
        // corresponding rhs component is zero is bit-identical to performing it
        // — it merely avoids the gcd/reduce work.
        if !rhs.real.is_zero() {
            self.real += rhs.real;
        }
        if !rhs.delta.is_zero() {
            self.delta += rhs.delta;
        }
    }
}

impl Sub for DeltaRational {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        Self {
            real: self.real - rhs.real,
            delta: self.delta - rhs.delta,
        }
    }
}

impl SubAssign for DeltaRational {
    fn sub_assign(&mut self, rhs: Self) {
        self.real -= rhs.real;
        self.delta -= rhs.delta;
    }
}

impl Mul<ArithRat> for DeltaRational {
    type Output = Self;

    fn mul(self, rhs: ArithRat) -> Self::Output {
        // Zero fast paths: `0/1 * c` produces exactly `0/1` (num-rational
        // reduces `0/d` to `0/1`), so returning the zero component unchanged is
        // bit-identical to performing the multiply.  Likewise `x * 0` yields
        // `0/1` in both lanes — exactly `Self::zero()`.
        if rhs.is_zero() {
            return Self::zero();
        }
        Self {
            real: self.real * rhs,
            delta: if self.delta.is_zero() {
                self.delta
            } else {
                self.delta * rhs
            },
        }
    }
}

impl MulAssign<ArithRat> for DeltaRational {
    fn mul_assign(&mut self, rhs: ArithRat) {
        self.real *= rhs;
        self.delta *= rhs;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_delta_rational_basic() {
        let a = DeltaRational::from_rational(ArithRat::from_integer(5));
        let b = DeltaRational::from_rational(ArithRat::from_integer(3));

        assert!(a > b);
        assert_eq!(a - b, DeltaRational::from(2));
    }

    #[test]
    fn test_delta_rational_with_epsilon() {
        let five = DeltaRational::from(5);
        let five_minus_eps = DeltaRational::new(ArithRat::from_integer(5), -ArithRat::one());
        let five_plus_eps = DeltaRational::new(ArithRat::from_integer(5), ArithRat::one());

        assert!(five_minus_eps < five);
        assert!(five < five_plus_eps);
        assert!(five_minus_eps < five_plus_eps);
    }

    #[test]
    fn test_delta_is_positive_negative() {
        let eps = DeltaRational::epsilon();
        let neg_eps = DeltaRational::neg_epsilon();
        let zero = DeltaRational::zero();

        assert!(eps.is_positive());
        assert!(!eps.is_negative());

        assert!(neg_eps.is_negative());
        assert!(!neg_eps.is_positive());

        assert!(zero.is_zero());
        assert!(!zero.is_positive());
        assert!(!zero.is_negative());
    }

    #[test]
    fn test_delta_floor_ceil() {
        // 5 - ε should have floor 4, ceil 5
        let five_minus_eps = DeltaRational::new(ArithRat::from_integer(5), -ArithRat::one());
        assert_eq!(five_minus_eps.floor(), 4);
        assert_eq!(five_minus_eps.ceil(), 5);

        // 5 + ε should have floor 5, ceil 6
        let five_plus_eps = DeltaRational::new(ArithRat::from_integer(5), ArithRat::one());
        assert_eq!(five_plus_eps.floor(), 5);
        assert_eq!(five_plus_eps.ceil(), 6);

        // 5.5 should have floor 5, ceil 6 (delta doesn't matter)
        let five_point_five = DeltaRational::from_rational(ArithRat::new(11, 2));
        assert_eq!(five_point_five.floor(), 5);
        assert_eq!(five_point_five.ceil(), 6);
    }

    /// Exactness proof for the zero fast paths in `Mul<ArithRat>`, `AddAssign`,
    /// and `add_mul`: over a grid that exercises every skip branch (zero reals,
    /// zero deltas, zero multipliers, negatives, non-integer ratios), the
    /// results must match the RAW lane-wise `ArithRat` operations (the original,
    /// fast-path-free semantics) in exact reduced representation — numerator and
    /// denominator compared directly, not just by value.
    #[test]
    fn test_zero_fast_paths_bit_identical_to_unfused_lanes() {
        let rats = [
            ArithRat::new(-5, 3),
            -ArithRat::one(),
            ArithRat::zero(),
            ArithRat::new(1, 2),
            ArithRat::from_integer(7),
            ArithRat::new(22, 7),
        ];
        let assert_lane = |got: ArithRat, want: ArithRat, what: &str| {
            assert_eq!(got.numer(), want.numer(), "{what}: numer mismatch");
            assert_eq!(got.denom(), want.denom(), "{what}: denom mismatch");
        };
        for &xr in &rats {
            for &xd in &rats {
                let x = DeltaRational::new(xr, xd);
                for &c in &rats {
                    // Mul<ArithRat> vs raw lanes
                    let prod = x * c;
                    assert_lane(prod.real, xr * c, "mul real");
                    assert_lane(prod.delta, xd * c, "mul delta");
                    for &ar in &rats {
                        for &ad in &rats {
                            // AddAssign vs raw lanes
                            let mut acc = DeltaRational::new(ar, ad);
                            acc += x;
                            assert_lane(acc.real, ar + xr, "add_assign real");
                            assert_lane(acc.delta, ad + xd, "add_assign delta");
                            // Fused add_mul vs raw unfused `acc += x * c` lanes
                            let mut fused = DeltaRational::new(ar, ad);
                            fused.add_mul(&x, &c);
                            assert_lane(fused.real, ar + xr * c, "add_mul real");
                            assert_lane(fused.delta, ad + xd * c, "add_mul delta");
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn test_delta_arithmetic() {
        let a = DeltaRational::new(ArithRat::from_integer(3), ArithRat::one());
        let b = DeltaRational::new(ArithRat::from_integer(2), -ArithRat::one());

        // (3 + δ) + (2 - δ) = 5
        let sum = a + b;
        assert_eq!(sum.real, ArithRat::from_integer(5));
        assert_eq!(sum.delta, ArithRat::zero());

        // (3 + δ) - (2 - δ) = 1 + 2δ
        let diff = a - b;
        assert_eq!(diff.real, ArithRat::from_integer(1));
        assert_eq!(diff.delta, ArithRat::from_integer(2));

        // (3 + δ) * 2 = 6 + 2δ
        let scaled = a * ArithRat::from_integer(2);
        assert_eq!(scaled.real, ArithRat::from_integer(6));
        assert_eq!(scaled.delta, ArithRat::from_integer(2));
    }
}
