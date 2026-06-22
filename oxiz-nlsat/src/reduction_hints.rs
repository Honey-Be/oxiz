//! Advisory transformation-hint engine — reduction-KB **rule F** (suggestion 3).
//!
//! When the reduction KB / solver cannot reduce or decide a system (verdict
//! `Unknown`), this suggests INVERTIBLE space transformations that would map it
//! into a KB-recognisable form.
//!
//! SOUNDNESS: the hints are **advisory only** — they never change a verdict.
//! `Unknown` stays `Unknown` until a hint is actually applied and the reduced
//! problem solved + verified. A wrong hint is merely unhelpful, never unsound;
//! and an invertible transform of ℝⁿ (rotation / translation / scaling) is a
//! bijection that PRESERVES the solution set, so following a hint yields a sound
//! result. This is "abduction for the transformation" — the same advisory
//! philosophy as adsmt's `(abduce)` surface (abduct = advice; the
//! user/downstream must justify). See `REDUCTION_KB_RULES.md` §F.
//!
//! This module is PURE / read-only: it touches no solver state and is not on any
//! `solve()` verdict path. Call [`suggest_transforms`] after an `Unknown`.

use num_rational::BigRational;
use num_traits::Zero;

use oxiz_math::polynomial::Polynomial;

use crate::discriminant::recognize_conic;

/// A suggested invertible change of variables that may make a system reducible.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TransformHint {
    /// Rotate the `(x, y)` axes to eliminate a `B·xy` cross-term. The rotation
    /// angle `θ` satisfies `tan(2θ) = B / (A − C)` (for `A = C`, `θ = π/4`).
    /// After rotation the conic is axis-aligned and the §A3 conic classifier
    /// (`discriminant::recognize_conic`) applies directly.
    Rotation {
        b: BigRational,
        a_minus_c: BigRational,
        note: String,
    },
    /// Translate (complete the square) to centre an off-centre conic at the
    /// origin, removing the linear `D·x + E·y` terms.
    Translation {
        d: BigRational,
        e: BigRational,
        note: String,
    },
}

/// Suggest invertible transformations for a set of (unreduced) polynomial
/// equalities. PURE / read-only / advisory — does not touch any solver state or
/// verdict. Intended to be called when a verdict came back `Unknown`, to help a
/// user find the reducing transform by hand.
///
/// Currently recognises degree-2 bivariate (conic) shapes:
/// - a non-zero `B·xy` cross-term ⇒ a [`TransformHint::Rotation`];
/// - non-zero linear `D·x` / `E·y` terms ⇒ a [`TransformHint::Translation`].
///
/// The list is the natural extension point for further invertible-transform
/// recognisers (scaling, shear, the §A2 `t = a·x + b·y + c` substitution, …).
pub fn suggest_transforms(polys: &[Polynomial]) -> Vec<TransformHint> {
    let mut hints: Vec<TransformHint> = Vec::new();
    for p in polys {
        let Some(form) = recognize_conic(p) else {
            continue;
        };
        if !form.b.is_zero() {
            let hint = TransformHint::Rotation {
                b: form.b.clone(),
                a_minus_c: &form.a - &form.c,
                note: "rotate the axes to remove the x·y cross-term (tan(2θ) = B/(A−C); θ=π/4 when A=C), then the conic classifier recognises the axis-aligned conic".to_string(),
            };
            if !hints.contains(&hint) {
                hints.push(hint);
            }
        }
        if !form.d.is_zero() || !form.e.is_zero() {
            let hint = TransformHint::Translation {
                d: form.d.clone(),
                e: form.e.clone(),
                note: "translate (complete the square) to centre the conic, removing the linear D·x + E·y terms".to_string(),
            };
            if !hints.contains(&hint) {
                hints.push(hint);
            }
        }
    }
    hints
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_bigint::BigInt;

    fn ri(n: i64) -> BigRational {
        BigRational::from_integer(BigInt::from(n))
    }

    #[test]
    fn rotated_conic_suggests_rotation() {
        // x·y − 1 = 0 : B = 1 ≠ 0 (a 45°-rotated hyperbola).
        let x = Polynomial::from_var(0);
        let y = Polynomial::from_var(1);
        let xy = Polynomial::mul(&x, &y);
        let p = Polynomial::sub(&xy, &Polynomial::constant(ri(1)));
        let hints = suggest_transforms(&[p]);
        assert!(
            hints
                .iter()
                .any(|h| matches!(h, TransformHint::Rotation { .. })),
            "expected a rotation hint for the x·y cross-term, got {hints:?}"
        );
    }

    #[test]
    fn axis_aligned_conic_gives_no_rotation_hint() {
        // x² + y² − 25 = 0 : B = 0, no cross-term ⇒ no rotation hint.
        let x = Polynomial::from_var(0);
        let y = Polynomial::from_var(1);
        let p = Polynomial::sub(
            &Polynomial::add(&Polynomial::mul(&x, &x), &Polynomial::mul(&y, &y)),
            &Polynomial::constant(ri(25)),
        );
        let hints = suggest_transforms(&[p]);
        assert!(
            !hints
                .iter()
                .any(|h| matches!(h, TransformHint::Rotation { .. })),
            "an axis-aligned circle needs no rotation, got {hints:?}"
        );
    }

    #[test]
    fn off_centre_conic_suggests_translation() {
        // x² + y² − 4x = 0 : D = −4 ≠ 0 ⇒ a translation hint.
        let x = Polynomial::from_var(0);
        let y = Polynomial::from_var(1);
        let four_x = Polynomial::mul(&Polynomial::constant(ri(4)), &x);
        let p = Polynomial::sub(
            &Polynomial::add(&Polynomial::mul(&x, &x), &Polynomial::mul(&y, &y)),
            &four_x,
        );
        let hints = suggest_transforms(&[p]);
        assert!(
            hints
                .iter()
                .any(|h| matches!(h, TransformHint::Translation { .. })),
            "expected a translation hint for the off-centre conic, got {hints:?}"
        );
    }

    #[test]
    fn non_conic_gives_no_hint() {
        // A linear polynomial is not a conic ⇒ no hint.
        let x = Polynomial::from_var(0);
        let p = Polynomial::sub(&x, &Polynomial::constant(ri(1)));
        assert!(suggest_transforms(&[p]).is_empty());
    }
}
