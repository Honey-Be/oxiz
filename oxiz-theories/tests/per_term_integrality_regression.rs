//! Regression (#427), `ArithSolver` level: integrality is a property of the
//! TERM's sort, not of the solver's global LIA/LRA mode.
//!
//! The mode is set from the `(set-logic …)` NAME by
//! `oxiz-solver/src/solver/config.rs`, which substring-matches
//! `NIA`/`NRA`/`LIA`/`IDL`/`LRA`/`RDL`/`BV` and otherwise keeps the default
//! `lra()`. `ALL`, a missing `(set-logic)`, and `AUFLIRA`/`QF_LIRA` all fall
//! through, so Int-sorted problems were solved over the rationals. These tests
//! drive `ArithSolver` directly so the arithmetic layer is pinned independently
//! of the front end (see `oxiz-solver/tests/logic_all_integrality_regression.rs`
//! for the end-to-end SMT-LIB verdicts).

use oxiz_core::ast::TermId;
use oxiz_theories::ArithRat;
use oxiz_theories::Theory;
use oxiz_theories::TheoryCheckResult;
use oxiz_theories::arithmetic::ArithSolver;

const REASON: TermId = TermId(0);

fn one() -> ArithRat {
    ArithRat::from_integer(1)
}

/// An LRA-mode solver (what `ALL` leaves you with) must still refute
/// `0 < x < 1` once `x` is DECLARED Int-sorted.
#[test]
fn lra_mode_with_declared_int_term_refutes_empty_interval() {
    let mut s = ArithSolver::lra();
    let x = TermId(1);
    s.declare_sort(x, true);
    s.assert_gt(&[(x, one())], ArithRat::from_integer(0), REASON);
    s.assert_lt(&[(x, one())], ArithRat::from_integer(1), REASON);
    assert!(
        matches!(s.check(), Ok(TheoryCheckResult::Unsat(_))),
        "declared Int-sorted `x` has no value strictly between 0 and 1, so the \
         strengthened bounds `x >= 1 /\\ x <= 0` must conflict in the simplex"
    );
}

/// The same solver must NOT refute it for a term declared Real-sorted — this is
/// the failure mode of the naive `ALL ⇒ lia()` fix.
#[test]
fn lra_mode_with_declared_real_term_keeps_empty_interval_sat() {
    let mut s = ArithSolver::lra();
    let x = TermId(1);
    s.declare_sort(x, false);
    s.assert_gt(&[(x, one())], ArithRat::from_integer(0), REASON);
    s.assert_lt(&[(x, one())], ArithRat::from_integer(1), REASON);
    assert!(matches!(s.check(), Ok(TheoryCheckResult::Sat)));
}

/// An LIA-mode solver must NOT force integrality onto a term declared
/// Real-sorted. Before per-term integrality this reported `Unsat` — a latent
/// false UNSAT under any `…LIA…`-named logic that also declares a `Real`.
#[test]
fn lia_mode_with_declared_real_term_keeps_empty_interval_sat() {
    let mut s = ArithSolver::lia();
    let x = TermId(1);
    s.declare_sort(x, false);
    s.assert_gt(&[(x, one())], ArithRat::from_integer(0), REASON);
    s.assert_lt(&[(x, one())], ArithRat::from_integer(1), REASON);
    assert!(
        matches!(s.check(), Ok(TheoryCheckResult::Sat)),
        "`x` is Real-sorted; the LIA logic NAME must not make it integral"
    );
}

/// Mixed sorts in one solver: the Int half is refuted, the Real half is not.
/// Neither a global LRA mode nor a global LIA mode gets both right.
#[test]
fn mixed_sorts_refute_only_the_integer_half() {
    let mut s = ArithSolver::lra();
    let xi = TermId(1);
    let xr = TermId(2);
    s.declare_sort(xi, true);
    s.declare_sort(xr, false);
    // Real half alone: satisfiable.
    s.assert_gt(&[(xr, one())], ArithRat::from_integer(0), REASON);
    s.assert_lt(&[(xr, one())], ArithRat::from_integer(1), REASON);
    assert!(matches!(s.check(), Ok(TheoryCheckResult::Sat)));
    // Adding the Int half makes it infeasible.
    s.assert_gt(&[(xi, one())], ArithRat::from_integer(0), REASON);
    s.assert_lt(&[(xi, one())], ArithRat::from_integer(1), REASON);
    assert!(matches!(s.check(), Ok(TheoryCheckResult::Unsat(_))));
}

/// The GCD infeasibility test in `assert_eq` must fire for a declared-Int
/// expression even in LRA mode (`2x + 2y = 7`).
#[test]
fn lra_mode_gcd_infeasibility_fires_for_declared_int_terms() {
    let mut s = ArithSolver::lra();
    let (x, y) = (TermId(1), TermId(2));
    s.declare_sort(x, true);
    s.declare_sort(y, true);
    s.assert_eq(
        &[
            (x, ArithRat::from_integer(2)),
            (y, ArithRat::from_integer(2)),
        ],
        ArithRat::from_integer(7),
        REASON,
    );
    assert!(matches!(s.check(), Ok(TheoryCheckResult::Unsat(_))));
}

/// …and must NOT fire when the coefficients are fractional, where the linear
/// form is not integer-valued at all. `(1/2)x = 3/2` is satisfied by `x = 3`,
/// yet the old global-mode gate took the "non-integer constant ⇒ infeasible"
/// branch and reported a conflict.
#[test]
fn fractional_coefficients_do_not_trigger_gcd_infeasibility() {
    let mut s = ArithSolver::lia();
    let x = TermId(1);
    s.declare_sort(x, true);
    s.assert_eq(
        &[(x, ArithRat::new(1, 2))],
        ArithRat::new(3, 2),
        REASON,
    );
    assert!(
        !matches!(s.check(), Ok(TheoryCheckResult::Unsat(_))),
        "`x = 3` satisfies `(1/2)x = 3/2`; reporting a conflict is a false UNSAT"
    );
}

/// The strict-bound strengthening is `Σ cᵢxᵢ < k ⇒ Σ cᵢxᵢ ≤ ⌈k⌉ − 1`. For a
/// FRACTIONAL `k` the old `k − 1` form was too strong: `2x < 1/2` became
/// `2x ≤ -1/2` (i.e. `x ≤ -1`), wrongly excluding `x = 0`.
#[test]
fn strict_bound_with_fractional_rhs_is_not_over_tightened() {
    let mut s = ArithSolver::lia();
    let x = TermId(1);
    s.declare_sort(x, true);
    s.assert_lt(&[(x, ArithRat::from_integer(2))], ArithRat::new(1, 2), REASON);
    s.assert_ge(&[(x, one())], ArithRat::from_integer(0), REASON);
    assert!(
        matches!(s.check(), Ok(TheoryCheckResult::Sat)),
        "`x = 0` satisfies `2x < 1/2 /\\ x >= 0`"
    );
}

/// Symmetric case for `assert_gt`: `2x > 1/2 ⇒ 2x ≥ ⌊1/2⌋ + 1 = 1`, which
/// admits `x = 1`. The old `k + 1` form gave `2x ≥ 3/2`, which also admits
/// `x = 1`, so this pins the bound rather than catching a past bug — it guards
/// the direction from being flipped.
#[test]
fn strict_lower_bound_with_fractional_rhs_admits_the_least_integer() {
    let mut s = ArithSolver::lia();
    let x = TermId(1);
    s.declare_sort(x, true);
    s.assert_gt(&[(x, ArithRat::from_integer(2))], ArithRat::new(1, 2), REASON);
    s.assert_le(&[(x, one())], one(), REASON);
    assert!(matches!(s.check(), Ok(TheoryCheckResult::Sat)));
}

/// An UNDECLARED term keeps the global-mode fallback, so every logic-named
/// path that was already correct stays bit-identical.
#[test]
fn undeclared_term_falls_back_to_the_global_mode() {
    let mut lia = ArithSolver::lia();
    let x = TermId(1);
    lia.assert_gt(&[(x, one())], ArithRat::from_integer(0), REASON);
    lia.assert_lt(&[(x, one())], ArithRat::from_integer(1), REASON);
    assert!(matches!(lia.check(), Ok(TheoryCheckResult::Unsat(_))));

    let mut lra = ArithSolver::lra();
    let y = TermId(1);
    lra.assert_gt(&[(y, one())], ArithRat::from_integer(0), REASON);
    lra.assert_lt(&[(y, one())], ArithRat::from_integer(1), REASON);
    assert!(matches!(lra.check(), Ok(TheoryCheckResult::Sat)));
}
