//! Regression: an Int/Real `Eq(lhs, rhs)` atom decided FALSE by the SAT
//! search must actually constrain the arithmetic (simplex) solver to
//! `lhs != rhs`. Before this fix that only happened when the atom appeared
//! in the exact syntactic shape `Not(Eq(a, b))` somewhere the AST pre-pass
//! `add_arith_diseq_split[_recursive]` (`oxiz-solver/src/solver/encode.rs`)
//! happened to walk: `Not`, `And`, `Or`, the RHS of `Implies`, or either
//! branch of `Ite`. Simplex has no native disequality primitive, so an
//! equality atom decided false with NO trichotomy clause backing it left
//! the arithmetic solver free to pick `lhs = rhs` anyway — producing a
//! model that contradicts the SAT layer's own Boolean assignment.
//!
//! Confirmed-missing positions (all fixed by this regression's shapes):
//!   - the ANTECEDENT of an `Implies` (`(=> (= a b) ...)`)
//!   - the CONDITION of an `Ite` (`(ite (= a b) ...)`)
//!   - a bare disjunct of an `Or` alongside another satisfying disjunct
//!     (`(or (= a b) flag)` with `flag` true)
//!
//! The fix moves the trichotomy-split clause `Eq(a,b) OR Lt(a,b) OR
//! Gt(a,b)` (a tautology over Int/Real, so it can never itself cause a
//! false UNSAT) to the single choke-point where every arithmetic equality
//! atom is first given its Tseitin variable (`encode.rs`'s `TermKind::Eq`
//! arm), so it is unconditionally present regardless of surrounding
//! syntactic context instead of depending on the AST walker recognizing a
//! specific shape.
//!
//! Each case below forces `X1 = X2` unconditionally via a sum-cancellation
//! equality (`X1 + X0 = X2 + X0`) that requires arithmetic simplification
//! to recognize as `X1 = X2` — deliberately not a syntactically-direct
//! `(= X1 X2)` atom, matching the shape that surfaced the bug. z3 and cvc5
//! independently agree all four `*_is_unsat` cases are `unsat`.

use oxiz_solver::Context;

fn verdict(script: &str) -> &'static str {
    let mut ctx = Context::new();
    ctx.set_timeout_ms(10_000);
    match ctx.execute_script(script) {
        Ok(out) => out
            .iter()
            .rev()
            .find_map(|l| match l.trim() {
                "sat" => Some("sat"),
                "unsat" => Some("unsat"),
                "unknown" => Some("unknown"),
                _ => None,
            })
            .unwrap_or("unknown"),
        Err(_) => "unknown",
    }
}

/// Eq atom as the ANTECEDENT of an `Implies`. This was the originally
/// discovered shape: oxiz reported `sat` with a self-contradictory model
/// (`X0=0, X1=1, X2=1`, under which `(= X2 X1)` is actually true, so the
/// implication requires `(< 5 3)` — which is false).
#[test]
fn eq_as_implies_antecedent_is_unsat() {
    let script = "\
(set-logic QF_LIA)
(declare-const X0 Int)
(declare-const X1 Int)
(declare-const X2 Int)
(assert (= (+ X1 X0) (+ X2 X0)))
(assert (=> (= X2 X1) (< 5 3)))
(check-sat)
";
    assert_eq!(
        verdict(script),
        "unsat",
        "X1=X2 is forced unconditionally by the cancellation equality, so \
         the implication reduces to the always-false `(< 5 3)`; `sat` means \
         the Eq atom was decided false without telling the arithmetic \
         solver `X1 != X2`"
    );
}

/// The same shape with a variable (rather than purely-constant) always-false
/// consequent, so the consequent atom also needs at least one theory
/// variable to reach the arithmetic solver (ruling out "constant-only atom
/// mishandling" as an alternative explanation).
#[test]
fn eq_as_implies_antecedent_variable_consequent_is_unsat() {
    let script = "\
(set-logic QF_LIA)
(declare-const X0 Int)
(declare-const X1 Int)
(declare-const X2 Int)
(assert (= (+ X1 X0) (+ X2 X0)))
(assert (=> (= X2 X1) (not (>= X2 X2))))
(check-sat)
";
    assert_eq!(verdict(script), "unsat");
}

/// Eq atom as the CONDITION of an `Ite`. `add_arith_diseq_split_recursive`
/// only ever recursed into an `Ite`'s two branches, never its condition, so
/// this position was equally unsplit.
#[test]
fn eq_as_ite_condition_is_unsat() {
    let script = "\
(set-logic QF_LIA)
(declare-const X0 Int)
(declare-const X1 Int)
(declare-const X2 Int)
(assert (= (+ X1 X0) (+ X2 X0)))
(assert (ite (= X2 X1) (< 5 3) true))
(check-sat)
";
    assert_eq!(verdict(script), "unsat");
}

/// Eq atom as a bare disjunct of an `Or`, satisfied via a different, true
/// disjunct (`flag`) rather than via an explicit `Not(Eq(..))` wrapper.
#[test]
fn eq_as_bare_or_disjunct_is_unsat() {
    let script = "\
(set-logic QF_LIA)
(declare-const X0 Int)
(declare-const X1 Int)
(declare-const X2 Int)
(declare-const flag Bool)
(assert (= (+ X1 X0) (+ X2 X0)))
(assert (or (= X2 X1) flag))
(assert flag)
(assert (=> (= X2 X1) (< 5 3)))
(check-sat)
";
    assert_eq!(verdict(script), "unsat");
}

/// Soundness control in the OTHER direction: the trichotomy clause added at
/// the atom's encode choke-point (`Eq OR Lt OR Gt`) is a tautology over
/// Int/Real, so it must never itself force a false UNSAT. A genuinely
/// satisfiable variant of the antecedent shape (consequent now trivially
/// TRUE instead of always-false) must stay `sat`.
#[test]
fn eq_as_implies_antecedent_true_consequent_stays_sat() {
    let script = "\
(set-logic QF_LIA)
(declare-const X0 Int)
(declare-const X1 Int)
(declare-const X2 Int)
(assert (= (+ X1 X0) (+ X2 X0)))
(assert (=> (= X2 X1) (>= 5 3)))
(check-sat)
";
    assert_eq!(verdict(script), "sat");
}

/// A second soundness control: when the equality is genuinely NOT forced
/// (no cancellation constraint tying `X1` and `X2` together), the Eq atom
/// legitimately CAN be decided false, and the formula stays `sat` via that
/// branch — the trichotomy split must not force `Eq` to hold.
#[test]
fn eq_as_implies_antecedent_unconstrained_vars_stays_sat() {
    let script = "\
(set-logic QF_LIA)
(declare-const X1 Int)
(declare-const X2 Int)
(assert (=> (= X2 X1) (< 5 3)))
(check-sat)
";
    assert_eq!(
        verdict(script),
        "sat",
        "X1 and X2 are otherwise unconstrained, so `X1 != X2` is a valid \
         witness (e.g. X1=0, X2=1) making the implication vacuously true"
    );
}
