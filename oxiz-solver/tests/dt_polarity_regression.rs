//! Permanent (z3-free) regressions for the datatype eager-check polarity bugs
//! found by adsmt's #392 randomized datatype-render differential (2026-07-03).
//!
//! `check_dt_constraints`'s collector walked `And` children regardless of the
//! enclosing polarity and recursed into `Eq` operands as if they were asserted
//! facts. Two spurious-UNSAT channels followed:
//!
//! 1. `(not (and (not (= k c00)) (not (= k c01))))` ≡ `k=c00 ∨ k=c01` — the
//!    collector read the negated-And's children as JOINT facts, collected the
//!    two distinct constructor equalities, and declared the disjunction a
//!    conflict (z3: sat).
//! 2. `(= b ((_ is c00) k))` — a Bool `=` is an iff; the tester inside its
//!    operand has undetermined polarity, but the collector asserted it
//!    positively, conflicting with a real `(= k c01)` (z3: sat).
//!
//! Ground truths are noted inline; no external oracle needed.

use oxiz_solver::Context;

fn verdict(script: &str) -> &'static str {
    let mut ctx = Context::new();
    ctx.set_timeout_ms(5000);
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

/// ≡ `k=c00 ∨ k=c01` over a 2-ctor enum: satisfiable (either ctor works).
#[test]
fn negated_and_of_diseqs_is_a_disjunction_not_a_conjunction() {
    let v = verdict(
        "(set-logic ALL)\n\
         (declare-datatypes ((D0 0)) (((c00) (c01))))\n\
         (declare-const k D0)\n\
         (assert (not (and (not (= k c00)) (not (= k c01)))))\n\
         (check-sat)\n",
    );
    assert_eq!(v, "sat", "k=c00 ∨ k=c01 over {{c00,c01}} is satisfiable");
}

/// Same shape, 3-ctor datatype (the ctor count is irrelevant to the truth).
#[test]
fn negated_and_of_diseqs_three_ctor_sat() {
    let v = verdict(
        "(set-logic ALL)\n\
         (declare-datatypes ((D0 0)) (((c00) (c01) (c02))))\n\
         (declare-const k D0)\n\
         (assert (not (and (not (= k c00)) (not (= k c01)))))\n\
         (check-sat)\n",
    );
    assert_eq!(v, "sat");
}

/// A Bool-sorted `=` is an iff: the tester operand is NOT an asserted fact.
/// Model: b=false, k=c01 (tester false, iff holds).
#[test]
fn bool_iff_tester_operand_is_not_an_asserted_fact() {
    let v = verdict(
        "(set-logic ALL)\n\
         (declare-datatypes ((D0 0)) (((c00) (c01))))\n\
         (declare-const k D0)\n\
         (declare-const b Bool)\n\
         (assert (= b ((_ is c00) k)))\n\
         (assert (= k c01))\n\
         (assert (not b))\n\
         (check-sat)\n",
    );
    assert_eq!(v, "sat", "b=false, k=c01 satisfies the iff");
}

/// The #392 differential's original counterexample (seed 48): a lukb `match`
/// goal lowered to a negated conjunction of disequalities — the goal is NOT
/// valid, so its negation must be satisfiable.
#[test]
fn match_goal_negation_render_is_sat() {
    let v = verdict(
        "(set-logic ALL)\n\
         (declare-datatypes ((D0 0) (D1 0)) (((c00) (c01)) ((c10) (c11) (c12))))\n\
         (declare-const k0 D1)\n\
         (declare-const k1 D0)\n\
         (declare-const k2 D0)\n\
         (assert (= k1 c00))\n\
         (assert (not (and (not (= k2 c00)) (not (= k2 c01)))))\n\
         (check-sat)\n",
    );
    assert_eq!(v, "sat");
}

/// The EXACT #392 seed-48 render — including the trivial self-equalities the
/// lukb axioms `k0 = k0` / `k2 = k2` lower to. These were load-bearing for a
/// SECOND spurious-unsat distinct from the collector polarity bug.
#[test]
fn match_goal_negation_render_with_self_equalities_is_sat() {
    let v = verdict(
        "(set-logic ALL)\n\
         (declare-datatypes ((D0 0) (D1 0)) (((c00) (c01)) ((c10) (c11) (c12))))\n\
         (declare-const k0 D1)\n\
         (declare-const k1 D0)\n\
         (declare-const k2 D0)\n\
         (assert (= k1 c00))\n\
         (assert (= k0 k0))\n\
         (assert (= k2 k2))\n\
         (assert (not (and (not (= k2 c00)) (not (= k2 c01)))))\n\
         (check-sat)\n",
    );
    assert_eq!(v, "sat");
}

/// Minimal self-equality catalyst: one datatype const, `k2 = k2`, then the
/// disjunctive goal negation.
#[test]
fn self_equality_plus_negated_and_is_sat() {
    let v = verdict(
        "(set-logic ALL)\n\
         (declare-datatypes ((D0 0)) (((c00) (c01))))\n\
         (declare-const k2 D0)\n\
         (assert (= k2 k2))\n\
         (assert (not (and (not (= k2 c00)) (not (= k2 c01)))))\n\
         (check-sat)\n",
    );
    assert_eq!(v, "sat");
}

/// Positive control — the eager check must still catch a REAL ground datatype
/// conflict: a positive tester against a different constructor equality.
#[test]
fn real_tester_vs_ctor_equality_conflict_still_unsat() {
    let v = verdict(
        "(set-logic ALL)\n\
         (declare-datatypes ((D0 0)) (((c00) (c01))))\n\
         (declare-const k D0)\n\
         (assert ((_ is c00) k))\n\
         (assert (= k c01))\n\
         (check-sat)\n",
    );
    assert_eq!(v, "unsat", "k is c00 AND k = c01 is a real conflict");
}

/// Positive control — two distinct constructor equalities asserted as REAL
/// top-level conjuncts stay a conflict.
#[test]
fn real_distinct_ctor_equalities_still_unsat() {
    let v = verdict(
        "(set-logic ALL)\n\
         (declare-datatypes ((D0 0)) (((c00) (c01))))\n\
         (declare-const k D0)\n\
         (assert (and (= k c00) (= k c01)))\n\
         (check-sat)\n",
    );
    assert_eq!(v, "unsat");
}

/// The dual rule added with the fix: a NEGATED Or IS a conjunction — its
/// children are real facts. A positive tester conflicting with a tester
/// inside a negated Or is a genuine conflict the collector now sees.
/// (The equality flavour `¬(k=c00 ∨ k=c01)` — unsat by nullary-ctor
/// exhaustiveness — was a separate pre-existing spurious-sat, CLOSED by the
/// #399 fix; see `dt_exhaustiveness_regression.rs`.)
#[test]
fn negated_or_collects_its_children_as_facts() {
    let v = verdict(
        "(set-logic ALL)\n\
         (declare-datatypes ((D0 0)) (((c00) (c01))))\n\
         (declare-const k D0)\n\
         (assert ((_ is c00) k))\n\
         (assert (not (or ((_ is c00) k) false)))\n\
         (check-sat)\n",
    );
    assert_eq!(v, "unsat", "is-c00(k) against ¬(is-c00(k) ∨ ⊥) is a real conflict");
}
