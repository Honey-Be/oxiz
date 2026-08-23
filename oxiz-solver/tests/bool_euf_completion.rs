// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors

//! #433 — Bool terms were second-class citizens in EUF, in two independent
//! ways, both false-SAT:
//!
//! 1. **A Bool equality never reached congruence.** `(= b1 b2)` was encoded as
//!    a Tseitin iff gate ONLY, which ties the equality literal to the
//!    operands' truth values and tells EUF nothing — so `h(b1) = 1` and
//!    `h(b2) != 1` with `b1 = b2` reported `sat`.
//! 2. **A Bool ARGUMENT's truth value never reached EUF.** `Constraint::
//!    BoolApp` completes Bool-valued application RESULTS, but a plain Bool
//!    variable or compound in argument position had no completion, so
//!    `p, q, k(p) != k(q)` reported `sat` even though `p` and `q` are both
//!    true.
//!
//! ONE mechanism closes both: a `Constraint::BoolValue` watch per Bool-sorted
//! UF argument, with the encoded literal's polarity folded in. The equality
//! family needs no mechanism of its own because Bool is a TWO-VALUED domain —
//! the iff gate forces equal operands to one value, the watches put both nodes
//! in the same canonical class, and unequal operands land in the two mutually-
//! disequal classes. (A `Constraint::Eq` registration for Bool equalities was
//! tried, measured at 2-3x on the long corpus rows, and removed as subsumed —
//! see the `is_bool_eq` arm in `encode.rs`.)
//!
//! Both shapes were found by testing upstream OxiZ v0.3.2's release notes
//! against this fork (which branched at v0.2.3 and never received the fixes);
//! the implementations here are independent of upstream's.
//!
//! Soundness controls sit at the bottom: every fix here ADDS merges to EUF,
//! and an over-merge turns `sat` into `unsat` — the fatal direction — so each
//! completion is paired with a genuinely-satisfiable twin.

use oxiz_solver::Context;

fn verdict(script: &str) -> String {
    let mut ctx = Context::new();
    let out = ctx.execute_script(script).expect("script parses");
    out.iter()
        .map(|l| l.trim())
        .find(|l| matches!(*l, "sat" | "unsat" | "unknown"))
        .unwrap_or("no-verdict")
        .to_owned()
}

// ---------------------------------------------------------------- fix 1: eq

/// The reported shape: a Bool equality feeding congruence through a UF.
/// Closed by the VALUE route: the iff gate forces `b1` and `b2` to one value,
/// and their argument watches put both in the same canonical class.
#[test]
fn bool_equality_reaches_congruence() {
    assert_eq!(
        verdict(
            "(set-logic QF_UFLIA)\n\
             (declare-fun b1 () Bool) (declare-fun b2 () Bool)\n\
             (declare-fun h (Bool) Int)\n\
             (assert (= b1 b2))\n\
             (assert (= (h b1) 1))\n\
             (assert (not (= (h b2) 1)))\n\
             (check-sat)\n"
        ),
        "unsat"
    );
}

/// The NEGATIVE direction: `(not (= b1 b2))` against a chain of two positive
/// equalities. Pure Bool, no UF — the iff gates alone make this propositionally
/// unsatisfiable, which is exactly the claim that a Bool equality with no
/// UF-argument operands has nothing to tell EUF.
#[test]
fn bool_disequality_reaches_congruence() {
    assert_eq!(
        verdict(
            "(set-logic QF_UF)\n\
             (declare-fun b1 () Bool) (declare-fun b2 () Bool) (declare-fun b3 () Bool)\n\
             (assert (= b1 b3))\n\
             (assert (= b3 b2))\n\
             (assert (not (= b1 b2)))\n\
             (check-sat)\n"
        ),
        "unsat"
    );
}

/// A compound Bool operand: `(= r (and p q))` merges `r` with the compound's
/// node, and congruence carries it through `k`.
#[test]
fn compound_bool_equality_reaches_congruence() {
    assert_eq!(
        verdict(
            "(set-logic QF_UFLIA)\n\
             (declare-fun p () Bool) (declare-fun q () Bool) (declare-fun r () Bool)\n\
             (declare-fun k (Bool) Int)\n\
             (assert (= r (and p q)))\n\
             (assert (= (k (and p q)) 1))\n\
             (assert (not (= (k r) 1)))\n\
             (check-sat)\n"
        ),
        "unsat"
    );
}

// ------------------------------------------------------------- fix 2: args

/// Two plain Bool variables, both asserted, used as UF arguments: their nodes
/// meet in the canonical true class, so the applications are congruent.
#[test]
fn bool_arguments_with_equal_values_are_congruent() {
    assert_eq!(
        verdict(
            "(set-logic QF_UFLIA)\n\
             (declare-fun p () Bool) (declare-fun q () Bool)\n\
             (declare-fun k (Bool) Int)\n\
             (assert p) (assert q)\n\
             (assert (not (= (k p) (k q))))\n\
             (check-sat)\n"
        ),
        "unsat"
    );
}

/// The polarity fold: `(not p)` as an argument encodes to `p`'s variable with
/// a NEGATIVE literal, so the watch must flip. `p` false makes `(not p)` true,
/// which puts it in `q`'s (true) class.
#[test]
fn negated_bool_argument_folds_polarity() {
    assert_eq!(
        verdict(
            "(set-logic QF_UFLIA)\n\
             (declare-fun p () Bool) (declare-fun q () Bool)\n\
             (declare-fun k (Bool) Int)\n\
             (assert (not p)) (assert q)\n\
             (assert (not (= (k (not p)) (k q))))\n\
             (check-sat)\n"
        ),
        "unsat"
    );
}

/// The two value routes must land in ONE class: `b` reaches true through an
/// equality with the LITERAL `true` (the `TermKind::True` intern path), `q`
/// through a `BoolValue` watch (the canonical-node path). If the literal
/// interned as a private leaf — as it used to — the two "true"s never meet and
/// `f(b) = f(q)` is missed.
#[test]
fn the_true_literal_and_a_true_assignment_share_one_class() {
    assert_eq!(
        verdict(
            "(set-logic QF_UFLIA)\n\
             (declare-fun b () Bool) (declare-fun q () Bool)\n\
             (declare-fun f (Bool) Int)\n\
             (assert (= b true))\n\
             (assert q)\n\
             (assert (not (= (f b) (f q))))\n\
             (check-sat)\n"
        ),
        "unsat"
    );
}

// ---------------------------------------------- soundness (anti-over-merge)

/// Opposite values must NOT be congruent: `p` true, `q` false leaves `k(p)` and
/// `k(q)` unrelated, and the disequality is satisfiable. An implementation
/// that merges every watched Bool argument into one class fails here with a
/// false `unsat` — the fatal direction.
#[test]
fn bool_arguments_with_opposite_values_stay_apart() {
    assert_eq!(
        verdict(
            "(set-logic QF_UFLIA)\n\
             (declare-fun p () Bool) (declare-fun q () Bool)\n\
             (declare-fun k (Bool) Int)\n\
             (assert p) (assert (not q))\n\
             (assert (not (= (k p) (k q))))\n\
             (check-sat)\n"
        ),
        "sat"
    );
}

/// A FALSE Bool equality is only a disequality, never a merge: `h` may still
/// map the two (distinct) Bools to one value.
#[test]
fn a_false_bool_equality_does_not_force_the_images_apart() {
    assert_eq!(
        verdict(
            "(set-logic QF_UFLIA)\n\
             (declare-fun b1 () Bool) (declare-fun b2 () Bool)\n\
             (declare-fun h (Bool) Int)\n\
             (assert (not (= b1 b2)))\n\
             (assert (= (h b1) (h b2)))\n\
             (check-sat)\n"
        ),
        "sat"
    );
}

/// Bool disequality alone is satisfiable — the two-valued domain admits it.
/// (With a THIRD mutually-disequal Bool it would not; that pigeonhole is
/// beyond plain EUF and stays with the SAT core, which decides it through the
/// iff gates.)
#[test]
fn a_single_bool_disequality_is_satisfiable() {
    assert_eq!(
        verdict(
            "(set-logic QF_UF)\n\
             (declare-fun p () Bool) (declare-fun q () Bool)\n\
             (assert (not (= p q)))\n\
             (check-sat)\n"
        ),
        "sat"
    );
}
