// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors

//! #433 (3 of 3) — the non-convex arith⇄EUF combination gap.
//!
//! `1 <= x <= 2` with `f(1) = f(2) = a` entails `f(x) = a`, but no SINGLE
//! value of `x` is entailed, so the fixed-value Nelson-Oppen propagation never
//! fires and `(not (= (f x) a))` reported `sat`. The fix asserts, before
//! accepting a model, the LIA tautology `bounds ⇒ (x = lo ∨ … ∨ x = hi)` for
//! every EUF-shared integer term whose ASSERTED unit-atom bounds pin a span of
//! at most 12, then re-solves; whichever disjunct the SAT core picks makes the
//! term FIXED, which the existing propagation carries into EUF.
//!
//! The clause is CONDITIONAL on the bound atoms in their model polarity, so it
//! is valid on every branch — the scope-locality test below is the pin for
//! that. Bounds come from an assert-time unit-bound journal
//! (`ArithSolver::unit_bounds`), because the simplex holds every constraint
//! through a slack variable and cannot answer "the asserted bounds of x";
//! the journal is truncate-rolled on `pop` (the pop-scrub rule).

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

/// Collect every check-sat verdict, for the incremental tests.
fn verdicts(script: &str) -> Vec<String> {
    let mut ctx = Context::new();
    let out = ctx.execute_script(script).expect("script parses");
    out.iter()
        .map(|l| l.trim())
        .filter(|l| matches!(*l, "sat" | "unsat" | "unknown"))
        .map(str::to_owned)
        .collect()
}

/// The reported shape (battery 05).
#[test]
fn a_two_point_span_reaches_congruence() {
    assert_eq!(
        verdict(
            "(set-logic QF_UFLIA)\n\
             (declare-fun x () Int) (declare-fun a () Int)\n\
             (declare-fun f (Int) Int)\n\
             (assert (<= 1 x)) (assert (<= x 2))\n\
             (assert (= (f 1) a)) (assert (= (f 2) a))\n\
             (assert (not (= (f x) a)))\n\
             (check-sat)\n"
        ),
        "unsat"
    );
}

/// A wider (but in-cap) span, and the images only PARTIALLY agree — the model
/// must be allowed to pick the value whose image differs. Anti-over-merge: a
/// split that forced all images equal would answer `unsat`.
#[test]
fn a_partially_agreeing_span_stays_sat() {
    assert_eq!(
        verdict(
            "(set-logic QF_UFLIA)\n\
             (declare-fun x () Int) (declare-fun a () Int)\n\
             (declare-fun f (Int) Int)\n\
             (assert (<= 1 x)) (assert (<= x 3))\n\
             (assert (= (f 1) a)) (assert (= (f 2) a))\n\
             (assert (not (= (f 3) a)))\n\
             (assert (not (= (f x) a)))\n\
             (check-sat)\n"
        ),
        "sat"
    );
}

/// SCOPE LOCALITY — the pin that the split clause is CONDITIONAL on its bound
/// atoms rather than an unconditional fact smuggled out of one branch. The
/// bounds live inside a `push`/`pop`; after the `pop`, `x = 5` must be
/// satisfiable. An unconditional `(or (= x 1) (= x 2))` would survive the pop
/// (learned clauses do) and wrongly forbid it.
#[test]
fn the_split_clause_does_not_leak_across_pop() {
    assert_eq!(
        verdicts(
            "(set-logic QF_UFLIA)\n\
             (declare-fun x () Int) (declare-fun a () Int)\n\
             (declare-fun f (Int) Int)\n\
             (assert (= (f 1) a)) (assert (= (f 2) a))\n\
             (push 1)\n\
             (assert (<= 1 x)) (assert (<= x 2))\n\
             (assert (not (= (f x) a)))\n\
             (check-sat)\n\
             (pop 1)\n\
             (assert (= x 5))\n\
             (check-sat)\n"
        ),
        vec!["unsat".to_owned(), "sat".to_owned()]
    );
}

/// The negative-atom polarity fold: here the UPPER bound comes from a
/// NEGATIVELY-assigned atom (`(not (<= 3 x))` is `x <= 2`), so the clause's
/// condition literal must be the atom in its false polarity. Getting the
/// polarity wrong makes the clause unsatisfied by the very model that
/// produced it, which shows up as a wrong verdict in one direction or the
/// other.
#[test]
fn a_bound_from_a_negated_atom_still_splits() {
    assert_eq!(
        verdict(
            "(set-logic QF_UFLIA)\n\
             (declare-fun x () Int) (declare-fun a () Int)\n\
             (declare-fun f (Int) Int)\n\
             (assert (<= 1 x)) (assert (not (<= 3 x)))\n\
             (assert (= (f 1) a)) (assert (= (f 2) a))\n\
             (assert (not (= (f x) a)))\n\
             (check-sat)\n"
        ),
        "unsat"
    );
}

/// Out-of-cap spans are out of scope BY DESIGN (span 12 cap): a 200-wide span
/// must not be enumerated. The verdict stays `sat` — incomplete in the sound
/// direction — and, more to the point for this pin, the solve must not take
/// the time a 200-way enumeration would.
#[test]
fn a_wide_span_is_not_enumerated() {
    assert_eq!(
        verdict(
            "(set-logic QF_UFLIA)\n\
             (declare-fun x () Int) (declare-fun a () Int)\n\
             (declare-fun f (Int) Int)\n\
             (assert (<= 0 x)) (assert (<= x 200))\n\
             (assert (= (f 0) a)) (assert (= (f 200) a))\n\
             (assert (not (= (f x) a)))\n\
             (check-sat)\n"
        ),
        "sat"
    );
}

/// The kill-switch restores the historical (gap) behaviour — proven by the
/// repro REGRESSING under it. Runs the env-touching case in-process, so it is
/// `#[ignore]`d for the serial pass like every other env-mutating test.
#[test]
#[ignore]
fn the_kill_switch_restores_the_gap() {
    unsafe { std::env::set_var("OXIZ_NO_INT_CASE_SPLIT", "1") };
    let v = verdict(
        "(set-logic QF_UFLIA)\n\
         (declare-fun x () Int) (declare-fun a () Int)\n\
         (declare-fun f (Int) Int)\n\
         (assert (<= 1 x)) (assert (<= x 2))\n\
         (assert (= (f 1) a)) (assert (= (f 2) a))\n\
         (assert (not (= (f x) a)))\n\
         (check-sat)\n",
    );
    unsafe { std::env::remove_var("OXIZ_NO_INT_CASE_SPLIT") };
    assert_eq!(v, "sat", "the switch must reach the historical behaviour");
}
