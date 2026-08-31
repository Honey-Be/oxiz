// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors

//! #434 — the Nelson-Oppen ARRANGEMENT obligation, closed by Ackermann lemmas.
//!
//! `model_based_combination` caught only one direction: EUF says two shared
//! terms are equal while arithmetic gives them different values. The other
//! direction was open — the arithmetic model gives `x1` and `3` the same value
//! and nothing tells EUF, so `(f0 x1)` and `(f0 3)` were free to differ and the
//! reported "model" was not a FUNCTION.
//!
//! The repair is NOT to propagate the equality the model exhibits: that value
//! is CHOSEN rather than entailed, and merging on it fabricates refutations
//! (measured, 2 per 200 seeds, when `persist_const_index` did exactly that).
//! It is to add the congruence CLAUSE
//!
//! ```text
//! (a₁ ≠ b₁) ∨ … ∨ (aₙ ≠ bₙ) ∨ (f(a⃗) = f(b⃗))
//! ```
//!
//! which is valid in first-order logic with equality. It holds in every model,
//! so it cannot turn a satisfiable problem unsatisfiable — the model's only job
//! is choosing WHICH pair is worth a lemma, and being wrong about that costs a
//! useless clause, never a verdict.

use oxiz_solver::Context;

/// Every test in this file takes this lock.
///
/// `the_kill_switch_restores_the_open_behaviour` sets `OXIZ_NO_ACKERMANN`,
/// which is PROCESS-GLOBAL — with the default parallel harness the other tests
/// observed it mid-run and reported `sat` on shapes that are `unsat`. The
/// failure looked like a broken fix and was a broken test. Serializing the file
/// is cheap (every script here decides in milliseconds) and makes the hazard
/// structural rather than a thing to remember.
static SERIAL: std::sync::Mutex<()> = std::sync::Mutex::new(());

fn guard() -> std::sync::MutexGuard<'static, ()> {
    SERIAL.lock().unwrap_or_else(|e| e.into_inner())
}

fn verdict(script: &str) -> String {
    let mut ctx = Context::new();
    let out = ctx.execute_script(script).expect("script parses");
    out.iter()
        .map(|l| l.trim())
        .find(|l| matches!(*l, "sat" | "unsat" | "unknown"))
        .unwrap_or("no-verdict")
        .to_owned()
}

/// The #434 minimal repro. `x0 ∈ [3,4]` and `x0 = x1 + 1` leave `x1 ∈ [2,3]`;
/// `f0(2) = f0(3) = a` and `f0(x1) = b ≠ a` is then unsatisfiable whichever
/// value `x1` takes — but only if something forces `f0(x1)` to agree with the
/// application whose argument it equals. z3 and cvc5: `unsat`.
#[test]
fn the_arrangement_over_a_model_chosen_value_is_discharged() {
    let _g = guard();
    let s = r"
(set-logic QF_UFLIA)
(declare-fun x0 () Int) (declare-fun x1 () Int)
(declare-fun a () Int) (declare-fun b () Int)
(declare-fun f0 (Int) Int)
(assert (<= 3 x0)) (assert (<= x0 4))
(assert (= x0 (+ x1 1)))
(assert (= (f0 2) a)) (assert (= (f0 3) a))
(assert (= (f0 x1) b))
(assert (not (= a b)))
(check-sat)
";
    assert_eq!(verdict(s), "unsat");
}

/// TWO ROUNDS ARE REQUIRED, and that is the point of doing this lazily. The
/// first model picks one value for `x1` and earns one lemma; the solver then
/// moves `x1` to the other value, which earns the second. An implementation
/// that emitted only the first pair, or that stopped after one round, reports
/// `sat` here.
///
/// The bounds on `x1` are DERIVED (through `x0 = x1 + 1`) rather than asserted,
/// which is what keeps #433's case split out of it — the split reads the
/// assert-time unit-bound journal, so it never sees `x1`. Verified by
/// attribution: `OXIZ_NO_ACKERMANN=1` answers `sat` on this shape while
/// `OXIZ_NO_INT_CASE_SPLIT=1` still answers `unsat`.
#[test]
fn a_second_value_earns_a_second_lemma() {
    let _g = guard();
    let s = r"
(set-logic QF_UFLIA)
(declare-fun x0 () Int) (declare-fun x1 () Int)
(declare-fun a () Int) (declare-fun b () Int)
(declare-fun f (Int) Int)
(assert (<= 6 x0)) (assert (<= x0 7))
(assert (= x0 (+ x1 1)))
(assert (= (f 5) a)) (assert (= (f 6) a))
(assert (= (f x1) b))
(assert (not (= a b)))
(check-sat)
";
    assert_eq!(verdict(s), "unsat");
}

/// ANTI-OVER-FIRING, the direction that would be a false proof. The same
/// derived-bound shape with `a` and `b` free to be equal is SATISFIABLE, and
/// the lemmas — being valid — must leave it that way. An Ackermannization that
/// asserted the CONCLUSION instead of the clause would report `unsat` here.
/// z3 and cvc5 both say `sat`.
#[test]
fn a_satisfiable_arrangement_stays_satisfiable() {
    let _g = guard();
    let s = r"
(set-logic QF_UFLIA)
(declare-fun x0 () Int) (declare-fun x1 () Int)
(declare-fun a () Int) (declare-fun b () Int)
(declare-fun f0 (Int) Int)
(assert (<= 3 x0)) (assert (<= x0 4))
(assert (= x0 (+ x1 1)))
(assert (= (f0 2) a)) (assert (= (f0 3) a))
(assert (= (f0 x1) b))
(check-sat)
";
    assert_eq!(verdict(s), "sat");
}

/// The arguments genuinely DIFFER in every model, so no lemma may collapse the
/// applications: `f(1)` and `f(2)` are unrelated and `f(1) ≠ f(2)` is
/// satisfiable. A filter that Ackermannized on syntactic shape rather than on
/// model agreement would break this.
#[test]
fn applications_with_different_arguments_are_not_forced_equal() {
    let _g = guard();
    let s = r"
(set-logic QF_UFLIA)
(declare-fun f (Int) Int)
(assert (not (= (f 1) (f 2))))
(check-sat)
";
    assert_eq!(verdict(s), "sat");
}

/// The control from the #434 triage: the same shape with the shared variable
/// bounded DIRECTLY is what #433's case split already closed. It must stay
/// closed — the new lemma path runs AFTER the split and must not disturb it.
/// Either mechanism suffices here, which is exactly why it cannot serve as an
/// Ackermann test and is kept only as a no-regression control.
#[test]
fn the_directly_bounded_control_is_still_closed() {
    let _g = guard();
    let s = r"
(set-logic QF_UFLIA)
(declare-fun x () Int)
(declare-fun a () Int) (declare-fun b () Int)
(declare-fun f (Int) Int)
(assert (= x 3))
(assert (= (f 3) a))
(assert (= (f x) b))
(assert (not (= a b)))
(check-sat)
";
    assert_eq!(verdict(s), "unsat");
}

/// Multi-argument applications: the lemma's antecedent is a DISJUNCTION over
/// every argument position, so a two-place function needs both pairs. Derived
/// bounds again, so the split is out of it (`OXIZ_NO_ACKERMANN=1` -> `sat`).
#[test]
fn a_two_argument_application_is_discharged() {
    let _g = guard();
    let s = r"
(set-logic QF_UFLIA)
(declare-fun x0 () Int) (declare-fun x () Int) (declare-fun y () Int)
(declare-fun a () Int) (declare-fun b () Int)
(declare-fun g (Int Int) Int)
(assert (<= 2 x0)) (assert (<= x0 3))
(assert (= x0 (+ x 1)))
(assert (= y 7))
(assert (= (g 1 7) a)) (assert (= (g 2 7) a))
(assert (= (g x y) b))
(assert (not (= a b)))
(check-sat)
";
    assert_eq!(verdict(s), "unsat");
}

/// The kill-switch restores the pre-#434 behaviour, so the corpus effect can be
/// attributed by A/B rather than argued. It uses the DERIVED-bound shape for
/// the same reason the tests above do: on a shape #433's case split also
/// closes, turning the lemmas off changes nothing and the switch would look
/// broken when it is merely redundant. Guarded by a serial lock because it
/// mutates process-global state.
#[test]
fn the_kill_switch_restores_the_open_behaviour() {
    let _g = guard();
    let s = r"
(set-logic QF_UFLIA)
(declare-fun x0 () Int) (declare-fun x1 () Int)
(declare-fun a () Int) (declare-fun b () Int)
(declare-fun f0 (Int) Int)
(assert (<= 3 x0)) (assert (<= x0 4))
(assert (= x0 (+ x1 1)))
(assert (= (f0 2) a)) (assert (= (f0 3) a))
(assert (= (f0 x1) b))
(assert (not (= a b)))
(check-sat)
";
    // SAFETY: single-threaded within the lock; no other test reads this var.
    unsafe { std::env::set_var("OXIZ_NO_ACKERMANN", "1") };
    let off = verdict(s);
    unsafe { std::env::remove_var("OXIZ_NO_ACKERMANN") };
    assert_eq!(off, "sat", "with the lemmas off, #434 is open again");
    assert_eq!(verdict(s), "unsat", "and on again with them back");
}
