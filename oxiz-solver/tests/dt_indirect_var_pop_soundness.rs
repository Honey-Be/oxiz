//! Push/pop soundness regressions for #418 item 2 — the check-sat-wide
//! indirect-variable selector/tester reduction pass
//! (`encode.rs::add_dt_indirect_var_reduction_axioms`, wired from
//! `mod.rs::check_level`).
//!
//! Unlike the direct structural passes (`add_dt_selector_reduction_axioms`/
//! `_tester_`), which run once per assertion at encode time, this pass reruns
//! EVERY check-sat over the CURRENT `var_ctor_bindings` map (built fresh each
//! time by `check_dt.rs::collect_var_ctor_bindings`). A binding established
//! inside a `push`ed scope (e.g. `z = (cons x y)`) must not leave behind a
//! SAT-level unit clause (`(hd z) = x`) that survives the matching `pop` —
//! that clause must die with the underlying SAT solver's own `pop()`
//! (`Solver::pop` calls `self.sat.pop()` 1:1 with `Solver::push`), and the
//! `dt_selector_reduced`/`dt_tester_reduced` dedup markers this pass reuses
//! must be dropped in lock-step (via the SAME `TrailOp::DtSelectorReduced`/
//! `DtTesterReduced` the direct passes already use) so a later, unrelated
//! scope's re-assertion of the SAME selector/tester term is free to be
//! re-derived from scratch rather than skipped as "already handled".

use oxiz_solver::Context;

fn verdicts(script: &str) -> Vec<String> {
    let mut ctx = Context::new();
    ctx.set_timeout_ms(5000);
    match ctx.execute_script(script) {
        Ok(out) => out
            .iter()
            .filter_map(|l| match l.trim() {
                "sat" => Some("sat".to_string()),
                "unsat" => Some("unsat".to_string()),
                "unknown" => Some("unknown".to_string()),
                _ => None,
            })
            .collect(),
        Err(_) => vec![],
    }
}

const LST_DT: &str = "(set-logic ALL)\n\
     (declare-datatypes ((Lst 0)) (((nil) (cons (hd Int) (tl Lst)))))\n\
     (declare-const x Int) (declare-const y Lst) (declare-const z Lst)\n";

/// Exact repro: a `push`ed scope establishes `z = (cons x y)` and asserts
/// `(hd z) != x` — correctly `unsat` (item 2). After `pop`, the SAME
/// disequality is re-asserted with NO binding for `z` in scope: this must be
/// `sat` (z3 agrees) — if the injected unit clause `(hd z) = x` had survived
/// the pop (a stale-clause leak), this would wrongly read `unsat`.
#[test]
fn popped_indirect_binding_selector_axiom_does_not_leak_into_later_scope() {
    let v = verdicts(&format!(
        "{LST_DT}\
         (push 1)\n\
         (assert (= z (cons x y)))\n\
         (assert (not (= (hd z) x)))\n\
         (check-sat)\n\
         (pop 1)\n\
         (assert (not (= (hd z) x)))\n\
         (check-sat)\n"
    ));
    assert_eq!(
        v,
        vec!["unsat".to_string(), "sat".to_string()],
        "the popped `z = cons(x,y)`-derived selector axiom must not survive \
         to conflict with the SAME `(hd z) != x` disequality reasserted in \
         a later, unrelated (binding-free) scope"
    );
}

/// TESTER analogue of the selector leak check above.
#[test]
fn popped_indirect_binding_tester_axiom_does_not_leak_into_later_scope() {
    let v = verdicts(&format!(
        "{LST_DT}\
         (push 1)\n\
         (assert (= z (cons x y)))\n\
         (assert (not ((_ is cons) z)))\n\
         (check-sat)\n\
         (pop 1)\n\
         (assert (not ((_ is cons) z)))\n\
         (check-sat)\n"
    ));
    assert_eq!(
        v,
        vec!["unsat".to_string(), "sat".to_string()],
        "the popped `z = cons(x,y)`-derived tester axiom must not survive \
         to conflict with the SAME `(not (is-cons z))` reasserted in a \
         later, unrelated (binding-free) scope"
    );
}

/// After the pop, re-establish a DIFFERENT (and still consistent) binding
/// for the SAME variable (`z = nil`) and confirm the freshly-derived facts
/// are the ones that hold — `(hd z)` stays fully unconstrained (`nil` has no
/// `hd` field), so both a concrete assignment and its negation stay `sat`.
#[test]
fn popped_indirect_binding_replaced_by_different_ctor_in_later_scope() {
    let v = verdicts(&format!(
        "{LST_DT}\
         (push 1)\n\
         (assert (= z (cons x y)))\n\
         (assert (not (= (hd z) x)))\n\
         (check-sat)\n\
         (pop 1)\n\
         (assert (= z nil))\n\
         (assert (= (hd z) 5))\n\
         (check-sat)\n"
    ));
    assert_eq!(
        v,
        vec!["unsat".to_string(), "sat".to_string()],
        "a fresh, unrelated `z = nil` binding in a later scope must leave \
         `(hd z)` unconstrained, not inherit the popped scope's `cons` \
         reduction axiom"
    );
}

/// A binding genuinely spanning a push (asserted BEFORE the push and never
/// popped) must still be usable for reduction INSIDE the pushed scope —
/// only a POPPED binding should stop mattering, not a still-active outer
/// one. Mirrors `dt_var_constructors_pop_soundness.rs`'s analogous control.
#[test]
fn indirect_binding_across_active_push_still_reduces() {
    let v = verdicts(&format!(
        "{LST_DT}\
         (assert (= z (cons x y)))\n\
         (push 1)\n\
         (assert (not (= (hd z) x)))\n\
         (check-sat)\n"
    ));
    assert_eq!(
        v,
        vec!["unsat".to_string()],
        "the outer (unpopped) `z = cons(x,y)` binding is still active \
         inside the pushed scope and must still drive the selector \
         reduction"
    );
}

/// Idempotency control: re-running `check-sat` multiple times in the SAME
/// scope with the SAME binding must not duplicate clauses or otherwise
/// misbehave (the pass is designed to be safe to re-run every check-sat).
#[test]
fn indirect_binding_reduction_is_idempotent_across_repeated_check_sat() {
    let v = verdicts(&format!(
        "{LST_DT}\
         (assert (= z (cons x y)))\n\
         (check-sat)\n\
         (check-sat)\n\
         (assert (not (= (hd z) x)))\n\
         (check-sat)\n\
         (check-sat)\n"
    ));
    assert_eq!(
        v,
        vec![
            "sat".to_string(),
            "sat".to_string(),
            "unsat".to_string(),
            "unsat".to_string(),
        ],
        "repeated check-sat calls over the same (or monotonically growing) \
         assertion set must be stable and idempotent"
    );
}
