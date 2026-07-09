//! Regression (found 2026-07-09 during #406 adversarial review): the
//! `dt_var_constructors` cache — a "datatype variable was equated to
//! constructor C" mutual-exclusivity table used by `Solver::assert`/
//! `assert_named` to flag `x = C1(...)` followed by `x = C2(...)` as an
//! immediate ground conflict — was populated at assert-time but was NEVER
//! trail-undone on `pop()` (no `TrailOp` variant referenced it; the only
//! place it was ever cleared was the full-context `Solver::clear()`).
//!
//! Consequence: a binding recorded inside a `push`ed scope survived the
//! matching `pop`, so a later, unrelated scope's fresh constructor
//! assignment to the SAME variable was wrongly compared against the stale
//! one and reported as conflicting — manufacturing a spurious `unsat`.
//!
//! This is the same recurring bug class already fixed twice this session
//! (oxiz-sat's `reduce_clause_database` clause-id-recycle stale-watcher fix,
//! and the `forget_learned_since`/`binary_graph` fix it mirrors): a
//! solver-side cache mutated at assert/encode time that isn't scrubbed by
//! the trail on `pop()`.
//!
//! Fixed by adding `TrailOp::DtVarConstructorAdded { var }`, pushed at the
//! same site `dt_var_constructors` is populated (`encode.rs`), undone in the
//! trail-undo match in `mod.rs` (mirrors `DtCoverAdded`/`DtSelectorReduced`/
//! `DtTesterReduced`'s existing pattern exactly).

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
     (declare-const a Int) (declare-const b Lst) (declare-const y Lst)\n";

/// Exact repro: a `push`ed scope binds `y` to `cons(a,b)`; after `pop`, a
/// fresh, unrelated binding of `y` to `nil` must NOT be compared against the
/// popped scope's stale binding. z3 agrees both `check-sat` calls are `sat`.
#[test]
fn popped_ctor_binding_does_not_leak_into_later_scope() {
    let v = verdicts(&format!(
        "{LST_DT}\
         (push 1)\n\
         (assert (= y (cons a b)))\n\
         (check-sat)\n\
         (pop 1)\n\
         (assert (= y nil))\n\
         (check-sat)\n"
    ));
    assert_eq!(
        v,
        vec!["sat".to_string(), "sat".to_string()],
        "the popped `y = cons(a,b)` binding must not survive to conflict \
         with the later, unrelated `y = nil` binding in a fresh scope \
         (dt_var_constructors pop-leak, found during #406 adversarial review)"
    );
}

/// Sanity control: the SAME conflict, both bindings in the SAME scope (no
/// intervening pop), must still be correctly detected as unsat — the fix
/// must not weaken the mutual-exclusivity check itself, only its scoping.
#[test]
fn conflicting_ctor_bindings_in_same_scope_stay_unsat() {
    let v = verdicts(&format!(
        "{LST_DT}\
         (assert (= y (cons a b)))\n\
         (assert (= y nil))\n\
         (check-sat)\n"
    ));
    assert_eq!(
        v,
        vec!["unsat".to_string()],
        "a variable bound to two different constructors in the SAME scope \
         is a genuine conflict and must stay unsat"
    );
}

/// A conflict genuinely spanning a push (the binding is asserted BEFORE the
/// push and never popped) must still be caught — only a POPPED binding
/// should stop mattering, not a still-active outer one.
#[test]
fn conflicting_ctor_binding_across_active_push_stays_unsat() {
    let v = verdicts(&format!(
        "{LST_DT}\
         (assert (= y (cons a b)))\n\
         (push 1)\n\
         (assert (= y nil))\n\
         (check-sat)\n"
    ));
    assert_eq!(
        v,
        vec!["unsat".to_string()],
        "the outer (unpopped) binding is still active and must still \
         conflict with the inner scope's binding"
    );
}
