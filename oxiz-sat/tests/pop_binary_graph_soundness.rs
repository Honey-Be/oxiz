//! Regression (audit 2026-06-20): `Solver::pop` must detach a popped clause's
//! binary-implication edges (and watchers) BEFORE freeing its id, else the next
//! `add_clause` recycles the id (clearing `deleted`) and the stale binary edge —
//! which `propagate` consumes with NO deleted-clause guard — keeps firing under
//! the recycled clause, fabricating a conflict → a spurious UNSAT (a false proof
//! for any consumer that reads `unsat` as "discharged"). Companion to the
//! `forget_learned_since` watcher fix (`bv_mul_aux_disjunction_const_is_sat_8bit`),
//! now extended to the binary graph + the `pop` path.

use oxiz_sat::{Lit, Solver, SolverResult};

#[test]
fn pop_scrubs_binary_graph_no_spurious_unsat() {
    let mut sat = Solver::new();
    let x = sat.new_var();
    let a = sat.new_var();

    sat.push();
    // (¬x ∨ a): the binary implication graph records `x ⇒ a`. This clause is
    // removed by the pop below — and its id will be recycled by the next add.
    sat.add_clause([Lit::neg(x), Lit::pos(a)]);
    sat.pop();

    // The `(¬x ∨ a)` constraint is now GONE. Recycle its id with fresh units and
    // assert a model the stale edge would forbid: x = true, a = false. `x ∧ ¬a`
    // with NO clause linking them is SAT; a surviving `x ⇒ a` edge would
    // propagate `a = true` and clash with `¬a` → a spurious UNSAT.
    sat.add_clause([Lit::pos(x)]);
    sat.add_clause([Lit::neg(a)]);

    assert_eq!(
        sat.solve(),
        SolverResult::Sat,
        "x ∧ ¬a is SAT after (¬x ∨ a) was popped — a stale binary implication \
         edge from the popped clause would fabricate a spurious unsat"
    );
}

#[test]
fn repeated_push_binary_pop_cycles_stay_sound() {
    // Stress the recycle path: many push/binary/pop cycles, each followed by a
    // satisfiable query that a leaked edge from a prior cycle could break.
    let mut sat = Solver::new();
    let x = sat.new_var();
    let y = sat.new_var();

    for _ in 0..8 {
        sat.push();
        sat.add_clause([Lit::neg(x), Lit::pos(y)]); // x ⇒ y, then dropped
        sat.pop();
    }
    // x ∧ ¬y is SAT once every (¬x ∨ y) is gone.
    sat.add_clause([Lit::pos(x)]);
    sat.add_clause([Lit::neg(y)]);
    assert_eq!(
        sat.solve(),
        SolverResult::Sat,
        "repeated popped binary clauses must not leak edges into a spurious unsat"
    );
}
