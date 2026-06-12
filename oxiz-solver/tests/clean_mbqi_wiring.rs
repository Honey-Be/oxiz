//! M4e end-to-end wiring tests: drive the FULL `Solver` (CDCL(T) + the clean
//! quantifier engine) with `config.clean_mbqi = true`, over the shapes that
//! made the legacy MBQI report a spurious `unsat`.
//!
//! The gate is soundness: a satisfiable formula must NEVER come back `Unsat`
//! (the verus-fork prelude gate is exactly "not unsat"; `Unknown` is fine).
//! The last test confirms the engine still produces a GENUINE `Unsat` via
//! conflict-driven instantiation — it is not merely "always Unknown".

use oxiz_core::ast::TermManager;
use oxiz_solver::{Solver, SolverConfig, SolverResult};

fn clean_solver() -> Solver {
    let mut config = SolverConfig::default();
    config.clean_mbqi = true;
    Solver::with_config(config)
}

#[test]
fn selfmatch_pattern_is_not_unsat() {
    // ∀x:Int. f(x)=g(x)  :pattern (f x).   No ground f(_) anywhere.
    // The legacy e-matcher could self-match the body (bug B: {x↦x}); the clean
    // engine's candidates come only from the ground index (which never holds a
    // body subterm), so it emits ZERO instances and the formula stays SAT.
    let mut s = clean_solver();
    let mut m = TermManager::new();
    let int = m.sorts.int_sort;
    let bool_s = m.sorts.bool_sort;

    let x = m.mk_var("x", int);
    let fx = m.mk_apply("f", [x], int);
    let gx = m.mk_apply("g", [x], int);
    let body = m.mk_eq(fx, gx);
    let q = m.mk_forall_with_patterns([("x", int)], body, [[fx]]);
    let _ = bool_s;
    s.assert(q, &mut m);

    let r = s.check(&mut m);
    assert_ne!(r, SolverResult::Unsat, "self-match must not drive unsat");
}

#[test]
fn trigger_free_empty_domain_is_not_unsat() {
    // ∀x y:Int. height_lt(x,y) = (po(x,y) ∧ ¬(x=y))   — the verus partial-order
    // shape: trigger-free, with NO ground terms of the quantified sort. The
    // legacy MBQI fabricated a witness grid (bug D) and reported a spurious
    // `unsat`. The clean engine has no real candidate to enumerate, cannot
    // model-verify the axiom (eval_forall = None), and returns the SOUND
    // `Unknown` — never `Unsat`.
    let mut s = clean_solver();
    let mut m = TermManager::new();
    let int = m.sorts.int_sort;
    let bool_s = m.sorts.bool_sort;

    let x = m.mk_var("x", int);
    let y = m.mk_var("y", int);
    let lt = m.mk_apply("height_lt", [x, y], bool_s);
    let po = m.mk_apply("po", [x, y], bool_s);
    let eq = m.mk_eq(x, y);
    let neq = m.mk_not(eq);
    let conj = m.mk_and([po, neq]);
    let body = m.mk_eq(lt, conj);
    let q = m.mk_forall([("x", int), ("y", int)], body);
    s.assert(q, &mut m);

    let r = s.check(&mut m);
    assert_ne!(
        r,
        SolverResult::Unsat,
        "trigger-free axiom over an empty domain must not be unsat"
    );
}

#[test]
fn ground_match_is_satisfiable_not_unsat() {
    // P(0), P(1), and ∀x:Int. P(x). The quantifier is consistent with the
    // ground facts; the clean engine instantiates only at the real ground
    // ints (0, 1) and must not refute the model.
    let mut s = clean_solver();
    let mut m = TermManager::new();
    let int = m.sorts.int_sort;
    let bool_s = m.sorts.bool_sort;

    let zero = m.mk_int(0);
    let one = m.mk_int(1);
    let p0 = m.mk_apply("P", [zero], bool_s);
    let p1 = m.mk_apply("P", [one], bool_s);
    s.assert(p0, &mut m);
    s.assert(p1, &mut m);

    let x = m.mk_var("x", int);
    let px = m.mk_apply("P", [x], bool_s);
    let q = m.mk_forall([("x", int)], px);
    s.assert(q, &mut m);

    let r = s.check(&mut m);
    assert_ne!(r, SolverResult::Unsat, "consistent ground facts: not unsat");
}

#[test]
fn genuine_conflict_is_unsat() {
    // ¬P(c) ∧ ∀x:Int. P(x).  Instantiating the quantifier at the real ground
    // constant `c` yields P(c), contradicting ¬P(c). The clean engine emits
    // the guarded instance Q ⇒ P(c) (via CDQI / enumeration over the ground
    // index), and the ground core derives the GENUINE `Unsat`. This proves the
    // engine is sound in BOTH directions — it is not merely conservative.
    let mut s = clean_solver();
    let mut m = TermManager::new();
    let int = m.sorts.int_sort;
    let bool_s = m.sorts.bool_sort;

    let c = m.mk_apply("c", [], int); // ground constant c:Int
    let pc = m.mk_apply("P", [c], bool_s);
    let not_pc = m.mk_not(pc);
    s.assert(not_pc, &mut m);

    let x = m.mk_var("x", int);
    let px = m.mk_apply("P", [x], bool_s);
    let q = m.mk_forall([("x", int)], px);
    s.assert(q, &mut m);

    let r = s.check(&mut m);
    assert_eq!(
        r,
        SolverResult::Unsat,
        "∀x.P(x) instantiated at c contradicts ¬P(c)"
    );
}

#[test]
fn injective_no_bounds_is_not_unsat() {
    // ∀x y:Int. f(x)=f(y) ⇒ x=y   (injectivity) ∧ f(1)=10 ∧ f(2)=20.
    // SATISFIABLE (an injective f with those values exists). The clean engine's
    // instantiation over ground terms drives OxiZ's INCREMENTAL CDCL(T) into a
    // spurious `unsat` (the same clause set solved single-shot is sound). The
    // unsat-verification backstop re-solves {facts ∪ ground instances} fresh,
    // finds it satisfiable, and returns the SOUND `Unknown` — never the
    // spurious `unsat`. Regression for the incremental-divergence class.
    let mut s = clean_solver();
    let mut m = TermManager::new();
    let int = m.sorts.int_sort;

    let x = m.mk_var("x", int);
    let y = m.mk_var("y", int);
    let fx = m.mk_apply("f", [x], int);
    let fy = m.mk_apply("f", [y], int);
    let feq = m.mk_eq(fx, fy);
    let xeqy = m.mk_eq(x, y);
    let body = m.mk_implies(feq, xeqy);
    let q = m.mk_forall([("x", int), ("y", int)], body);
    s.assert(q, &mut m);

    let one = m.mk_int(1);
    let f1 = m.mk_apply("f", [one], int);
    let ten = m.mk_int(10);
    let e1 = m.mk_eq(f1, ten);
    s.assert(e1, &mut m);
    let two = m.mk_int(2);
    let f2 = m.mk_apply("f", [two], int);
    let twenty = m.mk_int(20);
    let e2 = m.mk_eq(f2, twenty);
    s.assert(e2, &mut m);

    let r = s.check(&mut m);
    assert_ne!(
        r,
        SolverResult::Unsat,
        "injective f with f(1)=10, f(2)=20 is satisfiable — must not be unsat"
    );
}
