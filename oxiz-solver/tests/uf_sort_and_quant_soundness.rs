//! Regression tests for the quantifier / EUF soundness bug fixed alongside
//! adsmt rc.36 — see `docs/QUANTIFIER_EMATCH_SOUNDNESS_BUG.md`.
//!
//! Root cause: when a front-end feeds commands to `Context::execute_script`
//! ONE at a time (streaming stdin, or an embedder replaying commands
//! incrementally), each call built a fresh parser whose declared-function
//! table was empty, so a later `(f 3)` defaulted to `Bool` sort. That broke
//! every theory's reasoning about `f(3)`: `(= (f 3) 3)` and `(= (f 3) 4)`
//! were no longer a contradiction, and quantifier instantiation over `Add`
//! produced inverted verdicts. The fix persists the parser symbol tables
//! across `execute_script` calls (`ParserEnv`), pins distinct integer
//! constants apart in EUF on the equality path, and bounds the MBQI loop.
//!
//! These tests drive the solver the way the bug manifested — command by
//! command — and cross-check the verdict against the SMT-LIB semantics
//! (z3 is the reference oracle for each).

use oxiz_solver::{Context, SolverResult};

/// Feed each command to `execute_script` separately (so the parser symbol
/// tables only survive if they are persisted in the `Context`), returning the
/// final `(check-sat)` verdict.
fn solve_streamed(commands: &[&str]) -> SolverResult {
    let mut ctx = Context::new();
    let mut last = SolverResult::Unknown;
    for cmd in commands {
        let out = ctx.execute_script(cmd).expect("execute_script");
        for line in out {
            match line.as_str() {
                "sat" => last = SolverResult::Sat,
                "unsat" => last = SolverResult::Unsat,
                "unknown" => last = SolverResult::Unknown,
                _ => {}
            }
        }
    }
    last
}

#[test]
fn uf_of_int_equated_to_two_distinct_literals_is_unsat() {
    // f(3)=3 ∧ f(3)=4 — f(3) cannot be both 3 and 4. (z3: unsat.)
    // Pre-fix: `sat`, because per-command parsing gave `f(3)` Bool sort.
    let r = solve_streamed(&[
        "(declare-fun f (Int) Int)",
        "(assert (= (f 3) 3))",
        "(assert (= (f 3) 4))",
        "(check-sat)",
    ]);
    assert_eq!(r, SolverResult::Unsat, "f(3)=3 ∧ f(3)=4 must be unsat");
}

#[test]
fn uf_of_int_single_equality_is_sat() {
    let r = solve_streamed(&[
        "(declare-fun f (Int) Int)",
        "(assert (= (f 3) 3))",
        "(check-sat)",
    ]);
    assert_eq!(r, SolverResult::Sat);
}

#[test]
fn nullary_int_function_equated_to_two_literals_is_unsat() {
    // g = 3 ∧ g = 4 with g : Int (nullary declare-fun → constant). (z3: unsat.)
    let r = solve_streamed(&[
        "(declare-fun g () Int)",
        "(assert (= g 3))",
        "(assert (= g 4))",
        "(check-sat)",
    ]);
    assert_eq!(r, SolverResult::Unsat);
}

#[test]
fn uf_of_int_two_distinct_args_is_sat() {
    let r = solve_streamed(&[
        "(declare-fun f (Int) Int)",
        "(assert (= (f 3) 3))",
        "(assert (= (f 4) 4))",
        "(check-sat)",
    ]);
    assert_eq!(r, SolverResult::Sat);
}

#[test]
fn ematching_pattern_axiom_produces_the_conflict() {
    // ∀a. f(a)=a [:pattern (f a)] ∧ f(3)=4 — the trigger instantiates
    // f(3)=3, contradicting f(3)=4. (z3: unsat.) Pre-fix: `sat`.
    let r = solve_streamed(&[
        "(declare-fun f (Int) Int)",
        "(assert (forall ((a Int)) (! (= (f a) a) :pattern ((f a)))))",
        "(assert (= (f 3) 4))",
        "(check-sat)",
    ]);
    assert_eq!(r, SolverResult::Unsat, "e-matching must derive f(3)=3");
}

#[test]
fn ematching_pattern_axiom_consistent_instance_is_sat() {
    // ∀a. f(a)=a ∧ f(3)=3 — consistent. (z3: sat.)
    let r = solve_streamed(&[
        "(declare-fun f (Int) Int)",
        "(assert (forall ((a Int)) (! (= (f a) a) :pattern ((f a)))))",
        "(assert (= (f 3) 3))",
        "(check-sat)",
    ]);
    assert_eq!(r, SolverResult::Sat);
}

#[test]
fn axiomatized_add_consistent_ground_fact_is_sat() {
    // ∀a b. Add(a,b)=a+b [:pattern (Add a b)] ∧ Add(2,3)=5 — the axiom forces
    // Add(2,3)=2+3=5, consistent with the assertion (z3: sat).
    //
    // Pre-fix this returned the UNSOUND `unsat` (a spurious conflict from the
    // quant+LIA path with `Add` mis-sorted as Bool). With the pattern-guided
    // e-matching path (Phase 1) running to a fixpoint and the model-based
    // enumeration skipping trigger-annotated axioms, it now converges to `sat`
    // the way z3 does — no enumeration blow-up.
    let r = solve_streamed(&[
        "(declare-fun Add (Int Int) Int)",
        "(assert (forall ((a Int) (b Int)) (! (= (Add a b) (+ a b)) :pattern ((Add a b)))))",
        "(assert (= (Add 2 3) 5))",
        "(check-sat)",
    ]);
    assert_eq!(r, SolverResult::Sat, "Add(2,3)=5 is consistent with the axiom");
}

#[test]
fn axiomatized_add_genuine_contradiction_is_unsat() {
    // Add(2,3)=6 contradicts Add(2,3)=2+3=5. (z3: unsat.)
    let r = solve_streamed(&[
        "(declare-fun Add (Int Int) Int)",
        "(assert (forall ((a Int) (b Int)) (! (= (Add a b) (+ a b)) :pattern ((Add a b)))))",
        "(assert (= (Add 2 3) 6))",
        "(check-sat)",
    ]);
    assert_eq!(r, SolverResult::Unsat);
}

#[test]
fn axiomatized_add_entailment_with_precondition_is_unsat() {
    // The verus-fork repro: y>0 ∧ x≥0 ∧ ¬(Add(x,y)>0) — with Add(x,y)=x+y this
    // is x+y>0 under x≥0, y>0, so the negation is unsat (the goal is entailed).
    // (z3: unsat.) This is the per-subset entailment check the abductive
    // search delegates.
    let r = solve_streamed(&[
        "(declare-fun Add (Int Int) Int)",
        "(assert (forall ((a Int) (b Int)) (! (= (Add a b) (+ a b)) :pattern ((Add a b)))))",
        "(declare-const x Int)",
        "(declare-const y Int)",
        "(assert (> y 0))",
        "(assert (>= x 0))",
        "(assert (not (> (Add x y) 0)))",
        "(check-sat)",
    ]);
    assert_eq!(r, SolverResult::Unsat);
}

#[test]
fn axiomatized_add_satisfiable_countermodel_is_sat() {
    // y>0 ∧ ¬(Add(x,y)>0) is SAT — x can be ≪ 0, so x+y ≤ 0. This is the
    // abductive search's EMPTY-subset entailment probe (no extra hypothesis):
    // it must NOT report entailment. Pre-fix the model-based MBQI enumerated
    // `Add(v,w)` over the integers without converging (an infinite hang); the
    // pattern-guided path instantiates `Add(x,y)=x+y` once, saturates, and the
    // model is reported `sat` (matching z3) — terminating, and sound.
    let r = solve_streamed(&[
        "(declare-fun Add (Int Int) Int)",
        "(assert (forall ((a Int) (b Int)) (! (= (Add a b) (+ a b)) :pattern ((Add a b)))))",
        "(declare-const x Int)",
        "(declare-const y Int)",
        "(assert (> y 0))",
        "(assert (not (> (Add x y) 0)))",
        "(check-sat)",
    ]);
    assert_eq!(r, SolverResult::Sat, "a countermodel exists (x ≪ 0)");
}
