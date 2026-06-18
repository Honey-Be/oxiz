//! Bounded-guard finite-domain instantiation (clean MBQI).
//!
//! A guarded universal `∀x̄. (lo ≤ x̄ ≤ hi ⇒ φ)` must be instantiated over the
//! FINITE integer range the guard pins, not over every ground `Int` term. The
//! latter makes a `∀m,n` whose body mentions a function `f` instantiate `m,n`
//! across `f`'s own applications → an `f`-of-`f` matching loop. The synthetic
//! `UFLIA/ackermann.smt2` corpus case (bounded positivity `∀m,n.(0≤m≤2 ∧
//! 0≤n≤5) ⇒ ack(m,n)>0`) used to spin at 100% CPU forever; the bounded domain
//! defuses that — it solves in milliseconds with no hang.
//!
//! VERDICT NOTE: the bounded enumeration prevents the hang, but the clean
//! engine does NOT auto-conclude `Sat` from "all bounded instances emitted".
//! An earlier "finite exhaustion ⇒ sat" shortcut trusted the incremental
//! model, which can MISS a GLOBAL conflict among the instances (pigeonhole) and
//! so reported a spurious `sat`. The verdict now defers to `eval_forall`, so a
//! bounded grid the engine cannot model-verify reports the sound `Unknown` —
//! never a guessed `Sat`, and never the spurious `Unsat`.

use oxiz_solver::Context;

#[test]
fn bounded_grid_positivity_terminates_soundly_no_hang() {
    let script = "\
        (set-logic UFLIA)\
        (declare-fun ack (Int Int) Int)\
        (assert (forall ((n Int)) (=> (and (>= n 0) (<= n 5)) (= (ack 0 n) (+ n 1)))))\
        (assert (= (ack 1 0) (ack 0 1)))\
        (assert (= (ack 2 0) (ack 1 1)))\
        (assert (forall ((n Int)) (=> (and (>= n 0) (<= n 3)) (= (ack 1 n) (+ n 2)))))\
        (assert (= (ack 0 0) 1))\
        (assert (= (ack 1 0) 2))\
        (assert (= (ack 1 1) 3))\
        (assert (forall ((m Int) (n Int)) \
            (=> (and (>= m 0) (<= m 2) (>= n 0) (<= n 5)) (> (ack m n) 0))))\
        (check-sat)";
    let mut ctx = Context::new();
    ctx.set_clean_mbqi(true);
    ctx.set_timeout_ms(2000);
    let out = ctx.execute_script(script).expect("script runs");
    let verdict = out.iter().rev().find_map(|l| match l.trim() {
        "sat" => Some("sat"),
        "unsat" => Some("unsat"),
        "unknown" => Some("unknown"),
        _ => None,
    });
    // z3: sat. The bounded enumeration must terminate (no `f`-tower hang) and be
    // SOUND: the clean engine reports `Unknown` here (it cannot model-verify the
    // bounded monotonicity grid), NEVER the spurious `Unsat` and never a guessed
    // `Sat`. (Recovering the decisive `Sat` would need a sound finite-domain
    // model check — see task #277 follow-up.)
    assert_eq!(verdict, Some("unknown"), "bounded ackermann grid must be sound Unknown, got {out:?}");
}

#[test]
fn out_of_guard_unsat_still_caught() {
    // Soundness guard: a bounded axiom whose finite instances are themselves
    // contradictory must still be Unsat (the finite domain is fully asserted).
    // ∀x. (1≤x≤1 ⇒ p(x))  ∧  ¬p(1)  → instantiate x=1 → p(1) ∧ ¬p(1) → Unsat.
    let script = "\
        (set-logic UFLIA)\
        (declare-fun p (Int) Bool)\
        (assert (forall ((x Int)) (=> (and (>= x 1) (<= x 1)) (p x))))\
        (assert (not (p 1)))\
        (check-sat)";
    let mut ctx = Context::new();
    ctx.set_clean_mbqi(true);
    ctx.set_timeout_ms(2000);
    let out = ctx.execute_script(script).expect("script runs");
    let verdict = out.iter().rev().find_map(|l| match l.trim() {
        "sat" => Some("sat"),
        "unsat" => Some("unsat"),
        "unknown" => Some("unknown"),
        _ => None,
    });
    assert_eq!(verdict, Some("unsat"), "the single finite instance contradicts ¬p(1), got {out:?}");
}

#[test]
fn corpus_ackermann_file_is_sound_not_hang() {
    // The vendored `UFLIA/ackermann.smt2` (positivity via bounded monotonicity,
    // #benchmark-fix) must terminate soundly under the clean engine: the bounded
    // enumeration defuses the `f`-tower hang, and the verdict is the sound
    // `Unknown` (z3: sat — the clean engine is incomplete here, but NEVER
    // unsound: no spurious `Unsat`, no guessed `Sat`).
    let path = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/tests/corpus/z3_parity/benchmarks/UFLIA/ackermann.smt2"
    );
    let script = std::fs::read_to_string(path).expect("corpus file present");
    let mut ctx = Context::new();
    ctx.set_clean_mbqi(true);
    ctx.set_timeout_ms(2000);
    let out = ctx.execute_script(&script).expect("script runs");
    let verdict = out.iter().rev().find_map(|l| match l.trim() {
        "sat" => Some("sat"),
        "unsat" => Some("unsat"),
        "unknown" => Some("unknown"),
        _ => None,
    });
    assert_eq!(verdict, Some("unknown"), "corpus ackermann.smt2 must be sound Unknown, got {out:?}");
}
