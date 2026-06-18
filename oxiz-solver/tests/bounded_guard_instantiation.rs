//! Bounded-guard finite-domain instantiation (clean MBQI).
//!
//! A guarded universal `∀x̄. (lo ≤ x̄ ≤ hi ⇒ φ)` must be instantiated over the
//! FINITE integer range the guard pins, not over every ground `Int` term. The
//! latter makes a `∀m,n` whose body mentions a function `f` instantiate `m,n`
//! across `f`'s own applications → an `f`-of-`f` matching loop. The synthetic
//! `UFLIA/ackermann.smt2` corpus case (bounded positivity `∀m,n.(0≤m≤2 ∧
//! 0≤n≤5) ⇒ ack(m,n)>0`) used to spin at 100% CPU forever; with the bounded
//! domain it is `Sat` (= z3) in milliseconds.

use oxiz_solver::Context;

#[test]
fn bounded_grid_positivity_is_sat_not_hang() {
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
    // z3: sat. The bounded-guard finite instantiation + finite-exhaustion
    // saturation must reach Sat (and certainly never the spurious Unsat, nor
    // hang into the iteration cap).
    assert_eq!(verdict, Some("sat"), "bounded ackermann grid must be Sat, got {out:?}");
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
fn corpus_ackermann_file_is_sat() {
    // The vendored `UFLIA/ackermann.smt2` (positivity via bounded monotonicity,
    // #benchmark-fix) must solve `Sat` (= z3 4.16) under the clean engine.
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
    assert_eq!(verdict, Some("sat"), "corpus ackermann.smt2 must be Sat, got {out:?}");
}
