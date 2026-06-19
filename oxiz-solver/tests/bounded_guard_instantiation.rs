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
//! VERDICT NOTE: a bounded `∀` is FULLY captured by its box conjunction of
//! emitted instances, so the engine reaches `Saturated` and the SOLVER confirms
//! the verdict with a single-shot ground re-solve (#280). The re-solve carries
//! the logic, so it enables the EUF↔LIA combination that the incremental
//! `Saturated`-trusting shortcut missed (#277's pigeonhole spurious-`sat`): a
//! genuinely-sat grid (ackermann) comes back `Sat`, a jointly-unsat box
//! (pigeonhole) comes back `Unsat`. The bounded enumeration still prevents the
//! `f`-tower hang.

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
    // z3: sat. The bounded ∀ is fully instantiated over its box and the
    // solver-side single-shot re-solve (with the logic) confirms `Sat` — no
    // hang, no spurious `Unsat`, and no longer the conservative `Unknown` (#280).
    assert_eq!(verdict, Some("sat"), "bounded ackermann grid must be Sat (solver-verified), got {out:?}");
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
fn corpus_ackermann_file_is_sat_not_hang() {
    // The vendored `UFLIA/ackermann.smt2` (positivity via bounded monotonicity,
    // #benchmark-fix): the bounded enumeration defuses the `f`-tower hang, the
    // bounded `∀` reaches `Saturated`, and the solver-side single-shot re-solve
    // confirms `Sat` (= z3 4.16) — sound and decisive (#280).
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
    assert_eq!(verdict, Some("sat"), "corpus ackermann.smt2 must be Sat (solver-verified), got {out:?}");
}

#[test]
fn bounded_pigeonhole_is_unsat_via_resolve() {
    // The dual of the ackermann recovery: a bounded `∀` whose box conjunction is
    // jointly UNSAT must come back `Unsat`. `∀i,j∈[0,2]. i≠j ⇒ hole(i)≠hole(j)`
    // with hole(0..2) ∈ [1,2] is 3 distinct values in 2 slots — impossible. The
    // engine `Saturated`s the bounded `∀` and the solver-side re-solve (carrying
    // the logic, so EUF↔LIA combination fires) refutes the box. This is the case
    // the incremental `Saturated`-trust got wrong (#277). (z3: unsat.)
    let script = "\
        (set-logic UFLIA)\
        (declare-fun hole (Int) Int)\
        (assert (and (>= (hole 0) 1) (<= (hole 0) 2)))\
        (assert (and (>= (hole 1) 1) (<= (hole 1) 2)))\
        (assert (and (>= (hole 2) 1) (<= (hole 2) 2)))\
        (assert (forall ((i Int) (j Int)) \
            (=> (and (>= i 0) (<= i 2) (>= j 0) (<= j 2) (not (= i j))) \
                (not (= (hole i) (hole j))))))\
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
    assert_eq!(verdict, Some("unsat"), "bounded pigeonhole box is jointly unsat, got {out:?}");
}
