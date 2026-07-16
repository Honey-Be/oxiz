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

#[test]
fn nested_reverify_does_not_double_the_budget() {
    // Bug B (nested-reverification budget): `fresh_ground_resolve` builds a
    // fresh verifier from `config.clone()`, whose `check_level` used to
    // recompute a FULL fresh MBQI deadline from the cloned `timeout_ms` —
    // every `verify_clean_saturated`/`verify_clean_unsat` re-solve granted
    // itself a whole second budget, ~2× the configured guard per check-sat.
    // The fix injects the outer check's absolute deadline and clamps the
    // nested budget to `min(fresh, max(outer, now + own_ms/4))`.
    //
    // Vehicle: a LARGE bounded pigeonhole (63 holes in [1,62]) at
    // timeout_ms = 1500. The outer MBQI phase needs ~1.1 s to enumerate and
    // encode the ~3.9k box instances before it `Saturated`s, and the fresh
    // single-shot ground re-solve of that box does not converge inside any
    // budget this test grants — so the total wall-clock reads the nested
    // grant directly: pre-fix ≈ outer + full fresh 1.5 s ≈ 2.7 s (measured
    // 2.71 s); post-fix the clamp caps the nested at the remaining outer
    // budget (floored at 375 ms) ≈ 1.5–1.9 s total. Assert only the
    // egregious multiple (< 2.6 s) so a loaded machine does not flake.
    //
    // The box is genuinely UNSAT, so the only acceptable verdicts are
    // `unsat` (if a future ground core refutes it in time) or the sound
    // `unknown` — never `sat`.
    //
    // Runs on a big-stack thread: ~3.9k encoded instances overflow the
    // default 2 MiB test-thread stack (a pre-existing recursion-depth
    // limitation, unrelated to the budget fix).
    let n = 62usize;
    let mut script = String::from("(set-logic UFLIA)(declare-fun hole (Int) Int)");
    for i in 0..=n {
        script.push_str(&format!(
            "(assert (and (>= (hole {i}) 1) (<= (hole {i}) {n})))"
        ));
    }
    script.push_str(&format!(
        "(assert (forall ((i Int) (j Int)) \
           (=> (and (>= i 0) (<= i {n}) (>= j 0) (<= j {n}) (not (= i j))) \
               (not (= (hole i) (hole j))))))"
    ));
    script.push_str("(check-sat)");

    let handle = std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || {
            let mut ctx = Context::new();
            ctx.set_clean_mbqi(true);
            ctx.set_timeout_ms(1500);
            let start = std::time::Instant::now();
            let out = ctx.execute_script(&script).expect("script runs");
            (out, start.elapsed())
        })
        .expect("spawn big-stack test thread");
    let (out, elapsed) = handle.join().expect("no panic in solver thread");

    let verdict = out.iter().rev().find_map(|l| match l.trim() {
        "sat" => Some("sat"),
        "unsat" => Some("unsat"),
        "unknown" => Some("unknown"),
        _ => None,
    });
    assert_ne!(
        verdict,
        Some("sat"),
        "PHP box is jointly unsat — `sat` would be a soundness bug, got {out:?}"
    );
    assert!(
        elapsed < std::time::Duration::from_millis(2600),
        "nested re-verify must not grant itself a second full budget \
         (pre-fix ≈2.7 s, post-fix ≤ ~1.9 s), took {elapsed:?}"
    );
}

#[test]
fn multi_pattern_join_blowup_returns_unknown_in_guard() {
    // The e-match deadline fix, end-to-end. A multi-pattern trigger
    // `:pattern ((f x) (g x))` over N ground f- and g-applications makes the
    // CCFV join scan the N×N acc × seeds product INSIDE ONE `ematch_all` call
    // — N = 2000 measured >45 s pre-fix (the between-round loop-top deadline
    // check can't interrupt a running e-match, so the 1 s guard was overshot
    // >45×; the dm2/sv2 corpus rows are the same shape). Post-fix the matcher
    // polls the deadline every 1024 unify calls, aborts the join in-guard,
    // routes the abort through `budget_hit`, and the solver returns the sound
    // `unknown` — total wall ≈ guard + bounded emit, asserted with GENEROUS
    // slop (6 s for a 1 s guard) so a loaded machine does not flake.
    //
    // Soundness edge: the aborted e-match yields a PARTIAL match set, so the
    // verdict must be `unknown` — `sat` here would mean a truncated match set
    // was read as saturation (the exact spurious-Sat risk the abort signal
    // exists to prevent).
    let n = 1200usize;
    let mut script =
        String::from("(set-logic UFLIA)(declare-fun f (Int) Int)(declare-fun g (Int) Int)(declare-fun h (Int) Int)");
    for i in 0..n {
        script.push_str(&format!("(assert (>= (f {i}) 0))(assert (>= (g {i}) 0))"));
    }
    script.push_str(
        "(assert (forall ((x Int)) (! (>= (h x) 0) :pattern ((f x) (g x)))))(check-sat)",
    );

    // Big-stack thread: thousands of encoded assertions overflow the default
    // 2 MiB test-thread stack (pre-existing recursion-depth limitation,
    // unrelated to this fix — same workaround as
    // `nested_reverify_does_not_double_the_budget`).
    let handle = std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || {
            let mut ctx = Context::new();
            ctx.set_clean_mbqi(true);
            ctx.set_timeout_ms(1000);
            let start = std::time::Instant::now();
            let out = ctx.execute_script(&script).expect("script runs");
            (out, start.elapsed())
        })
        .expect("spawn big-stack test thread");
    let (out, elapsed) = handle.join().expect("no panic in solver thread");

    let verdict = out.iter().rev().find_map(|l| match l.trim() {
        "sat" => Some("sat"),
        "unsat" => Some("unsat"),
        "unknown" => Some("unknown"),
        _ => None,
    });
    assert_eq!(
        verdict,
        Some("unknown"),
        "aborted (partial) e-match must be the sound unknown — sat would be \
         the spurious-Saturated soundness bug, unsat a fabrication, got {out:?}"
    );
    assert!(
        elapsed < std::time::Duration::from_secs(6),
        "the 1 s guard must bound the e-match join (pre-fix: >45 s), took {elapsed:?}"
    );
}

#[test]
fn early_lemma_then_mid_round_ematch_abort_is_caught_by_loop_top() {
    // The NewLemmas leg of the abort contract, driven through the FULL
    // Solver/Context API. Round 1: an EARLIER cheap quantifier
    // (`:pattern (q x)`, one ground seed) e-matches and emits its lemma
    // BEFORE the deadline expires; then the LATER quantifier's N×N
    // multi-pattern join aborts mid-e-match. The round therefore returns
    // `NewLemmas` (lemmas win over `budget_hit` by design) — the engine
    // verdict alone does NOT surface the abort. What catches it is the
    // solver's loop-top deadline check on the NEXT iteration → the sound
    // `unknown`. A `sat` here would mean the aborted (partial) join was read
    // as saturation; pre-fix this shape overshot the guard by >45×.
    let n = 1200usize;
    let mut script = String::from(
        "(set-logic UFLIA)(declare-fun f (Int) Int)(declare-fun g (Int) Int)\
         (declare-fun h (Int) Int)(declare-fun q (Int) Int)(declare-fun h2 (Int) Int)\
         (assert (>= (q 0) 0))\
         (assert (forall ((x Int)) (! (>= (h2 x) 0) :pattern ((q x)))))",
    );
    for i in 0..n {
        script.push_str(&format!("(assert (>= (f {i}) 0))(assert (>= (g {i}) 0))"));
    }
    script.push_str(
        "(assert (forall ((x Int)) (! (>= (h x) 0) :pattern ((f x) (g x)))))(check-sat)",
    );

    let handle = std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || {
            let mut ctx = Context::new();
            ctx.set_clean_mbqi(true);
            ctx.set_timeout_ms(1000);
            let start = std::time::Instant::now();
            let out = ctx.execute_script(&script).expect("script runs");
            (out, start.elapsed())
        })
        .expect("spawn big-stack test thread");
    let (out, elapsed) = handle.join().expect("no panic in solver thread");

    let verdict = out.iter().rev().find_map(|l| match l.trim() {
        "sat" => Some("sat"),
        "unsat" => Some("unsat"),
        "unknown" => Some("unknown"),
        _ => None,
    });
    assert_eq!(
        verdict,
        Some("unknown"),
        "NewLemmas-with-abort must be caught by the solver loop-top deadline \
         check next round — sat would be the spurious-Saturated bug, got {out:?}"
    );
    assert!(
        elapsed < std::time::Duration::from_secs(6),
        "the 1 s guard must bound the round (loop-top catch), took {elapsed:?}"
    );
}

#[test]
fn reused_context_second_check_gets_full_fresh_budget() {
    // Bug B staleness guard — the reason the fix uses TWO fields
    // (`mbqi_deadline_override` written only externally on the throwaway
    // nested verifier; `check_deadline` overwritten by every check that
    // reaches the MBQI deadline block) instead of one: writing the effective
    // deadline back into a single override field would leave a STALE,
    // long-expired cap on a `Context`-reused solver, silently flooring every
    // LATER check-sat's budget at ms/4 (or instant-`unknown` without the
    // floor).
    //
    // Check 1 (inside a push/pop frame): the small bounded pigeonhole —
    // drives `Saturated` → `verify_clean_saturated` → `fresh_ground_resolve`,
    // which records this check's effective deadline in the solver and injects
    // it into the nested verifier. Completes in milliseconds and returns the
    // real `unsat`.
    //
    // Then wall-clock is deliberately slept PAST check 1's absolute deadline
    // — that is the staleness condition: any cap left over from check 1 is
    // now expired. (Without the sleep a written-back cap would still lie in
    // the future and be indistinguishable from a fresh grant; verified by
    // mutation: a single-field write-back passes this test without the sleep
    // and fails it with the sleep.)
    //
    // Check 2, SAME context: a non-converging genuinely-SAT axiom that runs
    // to whatever deadline it is given. A full fresh budget runs ≈1.2 s; a
    // leaked stale expired cap would return in ≤ ~300 ms (the ms/4 floor) —
    // the elapsed lower bound discriminates.
    let mut ctx = Context::new();
    ctx.set_clean_mbqi(true);
    ctx.set_timeout_ms(1200);

    let php = "\
        (set-logic UFLIA)\
        (push 1)\
        (declare-fun hole (Int) Int)\
        (assert (and (>= (hole 0) 1) (<= (hole 0) 2)))\
        (assert (and (>= (hole 1) 1) (<= (hole 1) 2)))\
        (assert (and (>= (hole 2) 1) (<= (hole 2) 2)))\
        (assert (forall ((i Int) (j Int)) \
            (=> (and (>= i 0) (<= i 2) (>= j 0) (<= j 2) (not (= i j))) \
                (not (= (hole i) (hole j))))))\
        (check-sat)\
        (pop 1)";
    let out1 = ctx.execute_script(php).expect("script 1 runs");
    let verdict1 = out1.iter().rev().find_map(|l| match l.trim() {
        "sat" => Some("sat"),
        "unsat" => Some("unsat"),
        "unknown" => Some("unknown"),
        _ => None,
    });
    // Precondition: the fresh_ground_resolve verify path actually ran (a
    // bounded-∀ `unsat` is only ever reported via that single-shot re-solve).
    assert_eq!(verdict1, Some("unsat"), "bounded pigeonhole must unsat via the re-solve, got {out1:?}");

    // Sleep past check 1's absolute deadline (1200 ms from its start) so any
    // leftover cap is genuinely EXPIRED by the time check 2 computes its own.
    std::thread::sleep(std::time::Duration::from_millis(1400));

    let chain = "\
        (declare-fun f (Int) Int)\
        (declare-fun c () Int)\
        (assert (forall ((x Int)) (! (> (f x) (f (f x))) :pattern ((f x)))))\
        (assert (> (f c) 0))\
        (check-sat)";
    let start = std::time::Instant::now();
    let out2 = ctx.execute_script(chain).expect("script 2 runs");
    let elapsed = start.elapsed();
    let verdict2 = out2.iter().rev().find_map(|l| match l.trim() {
        "sat" => Some("sat"),
        "unsat" => Some("unsat"),
        "unknown" => Some("unknown"),
        _ => None,
    });
    assert_ne!(
        verdict2,
        Some("unsat"),
        "genuinely-SAT non-converging problem must never come back unsat, got {out2:?}"
    );
    assert!(
        elapsed >= std::time::Duration::from_millis(900),
        "second check on a reused context must get a FULL fresh budget \
         (~1.2 s), not a stale expired cap leaked from the first check, returned in {elapsed:?}"
    );
    assert!(
        elapsed < std::time::Duration::from_millis(2600),
        "second check must still honour its own 1.2 s budget, took {elapsed:?}"
    );
}
