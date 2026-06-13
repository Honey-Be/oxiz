//! §4 redesign (Phase 2) differential: every instance must get the SAME verdict
//! from the legacy `TheoryCallback` driver (`solve_with_theory`) and the new
//! lock-step `TheoryHooks` driver (`solve_with_hooks`). Both run the SAME real
//! EUF/arith/BV theory state (`TheoryManager` implements both traits); the hooks
//! path is selected with `(set-option :oxiz.use-hooks-driver true)`.
//!
//! The soundness-critical direction is checked explicitly: the hooks path must
//! never report `unsat` where the legacy path reports `sat` (a spurious UNSAT is
//! the dangerous failure mode this redesign is built to make unrepresentable).

use oxiz_solver::Context;

fn verdict_with(script: &str, hooks: bool) -> &'static str {
    let mut ctx = Context::new();
    ctx.set_timeout_ms(10_000);
    if hooks {
        ctx.set_option("oxiz.use-hooks-driver", "true");
    }
    match ctx.execute_script(script) {
        Ok(out) => out
            .iter()
            .rev()
            .find_map(|l| match l.trim() {
                "sat" => Some("sat"),
                "unsat" => Some("unsat"),
                "unknown" => Some("unknown"),
                _ => None,
            })
            .unwrap_or("unknown"),
        Err(_) => "unknown",
    }
}

/// Scripts covering EUF, LIA, BV, combined theories, and a quantified instance.
/// The test asserts the two DRIVERS agree on each (a differential, not an
/// absolute-verdict, check — the absolute verdicts are pinned by the other
/// suites). The legacy path must also reach a definite `sat`/`unsat` (so the
/// agreement is meaningful, not "both unknown").
const CORPUS: &[&str] = &[
    // --- EUF ---
    "(set-logic QF_UF)\n(declare-sort U 0)\n(declare-fun f (U) U)\n\
     (declare-const a U)(declare-const b U)\n\
     (assert (= a b))(assert (not (= (f a) (f b))))\n(check-sat)\n", // unsat
    "(set-logic QF_UF)\n(declare-sort U 0)\n(declare-fun f (U) U)\n\
     (declare-const a U)(declare-const b U)\n\
     (assert (= (f a) (f b)))\n(check-sat)\n", // sat
    // --- LIA ---
    "(set-logic QF_LIA)\n(declare-const x Int)(declare-const y Int)\n\
     (assert (> x y))(assert (> y x))\n(check-sat)\n", // unsat
    "(set-logic QF_LIA)\n(declare-const x Int)(declare-const y Int)\n\
     (assert (>= x 3))(assert (<= y 1))(assert (> x y))\n(check-sat)\n", // sat
    // 2c = 3 has no integer solution.
    "(set-logic QF_LIA)\n(declare-const c Int)\n(assert (= c (- 3 c)))\n(check-sat)\n", // unsat
    // infeasible disjunct inside a satisfiable OR (the GCD-reason regression)
    "(set-logic QF_LIA)\n(declare-const c Int)(declare-const x Int)(declare-const y Int)\n\
     (declare-const p Bool)\n\
     (assert (or (= c (- 3 c)) (>= 10 3)))(assert (=> p (= x y)))\n(check-sat)\n", // sat
    // --- combined EUF + LIA ---
    "(set-logic QF_UFLIA)\n(declare-fun f (Int) Int)\n(declare-const a Int)(declare-const b Int)\n\
     (assert (= a b))(assert (not (= (f a) (f b))))\n(check-sat)\n", // unsat
    "(set-logic QF_UFLIA)\n(declare-fun f (Int) Int)\n(declare-const a Int)\n\
     (assert (> (f a) 0))(assert (< (f a) 10))\n(check-sat)\n", // sat
    // --- BV ---
    "(set-logic QF_BV)\n(declare-const x (_ BitVec 8))(declare-const y (_ BitVec 8))\n\
     (assert (= (bvadd x y) (bvadd y x)))\n(check-sat)\n", // sat
    "(set-logic QF_BV)\n(declare-const x (_ BitVec 8))\n\
     (assert (not (= (bvadd x #x01) (bvadd x #x01))))\n(check-sat)\n", // unsat
    // --- quantified: the inner SAT solves differ between drivers, the MBQI loop
    //     that wraps them is shared, so the drivers must still agree. ---
    "(set-logic UF)\n(declare-sort U 0)\n(declare-fun p (U) Bool)\n(declare-const a U)\n\
     (assert (forall ((x U)) (p x)))(assert (not (p a)))\n(check-sat)\n",
];

#[test]
fn hooks_and_legacy_agree_on_corpus() {
    let mut mismatches = Vec::new();
    let mut spurious_unsat = Vec::new();
    for (i, script) in CORPUS.iter().enumerate() {
        let legacy = verdict_with(script, false);
        let hooks = verdict_with(script, true);

        if legacy != hooks {
            mismatches.push((i, legacy, hooks));
        }
        // Soundness-critical: the hooks path must not invent an UNSAT where the
        // legacy path is SAT (a spurious UNSAT is the dangerous direction).
        if legacy == "sat" && hooks == "unsat" {
            spurious_unsat.push(i);
        }
    }
    assert!(
        spurious_unsat.is_empty(),
        "hooks driver produced SPURIOUS UNSAT on corpus indices {spurious_unsat:?}"
    );
    assert!(
        mismatches.is_empty(),
        "hooks vs legacy verdict mismatches (idx, legacy, hooks): {mismatches:?}"
    );
}

/// The ground (quantifier-free) cases must reach a DEFINITE verdict on BOTH
/// drivers — so the agreement above is "both sat" / "both unsat", never the
/// vacuous "both unknown".
#[test]
fn ground_cases_are_definite_on_both_drivers() {
    for (i, script) in CORPUS.iter().enumerate().take(10) {
        for &hooks in &[false, true] {
            let v = verdict_with(script, hooks);
            assert!(
                v == "sat" || v == "unsat",
                "corpus[{i}] hooks={hooks} gave non-definite {v}"
            );
        }
    }
}
