//! CCFV P4 — the model-completion verdict-flip (`:oxiz.ccfv-model-compl`).
//!
//! The flip lets a trigger-free universal the structural `eval_forall`
//! recognizers leave unverified contribute a `Sat`: it lowers `¬ψ` to a
//! (dis)equality DNF and runs the brute-force CCFV `solve` against the total
//! view `E_TOT`; an empty conflict set ⇒ the completed model satisfies the
//! universal. It is **OFF by default** (soundness-gated: a missed conflict is a
//! spurious `sat`); these tests pin (1) the default path is unchanged, (2) the
//! flip recovers a genuine `Sat` when armed, and — the bar that matters — (3) it
//! never certifies an `unsat` as `sat` (the live congruence reveals the conflict,
//! so the flip DECLINES). See `CCFV_UNIFIED_INSTANTIATION.md` §P4/§6.

use oxiz_solver::{Context, SolverResult};

/// Feed each command to `execute_script` separately (persistent `Context`),
/// returning the final `(check-sat)` verdict.
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

/// `∀x. f(x) ≠ a` with one consistent ground point `f(c)=c`, `a≠c`. Satisfiable
/// (complete `f` to avoid `a`), but no structural `eval_forall` recognizer
/// catches a NEGATED-equality body, so the DEFAULT path can only saturate to the
/// sound `Unknown`.
const FX_NEQ_A: &[&str] = &[
    "(declare-sort U 0)",
    "(declare-fun f (U) U)",
    "(declare-const a U)",
    "(declare-const c U)",
    "(assert (= (f c) c))",
    "(assert (not (= a c)))",
    "(assert (forall ((x U)) (not (= (f x) a))))",
    "(check-sat)",
];

#[test]
fn flip_off_by_default_leaves_unverified_forall_unknown() {
    // No `set-option` ⇒ the backstop is never consulted ⇒ the verdict is the
    // sound `Unknown` (the default path is byte-identical to pre-P4).
    assert_eq!(solve_streamed(FX_NEQ_A), SolverResult::Unknown);
}

#[test]
fn flip_on_recovers_sat_for_negated_equality_axiom() {
    // Armed, CCFV `¬ψ = (= (f x) a)` finds no conflict over `E_TOT` (every
    // enumerated witness is decidably ≠ a or under-specified-and-free), so the
    // completed model satisfies the universal ⇒ `Sat`.
    let mut cmds = vec!["(set-option :oxiz.ccfv-model-compl true)"];
    cmds.extend_from_slice(FX_NEQ_A);
    assert_eq!(solve_streamed(&cmds), SolverResult::Sat);
}

#[test]
fn flip_on_must_not_certify_unsat_as_sat() {
    // THE soundness bar. `f(c)=a` directly contradicts `∀x. f(x)≠a` (at x=c).
    // The flip's `solve` queries the LIVE congruence — which has `f(c)=a`
    // interned — so `Eq(f(c),a)` holds, a conflict survives, and the flip
    // DECLINES (`None`); the engine then instantiates at `c` and reports the
    // sound `unsat`. A spurious `sat` here would be the cardinal sin.
    let r = solve_streamed(&[
        "(set-option :oxiz.ccfv-model-compl true)",
        "(declare-sort U 0)",
        "(declare-fun f (U) U)",
        "(declare-const a U)",
        "(declare-const c U)",
        "(assert (= (f c) a))",
        "(assert (forall ((x U)) (not (= (f x) a))))",
        "(check-sat)",
    ]);
    assert_eq!(r, SolverResult::Unsat, "the flip must never hide an unsat");
}

#[test]
fn flip_must_not_certify_contradictory_predicate_body_as_sat() {
    // `∀x. (P x ∧ ¬(P x))` — the body is `false` for every `x`, so over a
    // non-empty domain the universal is UNSAT. `Bool` is a 2-valued sort, so the
    // total view's free-distinct completion is NOT sound for a bare predicate
    // (a `P(c)` distinct from both `true` and `false` is no legal Bool value);
    // the lowering therefore DECLINES the predicate fragment and the verdict is
    // never a flip-fabricated `sat`.
    let r = solve_streamed(&[
        "(set-option :oxiz.ccfv-model-compl true)",
        "(declare-sort U 0)",
        "(declare-fun p (U) Bool)",
        "(declare-const c U)",
        "(assert (forall ((x U)) (and (p x) (not (p x)))))",
        "(check-sat)",
    ]);
    assert_ne!(r, SolverResult::Sat, "a contradictory body must never be sat");
}

#[test]
fn flip_must_not_certify_arith_forced_conflict_as_sat() {
    // `∀x. f(x) ≠ 5` with `f(c)` arith-pinned to 5 (`5 ≤ f(c) ≤ 5`). UNSAT, but
    // the conflict lives in the ARITH theory, not the bare congruence — so the
    // flip declines the Int-sorted equality fragment (non-authoritative sort)
    // rather than risk missing the arith-forced merge.
    let r = solve_streamed(&[
        "(set-option :oxiz.ccfv-model-compl true)",
        "(declare-fun f (Int) Int)",
        "(declare-const c Int)",
        "(assert (<= (f c) 5))",
        "(assert (>= (f c) 5))",
        "(assert (forall ((x Int)) (not (= (f x) 5))))",
        "(check-sat)",
    ]);
    assert_ne!(r, SolverResult::Sat, "an arith-forced conflict must never be sat");
}

#[test]
fn flip_declines_when_symbol_constrained_by_two_quantifiers() {
    // `∀x. f(x)≠a` and `∀y. f(y)=a` jointly force a contradiction (x=y). The
    // accounting gate sees `f` under TWO quantifiers (under_quant_occ ≠ body_occ)
    // and declines the flip for each — the engine instantiates both at a shared
    // witness and reports the sound `unsat`, never a flip-fabricated `sat`.
    let r = solve_streamed(&[
        "(set-option :oxiz.ccfv-model-compl true)",
        "(declare-sort U 0)",
        "(declare-fun f (U) U)",
        "(declare-const a U)",
        "(declare-const c U)",
        "(assert (= (f c) c))",
        "(assert (forall ((x U)) (not (= (f x) a))))",
        "(assert (forall ((y U)) (= (f y) a)))",
        "(check-sat)",
    ]);
    assert_eq!(r, SolverResult::Unsat);
}
