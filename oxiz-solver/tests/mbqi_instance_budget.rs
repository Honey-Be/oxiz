// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors

//! Work-bounded MBQI round emission (`SolverConfig::mbqi_instance_budget`).
//!
//! The round loop's only real bound was the wall clock: the 100-iteration cap
//! never binds (2 to 7 rounds per episode, measured), so the verdict was a
//! function of machine speed — a faster engine emits more instances inside the
//! window, a contended one fewer. These tests pin the three properties the work
//! bound must have, in the order they matter:
//!
//! 1. **Soundness.** No budget setting may turn an abstain into a `sat`, and
//!    none may turn an `unsat` into a `sat`. A budget only ever REMOVES sound
//!    ground consequences from consideration.
//! 2. **`0` is the historical loop.** The default must be byte-for-byte the
//!    deadline-only behaviour.
//! 3. **It actually binds**, and binding is what lets the accumulated instances
//!    be re-read by the single-shot confirm instead of discarded.

use oxiz_solver::Context;

/// An axiom that instantiates without converging: `f` is strictly increasing
/// under a pattern that fires on every new `f` term, so each round produces the
/// next one. Unbounded emission, no model — the shape the budget exists for.
const DIVERGING: &str = r"
(set-logic UFLIA)
(declare-fun f (Int) Int)
(assert (forall ((x Int)) (! (> (f x) (f (- x 1))) :pattern ((f x)))))
(assert (= (f 0) 0))
(assert (< (f 1000000) 0))
(check-sat)
";

/// A ground-closable obligation: the quantifier is needed, but ONE instance
/// closes it. Any budget at or above 1 must keep proving it.
const CLOSES_FAST: &str = r"
(set-logic UFLIA)
(declare-fun g (Int) Int)
(declare-fun a () Int)
(assert (forall ((x Int)) (! (= (g x) 7) :pattern ((g x)))))
(assert (not (= (g a) 7)))
(check-sat)
";

/// Drive the budget the way a caller would — through `set-option`, not through
/// a private config seam, so the test also pins the option name and its parse.
/// Neither knob goes through process env, which would force these tests to run
/// serially.
fn solve_with_budget(script: &str, budget: usize, guard_ms: u64) -> String {
    let full = format!("(set-option :oxiz.mbqi-instance-budget {budget})\n{script}");
    let mut ctx = Context::new();
    ctx.set_timeout_ms(guard_ms);
    let out = ctx.execute_script(&full).expect("script parses");
    out.iter()
        .map(|l| l.trim())
        .find(|l| matches!(*l, "sat" | "unsat" | "unknown"))
        .unwrap_or("no-verdict")
        .to_owned()
}

/// SOUNDNESS, the only property that may never bend: no budget may produce a
/// `sat` on a diverging axiom set. The budget removes sound ground consequences
/// from consideration, which can only cost completeness — a `sat` would mean the
/// solver concluded "no model refutes this" from a lemma set it chose to stop
/// building, which is exactly the phantom-sat door the clean engine closes.
#[test]
fn no_budget_setting_may_answer_sat_on_a_diverging_axiom() {
    for budget in [0, 1, 2, 5, 50, 500] {
        let v = solve_with_budget(DIVERGING, budget, 4_000);
        assert_ne!(
            v, "sat",
            "budget {budget} fabricated a model for a diverging instantiation"
        );
    }
}

/// A budget must not cost a proof that ONE instance closes. This is the
/// completeness floor of the feature: the budget is a bound on emission, not a
/// bound on the proof, so any budget that permits the needed instance must
/// still reach it.
#[test]
fn a_generous_budget_keeps_a_one_instance_proof() {
    let baseline = solve_with_budget(CLOSES_FAST, 0, 4_000);
    assert_eq!(baseline, "unsat", "fixture precondition: it proves at all");
    for budget in [16, 64, 1_000] {
        assert_eq!(
            solve_with_budget(CLOSES_FAST, budget, 4_000),
            "unsat",
            "budget {budget} lost a proof that needs one instance"
        );
    }
}

/// The bound BINDS, and it binds on work rather than on time: the diverging
/// axiom under a tiny budget must stop while the wall clock still has room. The
/// assertion is on the verdict, not on the clock, because a timing assertion is
/// exactly the machine-speed dependence this feature removes — but a budget
/// that never fired would leave the diverging solve to burn the full guard,
/// which the enclosing `#[test]` harness would show as a slow test rather than
/// a wrong one. So this pins the reachable outcome: `unknown` (nothing the
/// accumulated instances entail), never `sat`, and never a hang.
#[test]
fn a_tiny_budget_stops_a_diverging_solve() {
    // Deliberately a LONG guard: if the budget did not bind, the only thing
    // that could stop this is the deadline, and the test would take 30 s.
    let v = solve_with_budget(DIVERGING, 4, 30_000);
    assert!(
        v == "unknown" || v == "unsat",
        "a stopped solve is sound-abstain or a confirmed refutation, got {v}"
    );
}

/// `0` disables the bound. Pinned separately from the default so that a future
/// change of the DEFAULT cannot silently change the meaning of `0` — the
/// kill-switch and the default are two different promises.
#[test]
fn zero_disables_the_bound() {
    assert_eq!(
        solve_with_budget(CLOSES_FAST, 0, 4_000),
        solve_with_budget(CLOSES_FAST, usize::MAX, 4_000),
        "an unreachable budget and a disabled budget must agree"
    );
}

/// ANTI-OVER-FIX control. A budget implemented by silently truncating a round's
/// lemma list while still letting the loop report saturation would look correct
/// on the tests above and be UNSOUND: the engine would conclude "every
/// quantifier is satisfied" from a lemma set it had truncated. The observable
/// signature is a `sat` on an obligation whose refutation lives in the dropped
/// tail, so this drives the diverging fixture at every budget from 1 to 12 —
/// the range where truncation mid-round is most likely — and demands abstention.
#[test]
fn truncation_must_never_be_reported_as_saturation() {
    for budget in 1..=12 {
        let v = solve_with_budget(DIVERGING, budget, 2_000);
        assert_ne!(
            v, "sat",
            "budget {budget} reported saturation over a truncated lemma set"
        );
    }
}
