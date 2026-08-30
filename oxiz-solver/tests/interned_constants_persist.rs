// SPDX-License-Identifier: Apache-2.0
// SPDX-FileCopyrightText: 2026 윤병익 (BYUNG-IK YEUN) and Y4 contributors

//! #434 — the canonical-constant index does not outlive the per-round
//! `TheoryManager`, and turning that off is a DELIBERATE, MEASURED trade.
//!
//! `TheoryManager::interned_int_constants` maps an integer VALUE to the
//! canonical EUF node for it. Two jobs depend on it: the entailed-value merge
//! in `model_based_combination` (which looks the node up by value) and the
//! pairwise constant-disequality edges. It is rebuilt EMPTY on every
//! `TheoryManager` construction — once per iteration of `check_level`'s loop —
//! while `euf` is carried forward, and `intern_term_for_congruence` returns
//! early for a term EUF already interned, so a value registered in round 1 can
//! never re-register. From round 2 on the index is permanently empty and both
//! jobs stop, silently, in the false-`sat` direction.
//!
//! `SolverConfig::persist_const_index` carries it forward and closes that.
//! It is **OFF by default**, because with it ON the re-enabled merge produces
//! false `unsat` — measured at 2 fabricated refutations per 200 seeds of
//! `corpus-triage/arith_euf_merge_diff.py`, against 0 with it off. The merge
//! is recorded in the EUF proof forest under a PLACEHOLDER reason (the merged
//! term, which has no SAT variable), so a conflict explained through that edge
//! yields a clause the theory does not entail. A completeness bug in the `sat`
//! direction beats a false proof, so the default keeps the bug.
//!
//! These tests therefore pin BOTH sides: the default behaviour (so a change of
//! default is loud), and what the option buys (so the knowledge is not lost).

use oxiz_solver::Context;

const PERSIST: &str = "(set-option :oxiz.persist-const-index true)\n";

fn verdict(script: &str) -> String {
    let mut ctx = Context::new();
    let out = ctx.execute_script(script).expect("script parses");
    out.iter()
        .map(|l| l.trim())
        .find(|l| matches!(*l, "sat" | "unsat" | "unknown"))
        .unwrap_or("no-verdict")
        .to_owned()
}

/// The obligation the index is needed for. Round 1 accepts a model; the #433
/// case split forces `x0`, which ENTAILS `x1 = 3`; round 2's
/// `model_based_combination` should merge `x1` with the canonical node for `3`,
/// fire the `f0` congruence and hit `a != b`.
const ENTAILED_IN_ROUND_TWO: &str = "(set-logic QF_UFLIA)\n\
     (declare-fun x0 () Int) (declare-fun x1 () Int)\n\
     (declare-fun a () Int) (declare-fun b () Int)\n\
     (declare-fun f0 (Int) Int)\n\
     (assert (<= 3 x0)) (assert (<= x0 4))\n\
     (assert (= x0 (+ x1 1)))\n\
     (assert (= (f0 2) a)) (assert (= (f0 3) a))\n\
     (assert (= (f0 x1) b))\n\
     (assert (not (= a b)))\n\
     (check-sat)\n";

/// DEFAULT behaviour, pinned so that flipping the default is a test change and
/// not a silent one: the conflict is MISSED and the answer is the sound-but-
/// incomplete `sat`. z3 and cvc5 both say `unsat`.
#[test]
fn the_default_still_misses_the_second_round_conflict() {
    assert_eq!(
        verdict(ENTAILED_IN_ROUND_TWO),
        "sat",
        "known gap — see the module docs and `persist_const_index`"
    );
}

/// What the option buys. This is the whole point of keeping the code: with the
/// index carried forward the merge fires and the obligation is refuted.
#[test]
fn the_option_closes_the_second_round_conflict() {
    assert_eq!(
        verdict(&format!("{PERSIST}{ENTAILED_IN_ROUND_TWO}")),
        "unsat"
    );
}

/// The SINGLE-round sibling: the shared variable is bounded directly, so the
/// split forces it in round 1 and the equality reaches EUF through the ordinary
/// `Constraint::Eq` path, never touching the value index. It was never broken
/// and must stay correct under BOTH settings — it is the control that says a
/// failure above is about the ROUND BOUNDARY, not about the merge logic.
#[test]
fn the_single_round_sibling_is_correct_either_way() {
    let script = "(set-logic QF_UFLIA)\n\
         (declare-fun x1 () Int)\n\
         (declare-fun a () Int) (declare-fun b () Int)\n\
         (declare-fun f0 (Int) Int)\n\
         (assert (<= 2 x1)) (assert (<= x1 3))\n\
         (assert (= (f0 2) a)) (assert (= (f0 3) a))\n\
         (assert (= (f0 x1) b))\n\
         (assert (not (= a b)))\n\
         (check-sat)\n";
    assert_eq!(verdict(script), "unsat");
    assert_eq!(verdict(&format!("{PERSIST}{script}")), "unsat");
}

/// ANTI-OVER-MERGE control, and the reason the option is off. `x1` is free to
/// be 2 OR 3 and only one of those conflicts, so a model exists — z3 and cvc5
/// both say `sat`. The DEFAULT must answer `sat`; a build that answers `unsat`
/// here has minted a false proof.
///
/// (With the option ON this particular script is also `sat` — the
/// `fixed_value_with_reasons` probe guard landed alongside closed it. The
/// fabricated refutations that keep the option off are the wider family in
/// `corpus-triage/arith_euf_merge_diff.py`, not this one.)
#[test]
fn a_merely_model_equal_value_is_never_merged() {
    let script = "(set-logic QF_UFLIA)\n\
         (declare-fun x0 () Int) (declare-fun x1 () Int)\n\
         (declare-fun a () Int) (declare-fun b () Int)\n\
         (declare-fun f0 (Int) Int)\n\
         (assert (<= 3 x0)) (assert (<= x0 4))\n\
         (assert (= x0 (+ x1 1)))\n\
         (assert (= (f0 3) a))\n\
         (assert (= (f0 x1) b))\n\
         (assert (not (= a b)))\n\
         (check-sat)\n";
    assert_eq!(verdict(script), "sat", "x1 = 2 satisfies everything");
    assert_eq!(verdict(&format!("{PERSIST}{script}")), "sat");
}

/// The index's OTHER job — pairwise disequalities between distinct constant
/// values — is lost across the round boundary too. `x1` is 2 or 3 and BOTH
/// branches contradict `(g x1) = 5`, but only if EUF holds `2 != 5` / `3 != 5`
/// edges. Pinned under the option, since that is where the edges survive.
#[test]
fn the_option_keeps_distinct_constants_distinct_across_rounds() {
    assert_eq!(
        verdict(
            &format!("{PERSIST}(set-logic QF_UFLIA)\n\
             (declare-fun x0 () Int) (declare-fun x1 () Int)\n\
             (declare-fun g (Int) Int)\n\
             (assert (<= 3 x0)) (assert (<= x0 4))\n\
             (assert (= x0 (+ x1 1)))\n\
             (assert (= (g 2) 2))\n\
             (assert (= (g 3) 3))\n\
             (assert (= (g x1) 5))\n\
             (check-sat)\n")
        ),
        "unsat"
    );
}

/// Sanity twin: change the required image to one the `x1 = 2` branch satisfies
/// and it must be `sat` under BOTH settings. Without this, a build that
/// answered `unsat` to everything would pass the test above.
#[test]
fn the_distinct_constant_shape_is_sat_when_one_branch_fits() {
    let script = "(set-logic QF_UFLIA)\n\
         (declare-fun x0 () Int) (declare-fun x1 () Int)\n\
         (declare-fun g (Int) Int)\n\
         (assert (<= 3 x0)) (assert (<= x0 4))\n\
         (assert (= x0 (+ x1 1)))\n\
         (assert (= (g 2) 2))\n\
         (assert (= (g 3) 3))\n\
         (assert (= (g x1) 2))\n\
         (check-sat)\n";
    assert_eq!(verdict(script), "sat");
    assert_eq!(verdict(&format!("{PERSIST}{script}")), "sat");
}
