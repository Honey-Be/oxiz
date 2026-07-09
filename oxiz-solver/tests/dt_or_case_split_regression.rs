//! Permanent (z3-cross-checked) regressions for #418 item 3 — OR-branch
//! CYCLIC DISJUNCTION case-split detection.
//!
//! `check_dt_acyclicity` (see `dt_acyclicity_regression.rs`) only detects a
//! cycle among equalities that are UNCONDITIONALLY (flatly) asserted true —
//! it deliberately ignores `Or` branches, since no single disjunct is
//! unconditionally true on its own. But an assertion set can still force a
//! datatype conflict even when NO single equality is unconditional, as long
//! as EVERY way of making it true independently forces a cycle. Minimal
//! repro: `(assert (or (= y (cons x y)) (and (= y (cons x z)) (= z (cons x
//! y)))))` — neither disjunct is unconditionally true, but BOTH force a
//! cycle through `y`, so the whole assertion does too (z3/cvc5: `unsat`;
//! pre-fix oxiz: `sat`).
//!
//! Fixed by `Solver::check_dt_or_case_split_conflict` (`check_dt.rs`): a
//! work-list-driven recursive evaluator over the Boolean skeleton of the
//! (implicitly-conjoined) assertion set. `And`/`Not` thread and extend a
//! hypothesis exactly like the existing flat collector; a genuine `Or`
//! (or De-Morgan-dual `And` under negative context) is a case split that is
//! "conflict-forced" only when EVERY branch, combined with the unchanged
//! rest of the work-list, is ALSO conflict-forced — which naturally composes
//! into full cross-product reasoning when multiple independent
//! disjunctions must all hold at once. See that function's doc comment for
//! the complete design and scope notes (acyclicity-only; no cross-theory
//! case-split reasoning).

use oxiz_solver::Context;

fn verdict(script: &str) -> &'static str {
    let mut ctx = Context::new();
    ctx.set_timeout_ms(5000);
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

const LST_DT: &str = "(set-logic ALL)\n\
     (declare-datatypes ((Lst 0)) (((nil) (cons (hd Int) (tl Lst)))))\n";

/// The exact #418 item-3 minimal repro: an `or` where EVERY branch
/// (individually, the second branch itself an `and` of two equalities)
/// forces a cycle through `y`. z3/cvc5: `unsat`. Pre-fix oxiz: `sat`.
#[test]
fn or_every_branch_cyclic_is_unsat() {
    let v = verdict(&format!(
        "{LST_DT}(declare-const x Int)\n\
         (declare-const y Lst)\n\
         (declare-const z Lst)\n\
         (assert (or (= y (cons x y)) (and (= y (cons x z)) (= z (cons x y)))))\n\
         (check-sat)\n"
    ));
    assert_eq!(v, "unsat");
}

/// SOUNDNESS CONTROL — only ONE branch of the `or` is cyclic; the other
/// establishes an unrelated, perfectly acyclic fact. This is the
/// pre-existing, already-verified behavior (a single cyclic disjunct must
/// NOT be enough — the whole point of a disjunction is that either branch
/// alone can be the reason it's true). Must stay `sat`.
#[test]
fn or_only_one_branch_cyclic_stays_sat() {
    let v = verdict(&format!(
        "{LST_DT}(declare-const x Int)\n\
         (declare-const w Int)\n\
         (declare-const y Lst)\n\
         (assert (or (= y (cons x y)) (= y (cons w nil))))\n\
         (check-sat)\n"
    ));
    assert_eq!(v, "sat");
}

/// Extend the 2-way case to a 3-way `or` where ALL THREE branches force a
/// cycle (the third via a longer chain through a fresh variable `u`).
#[test]
fn threeway_or_all_branches_cyclic_is_unsat() {
    let v = verdict(&format!(
        "{LST_DT}(declare-const x Int)\n\
         (declare-const y Lst)\n\
         (declare-const z Lst)\n\
         (declare-const u Lst)\n\
         (assert (or (= y (cons x y))\n\
                     (and (= y (cons x z)) (= z (cons x y)))\n\
                     (and (= y (cons x u)) (and (= u (cons x z)) (= z (cons x y))))))\n\
         (check-sat)\n"
    ));
    assert_eq!(v, "unsat");
}

/// Genuine recursive generality: a NESTED `(or (and A B) (or C D))` where no
/// single leaf conjunct/disjunct forces a cycle alone, but EVERY way of
/// making the whole formula true does (branch 1: `and A B` closes a cycle
/// through `y`/`z`; branch 2 is itself an `or` whose OWN two sub-branches
/// each independently close a (different) cycle — one through `w`, one
/// through `y`). Tests that the evaluator recurses through nested Boolean
/// structure, not just a flat top-level pattern match.
#[test]
fn nested_or_and_or_all_paths_cyclic_is_unsat() {
    let v = verdict(&format!(
        "{LST_DT}(declare-const x Int)\n\
         (declare-const y Lst)\n\
         (declare-const z Lst)\n\
         (declare-const w Lst)\n\
         (assert (or (and (= y (cons x z)) (= z (cons x y)))\n\
                     (or (= w (cons x w)) (= y (cons x y)))))\n\
         (check-sat)\n"
    ));
    assert_eq!(v, "unsat");
}

/// De Morgan dual path: `(not (and (not A) (not (and B C))))` is logically
/// `A or (B and C)` — the same shape as the main repro, but phrased so the
/// evaluator must take the "`And` reached under a NEGATIVE context is
/// itself a disjunctive case split" branch (rather than the more common
/// direct-`Or`-under-positive-context branch). Confirms both De Morgan
/// directions are handled, not just the surface-syntax `Or` case.
#[test]
fn demorgan_not_and_not_form_is_unsat() {
    let v = verdict(&format!(
        "{LST_DT}(declare-const x Int)\n\
         (declare-const y Lst)\n\
         (declare-const z Lst)\n\
         (assert (not (and (not (= y (cons x y)))\n\
                            (not (and (= y (cons x z)) (= z (cons x y)))))))\n\
         (check-sat)\n"
    ));
    assert_eq!(v, "unsat");
}

/// CROSS-PRODUCT case: `(and (or A1 A2) (or B1 B2))` where NEITHER `or`'s
/// branches force a cycle on their own (confirmed by the two `_only_sat`
/// controls below), but EVERY one of the 4 (A-branch, B-branch) COMBINATIONS
/// does — each pairing closes the SAME `y -> z -> y` cycle, just via a
/// different equality chain each time (`A2`/`B2` route the same edge through
/// an extra plain-variable-equality hop). This specifically exercises the
/// work-list evaluator's cross-product recursion (processing the SECOND
/// `or`'s branching independently inside EACH branch of the FIRST), not
/// just independent per-`Or` evaluation.
#[test]
fn and_of_two_ors_cross_product_forces_conflict_is_unsat() {
    let v = verdict(&format!(
        "{LST_DT}(declare-const x Int)\n\
         (declare-const y Lst)\n\
         (declare-const z Lst)\n\
         (declare-const z2 Lst)\n\
         (declare-const y2 Lst)\n\
         (assert (and (or (= y (cons x z)) (and (= y (cons x z2)) (= z2 z)))\n\
                      (or (= z (cons x y)) (and (= z (cons x y2)) (= y2 y)))))\n\
         (check-sat)\n"
    ));
    assert_eq!(v, "unsat");
}

/// SOUNDNESS CONTROL for the cross-product case above — asserting ONLY the
/// first `or` (no second `or` at all) must stay `sat`: it alone never closes
/// a cycle (`y` merely points at `z`, nothing points back). Confirms the
/// cross-product repro genuinely needs BOTH conjuncts together, not just one
/// already being independently forcing.
#[test]
fn and_of_two_ors_first_conjunct_alone_stays_sat() {
    let v = verdict(&format!(
        "{LST_DT}(declare-const x Int)\n\
         (declare-const y Lst)\n\
         (declare-const z Lst)\n\
         (declare-const z2 Lst)\n\
         (assert (or (= y (cons x z)) (and (= y (cons x z2)) (= z2 z))))\n\
         (check-sat)\n"
    ));
    assert_eq!(v, "sat");
}

/// SOUNDNESS CONTROL for the cross-product case — the SECOND `or` alone
/// (no first `or`) must also stay `sat`, symmetric to the control above.
#[test]
fn and_of_two_ors_second_conjunct_alone_stays_sat() {
    let v = verdict(&format!(
        "{LST_DT}(declare-const x Int)\n\
         (declare-const y Lst)\n\
         (declare-const z Lst)\n\
         (declare-const y2 Lst)\n\
         (assert (or (= z (cons x y)) (and (= z (cons x y2)) (= y2 y))))\n\
         (check-sat)\n"
    ));
    assert_eq!(v, "sat");
}

/// SOUNDNESS CONTROL — an `or` where each branch establishes a DIFFERENT,
/// entirely non-conflicting equality (no shared variable between the two
/// branches at all). Superficially similar to the main repro's shape (an
/// `or` of two constructor equalities) but must stay `sat` — there is no
/// cycle in either branch, and the branches don't even interact.
#[test]
fn or_different_noncyclic_equalities_stays_sat() {
    let v = verdict(&format!(
        "{LST_DT}(declare-const x Int)\n\
         (declare-const w Int)\n\
         (declare-const y Lst)\n\
         (declare-const z Lst)\n\
         (assert (or (= y (cons x nil)) (= z (cons w nil))))\n\
         (check-sat)\n"
    ));
    assert_eq!(v, "sat");
}

/// SOUNDNESS CONTROL — deeper nesting, each top-level `or` branch itself an
/// `and` that establishes a DIFFERENT non-conflicting fact plus a negation
/// of the other branch's fact. No cycle is forced by either branch. Must
/// stay `sat`.
#[test]
fn deep_nested_distinct_facts_no_cycle_stays_sat() {
    let v = verdict(&format!(
        "{LST_DT}(declare-const x Int)\n\
         (declare-const w Int)\n\
         (declare-const y Lst)\n\
         (declare-const z Lst)\n\
         (assert (or (and (= y (cons x nil)) (not (= z (cons w nil))))\n\
                     (and (= z (cons w nil)) (not (= y (cons x nil))))))\n\
         (check-sat)\n"
    ));
    assert_eq!(v, "sat");
}

/// SOUNDNESS CONTROL — the ORIGINAL flat/unconditional acyclicity case
/// (no `Or` at all) must still be caught, confirming this new case-split
/// evaluator's presence doesn't somehow interfere with (or duplicate-reject)
/// the simpler pre-existing check. Mirrors
/// `dt_acyclicity_regression.rs::direct_self_cycle_is_unsat`.
#[test]
fn no_or_flat_cycle_still_unsat() {
    let v = verdict(&format!(
        "{LST_DT}(declare-const x Int)\n\
         (declare-const y Lst)\n\
         (assert (= y (cons x y)))\n\
         (check-sat)\n"
    ));
    assert_eq!(v, "unsat");
}
