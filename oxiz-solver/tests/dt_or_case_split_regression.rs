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
//!
//! Extended for #419 (OR-branch wiring): `dt_items_force_conflict` now
//! closes each branch's accumulated hypothesis via `Solver::compute_dt_
//! equality_closure` (the same iterative closure the flat, non-OR
//! acyclicity check already uses — items 1/2's same-constructor ctor=ctor
//! derivation and selector-resolution derivation) BEFORE checking it for a
//! cycle, instead of checking the raw, unclosed hypothesis directly. See
//! the tests below the original #418 set, and `check_dt.rs::dt_items_
//! force_conflict`'s "#419 — equality closure wiring" doc section, for the
//! full design (branch isolation + shared step-budget with the case-split
//! work-list).

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

// ---------------------------------------------------------------------
// #419 (OR-branch wiring) — `dt_items_force_conflict` now closes each
// branch's hypothesis via `compute_dt_equality_closure` (item 1's
// same-constructor ctor=ctor derivation + item 2's selector-resolution
// derivation) before checking it for a cycle, instead of checking the RAW,
// unclosed hypothesis directly. Every test below was verified to read
// (wrongly) `sat` against the PRE-wiring binary and `unsat` (matching z3)
// against the POST-wiring binary — see `check_dt.rs::dt_items_force_
// conflict`'s "#419 — equality closure wiring" doc section for the design.
// ---------------------------------------------------------------------

/// #419 item 2 in ONE branch of an `or`, a plain flat cycle in the sibling.
/// Branch 1 (`z=cons(x,y)` + `(tl z)=z`) is NOT unconditionally cyclic on
/// its own raw syntax — it only becomes cyclic once `(tl z)` is resolved
/// (via `z`'s own binding) to `y`, giving the derived `y=z`, which combined
/// with `z=cons(x,y)` is exactly `y=cons(x,y)` — a cycle. Branch 2
/// (`w=cons(x,w)`) is the ordinary already-supported flat case. Both
/// branches conflict-forced => whole `or` unsat. Pre-fix: branch 1's
/// `(tl z)=z` fact was silently discarded (never threaded into `h_var`/
/// `h_ctor`), so branch 1 was NEVER flagged, and the whole `or` wrongly
/// stayed `sat`.
#[test]
fn or_branch_needs_selector_resolution_closure_to_reveal_cycle_is_unsat() {
    let v = verdict(&format!(
        "{LST_DT}(declare-const x Int)\n\
         (declare-const z Lst) (declare-const y Lst)\n\
         (declare-const w Lst)\n\
         (assert (or (and (= z (cons x y)) (= (tl z) z))\n\
                     (= w (cons x w))))\n\
         (check-sat)\n"
    ));
    assert_eq!(v, "unsat");
}

/// #419 item 2 in BOTH branches of an `or` (independent fresh variables per
/// branch) — each branch needs its OWN closure computation to reveal its
/// own cycle; neither is flat. Confirms the per-leaf closure call fires
/// correctly for every branch of a case split, not just the first one
/// visited.
#[test]
fn or_both_branches_need_selector_resolution_closure_is_unsat() {
    let v = verdict(&format!(
        "{LST_DT}(declare-const x1 Int) (declare-const z1 Lst) (declare-const y1 Lst)\n\
         (declare-const x2 Int) (declare-const z2 Lst) (declare-const y2 Lst)\n\
         (assert (or (and (= z1 (cons x1 y1)) (= (tl z1) z1))\n\
                     (and (= z2 (cons x2 y2)) (= (tl z2) z2))))\n\
         (check-sat)\n"
    ));
    assert_eq!(v, "unsat");
}

/// #419 item 2's closure-dependent branch NESTED inside an outer `and`
/// alongside an unrelated conjunct — confirms the leaf-time closure call
/// composes correctly with the pre-existing And/Or/Not work-list recursion
/// (the closure is computed once the FULL work-list — including the outer
/// `and`'s other conjunct — has been walked, not just the `or` node itself
/// in isolation).
#[test]
fn nested_and_or_selector_resolution_closure_is_unsat() {
    let v = verdict(&format!(
        "{LST_DT}(declare-const x Int) (declare-const z Lst) (declare-const y Lst)\n\
         (declare-const w Lst) (declare-const v Int)\n\
         (assert (and (= v 5)\n\
                      (or (and (= z (cons x y)) (= (tl z) z))\n\
                          (= w (cons x w)))))\n\
         (check-sat)\n"
    ));
    assert_eq!(v, "unsat");
}

/// A branch combining a same-constructor MULTI-BINDING fact (`x=cons(a,b)`
/// and `x=cons(c,b)`, item 1's shape) together with a selector-resolution
/// fact (`(tl x)=x`, item 2's shape) in the SAME branch — exercises `h_var`/
/// `h_ctor`/`h_sel` all being threaded and closed together for one branch.
/// (The multi-binding here is not itself LOAD-BEARING for the cycle — `x`
/// is already directly bound via either ctor-equality, so plain union-find
/// over the raw facts already reaches the cycle without needing item 1's
/// dedicated `derived_ctor_eqs` step; it is included to confirm a branch
/// mixing both shapes of hypothesis fact still closes and conflicts
/// correctly, not to claim item 1's derivation is uniquely load-bearing
/// for cycle detection specifically — see the session notes on why item 1's
/// value for THIS particular consumer is subsumed by ordinary transitive
/// union-find.)
#[test]
fn or_branch_combines_multibinding_and_selector_facts_is_unsat() {
    let v = verdict(&format!(
        "{LST_DT}(declare-const x Lst) (declare-const a Int) (declare-const b Lst)\n\
         (declare-const c Int) (declare-const w Lst)\n\
         (assert (or (and (= x (cons a b)) (= x (cons c b)) (= (tl x) x))\n\
                     (= w (cons a w))))\n\
         (check-sat)\n"
    ));
    assert_eq!(v, "unsat");
}

/// CROSS-BRANCH-LEAK CONTROL targeting THIS change specifically: branch A
/// alone would close (via the item-2 selector-resolution derivation) and
/// force a conflict, but branch B does NOT force any conflict (`w=cons(x,
/// nil)` is perfectly acyclic — `nil` terminates the list). Since NOT every
/// branch is conflict-forced, the whole `or` must stay `sat`. This is the
/// direct analogue of `or_only_one_branch_cyclic_stays_sat` for the NEW
/// closure-dependent branch shape: it confirms branch A's closure (and,
/// implicitly, whatever it derives) is never combined with — or allowed to
/// somehow force a verdict on — branch B's independent, non-conflicting
/// hypothesis. If closures somehow leaked across branches (e.g. via a
/// shared mutable accumulator instead of per-branch cloned `h_var`/`h_ctor`/
/// `h_sel` slices), this is exactly the kind of case that would wrongly
/// flip to `unsat`.
#[test]
fn or_one_branch_closure_forced_other_branch_not_stays_sat() {
    let v = verdict(&format!(
        "{LST_DT}(declare-const x Int) (declare-const z Lst) (declare-const y Lst)\n\
         (declare-const w Lst)\n\
         (assert (or (and (= z (cons x y)) (= (tl z) z))\n\
                     (= w (cons x nil))))\n\
         (check-sat)\n"
    ));
    assert_eq!(v, "sat");
}
