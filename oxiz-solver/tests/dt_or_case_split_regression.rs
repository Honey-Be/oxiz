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
//!
//! Extended for #422 item 1 (non-cycle, disequality-forced conflicts — see
//! the `#422 item 1` test section) and #423 item 1 (the `Eq` negative arm's
//! `dt_diseq_pairs` push is no longer DT-sort-gated — see the `#423 item 1`
//! test section): this evaluator has NO SAT-level fallback of its own, so
//! it is the shape where the `both_dt_sorted` gate's removal has the most
//! severe, DEFAULT-config-reachable impact (the flat path was already
//! masked under default settings by the SAT-level `simplify`-gated
//! injection — see the `#422 item 1 — FLAT PATH` section below).

use oxiz_core::ast::TermManager;
use oxiz_core::sort::DataTypeConstructor;
use oxiz_solver::{Context, Solver, SolverConfig, SolverResult};
use smallvec::smallvec;

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

// ---------------------------------------------------------------------
// #422 item 1 — OR-BRANCH NON-CYCLE CONFLICTS. `dt_items_force_conflict`
// previously checked each branch's closed hypothesis for an ACYCLICITY
// conflict ONLY (`cycle_exists_given`) — a branch internally contradictory
// for a DIFFERENT reason (constructor injectivity forcing an equality that
// contradicts an asserted disequality IN THE SAME BRANCH) was invisible to
// it. Closed by threading a fourth hypothesis slice, `h_diseq` (cloned by
// value through every recursive call exactly like `h_var`/`h_ctor`/`h_sel`
// — same branch-isolation discipline), and checking `closure.
// forces_disequality_conflict(h_diseq)` at the leaf alongside the existing
// cycle check. See `check_dt.rs::dt_items_force_conflict`'s "#422 — beyond
// acyclicity-only" doc section.
// ---------------------------------------------------------------------

/// #422 item 1's exact repro, OR-WRAPPED: `x=cons(a,b)`, `x=cons(c,b)`,
/// `(not (= a c))` all inside ONE branch of an `or`, with a plain
/// already-supported cyclic branch as the sibling. Neither branch is
/// unconditionally forcing on its own syntax (branch 1 needs injectivity +
/// the disequality check; branch 2 is an ordinary flat cycle), but BOTH are
/// conflict-forced, so the whole `or` is `unsat`. Uses DT-SORTED fields
/// (`Node`) so the disequality is collected via the DT-sort-gated `Eq`
/// negative arm (see `collect_dt_constraints_v2`'s doc comment) — the
/// literal target shape STEP 2 was written for. Pre-fix: `sat` (branch 1's
/// injectivity-forced disequality conflict was invisible to the OR-branch
/// evaluator, which only ever checked acyclicity). z3/cvc5: `unsat`.
#[test]
fn or_branch_injectivity_forced_disequality_dtfields_is_unsat() {
    let dt = "(set-logic ALL)\n\
        (declare-datatypes ((Node422a 0)) (((leaf422a) \
            (mk422a (mkf0_422a Bool) (mkf1_422a Int) (mkf2_422a Node422a)))))\n";
    let v = verdict(&format!(
        "{dt}(declare-const vb0 Bool) (declare-const vi1 Int)\n\
         (declare-const na Node422a) (declare-const nc Node422a)\n\
         (declare-const mbx Node422a) (declare-const w Node422a)\n\
         (assert (or\n\
           (and (= mbx (mk422a vb0 4 na)) (= mbx (mk422a vb0 vi1 nc)) (not (= na nc)))\n\
           (= w (mk422a vb0 0 w))\n\
         ))\n\
         (check-sat)\n"
    ));
    assert_eq!(v, "unsat");
}

/// The SAME OR-branch shape, but the injectivity-forced disequality is
/// expressed as `(distinct a c)` over Int-sorted fields instead — since
/// `Distinct`'s positive-context `dt_diseq_pairs` push is UNGATED by sort
/// (unlike the `Eq` negative arm), this closes the OR-branch case even for
/// NON-datatype-sorted fields, a strictly BROADER completeness win than the
/// DT-sort-gated `Eq` path alone provides. Pre-fix: `sat`. z3/cvc5: `unsat`.
#[test]
fn or_branch_injectivity_forced_distinct_intfields_is_unsat() {
    let pair_dt = "(set-logic ALL)\n\
        (declare-datatypes ((MyPair422 0)) (((cons422 (hd422 Int) (tl422 Int)))))\n\
        (declare-datatypes ((Lst422 0)) (((nil422) (lcons422 (lhd422 Int) (ltl422 Lst422)))))\n";
    let v = verdict(&format!(
        "{pair_dt}(declare-const x MyPair422) (declare-const a Int) (declare-const b Int)\n\
         (declare-const c Int)\n\
         (declare-const w Lst422) (declare-const wi Int)\n\
         (assert (or\n\
           (and (= x (cons422 a b)) (= x (cons422 c b)) (distinct a c))\n\
           (= w (lcons422 wi w))\n\
         ))\n\
         (check-sat)\n"
    ));
    assert_eq!(v, "unsat");
}

/// SOUNDNESS CONTROL for the two tests above: identical shape, but the
/// second (always-cyclic) branch is replaced with an ORDINARY satisfiable
/// fact, so NOT every branch is conflict-forced — the whole `or` must stay
/// `sat`, confirming `h_diseq` doesn't somehow leak across branches or
/// otherwise over-fire.
#[test]
fn or_branch_injectivity_forced_disequality_other_branch_not_stays_sat() {
    let dt = "(set-logic ALL)\n\
        (declare-datatypes ((Node422b 0)) (((leaf422b) \
            (mk422b (mkf0_422b Bool) (mkf1_422b Int) (mkf2_422b Node422b)))))\n";
    let v = verdict(&format!(
        "{dt}(declare-const vb0 Bool) (declare-const vi1 Int)\n\
         (declare-const na Node422b) (declare-const nc Node422b)\n\
         (declare-const mbx Node422b) (declare-const w Node422b)\n\
         (assert (or\n\
           (and (= mbx (mk422b vb0 4 na)) (= mbx (mk422b vb0 vi1 nc)) (not (= na nc)))\n\
           (= w leaf422b)\n\
         ))\n\
         (check-sat)\n"
    ));
    assert_eq!(v, "sat");
}

// ---------------------------------------------------------------------
// #423 item 1 — the MORE SEVERE manifestation: `dt_items_force_conflict`
// (this OR-branch evaluator) has NO SAT-level fallback at all (unlike the
// flat path, which the FLAT path's `simplify: true`-gated
// `inject_dt_derived_ctor_equalities` happens to mask under default
// settings). Before #423, a plain `(not (= a c))` between Int-sorted fields
// was invisible to `dt_diseq_pairs` (the `Eq` negative arm's push was
// DT-SORT-GATED), so this exact shape read spurious `sat` under DEFAULT
// config — no `simplify: false`, no special preset, just the ordinary
// `Context`/SMT-LIB front end. This is a STRICTLY BROADER-reach repro than
// `or_branch_injectivity_forced_disequality_dtfields_is_unsat` above (which
// used DT-sorted fields specifically to stay reachable through the old
// gate) — confirms #423 item 1 closes the gap for the common `=`/`not`
// surface syntax, not just `distinct`.
// ---------------------------------------------------------------------

/// #423 item 1's literal motivating repro: an `or` where branch 1
/// (injectivity-forced disequality over Int-sorted fields, `(not (= a
/// c))`) has no SAT-level fallback, and branch 2 is an ordinary
/// already-supported flat cycle. Pre-#423: `sat` (branch 1's conflict was
/// invisible to `dt_diseq_pairs`). z3/cvc5: `unsat`.
#[test]
fn or_branch_injectivity_forced_noteq_intfields_is_unsat() {
    let dt = "(set-logic ALL)\n\
        (declare-datatypes ((MyPair423 0)) (((cons423 (hd423 Int) (tl423 Int)))))\n\
        (declare-datatypes ((Lst423 0)) (((nil423) (lcons423 (lhd423 Int) (ltl423 Lst423)))))\n";
    let v = verdict(&format!(
        "{dt}(declare-const x MyPair423) (declare-const a Int) (declare-const b Int)\n\
         (declare-const c Int)\n\
         (declare-const w Lst423) (declare-const wi Int)\n\
         (assert (or\n\
           (and (= x (cons423 a b)) (= x (cons423 c b)) (not (= a c)))\n\
           (= w (lcons423 wi w))\n\
         ))\n\
         (check-sat)\n"
    ));
    assert_eq!(v, "unsat");
}

/// SAT-CONTROL sibling of the test above: the SAME always-injectivity-forced
/// first branch, but the second branch is replaced with an ORDINARY
/// satisfiable fact (no cycle) instead of another forced conflict — NOT
/// every branch is conflict-forced, so the whole `or` must stay `sat`,
/// confirming #423 item 1's ungated push doesn't over-fire (e.g. by somehow
/// making the evaluator treat the `or` as conjunctive).
#[test]
fn or_branch_injectivity_forced_noteq_intfields_other_branch_not_stays_sat() {
    let dt = "(set-logic ALL)\n\
        (declare-datatypes ((MyPair423b 0)) (((cons423b (hd423b Int) (tl423b Int)))))\n\
        (declare-datatypes ((Lst423b 0)) (((nil423b) (lcons423b (lhd423b Int) (ltl423b Lst423b)))))\n";
    let v = verdict(&format!(
        "{dt}(declare-const x MyPair423b) (declare-const a Int) (declare-const b Int)\n\
         (declare-const c Int)\n\
         (declare-const w Lst423b) (declare-const wi Int)\n\
         (assert (or\n\
           (and (= x (cons423b a b)) (= x (cons423b c b)) (not (= a c)))\n\
           (= w (lcons423b wi nil423b))\n\
         ))\n\
         (check-sat)\n"
    ));
    assert_eq!(v, "sat");
}

// ---------------------------------------------------------------------
// #422 item 1 — FLAT PATH, `:simplify false` INDEPENDENCE (STEP 6). The
// task's own motivating concern: the flat (non-OR) path used to catch this
// conflict "for free" only once the derived ctor=ctor fact was injected as
// a SAT-level clause AND decomposed by the simplifier
// (`inject_dt_derived_ctor_equalities`, gated on `config.simplify`) — a
// real, reachable config (`--preset minimal`, the portfolio's `LocalSearch`
// strategy). `compute_dt_equality_closure`'s result is simplify-independent
// by construction, so `check_dt_constraints`'s new `closure.
// forces_disequality_conflict(&dt_diseq_pairs)` call (STEP 6) closes this
// regardless.
//
// At the time these tests were written, the SMT-LIB front end
// (`Context::set_option("simplify", ...)`) did not wire through to
// `SolverConfig::simplify` at all — #423 item 3 fixed that separately (see
// `oxiz-solver/src/context.rs`'s `simplify` match arm and
// `context_simplify_option_wiring.rs`). These tests still use the public
// `Solver::with_config`/`Solver::assert`/`Solver::check` API directly
// (mirroring `clean_mbqi_wiring.rs`'s pattern) rather than
// `Context::execute_script`, since that remains the more direct way to get
// a genuine `simplify: false` run without depending on the CLI/SMT-LIB
// option-parsing layer.
// ---------------------------------------------------------------------

/// Item 1's repro with DT-SORTED fields (the literal Eq-negative-arm target
/// shape), flat (no `or` at all), under `simplify: false`. Must still be
/// `unsat` — `check_dt_constraints`'s Rust-level pre-pass runs
/// UNCONDITIONALLY (never gated on `config.simplify`), so this is expected
/// to hold regardless.
#[test]
fn flat_injectivity_forced_disequality_dtfields_simplify_false_is_unsat() {
    let mut cfg = SolverConfig::default();
    cfg.simplify = false;
    let mut s = Solver::with_config(cfg);
    let mut m = TermManager::new();

    let bool_sort = m.sorts.bool_sort;
    let int_sort = m.sorts.int_sort;
    let node_sort = m.sorts.mk_datatype_sort("Node422g");
    let mk_name = m.sorts.intern_str("mk422g");
    let f0 = m.sorts.intern_str("mkf0_422g");
    let f1 = m.sorts.intern_str("mkf1_422g");
    let f2 = m.sorts.intern_str("mkf2_422g");
    let leaf_name = m.sorts.intern_str("leaf422g");
    let mk = DataTypeConstructor {
        name: mk_name,
        selectors: smallvec![(f0, bool_sort), (f1, int_sort), (f2, node_sort)],
    };
    let leaf = DataTypeConstructor { name: leaf_name, selectors: smallvec![] };
    m.sorts.declare_datatype("Node422g", vec![mk, leaf]);

    let vb0 = m.mk_var("vb0", bool_sort);
    let vi1 = m.mk_var("vi1", int_sort);
    let na = m.mk_var("na", node_sort);
    let nc = m.mk_var("nc", node_sort);
    let mbx = m.mk_var("mbx", node_sort);
    let four = m.mk_int(4);

    let mk1 = m.mk_dt_constructor("mk422g", [vb0, four, na], node_sort);
    let mk2 = m.mk_dt_constructor("mk422g", [vb0, vi1, nc], node_sort);
    let eq1 = m.mk_eq(mbx, mk1);
    let eq2 = m.mk_eq(mbx, mk2);
    let eq_nanc = m.mk_eq(na, nc);
    let diseq = m.mk_not(eq_nanc);

    s.assert(eq1, &mut m);
    s.assert(eq2, &mut m);
    s.assert(diseq, &mut m);

    let r = s.check(&mut m);
    assert_eq!(
        r,
        SolverResult::Unsat,
        "the flat Rust-level pre-pass (check_dt_constraints) must close this \
         regardless of config.simplify"
    );
}

/// The SAME flat repro, but expressed via `(distinct a c)` over Int-sorted
/// (non-DT-sorted) fields under `simplify: false`. Since `Distinct`'s
/// positive-context `dt_diseq_pairs` push is UNGATED by sort, this ALSO
/// closes under `simplify: false` — a strictly broader completeness result
/// than the DT-sort-gated `Eq`-negative path (see the next test for that
/// path's own honest residual).
#[test]
fn flat_injectivity_forced_distinct_intfields_simplify_false_is_unsat() {
    let mut cfg = SolverConfig::default();
    cfg.simplify = false;
    let mut s = Solver::with_config(cfg);
    let mut m = TermManager::new();
    let int_sort = m.sorts.int_sort;
    let pair_sort = m.sorts.mk_datatype_sort("Pair422h");
    let cons_name = m.sorts.intern_str("cons422h");
    let hd = m.sorts.intern_str("hd422h");
    let tl = m.sorts.intern_str("tl422h");
    let ctor = DataTypeConstructor {
        name: cons_name,
        selectors: smallvec![(hd, int_sort), (tl, int_sort)],
    };
    m.sorts.declare_datatype("Pair422h", vec![ctor]);

    let x = m.mk_var("x", pair_sort);
    let a = m.mk_var("a", int_sort);
    let b = m.mk_var("b", int_sort);
    let c = m.mk_var("c", int_sort);
    let cons_ab = m.mk_dt_constructor("cons422h", [a, b], pair_sort);
    let cons_cb = m.mk_dt_constructor("cons422h", [c, b], pair_sort);
    let eq1 = m.mk_eq(x, cons_ab);
    let eq2 = m.mk_eq(x, cons_cb);
    let distinct = m.mk_distinct([a, c]);

    s.assert(eq1, &mut m);
    s.assert(eq2, &mut m);
    s.assert(distinct, &mut m);

    let r = s.check(&mut m);
    assert_eq!(r, SolverResult::Unsat);
}

/// CLOSED, #423 (previously a documented residual under #422 — this shape
/// was NEVER caught before #422, and #422 only narrowed, not eliminated,
/// it): the SAME flat repro, disequality expressed as plain `(not (= a
/// c))` over Int-sorted (non-DT-sorted) fields, under `simplify: false`.
/// The `Eq` negative arm's `dt_diseq_pairs` push used to be DT-SORT-GATED
/// (via the now-DELETED `both_dt_sorted` helper), so this exact combination
/// (non-DT sort AND `simplify: false` AND expressed via `=`/`not` rather
/// than `distinct`) was not closed. #423 item 1 removed that gate — the
/// push is now unconditional, identical to `Distinct`'s own always-safe
/// argument (see `check_dt.rs::collect_dt_constraints_v2`'s `Eq` negative
/// arm doc comment) — so this is now `Unsat`, matching z3/cvc5, with no
/// dependency on `config.simplify` at all.
#[test]
fn flat_injectivity_forced_noteq_intfields_simplify_false_is_unsat() {
    let mut cfg = SolverConfig::default();
    cfg.simplify = false;
    let mut s = Solver::with_config(cfg);
    let mut m = TermManager::new();
    let int_sort = m.sorts.int_sort;
    let pair_sort = m.sorts.mk_datatype_sort("Pair422i");
    let cons_name = m.sorts.intern_str("cons422i");
    let hd = m.sorts.intern_str("hd422i");
    let tl = m.sorts.intern_str("tl422i");
    let ctor = DataTypeConstructor {
        name: cons_name,
        selectors: smallvec![(hd, int_sort), (tl, int_sort)],
    };
    m.sorts.declare_datatype("Pair422i", vec![ctor]);

    let x = m.mk_var("x", pair_sort);
    let a = m.mk_var("a", int_sort);
    let b = m.mk_var("b", int_sort);
    let c = m.mk_var("c", int_sort);
    let cons_ab = m.mk_dt_constructor("cons422i", [a, b], pair_sort);
    let cons_cb = m.mk_dt_constructor("cons422i", [c, b], pair_sort);
    let eq1 = m.mk_eq(x, cons_ab);
    let eq2 = m.mk_eq(x, cons_cb);
    let eq_ac = m.mk_eq(a, c);
    let diseq = m.mk_not(eq_ac);

    s.assert(eq1, &mut m);
    s.assert(eq2, &mut m);
    s.assert(diseq, &mut m);

    let r = s.check(&mut m);
    assert_eq!(
        r,
        SolverResult::Unsat,
        "#423 item 1 closed this — the Eq negative arm's dt_diseq_pairs push \
         is no longer DT-sort-gated, so this is unsat regardless of \
         config.simplify"
    );
}

/// CONTROL — the IDENTICAL repro with the DEFAULT config (`simplify:
/// true`), via the pre-existing #419 SAT-level injection mechanism
/// (independent of #423 item 1's Rust-level pre-pass fix above). Both
/// configs now agree (`unsat`), confirming #423 introduces no regression on
/// the default (every real front end's) configuration.
#[test]
fn flat_injectivity_forced_noteq_intfields_simplify_true_default_is_unsat() {
    let mut s = Solver::new();
    let mut m = TermManager::new();
    let int_sort = m.sorts.int_sort;
    let pair_sort = m.sorts.mk_datatype_sort("Pair422j");
    let cons_name = m.sorts.intern_str("cons422j");
    let hd = m.sorts.intern_str("hd422j");
    let tl = m.sorts.intern_str("tl422j");
    let ctor = DataTypeConstructor {
        name: cons_name,
        selectors: smallvec![(hd, int_sort), (tl, int_sort)],
    };
    m.sorts.declare_datatype("Pair422j", vec![ctor]);

    let x = m.mk_var("x", pair_sort);
    let a = m.mk_var("a", int_sort);
    let b = m.mk_var("b", int_sort);
    let c = m.mk_var("c", int_sort);
    let cons_ab = m.mk_dt_constructor("cons422j", [a, b], pair_sort);
    let cons_cb = m.mk_dt_constructor("cons422j", [c, b], pair_sort);
    let eq1 = m.mk_eq(x, cons_ab);
    let eq2 = m.mk_eq(x, cons_cb);
    let eq_ac = m.mk_eq(a, c);
    let diseq = m.mk_not(eq_ac);

    s.assert(eq1, &mut m);
    s.assert(eq2, &mut m);
    s.assert(diseq, &mut m);

    let r = s.check(&mut m);
    assert_eq!(r, SolverResult::Unsat);
}

// ---------------------------------------------------------------------------
// 2026-07-17 — stack-overflow regression: `dt_items_force_conflict` was a
// self-recursive evaluator whose LINEAR continuation (consume one work-list
// item, recurse on the rest) grew the native stack with the total item count
// (assertions + emitted MBQI lemmas), not just case-split nesting. On the
// lemma-heavy corpus row `datatypes-match-2/ob07` it overflowed the 8 MiB
// main-thread stack (SIGSEGV ~8.4s, ~40% reproduction — timing-dependent via
// the MBQI guard). Third instance of the "pre-existing unbounded recursion
// newly reached" class (cf. `EufSolver::explain_equality`'s worklist rewrite
// and `check_dt_acyclicity`'s deliberately iterative DFS). Fixed by
// rewriting the evaluator iteratively: the linear continuation is an
// in-place loop, only genuine case splits push heap-allocated units.
//
// This test runs on a DEFAULT test thread (2 MiB stack): the old recursive
// code overflows it at a few thousand frames, the iterative version handles
// tens of thousands of work-list items in O(1) native stack. Verified as a
// genuine differential: with only check_dt.rs reverted to the recursive
// version (`git stash push -- oxiz-solver/src/solver/check_dt.rs`), this
// test dies with SIGSEGV/stack-overflow; with the rewrite it passes.
// ---------------------------------------------------------------------------

/// 25k flat Bool assertions = 25k linear work-list items for the case-split
/// evaluator, well within `DT_OR_CASE_SPLIT_BUDGET` (200k) so the whole
/// chain is actually walked before the leaf check. Old code: ~25k-deep
/// native recursion -> overflows the 2 MiB test-thread stack. New code:
/// bounded native stack, verdict `sat`.
#[test]
fn deep_linear_worklist_does_not_overflow_the_stack() {
    let n = 25_000;
    let mut script = String::with_capacity(n * 40 + 64);
    script.push_str("(set-logic ALL)\n");
    for i in 0..n {
        script.push_str(&format!("(declare-const dlb{i} Bool)\n(assert dlb{i})\n"));
    }
    script.push_str("(check-sat)\n");
    assert_eq!(verdict(&script), "sat");
}
