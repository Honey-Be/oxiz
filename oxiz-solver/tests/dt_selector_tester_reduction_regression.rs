//! Permanent (z3-cross-checked) regressions for #406 — ground selector-of-
//! constructor and tester-of-constructor reduction.
//!
//! Root cause (selector half): the parser had NO `dt_selectors` map (only
//! `dt_constructors`), so an applied selector symbol like `(hd v)` ALWAYS
//! parsed as a generic opaque `TermKind::Apply` — never `TermKind::DtSelector`
//! — and also silently defaulted to `Bool` sort (selector names were never
//! registered in `self.functions` either). `(assert (not (= (hd (cons x y))
//! x)))` therefore read `sat` (z3: `unsat`). Fixed by:
//!   1. a parser-side `dt_selectors: FxHashMap<String, (ctor, field_index,
//!      result_sort)>`, populated by the same `declare-datatypes`/
//!      `declare-datatype` handlers that populate `dt_constructors`;
//!   2. an applied selector symbol now builds a real `TermKind::DtSelector`
//!      node with the correct field sort;
//!   3. a new `Solver::add_dt_selector_reduction_axioms` pass (mirroring
//!      `add_dt_cover_axioms`'s worklist) that asserts the VALID ground fact
//!      `(= (sel (C args…)) args[i])` whenever a selector's argument is a
//!      SYNTACTICALLY manifest application of its own owning constructor.
//!
//! Root cause (tester half): discovered empirically THIS phase while
//! confirming #391/F3 already covered testers — it only covers testers keyed
//! by a DATATYPE VARIABLE (`is_dt_variable`); a tester of a manifest
//! `DtConstructor` application, e.g. `((_ is cons) (cons x y))`, was never
//! decided at all. Fixed by an analogous `add_dt_tester_reduction_axioms`
//! pass: unlike the selector case, a tester of a manifest constructor
//! application is ALWAYS decidable (constructors are pairwise distinct), so
//! both the true and false cases are asserted directly.
//!
//! Both passes originally only covered the DIRECT syntactic case (the
//! argument is a manifest `DtConstructor` application in the term graph
//! itself) — a selector/tester of a variable only later shown equal to a
//! constructor application through ground equalities/congruence during
//! solving, OR a selector/tester CHAIN of depth ≥ 2, was a documented
//! residual (filed as #418).
//!
//! #418 items 1 & 2 close both of those: `encode.rs::resolve_dt_normal_form`
//! generalizes the direct one-level check into a recursive structural
//! resolver (closing depth-N chains, item 1) that ALSO consults a
//! check-sat-wide variable→constructor binding map built from
//! `check_dt.rs::collect_var_ctor_bindings` (closing the indirect-variable
//! case, item 2, including through a chain of plain variable equalities).
//! See that function's doc comment for the full design. The
//! `nested_*_chain_depth_2_residual` tests below, once `#[ignore]`d, are now
//! permanent green regressions; `indirect_var_*` tests cover item 2 plus its
//! soundness controls.

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
     (declare-datatypes ((Lst 0)) (((nil) (cons (hd Int) (tl Lst)))))\n\
     (declare-const x Int)\n\
     (declare-const y Lst)\n";

/// Selector-reduction pin — the exact #406 minimal repro: `hd(cons(x,y))`
/// must equal `x` (pre-fix: `sat`; z3: `unsat`).
#[test]
fn selector_of_matching_constructor_negated_is_unsat() {
    let v = verdict(&format!(
        "{LST_DT}(assert (not (= (hd (cons x y)) x)))\n(check-sat)\n"
    ));
    assert_eq!(v, "unsat");
}

/// Sat control — the POSITIVE (consistent) form of the same fact.
#[test]
fn selector_of_matching_constructor_positive_is_sat() {
    let v = verdict(&format!(
        "{LST_DT}(assert (= (hd (cons x y)) x))\n(check-sat)\n"
    ));
    assert_eq!(v, "sat");
}

/// Selector-reduction pin — the field selector (`tl`) of a NESTED
/// constructor application reduces end-to-end.
#[test]
fn nested_selector_reduces_end_to_end() {
    let v = verdict(
        "(set-logic ALL)\n\
         (declare-datatypes ((Lst 0)) (((nil) (cons (hd Int) (tl Lst)))))\n\
         (declare-const x Int)\n\
         (declare-const y Int)\n\
         (declare-const z Lst)\n\
         (assert (not (= (tl (cons x (cons y z))) (cons y z))))\n\
         (check-sat)\n",
    );
    assert_eq!(v, "unsat");
}

/// Soundness control — a selector applied to a DIFFERENT constructor of the
/// same datatype (`hd` of `nil`) has NO defined value in free-datatype
/// semantics. Both a concrete assignment and its negation must stay
/// satisfiable in ISOLATION — the fix must never fabricate a value.
#[test]
fn selector_of_wrong_constructor_is_unconstrained_positive() {
    let v = verdict(&format!("{LST_DT}(assert (= (hd nil) 5))\n(check-sat)\n"));
    assert_eq!(v, "sat");
}

#[test]
fn selector_of_wrong_constructor_is_unconstrained_negative() {
    let v = verdict(&format!(
        "{LST_DT}(assert (not (= (hd nil) 5)))\n(check-sat)\n"
    ));
    assert_eq!(v, "sat");
}

/// Tester-reduction pin — the exact #406-item-5 minimal repro: `is-cons` of
/// a manifest `cons` application must hold (pre-fix: `sat`; z3: `unsat`).
#[test]
fn tester_of_matching_constructor_negated_is_unsat() {
    let v = verdict(&format!(
        "{LST_DT}(assert (not ((_ is cons) (cons x y))))\n(check-sat)\n"
    ));
    assert_eq!(v, "unsat");
}

/// Sat control — the POSITIVE (consistent) form of the same fact.
#[test]
fn tester_of_matching_constructor_positive_is_sat() {
    let v = verdict(&format!(
        "{LST_DT}(assert ((_ is cons) (cons x y)))\n(check-sat)\n"
    ));
    assert_eq!(v, "sat");
}

/// Tester-reduction pin — a tester of a DIFFERENT constructor of the same
/// datatype is decidably FALSE (`is-nil` of a manifest `cons` is unsat).
#[test]
fn tester_of_wrong_constructor_positive_is_unsat() {
    let v = verdict(&format!(
        "{LST_DT}(assert ((_ is nil) (cons x y)))\n(check-sat)\n"
    ));
    assert_eq!(v, "unsat");
}

/// Sat control — the negated form of the wrong-constructor tester.
#[test]
fn tester_of_wrong_constructor_negated_is_sat() {
    let v = verdict(&format!(
        "{LST_DT}(assert (not ((_ is nil) (cons x y))))\n(check-sat)\n"
    ));
    assert_eq!(v, "sat");
}

/// Sanity control — an unconstrained datatype constant is still satisfiable
/// with both reduction passes wired in (no accidental over-constraining).
#[test]
fn unconstrained_dt_vars_stay_sat() {
    let v = verdict(&format!("{LST_DT}(check-sat)\n"));
    assert_eq!(v, "sat");
}

/// FIXED (#418 item 1, was a #406 residual): a selector-of-selector CHAIN of
/// depth ≥ 2, e.g. `(hd (tl (cons a (cons b c))))`, now reduces end-to-end.
/// The inner `(tl (cons a (cons b c)))` reduces directly (its arg is a
/// manifest `DtConstructor`), producing `(tl (cons a (cons b c))) = (cons b
/// c)` — the OUTER `hd`'s literal argument in the term graph is that
/// `DtSelector` node, not a manifest `DtConstructor`, so the OLD one-level
/// check missed it. `encode.rs::resolve_dt_normal_form` closes this: it
/// recursively resolves a `DtSelector`'s argument (chasing through however
/// many nested selector hops) before checking whether the result is a
/// manifest constructor of the matching shape. z3: `unsat`.
#[test]
fn nested_selector_chain_depth_2_residual() {
    let v = verdict(
        "(set-logic ALL)\n\
         (declare-datatypes ((Lst 0)) (((nil) (cons (hd Int) (tl Lst)))))\n\
         (declare-const a Int)\n\
         (declare-const b Int)\n\
         (declare-const c Lst)\n\
         (assert (not (= (hd (tl (cons a (cons b c)))) b)))\n\
         (check-sat)\n",
    );
    assert_eq!(v, "unsat");
}

/// FIXED (#418 item 1, was a #406 residual): the SAME depth≥2 chain gap as
/// `nested_selector_chain_depth_2_residual`, but for the tester-reduction
/// pass — `((_ is cons) (tl (cons a (cons b c))))` is decidably true (the
/// inner `tl` reduces to `(cons b c)`, manifestly `cons`-shaped) and now IS
/// reduced via `resolve_dt_normal_form`. z3: `unsat`.
#[test]
fn nested_tester_chain_depth_2_residual() {
    let v = verdict(
        "(set-logic ALL)\n\
         (declare-datatypes ((Lst 0)) (((nil) (cons (hd Int) (tl Lst)))))\n\
         (declare-const a Int)\n\
         (declare-const b Int)\n\
         (declare-const c Lst)\n\
         (assert (not ((_ is cons) (tl (cons a (cons b c))))))\n\
         (check-sat)\n",
    );
    assert_eq!(v, "unsat");
}

/// #418 item 1 — depth-3 selector chain (one level deeper than the pinned
/// depth-2 regression above), same datatype/shape family as the
/// `sel^k(c01^k(v))` sweep from the #418 task write-up (here expressed over
/// `Lst`'s `tl` selector, so `tl^3(cons(x0,cons(x1,cons(x2,y))))` should
/// reduce to `y`).
#[test]
fn nested_selector_chain_depth_3() {
    let v = verdict(
        "(set-logic ALL)\n\
         (declare-datatypes ((Lst 0)) (((nil) (cons (hd Int) (tl Lst)))))\n\
         (declare-const x0 Int)\n\
         (declare-const x1 Int)\n\
         (declare-const x2 Int)\n\
         (declare-const y Lst)\n\
         (assert (not (= (tl (tl (tl (cons x0 (cons x1 (cons x2 y)))))) y)))\n\
         (check-sat)\n",
    );
    assert_eq!(v, "unsat");
}

/// #418 item 1 — depth-4 selector chain (mixed `hd`/`tl`, closing at an
/// `Int` field four selector-applications deep).
#[test]
fn nested_selector_chain_depth_4() {
    let v = verdict(
        "(set-logic ALL)\n\
         (declare-datatypes ((Lst 0)) (((nil) (cons (hd Int) (tl Lst)))))\n\
         (declare-const x0 Int)\n\
         (declare-const x1 Int)\n\
         (declare-const x2 Int)\n\
         (declare-const x3 Int)\n\
         (declare-const y Lst)\n\
         (assert (not (= (hd (tl (tl (tl (cons x0 (cons x1 (cons x2 (cons x3 y)))))))) x3)))\n\
         (check-sat)\n",
    );
    assert_eq!(v, "unsat");
}

/// #418 item 1 — depth-3 TESTER chain: `is-cons` of a term reached through
/// three nested `tl` applications must decide `true` (the innermost `y` is
/// unconstrained, but the resolved term itself is manifestly `cons`-shaped
/// regardless of what `y` is).
#[test]
fn nested_tester_chain_depth_3() {
    let v = verdict(
        "(set-logic ALL)\n\
         (declare-datatypes ((Lst 0)) (((nil) (cons (hd Int) (tl Lst)))))\n\
         (declare-const x0 Int)\n\
         (declare-const x1 Int)\n\
         (declare-const x2 Int)\n\
         (declare-const x3 Int)\n\
         (declare-const y Lst)\n\
         (assert (not ((_ is cons) (tl (tl (cons x0 (cons x1 (cons x2 (cons x3 y)))))))))\n\
         (check-sat)\n",
    );
    assert_eq!(v, "unsat");
}

/// #418 item 2 — a selector applied to a VARIABLE that is only later shown
/// equal to a constructor application via a SEPARATE ground equality (not a
/// manifest constructor application at the selector's own argument
/// position). The per-assert structural pass (item 1) cannot see this by
/// itself since `z`'s binding to `(cons x y)` arrives in a LATER assertion
/// than `(hd z)`'s own encoding; the check-sat-wide pass
/// (`add_dt_indirect_var_reduction_axioms`) closes it. z3: `unsat`.
#[test]
fn indirect_var_selector_via_separate_equality_is_unsat() {
    let v = verdict(
        "(set-logic ALL)\n\
         (declare-datatypes ((Lst 0)) (((nil) (cons (hd Int) (tl Lst)))))\n\
         (declare-const x Int)\n\
         (declare-const y Lst)\n\
         (declare-const z Lst)\n\
         (assert (= z (cons x y)))\n\
         (assert (not (= (hd z) x)))\n\
         (check-sat)\n",
    );
    assert_eq!(v, "unsat");
}

/// #418 item 2 — the TESTER analogue of
/// `indirect_var_selector_via_separate_equality_is_unsat`: `z` is only shown
/// `cons`-shaped by a separate equality, not at the tester's own argument
/// position. z3: `unsat`.
#[test]
fn indirect_var_tester_via_separate_equality_is_unsat() {
    let v = verdict(
        "(set-logic ALL)\n\
         (declare-datatypes ((Lst 0)) (((nil) (cons (hd Int) (tl Lst)))))\n\
         (declare-const x Int)\n\
         (declare-const y Lst)\n\
         (declare-const z Lst)\n\
         (assert (= z (cons x y)))\n\
         (assert (not ((_ is cons) z)))\n\
         (check-sat)\n",
    );
    assert_eq!(v, "unsat");
}

/// #418 item 2 — the indirect binding reached through a CHAIN of plain
/// variable equalities (`w = z`, `z = (cons x y)`) rather than a single
/// direct `var = constructor` equality: `check_dt.rs::collect_var_ctor_bindings`
/// must transitively close over `dt_var_equalities` so `w` inherits `z`'s
/// binding. z3: `unsat`.
#[test]
fn indirect_var_selector_via_equality_chain_is_unsat() {
    let v = verdict(
        "(set-logic ALL)\n\
         (declare-datatypes ((Lst 0)) (((nil) (cons (hd Int) (tl Lst)))))\n\
         (declare-const x Int)\n\
         (declare-const y Lst)\n\
         (declare-const z Lst)\n\
         (declare-const w Lst)\n\
         (assert (= w z))\n\
         (assert (= z (cons x y)))\n\
         (assert (not (= (hd w) x)))\n\
         (check-sat)\n",
    );
    assert_eq!(v, "unsat");
}

/// Soundness control (#418) — a selector on a variable with NO
/// `var_ctor_term_eqs` binding at all (fully unconstrained) must stay `sat`:
/// the indirect-var pass must never fabricate a binding out of thin air.
#[test]
fn indirect_var_no_binding_stays_sat() {
    let v = verdict(
        "(set-logic ALL)\n\
         (declare-datatypes ((Lst 0)) (((nil) (cons (hd Int) (tl Lst)))))\n\
         (declare-const z Lst)\n\
         (assert (= (hd z) 5))\n\
         (check-sat)\n",
    );
    assert_eq!(v, "sat");
}

/// Soundness control (#418) — a variable bound to the WRONG constructor
/// (`z = nil`, a nullary constructor with no `hd` field) must leave `(hd z)`
/// fully unconstrained in BOTH directions, exactly like the pre-#418 direct
/// wrong-constructor controls above, just reached indirectly through a
/// variable binding instead of a literal argument.
#[test]
fn indirect_var_wrong_constructor_positive_stays_sat() {
    let v = verdict(
        "(set-logic ALL)\n\
         (declare-datatypes ((Lst 0)) (((nil) (cons (hd Int) (tl Lst)))))\n\
         (declare-const z Lst)\n\
         (assert (= z nil))\n\
         (assert (= (hd z) 5))\n\
         (check-sat)\n",
    );
    assert_eq!(v, "sat");
}

#[test]
fn indirect_var_wrong_constructor_negative_stays_sat() {
    let v = verdict(
        "(set-logic ALL)\n\
         (declare-datatypes ((Lst 0)) (((nil) (cons (hd Int) (tl Lst)))))\n\
         (declare-const z Lst)\n\
         (assert (= z nil))\n\
         (assert (not (= (hd z) 5)))\n\
         (check-sat)\n",
    );
    assert_eq!(v, "sat");
}

/// Soundness control (#418) — a binding established only inside an INACTIVE
/// `or` branch must NOT be treated as a global `var_ctor_term_eqs` fact.
/// `check_dt.rs::collect_dt_constraints_v2`'s existing polarity gating
/// already protects this (an `Or`'s children are never collected under a
/// positive context — see that function's doc comments); this test
/// exercises the SAME protection through the new indirect-var reduction
/// pass, since `z = (cons x y)` here is only true in ONE disjunct of an
/// `or`, not unconditionally. Must stay `sat` (z3 agrees — the `or` is
/// satisfiable by taking the `z = nil` disjunct, under which `(hd z) = x`
/// is unconstrained).
#[test]
fn indirect_var_or_branch_binding_stays_sat() {
    let v = verdict(
        "(set-logic ALL)\n\
         (declare-datatypes ((Lst 0)) (((nil) (cons (hd Int) (tl Lst)))))\n\
         (declare-const x Int)\n\
         (declare-const y Lst)\n\
         (declare-const z Lst)\n\
         (assert (or (= z (cons x y)) (= z nil)))\n\
         (assert (not (= (hd z) x)))\n\
         (check-sat)\n",
    );
    assert_eq!(v, "sat");
}
