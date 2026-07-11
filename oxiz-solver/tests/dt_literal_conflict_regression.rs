//! Permanent (z3/cvc5-cross-checked) regressions for #424 item 3 —
//! literal-vs-literal forced-equal conflicts, a `:simplify false` gap.
//!
//! Root cause: `compute_dt_equality_closure`'s injectivity-decomposition
//! step derives per-field equalities as raw `(TermId, TermId)` pairs pushed
//! DIRECTLY into the closure's own internal equality list, WITHOUT ever
//! constructing a term-level `Eq` node via `manager.mk_eq` — so `mk_eq`'s
//! constant-folding (which only fires when an actual `Eq` TERM is built)
//! never gets a chance to notice that two forced field VALUES are different
//! literals. `(assert (= x (C 7 d))) (assert (= x (C 9 d)))` under
//! `:simplify false` therefore read spurious `sat` (z3/cvc5: `unsat`) —
//! nothing checked "does the closure force two DIFFERENT literal constants
//! into the same equivalence class" as an INTRINSIC, always-true conflict
//! (independent of any user-asserted disequality: two different literal
//! VALUES of the same base sort are trivially, definitionally distinct).
//!
//! Fix, in `DtEqualityClosure`'s impl block (`check_dt.rs`):
//!   1. `build_parent` — a PURE refactor extracting the union-find
//!      construction previously inlined in `forces_disequality_conflict`
//!      (behavior byte-for-byte unchanged).
//!   2. `has_intrinsic_literal_conflict(&self, manager: &TermManager) ->
//!      bool` — groups the closure's equality classes by root, and for
//!      EACH class independently (state reset per-class — see the
//!      dedicated soundness-scoping test below) scans for two different
//!      `IntConst`/`RealConst`/`BitVecConst`(same width)/`True`+`False`
//!      members.
//!   3. Wired via `||` into BOTH existing `forces_disequality_conflict`
//!      call sites (the flat `check_dt_constraints` path and
//!      `dt_items_force_conflict`'s OR-branch leaf).

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

const INT_PAIR_DT: &str = "(set-logic ALL)\n\
     (declare-datatypes ((IPD 0)) (((C (fld Int) (snd Int)))))\n";

const REAL_PAIR_DT: &str = "(set-logic ALL)\n\
     (declare-datatypes ((RPD 0)) (((C (fld Real) (snd Int)))))\n";

// `(_ BitVec n)` is NOT expressible as a datatype selector's sort by this
// parser's grammar today (`parse_declare_datatype{,s}` reads a selector sort
// via a single `expect_symbol()` token, so a compound sort expression like
// `(_ BitVec 8)` fails to parse there — a separate, pre-existing,
// out-of-scope grammar gap; ordinary `(declare-const x (_ BitVec 8))`
// parses fine, confirming it's specific to the datatype-field grammar). The
// parser's OWN "BitVecN" single-token compromise shorthand
// (`parse_sort_name`'s `strip_prefix("BitVec")` handling) works fine as a
// selector sort, so it's used here instead.
const BV8_PAIR_DT: &str = "(set-logic ALL)\n\
     (declare-datatypes ((BVPD 0)) (((C (fld BitVec8) (snd Int)))))\n";

const BOOL_PAIR_DT: &str = "(set-logic ALL)\n\
     (declare-datatypes ((BPD 0)) (((C (fld Bool) (snd Int)))))\n";

// ---------------------------------------------------------------------
// Core motivating repro — both `:simplify` settings.
// ---------------------------------------------------------------------

/// THE exact motivating repro, under `:simplify false` — the gap this item
/// closes. Pre-fix: spurious `sat`. Post-fix / z3 / cvc5: `unsat`.
#[test]
fn core_repro_simplify_false_is_unsat() {
    let v = verdict(&format!(
        "{INT_PAIR_DT}(set-option :simplify false)\n\
         (declare-const x IPD) (declare-const d Int)\n\
         (assert (= x (C 7 d)))\n\
         (assert (= x (C 9 d)))\n\
         (check-sat)\n"
    ));
    assert_eq!(v, "unsat");
}

/// SAME repro, DEFAULT `:simplify true` — confirms this was ALREADY `unsat`
/// via the independent SAT-level route (`DatatypeRewriter::
/// rewrite_constructor_eq`'s `config.simplify`-gated decomposition), i.e.
/// this fix introduces no regression on the already-working path.
#[test]
fn core_repro_default_simplify_is_unsat() {
    let v = verdict(&format!(
        "{INT_PAIR_DT}(declare-const x IPD) (declare-const d Int)\n\
         (assert (= x (C 7 d)))\n\
         (assert (= x (C 9 d)))\n\
         (check-sat)\n"
    ));
    assert_eq!(v, "unsat");
}

// ---------------------------------------------------------------------
// Sort coverage — Real, BitVec (same width / different width), Bool.
// ---------------------------------------------------------------------

/// `RealConst` variant — two different rational literals forced into the
/// same field. z3/cvc5: `unsat`.
#[test]
fn real_const_variant_simplify_false_is_unsat() {
    let v = verdict(&format!(
        "{REAL_PAIR_DT}(set-option :simplify false)\n\
         (declare-const x RPD) (declare-const d Int)\n\
         (assert (= x (C 1.5 d)))\n\
         (assert (= x (C 2.5 d)))\n\
         (check-sat)\n"
    ));
    assert_eq!(v, "unsat");
}

/// `BitVecConst` variant, SAME width, DIFFERING value — must be `unsat`.
/// z3/cvc5 (using the standard `(_ BitVec 8)` sort syntax, cross-checked
/// separately since this parser's own datatype-field grammar needs the
/// `BitVec8` shorthand instead — see `BV8_PAIR_DT`'s doc note): `unsat`.
#[test]
fn bitvec_const_same_width_differing_value_simplify_false_is_unsat() {
    let v = verdict(&format!(
        "{BV8_PAIR_DT}(set-option :simplify false)\n\
         (declare-const x BVPD) (declare-const d Int)\n\
         (assert (= x (C #x07 d)))\n\
         (assert (= x (C #x09 d)))\n\
         (check-sat)\n"
    ));
    assert_eq!(v, "unsat");
}

/// `BitVecConst` variant, DIFFERENT widths across two SEPARATE datatype
/// fields — must NOT be wrongly flagged BY THIS NEW CHECK: different widths
/// are different sorts and must never be compared against each other
/// (`has_intrinsic_literal_conflict` keys its BitVec tracking by width for
/// exactly this reason). No forcing assertion at all here, so this is
/// trivially `sat` regardless — the point is confirming no crash / no
/// mis-flagged conflict when a datatype mixes multiple BitVec widths.
#[test]
fn bitvec_const_different_widths_not_wrongly_flagged() {
    let dt = "(set-logic ALL)\n\
        (declare-datatypes ((MixedBV 0))\n\
          (((C8 (fld8 BitVec8)) (C16 (fld16 BitVec16)))))\n";
    let v = verdict(&format!(
        "{dt}(set-option :simplify false)\n\
         (declare-const x MixedBV)\n\
         (check-sat)\n"
    ));
    assert_eq!(v, "sat");
}

/// `True`/`False` variant — a Bool-sorted field forced to both `true` and
/// `false` in the same class. z3/cvc5: `unsat`.
#[test]
fn true_false_variant_simplify_false_is_unsat() {
    let v = verdict(&format!(
        "{BOOL_PAIR_DT}(set-option :simplify false)\n\
         (declare-const x BPD) (declare-const d Int)\n\
         (assert (= x (C true d)))\n\
         (assert (= x (C false d)))\n\
         (check-sat)\n"
    ));
    assert_eq!(v, "unsat");
}

// ---------------------------------------------------------------------
// Negative controls — must NOT fabricate a conflict.
// ---------------------------------------------------------------------

/// EQUAL-literals control: both bindings force the SAME field value (`7`
/// both times) — no conflict, must stay `sat`.
#[test]
fn equal_literals_negative_control_stays_sat() {
    let v = verdict(&format!(
        "{INT_PAIR_DT}(set-option :simplify false)\n\
         (declare-const x IPD) (declare-const d Int)\n\
         (assert (= x (C 7 d)))\n\
         (assert (= x (C 7 d)))\n\
         (check-sat)\n"
    ));
    assert_eq!(v, "sat");
}

/// SINGLE-BINDING control: only ONE `x = C(..)` binding at all — no forced
/// second value, nothing to compare, must stay `sat`. Proves this check
/// isn't fabricating a conflict from nothing.
#[test]
fn single_binding_negative_control_stays_sat() {
    let v = verdict(&format!(
        "{INT_PAIR_DT}(set-option :simplify false)\n\
         (declare-const x IPD) (declare-const d Int)\n\
         (assert (= x (C 7 d)))\n\
         (check-sat)\n"
    ));
    assert_eq!(v, "sat");
}

// ---------------------------------------------------------------------
// Per-class soundness-scoping control — the single highest soundness risk
// item 3 identifies: literal-tracking state must be declared/reset INSIDE
// the per-class loop, never hoisted outside it. A hoisting mistake would
// leak a literal value from one class into the scan of a completely
// UNRELATED class, fabricating a conflict between two literals that were
// NEVER actually unioned.
//
// This exact scenario was verified, live, via a deliberate mutation: with
// `seen_int` hoisted outside the per-class loop, this test's script reads
// `unsat` (a fabricated conflict, since the leaked "3" from the first class
// collides with the second class's unrelated "5"); with the correct
// per-class-scoped code, it reads `sat`, matching z3/cvc5.
// ---------------------------------------------------------------------

/// Two UNRELATED equivalence classes, each independently forcing its OWN
/// (internally consistent, non-conflicting) literal via injectivity — class
/// A forces `v1 = 3`, class B (completely disjoint variables/datatype
/// instance) forces `v2 = 5`. Must stay `sat`: neither class has an
/// INTERNAL conflict, and the two classes were never unioned with each
/// other, so `3` and `5` must never be compared.
#[test]
fn per_class_scoping_two_unrelated_classes_different_literals_stays_sat() {
    let v = verdict(&format!(
        "{INT_PAIR_DT}(set-option :simplify false)\n\
         (declare-const x1 IPD) (declare-const v1 Int) (declare-const w1 Int)\n\
         (assert (= x1 (C 3 w1)))\n\
         (assert (= x1 (C v1 w1)))\n\
         (declare-const x2 IPD) (declare-const v2 Int) (declare-const w2 Int)\n\
         (assert (= x2 (C 5 w2)))\n\
         (assert (= x2 (C v2 w2)))\n\
         (check-sat)\n"
    ));
    assert_eq!(
        v, "sat",
        "a literal seen in one equivalence class must never leak into an \
         unrelated class's scan — this would be a fabricated conflict"
    );
}

/// SANITY companion to the scoping test above: confirms `v1` really IS
/// forced to `3` by the same closure (i.e. the scoping test above isn't
/// vacuously `sat` because nothing was actually derived) — asserting `v1 !=
/// 3` on top of the identical setup must flip the verdict to `unsat`.
#[test]
fn per_class_scoping_control_confirms_derivation_is_real() {
    let v = verdict(&format!(
        "{INT_PAIR_DT}(set-option :simplify false)\n\
         (declare-const x1 IPD) (declare-const v1 Int) (declare-const w1 Int)\n\
         (assert (= x1 (C 3 w1)))\n\
         (assert (= x1 (C v1 w1)))\n\
         (declare-const x2 IPD) (declare-const v2 Int) (declare-const w2 Int)\n\
         (assert (= x2 (C 5 w2)))\n\
         (assert (= x2 (C v2 w2)))\n\
         (assert (not (= v1 3)))\n\
         (check-sat)\n"
    ));
    assert_eq!(
        v, "unsat",
        "v1 must genuinely be forced to 3 by injectivity — confirming the \
         scoping test above is a real, non-vacuous sat"
    );
}
