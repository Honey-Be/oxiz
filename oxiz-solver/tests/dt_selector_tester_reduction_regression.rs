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
//! Both passes only cover the DIRECT syntactic case (the argument is a
//! manifest `DtConstructor` application in the term graph itself) — a
//! selector/tester of a variable only later shown equal to a constructor
//! application through ground equalities/congruence during solving is a
//! documented residual, not covered here (see `encode.rs` doc comments).

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

/// KNOWN RESIDUAL (#406, tracked — not a regression from this phase): a
/// selector-of-selector CHAIN of depth ≥ 2, e.g. `(hd (tl (cons a (cons b
/// c))))`, is NOT reduced end-to-end. The inner `(tl (cons a (cons b c)))`
/// DOES reduce (its arg is a manifest `DtConstructor`), producing the unit
/// fact `(tl (cons a (cons b c))) = (cons b c)` — but the OUTER `hd`'s
/// literal argument in the ORIGINAL term graph is that `DtSelector` node,
/// not a manifest `DtConstructor`, so `add_dt_selector_reduction_axioms`'s
/// static one-pass walk never reduces the outer selector: this is exactly
/// the documented "selector applied to a term only later shown equal to a
/// constructor application through ground equalities/congruence" residual
/// (see that function's doc comment), just reached via a same-formula
/// selector chain instead of a separate assertion. Pre-fix AND
/// post-#406-fix: `sat` (incomplete, NOT unsound — a missed completeness
/// case stays `sat`, never fabricates `unsat`). z3: `unsat`. Left `#[ignore]`
/// until a congruence-driven (re-triggered, not one-shot) reduction pass
/// closes it; un-ignore and flip the assertion to `"unsat"` when it's fixed.
#[test]
#[ignore = "#406 residual: selector-of-selector chain depth>=2 not reduced (spurious sat, not unsound)"]
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

/// KNOWN RESIDUAL (#406, tracked — not a regression from this phase): the
/// SAME depth≥2 chain gap as `nested_selector_chain_depth_2_residual`, but
/// for the tester-reduction pass — `((_ is cons) (tl (cons a (cons b c))))`
/// is decidably true (the inner `tl` reduces to `(cons b c)`, which is
/// manifestly `cons`-shaped) but `add_dt_tester_reduction_axioms` only
/// reduces a tester whose LITERAL argument is a manifest `DtConstructor`,
/// and here it's a `DtSelector` node. Pre-fix AND post-#406-fix: `sat`
/// (incomplete, not unsound). z3: `unsat`.
#[test]
#[ignore = "#406 residual: tester-of-selector chain depth>=2 not reduced (spurious sat, not unsound)"]
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
