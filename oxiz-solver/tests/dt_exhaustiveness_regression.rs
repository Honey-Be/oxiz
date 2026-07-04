//! Permanent (z3-cross-checked) regressions for #399 — nullary-constructor
//! exhaustiveness (adsmt task #399, found by the #392 differential fallout,
//! fixed 2026-07-04).
//!
//! Every datatype value is built by some constructor, so a variable excluded
//! from EVERY constructor of its datatype is a ground conflict. Pre-fix,
//! `¬(k=c00 ∨ k=c01)` over a 2-ctor enum read `sat` (z3+cvc5: unsat): negative
//! constructor-equalities were never collected, and even negative TESTERS had
//! no exhaustiveness argument.
//!
//! The fix has three parts, each load-bearing:
//! 1. the SMT-LIB parser now REGISTERS the full datatype definition (ctor
//!    inventory + selector sorts) with the `SortManager` — previously only the
//!    bare sort was created, so no sort-driven datatype reasoning could see
//!    the constructor list;
//! 2. a plain sort SYMBOL naming a declared datatype now resolves to the
//!    DATATYPE sort — the uninterpreted fallback minted a same-named but
//!    different sort, so `(declare-const k D0)` variables never carried the
//!    datatype sort (this also fixed two latent cross-interner panics in
//!    `sort_id_to_string` / the printer, where a `Datatype` spur was resolved
//!    through the TERM manager's interner);
//! 3. `check_dt_constraints` collects negative NULLARY-ctor equalities (a
//!    diseq to a field-bearing ctor excludes one instance, not the class) and
//!    conflicts when negative testers + nullary diseqs cover every ctor.

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

/// The original #399 shape: both ctors of a 2-ctor enum excluded by diseqs.
#[test]
fn all_nullary_ctors_excluded_by_diseqs_is_unsat() {
    let v = verdict(
        "(set-logic ALL)\n\
         (declare-datatypes ((D0 0)) (((c00) (c01))))\n\
         (declare-const k D0)\n\
         (assert (not (or (= k c00) (= k c01))))\n\
         (check-sat)\n",
    );
    assert_eq!(v, "unsat");
}

/// Partial exclusion stays satisfiable (the sat control for the check).
#[test]
fn partial_exclusion_is_sat() {
    let v = verdict(
        "(set-logic ALL)\n\
         (declare-datatypes ((D0 0)) (((c00) (c01) (c02))))\n\
         (declare-const k D0)\n\
         (assert (not (or (= k c00) (= k c01))))\n\
         (check-sat)\n",
    );
    assert_eq!(v, "sat", "k = c02 remains");
}

/// A diseq to a FIELD-BEARING ctor instance excludes one value, not the
/// class — no exhaustiveness may fire from it.
#[test]
fn field_bearing_ctor_diseq_is_not_class_wide() {
    let v = verdict(
        "(set-logic ALL)\n\
         (declare-datatypes ((N 0)) (((zero) (succ (pred N)))))\n\
         (declare-const k N)\n\
         (assert (not (= k zero)))\n\
         (assert (not (= k (succ zero))))\n\
         (check-sat)\n",
    );
    assert_eq!(v, "sat", "k = succ(succ zero) remains");
}

/// Negative TESTERS exclude any ctor class (field-bearing included).
#[test]
fn all_ctors_excluded_by_negative_testers_is_unsat() {
    let v = verdict(
        "(set-logic ALL)\n\
         (declare-datatypes ((N 0)) (((zero) (succ (pred N)))))\n\
         (declare-const k N)\n\
         (assert (not ((_ is zero) k)))\n\
         (assert (not ((_ is succ) k)))\n\
         (check-sat)\n",
    );
    assert_eq!(v, "unsat");
}

/// Mixed exclusion: nullary diseq + field-bearing negative tester.
#[test]
fn mixed_diseq_and_tester_exclusion_is_unsat() {
    let v = verdict(
        "(set-logic ALL)\n\
         (declare-datatypes ((N 0)) (((zero) (succ (pred N)))))\n\
         (declare-const k N)\n\
         (assert (not (= k zero)))\n\
         (assert (not ((_ is succ) k)))\n\
         (check-sat)\n",
    );
    assert_eq!(v, "unsat");
}

/// A single exclusion over a 2-ctor enum is satisfiable (no over-eager fire).
#[test]
fn single_exclusion_is_sat() {
    let v = verdict(
        "(set-logic ALL)\n\
         (declare-datatypes ((D0 0)) (((c00) (c01))))\n\
         (declare-const k D0)\n\
         (assert (not (= k c00)))\n\
         (check-sat)\n",
    );
    assert_eq!(v, "sat");
}
