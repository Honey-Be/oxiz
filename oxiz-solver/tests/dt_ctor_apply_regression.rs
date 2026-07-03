//! Permanent (z3+cvc5-cross-checked) regressions for the APPLIED-constructor
//! parse opacity found by adsmt's #392 randomized datatype-render differential
//! (seed 982, 2026-07-03).
//!
//! The SMT-LIB parser routed only NULLARY constructor symbols to
//! `mk_dt_constructor` (`parse_symbol`); an applied constructor `(c01 a true)`
//! fell through to a generic `Apply`. Every datatype-aware component matches
//! on `TermKind::DtConstructor` — the simplifier's injectivity /
//! distinct-constructor rewrites, the eager datatype checks — so ground
//! equalities over applied constructors were OPAQUE: EUF modelled the
//! constructor as an uninterpreted function and `(= (c01 a true) (c01 1
//! false))` (unsat by injectivity: `true = false`) read `sat`.
//!
//! Ground truths verified against BOTH z3 4.16 and cvc5.

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

const PREAMBLE: &str = "(set-logic ALL)\n\
    (declare-datatypes ((D0 0)) (((c00) (c01 (s0 Int) (s1 Bool)) (c02))))\n\
    (declare-const a Int)\n";

/// Same constructor, clashing Bool field: injectivity forces `true = false`.
#[test]
fn same_ctor_field_clash_is_unsat() {
    let v = verdict(&format!(
        "{PREAMBLE}(assert (= (c01 a true) (c01 1 false)))\n(check-sat)\n"
    ));
    assert_eq!(v, "unsat", "injectivity forces true = false");
}

/// Same constructor, compatible fields: satisfiable via `a = 1`. Guards the
/// fix against over-eager unsat.
#[test]
fn same_ctor_compatible_fields_is_sat() {
    let v = verdict(&format!(
        "{PREAMBLE}(assert (= (c01 a true) (c01 1 true)))\n(check-sat)\n"
    ));
    assert_eq!(v, "sat", "a = 1 satisfies the decomposed equality");
}

/// Applied constructor vs a DIFFERENT nullary constructor: no-confusion.
#[test]
fn applied_ctor_vs_other_ctor_is_unsat() {
    let v = verdict(&format!(
        "{PREAMBLE}(assert (= (c01 a true) c00))\n(check-sat)\n"
    ));
    assert_eq!(v, "unsat", "distinct constructors construct distinct values");
}

/// The #392 seed-982 render end-to-end: the goal hypothesis
/// `c01(k0,true) = c01(1,false)` is false by injectivity, so the goal holds
/// vacuously and its negation is unsat.
#[test]
fn seed982_render_is_unsat() {
    let v = verdict(
        "(set-logic ALL)\n\
         (declare-datatypes ((D0 0) ) (((c00) (c01 (c01!sel0 Int) (c01!sel1 Bool)) (c02) ) ))\n\
         (declare-const k0 Int)\n\
         (declare-const k1 D0)\n\
         (assert (not (=> (= (c01 k0 true) (c01 1 false)) (and (=> (= k1 (c01 (c01!sel0 k1) (c01!sel1 k1))) (>= (c01!sel0 k1) 0)) (not (= k1 c02))))))\n\
         (check-sat)\n",
    );
    assert_eq!(v, "unsat");
}

/// Nested applied constructors decompose recursively.
#[test]
fn nested_ctor_clash_is_unsat() {
    let v = verdict(
        "(set-logic ALL)\n\
         (declare-datatypes ((N 0)) (((zero) (succ (pred N)))))\n\
         (declare-const n N)\n\
         (assert (= (succ (succ n)) (succ zero)))\n\
         (check-sat)\n",
    );
    assert_eq!(v, "unsat", "peel one succ: succ(n) = zero is a ctor clash");
}
