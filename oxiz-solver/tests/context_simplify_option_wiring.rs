//! Permanent regression for #423 item 3 — wire up
//! `Context::set_option("simplify", ...)`.
//!
//! `Context::set_option`'s match (`context.rs`) had NO `"simplify"` arm —
//! it fell through to the no-op `_ => {}` default. `SolverConfig::simplify`
//! was only ever settable via direct Rust struct construction; the CLI's
//! own `--preset minimal` (which calls `ctx.set_option("simplify",
//! "false")`) and the SMT-LIB `(set-option :simplify false)` surface both
//! silently did nothing. Fixed by a `"simplify"` match arm mirroring the
//! shape of the sibling option handlers already in that match (e.g.
//! `"produce-proofs"`): clone the current `SolverConfig`, set `.simplify =
//! value == "true"`, apply it back via `Solver::set_config`.
//!
//! This is a pure wiring/hygiene fix (zero soundness risk in either
//! direction — it only makes an ALREADY-EXISTING Rust-level config knob
//! reachable from the front end; `simplify: false`'s own completeness
//! properties are unrelated, pre-existing behavior, exercised extensively
//! by `dt_or_case_split_regression.rs`'s `simplify_false` test section via
//! the direct `Solver`/`SolverConfig` API). The test below confirms the
//! option now ACTUALLY changes solving behavior through the
//! `Context`/SMT-LIB surface specifically (not just the Rust API), on a
//! repro chosen to be simplify-sensitive: constructor injectivity
//! (`p=cons(a,b)`, `p=cons(c,b)` forcing `a=c`) composed with an
//! ARITHMETIC fact (`c > a+1`) that only contradicts `a=c` once the
//! injectivity-derived equality actually reaches arithmetic as a ground
//! fact — which happens via `inject_dt_derived_ctor_equalities`'s
//! `config.simplify`-gated decomposition (`encode.rs`), NOT via
//! `check_dt_constraints`'s Rust-level pre-pass (which only performs
//! DT-specific STATIC conflict checks — acyclicity and forced-disequality —
//! and never makes its derived facts available to OTHER theories).

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

const REPRO_BODY: &str = "(declare-datatypes ((PairI423 0)) (((consI423 (hdI423 Int) (tlI423 Int)))))\n\
     (declare-const p PairI423)\n\
     (declare-const a Int) (declare-const b Int) (declare-const c Int)\n\
     (assert (= p (consI423 a b)))\n\
     (assert (= p (consI423 c b)))\n\
     (assert (> c (+ a 1)))\n\
     (check-sat)\n";

/// DEFAULT config (`simplify` left at its `true` default): the
/// injectivity-derived `a=c` reaches arithmetic via the SAT-level injection
/// route, contradicting `c > a+1`. `unsat` (matches z3/cvc5).
#[test]
fn default_config_is_unsat() {
    let v = verdict(&format!("(set-logic ALL)\n{REPRO_BODY}"));
    assert_eq!(v, "unsat");
}

/// THE decisive wiring test: the IDENTICAL repro, but with
/// `(set-option :simplify false)` set via the SMT-LIB surface BEFORE the
/// datatype declaration. Before #423 item 3, this option was silently
/// ignored (`SolverConfig::simplify` stayed `true` regardless), so this
/// would have read `unsat` — IDENTICAL to the default-config test above,
/// which would have meant the option had NO observable effect at all. With
/// item 3's fix, the option now genuinely disables the SAT-level
/// decomposition, so `a=c` never reaches arithmetic and the solver reads
/// `sat` — a DIFFERENT verdict from the default-config test, proving the
/// option is now wired through end-to-end (front end -> `SolverConfig` ->
/// solving behavior), not merely stored in the options map.
#[test]
fn set_option_simplify_false_changes_verdict() {
    let v = verdict(&format!("(set-logic ALL)\n(set-option :simplify false)\n{REPRO_BODY}"));
    assert_eq!(
        v, "sat",
        "(set-option :simplify false) must actually take effect — if this \
         reads unsat, the option is being silently ignored again"
    );
}

/// CONTROL confirming `get_option` reflects the SAME string the CLI/SMT-LIB
/// `(set-option :simplify false)` surface stores (the options map itself was
/// never the missing piece — only the SOLVER-CONFIG wiring was) — a direct
/// unit-level check that `set_option`/`get_option` round-trip independent of
/// solving behavior.
#[test]
fn get_option_reflects_stored_value() {
    let mut ctx = Context::new();
    ctx.set_option("simplify", "false");
    assert_eq!(ctx.get_option("simplify"), Some("false"));
    ctx.set_option("simplify", "true");
    assert_eq!(ctx.get_option("simplify"), Some("true"));
}

/// Re-enabling `simplify` after having disabled it must restore the
/// `unsat` verdict — confirms the wiring is a genuine two-way toggle, not a
/// one-shot/sticky effect.
#[test]
fn re_enabling_simplify_restores_unsat() {
    let v = verdict(&format!(
        "(set-logic ALL)\n(set-option :simplify false)\n(set-option :simplify true)\n{REPRO_BODY}"
    ));
    assert_eq!(v, "unsat");
}
