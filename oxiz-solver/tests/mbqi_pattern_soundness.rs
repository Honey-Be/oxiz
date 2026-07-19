//! #425 — parsed-`:pattern` spurious-`sat` regressions, SMT level.
//!
//! The two scripts are embedded VERBATIM from the committed corpus-triage
//! repros in the AD1 workspace:
//!   adsmt-delegate/corpus-triage/425-dead-pattern-spurious-sat.smt2
//!   adsmt-delegate/corpus-triage/425-illarity-pattern-spurious-sat.smt2
//! (z3 4.16: `unsat` on both; OxiZ pre-E1: `sat` on both.)
//!
//! Both axioms are UNSAT with their ground facts, but the author's `:pattern`
//! can never fire (a dead symbol `h` never applied in a ground term; an
//! ill-arity `(g2 x)` against a binary `g2`). Pre-E1 the non-empty parsed
//! trigger EXEMPTED the quantifier from model verification, so "e-matching
//! added nothing" saturated into a spurious `sat`. E1's ever-fired gate
//! model-verifies a never-fired parsed trigger → the sound `unknown`; the
//! additive-patterns mode (`:oxiz.mbqi-additive-patterns` /
//! `OXIZ_MBQI_ADDITIVE`) augments the parsed trigger with inferred groups and
//! recovers the real `unsat`.

use oxiz_solver::{Context, SolverResult};

const DEAD_PATTERN: &str = "\
(set-logic ALL)
(declare-sort P 0)
(declare-fun f (P) Int)
(declare-fun g (P) P)
(declare-fun h (P) Int)
(declare-const a P)
(assert (forall ((x P)) (! (= (f (g x)) (+ (f x) 1)) :pattern ((h x)))))
(assert (not (= (f (g (g a))) (+ (f a) 2))))
(check-sat)
";

const ILLARITY_PATTERN: &str = "\
(set-logic ALL)
(declare-sort P 0)
(declare-fun f (P) Int)
(declare-fun g2 (P P) P)
(declare-const a P)
(assert (forall ((x P)) (! (= (f (g2 x x)) (+ (f x) 1)) :pattern ((g2 x)))))
(assert (not (= (f (g2 (g2 a a) (g2 a a))) (+ (f a) 2))))
(check-sat)
";

/// Run a script, optionally arming the additive-patterns mode via the
/// `set-option` (the race-free per-Context seam; the `OXIZ_MBQI_ADDITIVE`
/// env override is process-global and exercised by the CLI gates instead).
fn run(script: &str, additive: bool) -> SolverResult {
    let mut ctx = Context::new();
    if additive {
        ctx.execute_script("(set-option :oxiz.mbqi-additive-patterns true)")
            .expect("set-option");
    }
    let out = ctx.execute_script(script).expect("execute_script");
    let mut last = SolverResult::Unknown;
    for line in out {
        match line.as_str() {
            "sat" => last = SolverResult::Sat,
            "unsat" => last = SolverResult::Unsat,
            "unknown" => last = SolverResult::Unknown,
            _ => {}
        }
    }
    last
}

/// Default config: the dead-pattern quantifier never fires, so it must be
/// model-verified — the verdict is NOT `sat` (`unknown` expected; `unsat`
/// would also be sound).
///
/// Phase 2 note: this also pins `saturated_unverified_never_sat` — the
/// engine verdict here is now `SaturatedUnverified` with an EMPTY instance
/// set (nothing ever fired), which must take the host's empty-instances arm
/// → `Unknown`, never `sat`.
#[test]
fn t425_dead_pattern_not_sat() {
    assert_ne!(
        run(DEAD_PATTERN, false),
        SolverResult::Sat,
        "a never-fired parsed :pattern must not saturate into sat"
    );
}

/// Default config: same for the ill-arity pattern (arity is not validated
/// statically behind the term view — the dynamic ever-fired gate covers it).
#[test]
fn t425_illarity_pattern_not_sat() {
    assert_ne!(
        run(ILLARITY_PATTERN, false),
        SolverResult::Sat,
        "an ill-arity parsed :pattern must not saturate into sat"
    );
}

/// Additive mode ON: the inferred group `(g x)` joins the dead `(h x)`,
/// e-matching fires on the ground `g`-chain, and the instances close the
/// contradiction → the real `unsat` (z3-parity).
#[test]
fn t425_dead_pattern_additive_unsat() {
    assert_eq!(run(DEAD_PATTERN, true), SolverResult::Unsat);
}

/// Additive mode ON: the inferred group `(g2 x x)` joins the ill-arity
/// `(g2 x)` → the real `unsat` (z3-parity).
#[test]
fn t425_illarity_pattern_additive_unsat() {
    assert_eq!(run(ILLARITY_PATTERN, true), SolverResult::Unsat);
}

/// #425 phase 2 — the `SaturatedUnverified` CONFIRM path yields the real
/// `unsat` (default config, no additive mode). The bounded pigeonhole `∀`
/// emits its whole box, whose conjunction is jointly UNSAT — a GLOBAL
/// conflict the incremental CDCL(T) misses (#277's class), so rounds close
/// with no new lemmas. The dead-pattern quantifier over the free sort `P`
/// (`h` heads no ground term; its body is unevaluable by the structural
/// recognizers — the same quantifier `t425_dead_pattern_not_sat` pins as
/// non-`sat`) blocks `Saturated`, so the engine verdict is
/// `SaturatedUnverified` — and the host must still run the single-shot
/// ground confirm and trust its `unsat` half. Phase 1 returned the
/// over-conservative `unknown` here (the dm3 corpus regression: verified
/// rows became 90 s saturators); pre-E1 the same `unsat` came via the
/// (unsoundly-exempt) `Saturated` confirm.
///
/// UFLIA, not ALL: the single-shot confirm carries the script's logic, and
/// under `ALL` the ground re-solve misses the EUF↔LIA pigeonhole conflict
/// (pre-existing — the plain bounded pigeonhole WITHOUT the extra quantifier
/// already answers `sat` under `ALL`; `bounded_guard_instantiation.rs` pins
/// the same script family as UFLIA for the same reason).
#[test]
fn saturated_unverified_confirm_path_yields_unsat() {
    let script = "\
(set-logic UFLIA)
(declare-fun hole (Int) Int)
(assert (and (>= (hole 0) 1) (<= (hole 0) 2)))
(assert (and (>= (hole 1) 1) (<= (hole 1) 2)))
(assert (and (>= (hole 2) 1) (<= (hole 2) 2)))
(assert (forall ((i Int) (j Int)) \
    (=> (and (>= i 0) (<= i 2) (>= j 0) (<= j 2) (not (= i j))) \
        (not (= (hole i) (hole j))))))
(declare-sort P 0)
(declare-fun f (P) Int)
(declare-fun g (P) P)
(declare-fun h (P) Int)
(declare-const a P)
(assert (forall ((x P)) (! (= (f (g x)) (+ (f x) 1)) :pattern ((h x)))))
(check-sat)
";
    assert_eq!(
        run(script, false),
        SolverResult::Unsat,
        "SaturatedUnverified must confirm the accumulated ground set and trust its unsat half"
    );
}
