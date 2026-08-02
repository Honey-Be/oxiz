//! #426 — fired-but-INSUFFICIENT parsed-`:pattern` spurious-`sat`, SMT level.
//!
//! Sibling of `mbqi_pattern_soundness.rs` (#425). E1 closed the NEVER-fired
//! half of the trigger-semantics saturation exemption; this is the residual
//! half. Every script below has a parsed `:pattern` that **does fire** — so
//! E1's static validation gate keeps it and E1's ever-fired gate is satisfied
//! — and is nevertheless INSUFFICIENT: it matches something, just never the
//! instances that derive the contradiction. Pre-#426 the fired trigger bought
//! the full exemption, "e-matching added nothing" saturated, and OxiZ
//! answered `sat` on problems that are UNSAT.
//!
//! Dual-oracle ground truth on `THIN_CHAIN` (the minimal repro):
//!   z3 4.16.0  `unsat` (both patterned and `:pattern`-stripped)
//!   cvc5 1.3.0 `unsat` stripped, `unknown` patterned — cvc5 never says `sat`
//!   OxiZ pre-#426 `sat`   ← the bug
//!   OxiZ post-#426 `unknown`
//!
//! `:pattern` is a heuristic annotation in SMT-LIB, not semantics
//! (`(! φ :pattern p)` IS `φ`), so an e-match fixpoint never justifies `sat`.
//! The engine now demands positive justification and otherwise reports
//! `SaturatedUnverified` — confirm-but-never-sat, which still runs the
//! accumulated-instance ground confirm and so can still reach a real `unsat`.

use oxiz_solver::{Context, SolverResult};

/// The minimal repro. Side predicate `k` is seeded only at `a`, so the
/// pattern `(k x)` fires exactly once (x := a) and emits
/// `f(g(a)) = f(a) + 1`. The contradiction additionally needs x := (g a),
/// which `(k x)` can never reach because `k(g(a))` is not a ground term.
const THIN_CHAIN: &str = "\
(set-logic UFLIA)
(declare-sort P 0)
(declare-fun f (P) Int)
(declare-fun g (P) P)
(declare-fun k (P) Bool)
(declare-const a P)
(assert (forall ((x P)) (! (= (f (g x)) (+ (f x) 1)) :pattern ((k x)))))
(assert (k a))
(assert (= (f a) 0))
(assert (not (= (f (g (g a))) (+ (f a) 2))))
(check-sat)
";

/// Multi-group: one group fires but is thin, the other is a dead symbol.
/// The ever-fired gate (#425) is satisfied by the FIRST group, so nothing
/// before #426 catches this.
const MULTIGROUP_ONE_FIRES: &str = "\
(set-logic UFLIA)
(declare-sort P 0)
(declare-fun f (P) Int)
(declare-fun g (P) P)
(declare-fun k (P) Bool)
(declare-fun dead (P) Bool)
(declare-const a P)
(assert (forall ((x P))
  (! (= (f (g x)) (+ (f x) 1)) :pattern ((k x)) :pattern ((dead x)))))
(assert (k a))
(assert (= (f a) 0))
(assert (not (= (f (g (g a))) (+ (f a) 2))))
(check-sat)
";

/// Wrong ARGUMENT POSITIONS: the group `(r y x)` covers both bound variables
/// (so the static gate keeps it) and fires against the ground `r(a,b)` — but
/// it binds them the wrong way round, so the emitted instance is about the
/// pair the contradiction does not mention.
const WRONG_ARG_POSITION: &str = "\
(set-logic UFLIA)
(declare-sort P 0)
(declare-fun r (P P) Bool)
(declare-const a P)
(declare-const b P)
(declare-const c P)
(assert (forall ((x P) (y P)) (! (=> (r x y) (r y x)) :pattern ((r y x)))))
(assert (r a b))
(assert (r c c))
(assert (not (r b a)))
(check-sat)
";

fn run(script: &str) -> SolverResult {
    let mut ctx = Context::new();
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

/// THE #426 PIN. `unknown` is the expected verdict; `unsat` would also be
/// sound (and is what the additive-patterns mode recovers) — the assertion is
/// the soundness one: NEVER `sat`.
#[test]
fn t426_thin_trigger_not_sat() {
    assert_ne!(
        run(THIN_CHAIN),
        SolverResult::Sat,
        "a FIRED but INSUFFICIENT parsed :pattern must not saturate into sat"
    );
}

#[test]
fn t426_multigroup_one_group_fires_not_sat() {
    assert_ne!(
        run(MULTIGROUP_ONE_FIRES),
        SolverResult::Sat,
        "one firing group must not buy the exemption for the whole quantifier"
    );
}

#[test]
fn t426_wrong_argument_position_not_sat() {
    assert_ne!(
        run(WRONG_ARG_POSITION),
        SolverResult::Sat,
        "a pattern that fires on the wrong argument positions justifies nothing"
    );
}

/// The additive-patterns mode augments the parsed trigger with inferred
/// groups and recovers the REAL `unsat` on the same input — pinned so the two
/// levers stay complementary (#426 makes the default verdict honest; additive
/// makes it useful). Still asserted only up to "not sat" plus the positive
/// `unsat`, so a future scheduling change cannot silently flip it to `sat`.
#[test]
fn t426_additive_recovers_the_unsat() {
    let mut ctx = Context::new();
    ctx.execute_script("(set-option :oxiz.mbqi-additive-patterns true)")
        .expect("set-option");
    let out = ctx.execute_script(THIN_CHAIN).expect("execute_script");
    let mut last = SolverResult::Unknown;
    for line in out {
        match line.as_str() {
            "sat" => last = SolverResult::Sat,
            "unsat" => last = SolverResult::Unsat,
            "unknown" => last = SolverResult::Unknown,
            _ => {}
        }
    }
    assert_eq!(
        last,
        SolverResult::Unsat,
        "additive patterns recover the real unsat under the thin trigger"
    );
}
