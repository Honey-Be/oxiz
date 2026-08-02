//! #426 — the FIRED-BUT-INSUFFICIENT parsed-`:pattern` saturation exemption.
//!
//! E1 (#425) closed the NEVER-fired half of the trigger-semantics saturation
//! exemption: a dead / ill-arity / shape-unmatched `:pattern` silenced its
//! quantifier forever, and "e-matching added nothing" was then read as
//! saturation → the host reported `sat` on unsat problems. #426 is the
//! residual half — a trigger that DOES fire but is INSUFFICIENT (it matches
//! *something*, just not the instances needed to derive the contradiction)
//! bought exactly the same exemption, with exactly the same spurious `sat`.
//!
//! The randomized dual-oracle differential over this shape family (patterns
//! seeded for a strict subset of the needed constants, patterns over the
//! wrong argument positions, multi-group quantifiers where only one group
//! fires) measured **207/800 seeds** spurious `sat` before the fix and **0**
//! after, on both of two independent seeds; E1's own `undertrig` class went
//! 23/2000 → 0.
//!
//! The fix: SMT-LIB `:pattern` is a heuristic annotation, not semantics —
//! `(! φ :pattern p)` IS `φ` — so an e-match fixpoint only ever witnesses
//! that the INSTANTIATION HEURISTIC is exhausted, never that `φ` holds.
//! A fired parsed trigger is therefore only PROVISIONALLY exempt: it must
//! still be corroborated (`eval_forall`/model-completion `Some(true)`, or a
//! finite guard box) before a pass may conclude `Saturated`. What it keeps
//! over a genuine obligation is the FAILURE handling — a model-REFUTED
//! provisional quantifier demotes to `SaturatedUnverified`
//! (confirm-but-never-sat, so the accumulated-instance ground confirm still
//! runs and can still reach a real `unsat`), never to `Inconclusive`.
//!
//! Both reference solvers agree with the new verdict on the repro: z3 falls
//! through to MBQI and answers `unsat`, cvc5 answers `unknown`. Neither ever
//! answers `sat`.

use oxiz_mbqi::toy::{Toy, ToySig};
use oxiz_mbqi::{Config, Engine, ModelEval, Verdict};

type Tid = u32;

const BOOL: u32 = 0;
const INT: u32 = 1;

/// Every quantifier active; `eval_forall` answers `verdict` (`None` =
/// unevaluable, `Some(true)` = certified, `Some(false)` = model-REFUTED).
struct Model(Option<bool>);
impl ModelEval<Toy> for Model {
    fn eval_bool(&self, _lang: &Toy, _t: Tid) -> Option<bool> {
        None
    }
    fn eval_forall<C: oxiz_mbqi::Congruence<ToySig>>(
        &self,
        _lang: &Toy,
        _cong: &C,
        _q: Tid,
    ) -> Option<bool> {
        self.0
    }
    fn is_active(&self, _lang: &Toy, _q: Tid) -> bool {
        true
    }
}

fn drain(e: &mut Engine<ToySig>, t: &mut Toy, m: &Model) -> (usize, &'static str) {
    let mut n = 0;
    loop {
        match e.round_with(t, m) {
            Verdict::NewLemmas(ls) => n += ls.len(),
            Verdict::Saturated => return (n, "Sat"),
            Verdict::SaturatedUnverified => return (n, "SatUnverified"),
            Verdict::Inconclusive => return (n, "Unknown"),
            Verdict::BudgetExhausted => return (n, "Budget"),
        }
    }
}

/// `∀x. P(f(x))` with the PARSED, SUFFICIENT-LOOKING pattern `(f x)` and one
/// ground `f(a)` — the exact shape E1 pinned as `Saturated`.
fn fired_parsed_trigger(t: &mut Toy) -> (Tid, Tid) {
    let x = t.var(1, INT);
    let f_x = t.app(100, &[x], INT);
    let body = t.app(102, &[f_x], BOOL); // P(f(x))
    let q = t.forall(&[(1, INT)], &[&[f_x]], body, BOOL);
    let a = t.konst(7, INT);
    let f_a = t.app(100, &[a], INT);
    let ground = t.app(103, &[f_a], BOOL);
    (q, ground)
}

fn engine_with(cfg: Config, t: &mut Toy) -> Engine<ToySig> {
    let (q, ground) = fired_parsed_trigger(t);
    let mut e = Engine::new(cfg);
    e.assert(t, ground);
    e.assert(t, q);
    e
}

/// THE #426 PIN. The trigger fires (one instance), e-matching then closes,
/// and the model cannot certify the quantifier — `Saturated` is NOT earned.
#[test]
fn fired_but_unverifiable_parsed_trigger_is_never_saturated() {
    let mut t = Toy::new();
    let mut e = engine_with(Config::default(), &mut t);
    let (lemmas, verdict) = drain(&mut e, &mut t, &Model(None));
    assert_eq!(lemmas, 1, "the parsed trigger really does fire");
    assert_ne!(
        verdict, "Sat",
        "#426: a fired trigger alone justifies nothing"
    );
    assert_eq!(verdict, "SatUnverified", "confirm-but-never-sat");
}

/// The fix is a NARROWING, not a removal: when the model positively certifies
/// the quantifier (`eval_forall` = `Some(true)`) the pass still concludes
/// `Saturated`, so the host can still report `sat`. Without this, #426 would
/// have amputated the engine's `sat` capability outright.
#[test]
fn fired_parsed_trigger_still_saturates_when_the_model_certifies_it() {
    let mut t = Toy::new();
    let mut e = engine_with(Config::default(), &mut t);
    let (lemmas, verdict) = drain(&mut e, &mut t, &Model(Some(true)));
    assert_eq!(lemmas, 1);
    assert_eq!(
        verdict, "Sat",
        "a POSITIVELY justified saturation is still `Saturated`"
    );
}

/// The completeness-preserving refinement, and the reason #426 is landable.
/// A model-REFUTED *provisional* quantifier must demote to
/// `SaturatedUnverified`, NOT to `Inconclusive`: `Inconclusive` is the host's
/// bare `Unknown` and skips the accumulated-instance ground confirm, which is
/// exactly what rescues the under-triggered UNSAT rows (E1 measured the
/// corpus depending on that confirm). The demotion is sound either way — each
/// emitted instance is a guarded ground consequence `Q ⇒ φ[t̄]`, so a ground
/// UNSAT over them proves the input unsat no matter what the model claims.
#[test]
fn model_refuted_provisional_quantifier_demotes_to_unverified_not_inconclusive() {
    let mut t = Toy::new();
    let mut e = engine_with(Config::default(), &mut t);
    let (_, verdict) = drain(&mut e, &mut t, &Model(Some(false)));
    assert_ne!(verdict, "Sat", "a refuted quantifier is certainly not Sat");
    assert_eq!(
        verdict, "SatUnverified",
        "must keep the ground-confirm path, not collapse to Inconclusive"
    );
}

/// The OBLIGATION path is untouched: a TRIGGER-FREE universal that the model
/// REFUTES keeps its pre-#426 dominating `Inconclusive`. #426 only relaxes
/// the `Some(false)` handling for quantifiers that were previously EXEMPT and
/// so never reached `eval_forall` at all — it must not weaken the verdict of
/// anything that was already being verified.
#[test]
fn trigger_free_obligation_keeps_its_dominating_inconclusive() {
    let mut t = Toy::new();
    let x = t.var(1, INT);
    let f_x = t.app(100, &[x], INT);
    let body = t.app(102, &[f_x], BOOL);
    // Trigger-free: no parsed group at all.
    let q = t.forall(&[(1, INT)], &[], body, BOOL);
    let a = t.konst(7, INT);
    let f_a = t.app(100, &[a], INT);
    let ground = t.app(103, &[f_a], BOOL);
    let mut e = Engine::new(Config::default());
    e.assert(&t, ground);
    e.assert(&t, q);
    let (_, verdict) = drain(&mut e, &mut t, &Model(Some(false)));
    assert_eq!(
        verdict, "Unknown",
        "a model-refuted OBLIGATION still dominates with Inconclusive"
    );
}

/// An INACTIVE quantifier stays unconditionally exempt (vacuously satisfied
/// under a false guard) — the one exemption #426 deliberately leaves alone.
/// Pinned because the restructure moved the `is_active` test to the head of
/// the scan.
#[test]
fn inactive_quantifier_stays_exempt() {
    struct Inactive;
    impl ModelEval<Toy> for Inactive {
        fn eval_bool(&self, _l: &Toy, _t: Tid) -> Option<bool> {
            None
        }
        fn eval_forall<C: oxiz_mbqi::Congruence<ToySig>>(
            &self,
            _l: &Toy,
            _c: &C,
            _q: Tid,
        ) -> Option<bool> {
            panic!("an INACTIVE quantifier must never be model-verified");
        }
        fn is_active(&self, _l: &Toy, _q: Tid) -> bool {
            false
        }
    }
    let mut t = Toy::new();
    let (q, ground) = fired_parsed_trigger(&mut t);
    let mut e = Engine::new(Config::default());
    e.assert(&t, ground);
    e.assert(&t, q);
    assert!(
        matches!(e.round_with(&mut t, &Inactive), Verdict::Saturated),
        "an inactive quantifier is vacuously satisfied"
    );
}

/// `strict_pattern_saturation` defaults ON (sound), and clearing it restores
/// the pre-#426 lax exemption verbatim. The flag exists ONLY as the
/// no-recompile A/B kill-switch (`OXIZ_MBQI_LAX_PATTERN_SAT=1`) — clearing it
/// re-opens the spurious-`sat` door, which is what this test documents.
#[test]
fn lax_kill_switch_restores_the_pre_426_exemption() {
    assert!(
        Config::default().strict_pattern_saturation,
        "the sound behaviour must be the DEFAULT"
    );
    let mut t = Toy::new();
    let mut e = engine_with(
        Config {
            strict_pattern_saturation: false,
            ..Config::default()
        },
        &mut t,
    );
    let (lemmas, verdict) = drain(&mut e, &mut t, &Model(None));
    assert_eq!(lemmas, 1);
    assert_eq!(
        verdict, "Sat",
        "the lax kill-switch reproduces the pre-#426 (unsound) exemption"
    );
}

/// E1's load-bearing invariant, re-pinned under #426: `budget_hit` is checked
/// BEFORE saturation on every pass, so an ABORTED round can never be read as
/// `Saturated` — not even now that the model CERTIFIES the quantifier
/// (`Some(true)`), which is the one configuration in which the saturation
/// verdict would otherwise be `Saturated`.
#[test]
fn expired_deadline_still_dominates_a_certified_saturation() {
    let mut t = Toy::new();
    let mut e = engine_with(Config::default(), &mut t);
    e.set_deadline(Some(
        std::time::Instant::now() - std::time::Duration::from_millis(1),
    ));
    assert!(
        matches!(
            e.round_with(&mut t, &Model(Some(true))),
            Verdict::BudgetExhausted
        ),
        "budget_hit precedes saturation: an aborted pass is never Saturated"
    );
}
