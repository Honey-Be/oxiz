//! E1 `:pattern` validation + ever-fired gating + additive-patterns mode
//! (#425), via the toy lang. The corpus shape: a quantifier whose PARSED
//! trigger can never fire (dead symbol, ill-arity, uncovered group) used to
//! keep the trigger-semantics saturation exemption — "e-matching added
//! nothing" was read as saturation although the quantifier was never
//! instantiated even once → spurious `Sat`. The static gate drops only
//! PROVABLY-unusable groups (a bare-`Var` member; an all-analyzable group
//! that cannot cover the bound vars — falling back to lazy inference) and
//! conservatively KEEPS groups it cannot analyze (an `Opaque`-viewing
//! member/subterm — e.g. the OxiZ bridge's unclassified Dt kinds); the
//! dynamic ever-fired gate (`Quant::matched`) strips the saturation
//! exemption from any parsed trigger that never matched — the verdict is
//! then `SaturatedUnverified` (confirm-but-never-sat: the host may trust a
//! ground UNSAT over the accumulated instances, never a `sat`); the
//! additive mode (default OFF) augments parsed triggers with inferred
//! groups to recover the lost instances.

use oxiz_mbqi::toy::{Toy, ToySig};
use oxiz_mbqi::{Config, Engine, ModelEval, TermLang, Verdict};

type Tid = u32;

const BOOL: u32 = 0;
const INT: u32 = 1;

/// A model that asserts every quantifier and never verifies one — forces the
/// engine down the instantiation path (CDQI is a no-op without a congruence
/// oracle carrying conflicts; e-matching/enumeration do the work).
struct Active;
impl ModelEval<Toy> for Active {
    fn eval_bool(&self, _lang: &Toy, _t: Tid) -> Option<bool> {
        None
    }
    fn eval_forall<C: oxiz_mbqi::Congruence<ToySig>>(
        &self,
        _lang: &Toy,
        _cong: &C,
        _q: Tid,
    ) -> Option<bool> {
        None
    }
    fn is_active(&self, _lang: &Toy, _q: Tid) -> bool {
        true
    }
}

fn drain(e: &mut Engine<ToySig>, t: &mut Toy) -> (Vec<Tid>, &'static str) {
    let mut all = Vec::new();
    loop {
        match e.round_with(t, &Active) {
            Verdict::NewLemmas(ls) => all.extend(ls),
            Verdict::Saturated => return (all, "Sat"),
            // Confirm-but-never-sat (#425 phase 2): distinct from both `Sat`
            // (the host must not report sat) and `Unknown` (the host may
            // still confirm a ground UNSAT over the accumulated instances).
            Verdict::SaturatedUnverified => return (all, "SatUnverified"),
            Verdict::Inconclusive => return (all, "Unknown"),
            Verdict::BudgetExhausted => return (all, "Budget"),
        }
    }
}

/// `∀x,y. P(Sub(x,y)) ∨ g(x,y)` with the parsed group `[(p1 x)]` covering
/// only `x`: the STATIC gate drops the group (an uncovered group can never
/// yield an instance — the fullness filter drops partial bindings — so its
/// only effect was the unsound saturation exemption), `triggers` becomes
/// empty, and the LAZY-INFERENCE path takes over unmodified: the inferred
/// trigger fires on the ground `Sub(a,b)` occurrence. Without the static
/// drop there would be ZERO lemmas (the parsed group blocks inference), so
/// the non-empty lemma set pins the fallback.
#[test]
fn uncovered_group_dropped_falls_back_to_inference() {
    let mut t = Toy::new();
    let x = t.var(1, INT);
    let y = t.var(2, INT);
    let sub_xy = t.app(100, &[x, y], INT);
    let p_sub = t.app(102, &[sub_xy], BOOL);
    let g_xy = t.app(101, &[x, y], BOOL);
    let body = t.mk_or(vec![p_sub, g_xy]);
    let pat = t.app(104, &[x], BOOL); // covers x only — invalid group
    let q = t.forall(&[(1, INT), (2, INT)], &[&[pat]], body, BOOL);
    let a = t.konst(7, INT);
    let b = t.konst(8, INT);
    let sub_ab = t.app(100, &[a, b], INT);
    let ground = t.app(103, &[sub_ab], BOOL);

    let mut e = Engine::new(Config::default());
    e.assert(&t, ground);
    e.assert(&t, q);
    let (lemmas, verdict) = drain(&mut e, &mut t);
    assert!(
        !lemmas.is_empty(),
        "the uncovered group must be dropped so lazy inference fires on Sub(a,b)"
    );
    // An inferred trigger is not a user contract → model-verified; `eval_forall`
    // is `None` here, so the verdict is the phase-2 `SaturatedUnverified`
    // (confirm-but-never-sat) rather than the pre-phase-2 `Inconclusive`.
    assert_eq!(verdict, "SatUnverified");
}

/// `∀x. P(f(x))` with parsed pattern `(h x)` where `h` heads NO ground term:
/// the pattern is statically valid (App, covers `x`) but never fires — the
/// dead-symbol case is not statically decidable behind the `TermLang` view.
/// The ever-fired gate must strip the exemption at saturation; the
/// quantifier is unevaluable (`eval_forall` = `None`), so the verdict is
/// `SaturatedUnverified` (#425 phase 2: confirm-but-never-sat), NEVER
/// `Saturated`. (Pre-E1 this returned "Sat" — the #425 spurious verdict;
/// E1 phase 1 returned `Inconclusive`, which also threw away the sound
/// confirm-then-unsat half.)
#[test]
fn never_fired_parsed_trigger_not_saturated() {
    let mut t = Toy::new();
    let x = t.var(1, INT);
    let f_x = t.app(100, &[x], INT);
    let body = t.app(102, &[f_x], BOOL); // P(f(x))
    let h_x = t.app(110, &[x], INT); // (h x): h never applied to ground terms
    let q = t.forall(&[(1, INT)], &[&[h_x]], body, BOOL);
    let a = t.konst(7, INT);
    let f_a = t.app(100, &[a], INT);
    let ground = t.app(103, &[f_a], BOOL);

    let mut e = Engine::new(Config::default());
    e.assert(&t, ground);
    e.assert(&t, q);
    let (lemmas, verdict) = drain(&mut e, &mut t);
    assert!(lemmas.is_empty(), "a dead trigger yields no instances");
    assert_ne!(
        verdict, "Sat",
        "a never-fired parsed trigger must NOT keep the saturation exemption"
    );
    assert_eq!(
        verdict, "SatUnverified",
        "a never-fired unevaluable parsed trigger is the confirm-but-never-sat verdict"
    );
}

/// #426 SUCCESSOR of E1's `fired_parsed_trigger_keeps_exemption` over-reach
/// pin. E1 pinned that a parsed trigger which DID fire keeps the
/// trigger-semantics exemption outright — that residual exemption was itself
/// a spurious-`sat` class (a trigger can fire and still be INSUFFICIENT), so
/// the exemption is now only PROVISIONAL: `Saturated` must be earned
/// positively. `∀x. P(f(x))` with pattern `(f x)`, ground `f(a)`: one
/// instance is emitted, e-matching then adds nothing, and with the `Active`
/// model (`eval_forall` = `None`) the verdict is the confirm-but-never-sat
/// `SaturatedUnverified` — NOT `Sat`.
///
/// The full #426 battery (insufficiency, model-refutation, the obligation
/// path, the kill-switch) lives in `pattern_sufficiency.rs`.
#[test]
fn fired_parsed_trigger_exemption_is_only_provisional() {
    let mut t = Toy::new();
    let x = t.var(1, INT);
    let f_x = t.app(100, &[x], INT);
    let body = t.app(102, &[f_x], BOOL); // P(f(x))
    let q = t.forall(&[(1, INT)], &[&[f_x]], body, BOOL);
    let a = t.konst(7, INT);
    let f_a = t.app(100, &[a], INT);
    let ground = t.app(103, &[f_a], BOOL);

    let mut e = Engine::new(Config::default());
    e.assert(&t, ground);
    e.assert(&t, q);
    let (lemmas, verdict) = drain(&mut e, &mut t);
    assert_eq!(lemmas.len(), 1, "the parsed trigger fires on f(a)");
    assert_ne!(
        verdict, "Sat",
        "#426: firing alone is NOT positive justification for `Saturated`"
    );
    assert_eq!(
        verdict, "SatUnverified",
        "a fired-but-unverifiable parsed trigger is confirm-but-never-sat"
    );
}

/// Additive mode: `∀x. P(f(x))` with the DEAD parsed pattern `(h x)` and
/// ground `f(a)`. Pass 1 concludes Inconclusive (never fired) → augmentation
/// appends the inferred group `(f x)` ONCE (rescan from zero) → pass 2 emits
/// the instance. The next round finds nothing new, augmentation returns
/// false (already augmented — the pass loop terminates), and the AUGMENTED
/// quantifier has LOST the exemption → model-verified; unevaluable here →
/// `SaturatedUnverified` (#425 phase 2), not Sat.
#[test]
fn additive_augments_once_and_terminates() {
    let mut t = Toy::new();
    let x = t.var(1, INT);
    let f_x = t.app(100, &[x], INT);
    let body = t.app(102, &[f_x], BOOL); // P(f(x))
    let h_x = t.app(110, &[x], INT); // dead parsed pattern
    let q = t.forall(&[(1, INT)], &[&[h_x]], body, BOOL);
    let a = t.konst(7, INT);
    let f_a = t.app(100, &[a], INT);
    let ground = t.app(103, &[f_a], BOOL);

    let cfg = Config { additive_patterns: true, ..Config::default() };
    let mut e = Engine::new(cfg);
    e.assert(&t, ground);
    e.assert(&t, q);
    let (lemmas, verdict) = drain(&mut e, &mut t);
    assert_eq!(
        lemmas.len(),
        1,
        "the augmented inferred trigger recovers exactly the f(a) instance"
    );
    // Phase 2: the unevaluable augmented quantifier lands in the
    // confirm-but-never-sat bucket instead of the pre-phase-2 `Inconclusive`.
    assert_eq!(
        verdict, "SatUnverified",
        "an augmented quantifier loses the exemption (model-verified)"
    );
}

/// The A-fix pin (dm3 misdrop): a group with an `App` member + an
/// `Opaque`-viewing member (the OxiZ bridge's unclassified Dt kinds present
/// exactly like this) must be KEPT — the gate cannot see an unclassified
/// member's children, so the member may cover the remaining bound vars.
/// Retention is observable at the public surface: had the group been dropped
/// (the pre-fix behaviour — the App member alone covers only `x`), `triggers`
/// would be empty and lazy inference would fire on the ground `Sub(a,b)` →
/// non-empty lemmas. Kept, the group never fires (the Opaque member is
/// unmatchable), so the ever-fired gate strips the exemption →
/// `SaturatedUnverified`, never `Sat` — the conservative keep costs no
/// soundness.
#[test]
fn unanalyzable_member_group_kept() {
    let mut t = Toy::new();
    let x = t.var(1, INT);
    let y = t.var(2, INT);
    let sub_xy = t.app(100, &[x, y], INT);
    let p_sub = t.app(102, &[sub_xy], BOOL);
    let g_xy = t.app(101, &[x, y], BOOL);
    let body = t.mk_or(vec![p_sub, g_xy]);
    let pat_app = t.app(104, &[x], BOOL); // App member covering x only
    let pat_opaque = t.opaque(0xD7, BOOL); // unclassified member — may cover y unseen
    let q = t.forall(&[(1, INT), (2, INT)], &[&[pat_app, pat_opaque]], body, BOOL);
    let a = t.konst(7, INT);
    let b = t.konst(8, INT);
    let sub_ab = t.app(100, &[a, b], INT);
    let ground = t.app(103, &[sub_ab], BOOL);

    let mut e = Engine::new(Config::default());
    e.assert(&t, ground);
    e.assert(&t, q);
    let (lemmas, verdict) = drain(&mut e, &mut t);
    assert!(
        lemmas.is_empty(),
        "the KEPT unanalyzable group blocks lazy inference and never fires"
    );
    assert_eq!(
        verdict, "SatUnverified",
        "kept-but-never-fired group: exemption stripped, confirm-but-never-sat"
    );
}

/// The budget-before-saturation invariant on the AUGMENTED pass. Same shape
/// as above but `max_match_substs = 0`: pass 1 is budget-clean (the dead
/// group has ZERO candidates, so its e-match never starts and cannot abort),
/// augmentation appends `(f x)` and re-passes; pass 2's rescan has a real
/// candidate, so CCFV aborts instantly at the cap with a PARTIAL (empty)
/// match set → `budget_hit` → the tail must return `BudgetExhausted`, never
/// read the empty pass as `Saturated`.
///
/// (A wall-clock variant is not constructible deterministically: an expired
/// deadline is caught at the PASS-1 loop head — budget is checked before
/// augmentation ever runs — so this uses the `max_match_substs` abort, which
/// routes through the identical `budget_hit` plumbing as a deadline abort.)
#[test]
fn additive_budget_before_saturation() {
    let mut t = Toy::new();
    let x = t.var(1, INT);
    let f_x = t.app(100, &[x], INT);
    let body = t.app(102, &[f_x], BOOL); // P(f(x))
    let h_x = t.app(110, &[x], INT); // dead parsed pattern
    let q = t.forall(&[(1, INT)], &[&[h_x]], body, BOOL);
    let a = t.konst(7, INT);
    let f_a = t.app(100, &[a], INT);
    let ground = t.app(103, &[f_a], BOOL);

    let cfg = Config { additive_patterns: true, max_match_substs: 0, ..Config::default() };
    let mut e = Engine::new(cfg);
    e.assert(&t, ground);
    e.assert(&t, q);
    let (lemmas, verdict) = drain(&mut e, &mut t);
    assert!(lemmas.is_empty(), "the aborted rescan may emit nothing");
    assert_eq!(
        verdict, "Budget",
        "an aborted augmented rescan must be BudgetExhausted, never Saturated"
    );
}
