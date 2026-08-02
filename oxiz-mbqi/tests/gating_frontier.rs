//! M3.5 tests: relevance gating (respecting a quantifier's guard) and the
//! frontier watermark. Gating is the mechanism that addresses the verus
//! "fuel" trigger — a quantifier under a false guard must not be
//! instantiated at all.

use oxiz_mbqi::toy::{Tid, Toy, ToySig};
use oxiz_mbqi::{Config, Engine, ModelEval, Verdict};

const BOOL: u32 = 0;
const FUELID: u32 = 3;
const FUEL_BOOL: u32 = 30;
const FUEL_BOOL_DEFAULT: u32 = 31;
const EQ: u32 = 12;

/// Model that reports a quantifier active/inactive and verifies trigger-free
/// quants as satisfied. Mirrors a host where the quantifier's guard literal
/// `Q` is false (inactive) vs true.
struct Gated {
    active: bool,
    /// Whether the model can VERIFY a reached trigger-free quantifier
    /// (`eval_forall` ⇒ `Some(true)`). When it can, the engine's M3
    /// model-completion short-circuit skips enumeration entirely (the quantifier
    /// needs no ground instances); when it cannot (`None`), the engine falls back
    /// to enumerating at the real ground terms.
    verifies: bool,
}
impl ModelEval<Toy> for Gated {
    fn eval_bool(&self, _l: &Toy, _t: Tid) -> Option<bool> {
        None
    }
    fn eval_forall<C: oxiz_mbqi::Congruence<ToySig>>(
        &self,
        _l: &Toy,
        _c: &C,
        _q: Tid,
    ) -> Option<bool> {
        if self.verifies { Some(true) } else { None }
    }
    fn is_active(&self, _l: &Toy, _q: Tid) -> bool {
        self.active
    }
}

/// The fuel-defaults shape: `∀id:FuelId. fuel_bool(id) = fuel_bool_default(id)`
/// — in the prelude this sits under `(=> fuel_defaults …)`. Plus a ground
/// `fuel_bool_default(c)` so a candidate FuelId exists.
fn fuel_quant(t: &mut Toy) -> (Tid, Tid) {
    let c = t.konst(FUELID + 1, FUELID);
    let fbd_c = t.app(FUEL_BOOL_DEFAULT, &[c], BOOL); // ground fuel_bool_default(c)
    let id = t.var(500, FUELID);
    let fb = t.app(FUEL_BOOL, &[id], BOOL);
    let fbd = t.app(FUEL_BOOL_DEFAULT, &[id], BOOL);
    let body = t.app(EQ, &[fb, fbd], BOOL);
    let q = t.forall(&[(500, FUELID)], &[], body, BOOL); // trigger-free
    (q, fbd_c)
}

fn run(e: &mut Engine<ToySig>, t: &mut Toy, m: &impl ModelEval<Toy>) -> (&'static str, usize) {
    let mut emitted = 0;
    loop {
        match e.round_with(t, m) {
            Verdict::NewLemmas(ls) => emitted += ls.len(),
            Verdict::Saturated => return ("Sat", emitted),
            // #425 phase 2 confirm-but-never-sat: at the host it collapses to
            // `Unknown` unless the ground confirm refutes — for these
            // engine-level pins the "not Sat" half is what matters.
            Verdict::SaturatedUnverified
            | Verdict::Inconclusive
            | Verdict::BudgetExhausted => return ("Unknown", emitted),
        }
    }
}

#[test]
fn guarded_quantifier_when_inactive_is_skipped_entirely() {
    // Guard false ⇒ quantifier inactive ⇒ NOT instantiated and NOT required to
    // verify (vacuously satisfied) ⇒ Sat with zero lemmas. This is the precise
    // respect-the-guard behaviour the old OxiZ fuel path dropped.
    let mut t = Toy::new();
    let (q, fbd_c) = fuel_quant(&mut t);
    let mut e = Engine::new(Config::default());
    e.assert(&t, fbd_c);
    e.assert(&t, q);
    let (verdict, lemmas) = run(&mut e, &mut t, &Gated { active: false, verifies: true });
    assert_eq!(verdict, "Sat");
    assert_eq!(lemmas, 0, "inactive quantifier emits nothing");
    assert_eq!(e.rejected(), 0);
}

#[test]
fn guarded_quantifier_when_active_and_verified_saturates_sat() {
    // Guard true ⇒ active, and the model verifies it (`eval_forall ⇒
    // Some(true)`). Since trigger INFERENCE landed, this quantifier carries
    // an inferred trigger, so it e-matches its (bounded, trigger-confined)
    // ground occurrences instead of taking the trigger-free M3 short-circuit
    // — the instances are sound consequences and cannot diverge (frontier-
    // filtered). The verdict still saturates to Sat because an
    // inferred-trigger quantifier is model-verified at saturation exactly
    // like a trigger-free one (never trigger-semantics `Sat`).
    let mut t = Toy::new();
    let (q, fbd_c) = fuel_quant(&mut t);
    let mut e = Engine::new(Config::default());
    e.assert(&t, fbd_c);
    e.assert(&t, q);
    let (verdict, _lemmas) = run(&mut e, &mut t, &Gated { active: true, verifies: true });
    assert_eq!(verdict, "Sat");
    assert_eq!(e.rejected(), 0);
}

#[test]
fn guarded_quantifier_when_active_but_unverified_enumerates_real_ground() {
    // Guard true ⇒ active, but the model CANNOT verify it (`eval_forall ⇒
    // None`). The engine then enumerates at the REAL ground FuelId `c` (sound,
    // no fabrication — at least the `c` instance is emitted), and since the
    // quantifier stays unverified the sound verdict is `Unknown` (never a
    // guessed Sat, never a fabricated Unsat).
    let mut t = Toy::new();
    let (q, fbd_c) = fuel_quant(&mut t);
    let mut e = Engine::new(Config::default());
    e.assert(&t, fbd_c);
    e.assert(&t, q);
    let (verdict, lemmas) = run(&mut e, &mut t, &Gated { active: true, verifies: false });
    assert!(lemmas >= 1, "active+unverified: instantiated at the real ground FuelId");
    assert_eq!(verdict, "Unknown", "unverified trigger-free quant ⇒ sound Unknown");
    assert_eq!(e.rejected(), 0);
}

/// A toy model that reports a fixed set of terms false (others unknown) —
/// the CDQI driver (mirrors `ematch_cdqi.rs`).
struct FalseSet(rustc_hash::FxHashSet<Tid>);
impl ModelEval<Toy> for FalseSet {
    fn eval_bool(&self, _lang: &Toy, t: Tid) -> Option<bool> {
        if self.0.contains(&t) { Some(false) } else { None }
    }
}

/// #404 — the frontier watermark must NOT advance on a round whose e-match
/// step never ran. `∀x. P(x)` (trigger-less → inference installs `[P x]`)
/// with TWO pre-existing ground seeds `P(a)`, `P(b)`: round 1's model
/// falsifies `P(a)`, so CDQI emits that single conflict instance and
/// `continue`s — e-matching is skipped for this quantifier this round. The
/// old blanket end-of-round sweep then aged BOTH seeds below the watermark,
/// so round 2's frontier-filtered e-match saw nothing and `P(b)` was never
/// instantiated — the quantifier permanently starved on terms that existed
/// BEFORE its first real scan (the corpus decreases-check wall: measured as
/// `ematch_all -> 0 binding(s)` on the minimized `datatypes-match-3` core,
/// flipping to 8 with the sweep moved into the consuming branch). Round 2
/// must still see `b` and emit `Q ⇒ P(b)`.
#[test]
fn frontier_survives_a_cdqi_short_circuited_round() {
    const INT: u32 = 2;
    const P: u32 = 22;
    let mut t = Toy::new();
    let a = t.konst(P + 100, INT);
    let b = t.konst(P + 101, INT);
    let pa = t.app(P, &[a], BOOL);
    let pb = t.app(P, &[b], BOOL);
    let x = t.var(302, INT);
    let body = t.app(P, &[x], BOOL);
    let q = t.forall(&[(302, INT)], &[], body, BOOL); // trigger-less

    let mut e = Engine::new(Config::default());
    e.assert(&t, pa);
    e.assert(&t, pb);
    e.assert(&t, q);

    // Round 1: `P(a)` false ⇒ CDQI emits exactly the `a` conflict instance
    // and short-circuits e-matching (the round that also inferred `[P x]`).
    let m1 = FalseSet([pa].into_iter().collect());
    match e.round_with(&mut t, &m1) {
        Verdict::NewLemmas(ls) => assert_eq!(ls.len(), 1, "one CDQI conflict instance"),
        _ => panic!("round 1 must emit the CDQI conflict"),
    }

    // Round 2: nothing falsified ⇒ CDQI silent ⇒ e-matching runs — and must
    // still see the PRE-round-1 seeds (the `a` tuple dedups; `b` is new).
    let m2 = FalseSet(rustc_hash::FxHashSet::default());
    match e.round_with(&mut t, &m2) {
        Verdict::NewLemmas(ls) => {
            assert_eq!(ls.len(), 1, "the `b` instance must not be starved by the watermark");
        }
        _ => panic!("round 2 must e-match the pre-existing seed `P(b)`"),
    }
    assert_eq!(e.rejected(), 0);
}

// ── engine wall-clock deadline (set_deadline → budget_hit → BudgetExhausted) ──

/// A PARSED-trigger quantifier `∀x. p(x) :pattern (p x)` with a ground seed
/// `p(a)` the trigger genuinely matches (so e-matching WOULD find the
/// instance). Distinct from `fuel_quant`: the trigger is the user's
/// `:pattern`.
///
/// #426 — this used to be paired with a model that could NOT verify, because
/// a FIRED parsed trigger was then exempt from the per-quant model-verify loop
/// and its `Sat` rested entirely on "e-matching added nothing". That exemption
/// is gone (a fired-but-INSUFFICIENT trigger justifies nothing), so the
/// deadline/abort pins below now pair it with `Gated { verifies: true }`: the
/// saturation is POSITIVELY earned, which makes the abort the SOLE difference
/// between the control and the pin — a strictly stronger pin than before.
fn parsed_trigger_quant(t: &mut Toy) -> (Tid, Tid) {
    const INT: u32 = 2;
    const P: u32 = 40;
    let a = t.konst(P + 100, INT);
    let pa = t.app(P, &[a], BOOL); // ground seed p(a)
    let x = t.var(600, INT);
    let px = t.app(P, &[x], BOOL);
    let pat: &[Tid] = &[px];
    let q = t.forall(&[(600, INT)], &[pat], px, BOOL); // parsed :pattern (p x)
    (q, pa)
}

/// THE SOUNDNESS PIN for the deadline fix. Without a deadline this scenario
/// saturates to `Sat` by parsed-trigger semantics (round 1 emits the `p(a)`
/// instance, round 2's e-match adds nothing). With an ALREADY-EXPIRED deadline
/// the e-match work is aborted — and the verdict MUST be `BudgetExhausted`
/// (host: `Unknown`), NEVER `Saturated`/`Sat`: the per-quant verify loop skips
/// parsed-trigger quantifiers, and the host's `verify_clean_saturated`
/// re-solve does not re-run e-matching, so a silently-skipped e-match would
/// sail through as a spurious `Sat` with the violating instance undiscovered.
#[test]
fn expired_deadline_never_saturates_a_parsed_trigger_quantifier() {
    // Control: no deadline ⇒ the parsed-trigger path saturates to Sat with
    // exactly the one e-matched instance (the behaviour the pin protects).
    // #426: `verifies: true` — the saturation must be POSITIVELY earned now.
    let mut t = Toy::new();
    let (q, pa) = parsed_trigger_quant(&mut t);
    let mut e = Engine::new(Config::default());
    e.assert(&t, pa);
    e.assert(&t, q);
    let (verdict, lemmas) = run(&mut e, &mut t, &Gated { active: true, verifies: true });
    assert_eq!(verdict, "Sat", "control: parsed-trigger saturation");
    assert_eq!(lemmas, 1, "control: the p(a) instance was e-matched");

    // Pin: the same scenario with an expired deadline must abort, not saturate.
    // Same `verifies: true` model as the control, so the EXPIRED DEADLINE is
    // the only difference — nothing else can be blamed for the `Unknown`.
    let mut t = Toy::new();
    let (q, pa) = parsed_trigger_quant(&mut t);
    let mut e = Engine::new(Config::default());
    e.assert(&t, pa);
    e.assert(&t, q);
    e.set_deadline(Some(std::time::Instant::now() - std::time::Duration::from_millis(1)));
    let m = Gated { active: true, verifies: true };
    // Single-round shape: zero lemmas + BudgetExhausted (never Saturated).
    assert!(
        matches!(e.round_with(&mut t, &m), Verdict::BudgetExhausted),
        "expired deadline ⇒ BudgetExhausted, never Saturated"
    );
    // And through the host-shaped harness: "Unknown" with zero-or-partial
    // lemmas — the harness loops, so this also pins that NO later round can
    // sneak to Saturated while the deadline stays expired.
    let (verdict, lemmas) = run(&mut e, &mut t, &m);
    assert_eq!(verdict, "Unknown", "aborted e-match must surface as Unknown");
    assert_eq!(lemmas, 0, "zero-or-partial lemmas on the aborted path");
}

/// A parsed-trigger quantifier with TWO genuine matches (`p(a)`, `p(b)`) but
/// `max_match_substs = 1`: the matcher truncates to one substitution and
/// raises the abort signal. Round 1 emits the one kept instance → `NewLemmas`
/// (with `budget_hit` set but overridden by the lemmas, by design). Round 2
/// re-runs the SAME e-match over the un-advanced watermark span, truncates to
/// the SAME substitution, which `seen`-dedups to ZERO lemmas — and the verdict
/// MUST be `BudgetExhausted`, never `Saturated`: the dropped `p(b)` match is
/// still undiscovered, so "e-matching added nothing" is a lie here.
///
/// This is the ONE deterministic shape where the `ematch_aborted ⇒ budget_hit`
/// line in `round_with_cong` stands ALONE between an abort and a spurious
/// `Sat` (an expired DEADLINE is also caught by the per-quant loop-head check,
/// so `expired_deadline_never_saturates_a_parsed_trigger_quantifier` does not
/// exercise that line; a `max_match_substs` abort reaches it exclusively).
/// It equally pins the watermark NON-advance on abort: had `scanned[qi]`
/// advanced in round 1, round 2 would see an empty frontier, e-match would
/// return (∅, aborted=false), and the round would sail to `Saturated`.
#[test]
fn max_substs_abort_with_all_lemmas_deduped_never_saturates() {
    const INT: u32 = 2;
    const P: u32 = 40;
    let mut t = Toy::new();
    let a = t.konst(P + 100, INT);
    let b = t.konst(P + 101, INT);
    let pa = t.app(P, &[a], BOOL);
    let pb = t.app(P, &[b], BOOL);
    let x = t.var(600, INT);
    let px = t.app(P, &[x], BOOL);
    let pat: &[Tid] = &[px];
    let q = t.forall(&[(600, INT)], &[pat], px, BOOL); // parsed :pattern (p x)

    let mut e = Engine::new(Config { max_match_substs: 1, ..Config::default() });
    e.assert(&t, pa);
    e.assert(&t, pb);
    e.assert(&t, q);
    // #426: `verifies: true` — with the fired-trigger exemption gone, the
    // model must be able to certify the quantifier, so the ONLY thing that can
    // block `Saturated` in round 2 is the `max_match_substs` abort signal.
    let m = Gated { active: true, verifies: true };

    // Round 1: truncated match set (1 of 2) still emits its kept instance.
    match e.round_with(&mut t, &m) {
        Verdict::NewLemmas(ls) => assert_eq!(ls.len(), 1, "one truncated-set instance"),
        _ => panic!("round 1 must be NewLemmas(1)"),
    }
    // Round 2: same truncated set dedups to zero lemmas — the abort signal is
    // now the ONLY thing standing between the dropped p(b) match and a
    // spurious Saturated/Sat.
    assert!(
        matches!(e.round_with(&mut t, &m), Verdict::BudgetExhausted),
        "a max_match_substs abort with zero net lemmas must be BudgetExhausted, never Saturated"
    );

    // Control (exactly-at-cap): cap == the true match count ⇒ nothing dropped,
    // NO abort, the watermark advances, and saturation is genuinely earned.
    let mut t2 = Toy::new();
    let a2 = t2.konst(P + 100, INT);
    let b2 = t2.konst(P + 101, INT);
    let pa2 = t2.app(P, &[a2], BOOL);
    let pb2 = t2.app(P, &[b2], BOOL);
    let x2 = t2.var(600, INT);
    let px2 = t2.app(P, &[x2], BOOL);
    let pat2: &[Tid] = &[px2];
    let q2 = t2.forall(&[(600, INT)], &[pat2], px2, BOOL);
    let mut e2 = Engine::new(Config { max_match_substs: 2, ..Config::default() });
    e2.assert(&t2, pa2);
    e2.assert(&t2, pb2);
    e2.assert(&t2, q2);
    let (verdict, lemmas) = run(&mut e2, &mut t2, &m);
    assert_eq!(verdict, "Sat", "len == max_substs with nothing dropped must NOT abort");
    assert_eq!(lemmas, 2, "both instances emitted at the exact cap");
}

/// No stale-deadline residue: an expired deadline aborts the round, and
/// clearing it (set_deadline(None)) restores full normal behaviour on the
/// SAME engine — the persistence property the per-round `set_deadline` call
/// in the host relies on.
#[test]
fn deadline_cleared_after_expiry_restores_normal_rounds() {
    let mut t = Toy::new();
    let (q, pa) = parsed_trigger_quant(&mut t);
    let mut e = Engine::new(Config::default());
    e.assert(&t, pa);
    e.assert(&t, q);
    // #426: `verifies: true` — saturation must be positively earned, so the
    // expired deadline is the sole cause of the abort.
    let m = Gated { active: true, verifies: true };

    // Expired deadline: aborted round, no lemmas.
    e.set_deadline(Some(std::time::Instant::now() - std::time::Duration::from_millis(1)));
    assert!(matches!(e.round_with(&mut t, &m), Verdict::BudgetExhausted));

    // Cleared: the SAME engine now e-matches the seed and saturates normally.
    e.set_deadline(None);
    let (verdict, lemmas) = run(&mut e, &mut t, &m);
    assert_eq!(verdict, "Sat", "no stale-deadline residue after set_deadline(None)");
    assert_eq!(lemmas, 1, "the p(a) instance is found once the deadline is lifted");
    assert_eq!(e.rejected(), 0);

    // And a FUTURE deadline behaves like no deadline for fast rounds.
    let mut t2 = Toy::new();
    let (q2, pa2) = parsed_trigger_quant(&mut t2);
    let mut e2 = Engine::new(Config::default());
    e2.assert(&t2, pa2);
    e2.assert(&t2, q2);
    e2.set_deadline(Some(std::time::Instant::now() + std::time::Duration::from_secs(600)));
    let (verdict2, lemmas2) = run(&mut e2, &mut t2, &m);
    assert_eq!(verdict2, "Sat", "a far-future deadline does not perturb fast rounds");
    assert_eq!(lemmas2, 1);
}
