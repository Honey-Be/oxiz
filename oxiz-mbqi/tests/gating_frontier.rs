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
            Verdict::Inconclusive | Verdict::BudgetExhausted => return ("Unknown", emitted),
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

/// P2 (design `FUEL_AWARE_COST_SCHEDULER.md` §5.3): the cost-scheduled round
/// (flag ON) must emit the SAME instance set and reach the SAME verdict as the
/// fire-all path (it only reorders/defers sound instances). Single-tier
/// Z3-parity cost by default, so this checks the discover⇄drain fixpoint's
/// completeness. `∀x. P(x)` with ground `P(a), P(b)`, model unverified ⇒ both
/// paths enumerate `P(a), P(b)` then report the sound `Unknown`.
#[test]
fn scheduled_round_matches_fire_all_verdict_and_count() {
    const P: u32 = 22;
    const IINT: u32 = 2;
    fn once(cost_schedule: bool) -> (&'static str, usize) {
        let mut t = Toy::new();
        let a = t.konst(P + 200, IINT);
        let b = t.konst(P + 201, IINT);
        let pa = t.app(P, &[a], BOOL);
        let pb = t.app(P, &[b], BOOL);
        let x = t.var(303, IINT);
        let body = t.app(P, &[x], BOOL);
        let q = t.forall(&[(303, IINT)], &[], body, BOOL); // trigger-less
        let mut cfg = Config::default();
        cfg.cost_schedule = cost_schedule;
        let mut e = Engine::new(cfg);
        e.assert(&t, pa);
        e.assert(&t, pb);
        e.assert(&t, q);
        run(&mut e, &mut t, &Gated { active: true, verifies: false })
    }
    let (fire_v, fire_n) = once(false);
    let (sched_v, sched_n) = once(true);
    assert_eq!(fire_v, sched_v, "cost-scheduled path reaches the same verdict");
    assert_eq!(fire_n, sched_n, "cost-scheduled path emits the same instance count");
    assert_eq!(fire_v, "Unknown", "unverified trigger-free ∀ ⇒ sound Unknown");
    assert!(fire_n >= 2, "P(a) and P(b) both instantiated");
}

/// P3a (design `FUEL_AWARE_COST_SCHEDULER.md` §8, task #413): the scheduled
/// round fixpoint must honour the wall-clock non-termination guard. The host's
/// between-round check cannot interrupt a single `round_cost_scheduled` call, so
/// the deadline is threaded into the engine and polled inside the fixpoint /
/// discovery loop. On expiry the round bails as a budget event ⇒ the §8 gate
/// forbids `Saturated` (a sound candidate may still be queued) ⇒ `Unknown` —
/// never a guessed Sat. Here an already-expired deadline makes the very first
/// fixpoint pass bail: zero lemmas, sound `Unknown`, and no hang.
#[test]
fn scheduled_round_bails_to_unknown_on_deadline() {
    const P: u32 = 22;
    const IINT: u32 = 2;
    let mut t = Toy::new();
    let a = t.konst(P + 210, IINT);
    let pa = t.app(P, &[a], BOOL);
    let x = t.var(304, IINT);
    let body = t.app(P, &[x], BOOL);
    let q = t.forall(&[(304, IINT)], &[], body, BOOL); // trigger-less
    let mut cfg = Config::default();
    cfg.cost_schedule = true;
    let mut e = Engine::new(cfg);
    // Deadline captured NOW is already in the past by the time the fixpoint's
    // monotonic-clock check runs (`Instant::now() >= d`), so the guard fires on
    // the first pass — the mechanism, not a real timeout, is what we assert.
    e.set_deadline(Some(std::time::Instant::now()));
    e.assert(&t, pa);
    e.assert(&t, q);
    let (verdict, lemmas) = run(&mut e, &mut t, &Gated { active: true, verifies: false });
    assert_eq!(verdict, "Unknown", "expired deadline ⇒ sound Unknown, never Saturated");
    assert_eq!(lemmas, 0, "guard fires before any candidate is drained");
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
