//! M3.5 tests: relevance gating (respecting a quantifier's guard) and the
//! frontier watermark. Gating is the mechanism that addresses the verus
//! "fuel" trigger — a quantifier under a false guard must not be
//! instantiated at all.

use oxiz_mbqi::toy::{Tid, Toy};
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
}
impl ModelEval<Toy> for Gated {
    fn eval_bool(&self, _l: &Toy, _t: Tid) -> Option<bool> {
        None
    }
    fn eval_forall(&self, _l: &Toy, _q: Tid) -> Option<bool> {
        Some(true) // when active & reached, the model verifies it
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

fn run(e: &mut Engine<Toy>, t: &mut Toy, m: &impl ModelEval<Toy>) -> (&'static str, usize) {
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
    let (verdict, lemmas) = run(&mut e, &mut t, &Gated { active: false });
    assert_eq!(verdict, "Sat");
    assert_eq!(lemmas, 0, "inactive quantifier emits nothing");
    assert_eq!(e.rejected(), 0);
}

#[test]
fn guarded_quantifier_when_active_instantiates_then_verifies() {
    // Guard true ⇒ active. The trigger-free quant enumerates at the real
    // ground FuelId c (sound, no fabrication), then the model verifies it →
    // Sat. (At least the c instance is emitted.)
    let mut t = Toy::new();
    let (q, fbd_c) = fuel_quant(&mut t);
    let mut e = Engine::new(Config::default());
    e.assert(&t, fbd_c);
    e.assert(&t, q);
    let (verdict, lemmas) = run(&mut e, &mut t, &Gated { active: true });
    assert_eq!(verdict, "Sat");
    assert!(lemmas >= 1, "active: instantiated at the real ground FuelId");
    assert_eq!(e.rejected(), 0);
}
