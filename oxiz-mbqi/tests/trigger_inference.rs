//! Trigger INFERENCE (the z3 auto-pattern parity) — selection unit tests via
//! the toy lang + engine registration/flattening behavior. The inference
//! itself is engine-internal (`infer_triggers`), so these tests observe it
//! through the engine: a quantifier that e-matches (instead of enumerating)
//! got a trigger; the flattened chain binds every variable in ONE instance.

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
            Verdict::Inconclusive => return (all, "Unknown"),
            Verdict::BudgetExhausted => return (all, "Budget"),
        }
    }
}

/// `∀x,y. Sub(x,y) = …` (toy shape: `Or(Sub(x,y), g(x,y))`) with a ground
/// `Sub(a,b)` occurrence: inference picks the full-cover app(s), e-matching
/// fires EXACTLY on the ground occurrence — one instance, then saturation
/// (model-verified fails ⇒ the sound Unknown, but crucially NO enumeration
/// blow-up and no zero-instance starvation).
#[test]
fn inference_ematches_the_ground_occurrence() {
    let mut t = Toy::new();
    let x = t.var(1, INT);
    let y = t.var(2, INT);
    let sub_xy = t.app(100, &[x, y], INT);
    let g_xy = t.app(101, &[x, y], BOOL);
    let sub_pred = t.app(102, &[sub_xy], BOOL); // P(Sub(x,y)) — minimality: Sub(x,y) wins
    let body = t.mk_or(vec![sub_pred, g_xy]);
    let q = t.forall(&[(1, INT), (2, INT)], &[], body, BOOL);
    // ground occurrence Sub(a,b)
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
        "inferred trigger must fire on the ground Sub(a,b) occurrence"
    );
    // never trigger-semantics Sat for an INFERRED trigger: unverified ⇒ Unknown
    assert_eq!(verdict, "Unknown");
}

/// A directly-nested same-polarity `∀x.∀y.φ` chain FLATTENS at registration:
/// one instance binds BOTH variables (the lemma is ground — the two-level
/// outer-enumerated/inner-re-registered dance is gone).
#[test]
fn nested_forall_chain_flattens_and_grounds_in_one_step() {
    let mut t = Toy::new();
    let x = t.var(1, INT);
    let y = t.var(2, INT);
    let f_xy = t.app(100, &[x, y], BOOL);
    let inner = t.forall(&[(2, INT)], &[], f_xy, BOOL);
    let outer = t.forall(&[(1, INT)], &[], inner, BOOL);
    let a = t.konst(7, INT);
    let b = t.konst(8, INT);
    let f_ab = t.app(100, &[a, b], BOOL);

    let mut e = Engine::new(Config::default());
    e.assert(&t, f_ab);
    e.assert(&t, outer);
    let (lemmas, _) = drain(&mut e, &mut t);
    assert_eq!(lemmas.len(), 1, "one flattened instance, fully ground");
    // The lemma is the guarded `Q ⇒ φ[x̄↦t̄]` — the GUARD `Q` is the original
    // (nested) quantifier term by design (invariant #3), so only the
    // CONSEQUENT must be quantifier-free: the flattened instantiation bound
    // BOTH variables in one step (no residual inner ∀ to re-register).
    fn has_quant(t: &Toy, id: Tid) -> bool {
        match t.view(id) {
            oxiz_mbqi::TermView::Quant { .. } => true,
            _ => t.children(id).iter().any(|&c| has_quant(t, c)),
        }
    }
    let consequent = t.children(lemmas[0])[1];
    assert!(
        !has_quant(&t, consequent),
        "no inner ∀ survives the flattened instance's consequent"
    );
}

/// No e-matchable candidate (pure-opaque body) ⇒ no inference ⇒ today's
/// enumeration path is untouched (instances over the ground index).
#[test]
fn no_candidate_keeps_the_enumeration_path() {
    let mut t = Toy::new();
    let x = t.var(1, INT);
    // body references x only through a NON-matchable node: Or(x-as-bool…)
    // (toy: use Or with the var itself; Or is a reserved pseudo-sym).
    let body = t.mk_or(vec![x]);
    let q = t.forall(&[(1, INT)], &[], body, BOOL);
    let c = t.konst(7, INT);
    let g = t.app(103, &[c], BOOL); // seeds the ground index with an INT term

    let mut e = Engine::new(Config::default());
    e.assert(&t, g);
    e.assert(&t, q);
    let (lemmas, _) = drain(&mut e, &mut t);
    assert!(
        !lemmas.is_empty(),
        "trigger-free (uninferable) quantifier still enumerates the ground index"
    );
}
