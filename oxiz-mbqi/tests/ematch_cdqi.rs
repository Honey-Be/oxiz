//! M2 tests: e-matching (trigger strategy) and CDQI (conflict strategy).
//!
//! The headline soundness result: e-matching against the ground index can
//! never match a quantifier's own body (OxiZ bug B) because body subterms
//! are not in the index — so a `:pattern` with no real ground match emits
//! ZERO lemmas (not the spurious identity `{i↦i}`).

use oxiz_mbqi::toy::{Tid, Toy};
use oxiz_mbqi::{Config, Engine, ModelEval, Verdict};
use rustc_hash::FxHashSet;

const BOOL: u32 = 0;
const INT: u32 = 2;
const F: u32 = 20;
const G: u32 = 21;
const P: u32 = 22;
const EQ: u32 = 12;

fn drain_syntactic(e: &mut Engine<Toy>, t: &mut Toy) -> usize {
    let mut total = 0;
    loop {
        match e.round(t) {
            Verdict::NewLemmas(ls) => total += ls.len(),
            _ => break,
        }
    }
    total
}

#[test]
fn ematch_fires_only_at_real_ground_pattern_terms() {
    // ∀x:Int. f(x)=g(x)  :pattern (f x).   Ground: f(c).
    // e-match binds x↦c (a subterm of the real ground term f(c)) → emits
    // `Q ⇒ f(c)=g(c)`. Exactly one instance; nothing fabricated.
    let mut t = Toy::new();
    let c = t.konst(F + 100, INT);
    let fc = t.app(F, &[c], INT); // ground f(c)

    let x = t.var(300, INT);
    let fx = t.app(F, &[x], INT);
    let gx = t.app(G, &[x], INT);
    let body = t.app(EQ, &[fx, gx], BOOL);
    let pat: &[Tid] = &[fx];
    let q = t.forall(&[(300, INT)], &[pat], body, BOOL);

    let mut e = Engine::new(Config::default());
    e.assert(&t, fc);
    e.assert(&t, q);
    let n = drain_syntactic(&mut e, &mut t);
    assert_eq!(n, 1, "exactly one e-match instance at the real ground f(c)");
    assert_eq!(e.rejected(), 0);
}

#[test]
fn ematch_cannot_self_match_its_own_body_bug_b() {
    // ∀x:Int. f(x)=g(x)  :pattern (f x).   NO ground f(_) term exists (the
    // only f(x) is inside the quantifier body). e-match must find NOTHING —
    // the old engine produced the identity {x↦x} by matching the body. Here
    // the body subterm f(x) is not in the ground index (the index never
    // descends into quantifiers), so zero instances.
    let mut t = Toy::new();
    let x = t.var(301, INT);
    let fx = t.app(F, &[x], INT);
    let gx = t.app(G, &[x], INT);
    let body = t.app(EQ, &[fx, gx], BOOL);
    let pat: &[Tid] = &[fx];
    let q = t.forall(&[(301, INT)], &[pat], body, BOOL);

    let mut e = Engine::new(Config::default());
    e.assert(&t, q); // only the quantifier; no ground f(_)
    let n = drain_syntactic(&mut e, &mut t);
    assert_eq!(n, 0, "no ground f(_) ⇒ no instance (self-match impossible)");
    assert_eq!(e.rejected(), 0);
}

/// A toy model that reports a fixed set of terms false (others unknown).
struct FalseSet(FxHashSet<Tid>);
impl ModelEval<Toy> for FalseSet {
    fn eval_bool(&self, _lang: &Toy, t: Tid) -> Option<bool> {
        if self.0.contains(&t) { Some(false) } else { None }
    }
}

#[test]
fn cdqi_finds_a_conflicting_instance() {
    // ∀x:Int. P(x)  (trigger-free). Ground: P(c). Model: P(c) is false.
    // CDQI enumerates x∈{c}, evaluates P(c)=false → conflict → emits the
    // guarded instance `Q ⇒ P(c)` (which the host core then uses to refute).
    let mut t = Toy::new();
    let c = t.konst(P + 100, INT);
    let pc = t.app(P, &[c], BOOL); // ground P(c)

    let x = t.var(302, INT);
    let body = t.app(P, &[x], BOOL);
    let q = t.forall(&[(302, INT)], &[], body, BOOL); // trigger-free

    let mut e = Engine::new(Config::default());
    e.assert(&t, pc); // P(c) ground (so c is a candidate)
    e.assert(&t, q);

    let model = FalseSet([pc].into_iter().collect());
    let mut emitted = 0;
    loop {
        match e.round_with(&mut t, &model) {
            Verdict::NewLemmas(ls) => emitted += ls.len(),
            _ => break,
        }
    }
    assert!(emitted >= 1, "CDQI should emit the conflicting instance P(c)");
    assert_eq!(e.rejected(), 0);
}
