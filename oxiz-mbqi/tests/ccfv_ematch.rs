//! P2 — CCFV congruence-aware e-matching (opt-in `Config::ccfv_ematch`) fires a
//! trigger instance where the syntactic matcher cannot, because the match holds
//! only *modulo the congruence*. The default path (flag off) is unaffected.
//!
//! Shape: `∀x:Int. f(g(x)) = h(x)  :pattern (f (g x))`, with ground `f(c)` and
//! `g(a)` and the congruence `c ≡ g(a)`. The trigger's seed is `f(c)`; matching
//! `f(g(x))` against it needs `g(x)` to match `c`, which only works once `c`'s
//! class is seen to contain `g(a)` — then `x ↦ a`. Syntactically `c` is a
//! constant, so the syntactic matcher finds nothing.

use oxiz_mbqi::toy::{Tid, Toy, ToySig};
use oxiz_mbqi::{Config, Congruence, Engine, FuncApp, NoModel, Verdict};
use rustc_hash::FxHashMap;

const BOOL: u32 = 0;
const INT: u32 = 2;
const EQ: u32 = 12;
const F: u32 = 20;
const G: u32 = 21;
const H: u32 = 23;

/// A toy congruence over explicit equivalence classes (the live oracle is the
/// EUF; this lets the test control `equal`/`class`/`rep`).
struct ToyCong {
    classes: Vec<Vec<Tid>>,
    of: FxHashMap<Tid, usize>,
}
impl ToyCong {
    fn new(classes: Vec<Vec<Tid>>) -> Self {
        let mut of = FxHashMap::default();
        for (i, c) in classes.iter().enumerate() {
            for &t in c {
                of.insert(t, i);
            }
        }
        ToyCong { classes, of }
    }
}
impl Congruence<ToySig> for ToyCong {
    fn rep(&self, t: Tid) -> Tid {
        self.of.get(&t).map(|&i| self.classes[i][0]).unwrap_or(t)
    }
    fn equal(&self, a: Tid, b: Tid) -> bool {
        a == b || matches!((self.of.get(&a), self.of.get(&b)), (Some(i), Some(j)) if i == j)
    }
    fn class(&self, t: Tid) -> Vec<Tid> {
        self.of.get(&t).map(|&i| self.classes[i].clone()).unwrap_or_else(|| vec![t])
    }
    fn apps_like(&self, _: Tid) -> Vec<FuncApp<ToySig>> {
        Vec::new()
    }
}

/// Build the engine over `∀x. f(g(x))=h(x) :pat (f(g x))` with ground `f(c)`,
/// `g(a)`. Returns the engine, host, and the binding witnesses `(a, c, ga)`.
fn setup(ccfv_ematch: bool) -> (Engine<ToySig>, Toy, Tid, Tid, Tid) {
    let mut t = Toy::new();
    let a = t.konst(100, INT);
    let c = t.konst(101, INT);
    let ga = t.app(G, &[a], INT); // g(a)
    let fc = t.app(F, &[c], INT); // f(c) — the ground f-application (seed)

    let x = t.var(300, INT);
    let gx = t.app(G, &[x], INT);
    let fgx = t.app(F, &[gx], INT); // f(g(x)) — the trigger pattern
    let hx = t.app(H, &[x], INT);
    let body = t.app(EQ, &[fgx, hx], BOOL);
    let pat: &[Tid] = &[fgx];
    let q = t.forall(&[(300, INT)], &[pat], body, BOOL);

    let mut e = Engine::new(Config { ccfv_ematch, ..Config::default() });
    e.assert(&t, fc); // ground f(c)  (seeds the trigger head F)
    e.assert(&t, ga); // ground g(a)  (registers a, the binding target)
    e.assert(&t, q);
    (e, t, a, c, ga)
}

#[test]
fn syntactic_path_finds_no_match() {
    // Default (ccfv_ematch = false): `f(g(x))` cannot match `f(c)` syntactically
    // (c is a constant, not a g-application) ⇒ zero e-match instances.
    let (mut e, mut t, _a, _c, _ga) = setup(false);
    let n = match e.round(&mut t) {
        Verdict::NewLemmas(ls) => ls.len(),
        _ => 0,
    };
    assert_eq!(n, 0, "syntactic e-matching finds nothing");
    assert_eq!(e.rejected(), 0);
}

#[test]
fn ccfv_path_matches_modulo_congruence() {
    // ccfv_ematch = true + congruence c ≡ g(a): `f(g(x))` matches `f(c)` because
    // c's class contains g(a) ⇒ x ↦ a ⇒ one guarded instance is emitted.
    let (mut e, mut t, _a, c, ga) = setup(true);
    let cong = ToyCong::new(vec![vec![c, ga]]); // c ≡ g(a)
    let n = match e.round_with_cong(&mut t, &NoModel, &cong) {
        Verdict::NewLemmas(ls) => ls.len(),
        _ => 0,
    };
    assert_eq!(n, 1, "CCFV e-matching fires modulo congruence (x ↦ a)");
    assert_eq!(e.rejected(), 0, "the instance is ground ⇒ passes the firewall");
}

#[test]
fn ccfv_path_without_the_congruence_still_finds_nothing() {
    // ccfv_ematch = true but the trivial congruence (c ≢ g(a)): the CCFV matcher
    // degrades to syntactic and finds nothing — confirms the match above is the
    // congruence doing the work, not the code path.
    let (mut e, mut t, _a, _c, _ga) = setup(true);
    let cong = ToyCong::new(vec![]); // no equalities
    let n = match e.round_with_cong(&mut t, &NoModel, &cong) {
        Verdict::NewLemmas(ls) => ls.len(),
        _ => 0,
    };
    assert_eq!(n, 0, "no congruence ⇒ CCFV matches nothing either");
}
