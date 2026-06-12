//! M1 soundness-core tests against the toy host.
//!
//! These encode the SHAPES of the OxiZ spurious-`unsat` triggers and assert
//! the clean engine's behaviour: it emits only sound, ground, guarded
//! lemmas, and — crucially — fabricates nothing, so a trigger-free
//! quantifier over a sort with no ground terms yields ZERO lemmas (the host
//! would then report `sat`, matching z3/native, instead of the old spurious
//! `unsat`).

use oxiz_mbqi::toy::Toy;
use oxiz_mbqi::{Config, Engine, Verdict};

const BOOL: u32 = 0;
const HEIGHT: u32 = 1;
const INT: u32 = 2;

// symbols
const HEIGHT_LT: u32 = 10;
const PO: u32 = 11;
const EQ: u32 = 12;
const AND: u32 = 13;
const NOT: u32 = 14;
const F: u32 = 20;

fn drain(engine: &mut Engine<Toy>, toy: &mut Toy) -> (usize, usize) {
    // run rounds to saturation/budget; return (total lemmas, rejected)
    let mut total = 0;
    loop {
        match engine.round(toy) {
            Verdict::NewLemmas(ls) => total += ls.len(),
            Verdict::Saturated | Verdict::Inconclusive | Verdict::BudgetExhausted => break,
        }
    }
    (total, engine.rejected())
}

#[test]
fn trigger_free_over_empty_uninterpreted_sort_fabricates_nothing() {
    // ∀x y:Height. height_lt(x,y) = (po(x,y) ∧ x≠y)   — the partial-order /
    // triggerD shape. There are NO ground Height terms in the problem.
    // The clean engine must emit ZERO lemmas (no fabricated `u!N`), so the
    // host stays sat. (OxiZ used to enumerate a fabricated 8×8 grid → unsat.)
    let mut t = Toy::new();
    let x = t.var(100, HEIGHT);
    let y = t.var(101, HEIGHT);
    let lt = t.app(HEIGHT_LT, &[x, y], BOOL);
    let po = t.app(PO, &[x, y], BOOL);
    let eq = t.app(EQ, &[x, y], BOOL);
    let neq = t.app(NOT, &[eq], BOOL);
    let conj = t.app(AND, &[po, neq], BOOL);
    let body = t.app(EQ, &[lt, conj], BOOL);
    let q = t.forall(&[(100, HEIGHT), (101, HEIGHT)], &[], body, BOOL);

    let mut e = Engine::new(Config::default());
    e.assert(&t, q);
    let (lemmas, rejected) = drain(&mut e, &mut t);
    assert_eq!(lemmas, 0, "must not fabricate any Height instances");
    assert_eq!(rejected, 0, "no candidate should be rejected (none generated)");
}

#[test]
fn instantiates_only_at_real_ground_terms() {
    // ∀x:Int. f(x) = x   plus a ground constant c:Int.
    // The engine instantiates ONLY at c (the one real ground Int term),
    // producing the guarded lemma `Q ⇒ f(c)=c`. No fabricated values.
    let mut t = Toy::new();
    let c = t.konst(F + 1, INT); // a ground Int constant `c`
    // assert a ground fact that puts c in the index, e.g. f(c) (so c is ground)
    let fc = t.app(F, &[c], INT);
    let _ = fc;

    let x = t.var(200, INT);
    let fx = t.app(F, &[x], INT);
    let body = t.app(EQ, &[fx, x], BOOL);
    let q = t.forall(&[(200, INT)], &[], body, BOOL);

    let mut e = Engine::new(Config::default());
    e.assert(&t, fc); // ground term f(c) → indexes c and f(c)
    e.assert(&t, q);
    let (lemmas, rejected) = drain(&mut e, &mut t);
    assert!(lemmas >= 1, "should instantiate at the real ground term c");
    assert_eq!(rejected, 0, "every emitted candidate came from the ground index");
}

#[test]
fn engine_has_no_unsat_verdict() {
    // Type-level guarantee: `Verdict` has no `Unsat` variant. This test
    // documents the invariant — refutation is the host core's job.
    fn assert_variants(v: &Verdict<u32>) -> &'static str {
        match v {
            Verdict::NewLemmas(_) => "lemmas",
            Verdict::Saturated => "saturated",
            Verdict::Inconclusive => "inconclusive",
            Verdict::BudgetExhausted => "budget",
        }
    }
    let _ = assert_variants; // compile-time check is the point
}
