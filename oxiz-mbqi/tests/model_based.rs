//! M3 tests: model-based verification of trigger-free quantifiers, with the
//! D-bug firewall (synthetic witnesses never become lemmas).

use oxiz_mbqi::toy::{Tid, Toy};
use oxiz_mbqi::{Config, Engine, ModelEval, Verdict};

const BOOL: u32 = 0;
const HEIGHT: u32 = 1;
const HEIGHT_LT: u32 = 10;
const PO: u32 = 11;
const EQ: u32 = 12;
const AND: u32 = 13;
const NOT: u32 = 14;

/// A model that answers `eval_forall` with a fixed verdict (verifying or not),
/// and determines no ground atoms (so CDQI finds nothing).
struct ForallOracle(Option<bool>);
impl ModelEval<Toy> for ForallOracle {
    fn eval_bool(&self, _l: &Toy, _t: Tid) -> Option<bool> {
        None
    }
    fn eval_forall(&self, _l: &Toy, _q: Tid) -> Option<bool> {
        self.0
    }
}

fn partial_order_def(t: &mut Toy) -> Tid {
    // ∀x y:Height. height_lt(x,y) = (po(x,y) ∧ x≠y)   — trigger-free, NO
    // ground Height terms anywhere. This is verus-fork's adsmt "trigger D".
    let x = t.var(400, HEIGHT);
    let y = t.var(401, HEIGHT);
    let lt = t.app(HEIGHT_LT, &[x, y], BOOL);
    let po = t.app(PO, &[x, y], BOOL);
    let eq = t.app(EQ, &[x, y], BOOL);
    let neq = t.app(NOT, &[eq], BOOL);
    let conj = t.app(AND, &[po, neq], BOOL);
    let body = t.app(EQ, &[lt, conj], BOOL);
    t.forall(&[(400, HEIGHT), (401, HEIGHT)], &[], body, BOOL)
}

fn run(e: &mut Engine<Toy>, t: &mut Toy, model: &impl ModelEval<Toy>) -> (&'static str, usize) {
    let mut emitted = 0;
    loop {
        match e.round_with(t, model) {
            Verdict::NewLemmas(ls) => emitted += ls.len(),
            Verdict::Saturated => return ("Sat", emitted),
            Verdict::Inconclusive => return ("Unknown", emitted),
            Verdict::BudgetExhausted => return ("Unknown", emitted),
        }
    }
}

#[test]
fn trigger_d_with_a_verifying_model_is_genuine_sat() {
    // The model confirms the definitional axiom holds in its completion
    // (`Some(true)`). The engine then saturates as `Sat` — and emits ZERO
    // lemmas. This is the genuine `sat` the old OxiZ could not produce: it
    // fabricated an 8×8 grid over `u!N` witnesses and reported a spurious
    // `unsat`. Here witnesses never cross into the engine.
    let mut t = Toy::new();
    let q = partial_order_def(&mut t);
    let mut e = Engine::new(Config::default());
    e.assert(&t, q);
    let (verdict, lemmas) = run(&mut e, &mut t, &ForallOracle(Some(true)));
    assert_eq!(verdict, "Sat");
    assert_eq!(lemmas, 0, "no fabricated lemmas — witnesses firewalled out");
    assert_eq!(e.rejected(), 0);
}

#[test]
fn trigger_free_unverifiable_is_unknown_not_unsat() {
    // The model cannot confirm the quantifier (`None`). The sound outcome is
    // `Unknown` (matching native lu-smt / z3-times-out), never a fabricated
    // `Unsat`. Still zero lemmas.
    let mut t = Toy::new();
    let q = partial_order_def(&mut t);
    let mut e = Engine::new(Config::default());
    e.assert(&t, q);
    let (verdict, lemmas) = run(&mut e, &mut t, &ForallOracle(None));
    assert_eq!(verdict, "Unknown");
    assert_eq!(lemmas, 0);
    assert_eq!(e.rejected(), 0);
}
