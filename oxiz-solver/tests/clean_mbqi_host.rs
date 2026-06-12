//! M4 port smoke tests: drive the clean-room engine over REAL OxiZ terms via
//! `OxizHost`, validating the `TermLang` mapping end-to-end.

use oxiz_core::ast::TermManager;
use oxiz_mbqi::{Config, Engine, Verdict};
use oxiz_solver::clean_mbqi::{OxizHost, OxizSig, SolverModel};
use rustc_hash::FxHashMap;

// `Engine<OxizSig>` is lifetime-free (keyed on the `Sig` marker, not the
// borrowing `OxizHost<'a>`), so it no longer ties the engine to the host's
// borrow — the M4e unblock. The host is re-borrowed per round.
fn drain(e: &mut Engine<OxizSig>, host: &mut OxizHost<'_>) -> usize {
    let mut emitted = 0;
    loop {
        match e.round(&mut *host) {
            Verdict::NewLemmas(ls) => emitted += ls.len(),
            _ => break,
        }
    }
    emitted
}

#[test]
fn host_ematch_instantiates_at_a_real_ground_constant() {
    // ∀x:Int. f(x)=g(x)  :pattern (f x).   Ground: f(c), c a declared
    // constant (a `Var` in OxiZ). e-match binds x↦c → emits Q ⇒ f(c)=g(c).
    let mut tm = TermManager::new();
    let int = tm.sorts.int_sort;
    let c = tm.mk_var("c", int); // declared constant — Var in OxiZ
    let fc = tm.mk_apply("f", [c], int); // ground f(c)
    let x = tm.mk_var("x", int);
    let fx = tm.mk_apply("f", [x], int);
    let gx = tm.mk_apply("g", [x], int);
    let body = tm.mk_eq(fx, gx);
    let q = tm.mk_forall_with_patterns([("x", int)], body, [[fx]]);

    let mut host = OxizHost::new(&mut tm);
    let mut e = Engine::new(Config::default());
    e.assert(&host, fc);
    e.assert(&host, q);
    let emitted = drain(&mut e, &mut host);
    assert!(emitted >= 1, "should e-match at the real ground f(c)");
    assert_eq!(e.rejected(), 0, "every candidate came from the ground index");
}

#[test]
fn host_patterned_quant_with_no_ground_match_fabricates_nothing() {
    // ∀x:Int. f(x)=g(x)  :pattern (f x).   NO ground f(_) exists. The clean
    // engine emits ZERO instances (the OxiZ B-bug self-match is impossible —
    // the body's f(x) is under the quantifier, never in the ground index).
    let mut tm = TermManager::new();
    let int = tm.sorts.int_sort;
    let x = tm.mk_var("x", int);
    let fx = tm.mk_apply("f", [x], int);
    let gx = tm.mk_apply("g", [x], int);
    let body = tm.mk_eq(fx, gx);
    let q = tm.mk_forall_with_patterns([("x", int)], body, [[fx]]);

    let mut host = OxizHost::new(&mut tm);
    let mut e = Engine::new(Config::default());
    e.assert(&host, q);
    let emitted = drain(&mut e, &mut host);
    assert_eq!(emitted, 0, "no ground f(_) ⇒ no instance");
    assert_eq!(e.rejected(), 0);
}

#[test]
fn host_cdqi_finds_a_conflicting_instance_via_solver_model() {
    // ∀x:Int. P(x) (trigger-free). Ground P(c). Model: P(c) is false.
    // The SolverModel oracle's eval_bool resolves P(c)=false → CDQI emits the
    // guarded conflicting instance Q ⇒ P(c).
    let mut tm = TermManager::new();
    let int = tm.sorts.int_sort;
    let bool_s = tm.sorts.bool_sort;
    let c = tm.mk_var("c", int);
    let pc = tm.mk_apply("P", [c], bool_s); // ground P(c)
    let x = tm.mk_var("x", int);
    let body = tm.mk_apply("P", [x], bool_s);
    let q = tm.mk_forall_with_patterns::<[[_; 0]; 0], _>([("x", int)], body, []); // trigger-free
    let true_id = tm.mk_true();
    let false_id = tm.mk_false();

    // Model assignment: P(c) = false.
    let mut assign: FxHashMap<_, _> = FxHashMap::default();
    assign.insert(pc, false_id);
    let model = SolverModel::new(assign, true_id, false_id);

    let mut host = OxizHost::new(&mut tm);
    let mut e = Engine::new(Config::default());
    e.assert(&host, pc);
    e.assert(&host, q);
    let mut emitted = 0;
    loop {
        match e.round_with(&mut host, &model) {
            Verdict::NewLemmas(ls) => emitted += ls.len(),
            _ => break,
        }
    }
    assert!(emitted >= 1, "CDQI should emit the conflicting P(c) instance");
    assert_eq!(e.rejected(), 0);
}
