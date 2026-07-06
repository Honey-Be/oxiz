//! P0.5 host/engine extension slice (design `FUEL_AWARE_COST_SCHEDULER.md` §2.5):
//! E1 generation tracking on [`GroundIndex`], and the E2/E3 accessor default-None
//! degrade path. Additive — nothing consumes these yet, so verdicts are unchanged;
//! these tests pin the primitive behaviour the cost-scheduler will build on.

use oxiz_mbqi::ground::GroundIndex;
use oxiz_mbqi::toy::{Toy, ToySig};
use oxiz_mbqi::TermLang;

const INT: u32 = 2;
const F: u32 = 40;

#[test]
fn e1_generation_accounting() {
    let mut t = Toy::new();
    let a = t.konst(100, INT);
    let fa = t.app(F, &[a], INT);
    let ffa = t.app(F, &[fa], INT);
    let fffa = t.app(F, &[ffa], INT);

    let mut g = GroundIndex::<ToySig>::new();

    // Assertion terms register at generation 0.
    g.add_term(&t, fa); // registers a and f(a)
    assert_eq!(g.gen_of(a), 0);
    assert_eq!(g.gen_of(fa), 0);
    assert_eq!(g.max_gen(), 0);

    // A minted term at generation 1: only the FRESH subterm f(f(a)) takes gen 1;
    // the already-known f(a)/a keep generation 0 (write-once, like `idx`).
    g.add_term_gen(&t, ffa, 1);
    assert_eq!(g.gen_of(ffa), 1);
    assert_eq!(g.gen_of(fa), 0, "existing term keeps its first generation");
    assert_eq!(g.gen_of(a), 0);
    assert_eq!(g.max_gen(), 1);

    // Deeper mint.
    g.add_term_gen(&t, fffa, 2);
    assert_eq!(g.gen_of(fffa), 2);
    assert_eq!(g.max_gen(), 2);

    // Write-once: re-registering an existing term at a different generation does
    // not change its generation (the FIRST registration wins, like `idx`).
    g.add_term_gen(&t, fa, 9);
    assert_eq!(g.gen_of(fa), 0, "generation is write-once");
    assert_eq!(g.max_gen(), 2);

    // An unregistered term reads as generation 0.
    let other = t.konst(200, INT);
    assert_eq!(g.gen_of(other), 0);
}

#[test]
fn e1_generation_dropped_on_rollback() {
    // The reserved GroundLedger rollback path must drop generation tags with the
    // terms and recompute the high-water mark over the survivors.
    let mut t = Toy::new();
    let a = t.konst(100, INT);
    let fa = t.app(F, &[a], INT);
    let ffa = t.app(F, &[fa], INT);

    let mut g = GroundIndex::<ToySig>::new();
    g.add_term(&t, fa); // gen 0; frontier now 2 (a, f(a))
    let mark = g.frontier();
    g.add_term_gen(&t, ffa, 3); // gen 3, idx 2
    assert_eq!(g.max_gen(), 3);

    g.rollback_to(mark);
    assert!(!g.contains(ffa));
    assert_eq!(g.gen_of(ffa), 0, "rolled-back term reads as generation 0");
    assert_eq!(g.max_gen(), 0, "high-water mark recomputed over survivors");
}

#[test]
fn e2_e3_default_degrade_to_none() {
    // The toy host does not override the E2/E3 accessors, so both degrade to
    // `None` — the scheduler then prices on `weight + generation` only (Z3 parity)
    // and falls back to the raw id for ordering. This pins the graceful-degrade
    // contract every non-fuel host relies on.
    let t = Toy::new();
    assert_eq!(t.fuel_role(F), None);
    assert_eq!(t.content_key(F), None);
}
