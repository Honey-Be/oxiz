//! `GroundLedger` — the single funnel that makes the GroundIndex ⇄ congruence
//! (EUF) desync class **structurally unrepresentable** (design
//! `CCFV_UNIFIED_INSTANTIATION.md` §10).
//!
//! The MBQI engine's [`GroundIndex`] (the candidate source) and the EUF's
//! term-set are today two stores owned by two subsystems, fed by two drivers, at
//! two phases, with *opposite* backtracking — so a scope pop can strand a term in
//! one while the other keeps it. Guarding each call site cannot fix a *class* of
//! desync; the structure must. Borrowing the project's two precedents — the
//! `portable-collections` ScopedRollback single-append funnel and the
//! `oxiz-sat` four-writer trail spine (one writer, one rollback, invariant by
//! construction) — the `GroundLedger` owns BOTH stores **privately** and exposes
//! exactly one writer ([`register`](GroundLedger::register)) and one rollback
//! ([`rollback_to`](GroundLedger::rollback_to)), each of which touches both. With
//! no public path to mutate either store alone, "update A but forget B" — and a
//! pop that shrinks one store but not the other — are unrepresentable, not merely
//! guarded.
//!
//! **Spike (this file): the data structure + its invariant, tested in isolation.**
//! Store B is abstracted behind [`CongruenceSink`] so the funnel is a clean
//! generic in `oxiz-mbqi`; the live EUF adapter (interning is entangled with the
//! theory manager) is the *port* half, landed when CCFV (Phase P1+) consumes the
//! ledger. Pure addition — no current consumer, no behaviour change.
//!
//! ## ⚠️ NOT YET USED — reserved substrate (as of 2026-07-06)
//!
//! Nothing in the live solver consumes this module. The clean-MBQI engine is
//! **monotone by design** (never-conclude-unsat = only ever *add* sound lemmas),
//! so it needs no scoped rollback and never calls [`GroundLedger`] /
//! [`GroundIndex::rollback_to`]. It is kept, tested (see the tests below — the
//! rot-guard), and public deliberately, reserved for its two named future
//! consumers, either of which activates it:
//!   1. **CCFV Phase P2+** — the deferred E-ground-(dis)unification wiring this
//!      spike was landed for (design `CCFV_UNIFIED_INSTANTIATION.md` §10).
//!   2. **The fuel-aware cost-scheduler's *persist-across-obligations* path**
//!      (`.claude-research-library/FUEL_AWARE_INSTANTIATION_RESEARCH.md` §5) — a
//!      `QiMark` funnel folding {pending PQ, scoped fingerprints, [`GroundIndex`]}
//!      that mirrors this ledger, needed ONLY if the engine is later made to assert
//!      the prelude once and push/pop per-obligation deltas. The scheduler's
//!      **default is monotone**, so even that redesign does not consume this by
//!      default.
//!
//! The `#![allow(dead_code)]` below is a reader signal, not a functional gate
//! (the items are `pub`, so the lint is inert): it flags the whole module as
//! intentionally-unused-for-now. Delete this module (blueprint survives in the
//! §10 design doc + git) OR wire a consumer — do not let it drift silently.
#![allow(dead_code)]
use crate::ground::GroundIndex;
use crate::term::{Sig, TermLang};

/// The scoped congruence store behind the ledger (store "B" — the EUF, live).
/// The ledger drives it in lock-step with the [`GroundIndex`] so the two can
/// never hold a different ground-term set. A host implements it over its
/// congruence (insert = intern the term and its ground subterms;
/// checkpoint/rollback = push/pop an EUF scope).
pub trait CongruenceSink<S: Sig> {
    /// An opaque scope marker (e.g. the EUF's scope depth). `Copy` so a
    /// [`LedgerMark`] is `Copy`.
    type Mark: Copy;

    /// Register a ground term (and its ground subterms, mirroring the index)
    /// into the congruence. Driven ONLY by [`GroundLedger::register`].
    fn insert<L: TermLang<Sig = S>>(&mut self, host: &L, t: S::Term);

    /// Open a scope; the returned mark restores exactly this state.
    fn checkpoint(&mut self) -> Self::Mark;

    /// Discard everything inserted since `mark` — the inverse of the inserts done
    /// after it. Driven ONLY by [`GroundLedger::rollback_to`].
    fn rollback_to(&mut self, mark: Self::Mark);
}

/// A ledger scope mark — pairs the index frontier with the sink's mark, so one
/// [`rollback_to`](GroundLedger::rollback_to) restores BOTH stores to exactly the
/// checkpoint state. Opaque: only [`GroundLedger`] constructs and consumes it.
#[derive(Clone, Copy)]
pub struct LedgerMark<M> {
    index_frontier: u32,
    sink_mark: M,
}

/// The single funnel for ground-term registration (design §10).
///
/// Owns the [`GroundIndex`] (store A) and a [`CongruenceSink`] (store B)
/// **privately**: there is no public path to mutate one without the other,
/// because [`register`](Self::register) is the only writer and
/// [`rollback_to`](Self::rollback_to) the only rollback, and each touches both.
/// The cross-store desync class is therefore impossible by construction.
pub struct GroundLedger<S: Sig, B: CongruenceSink<S>> {
    index: GroundIndex<S>,
    sink: B,
}

impl<S: Sig, B: CongruenceSink<S>> GroundLedger<S, B> {
    /// A fresh ledger over an empty index and the given (fresh) sink.
    pub fn new(sink: B) -> Self {
        GroundLedger { index: GroundIndex::new(), sink }
    }

    /// THE SOLE WRITER. Registers `t` (and its ground subterms) into BOTH stores
    /// in one call — they can never disagree on the ground-term set.
    pub fn register<L: TermLang<Sig = S>>(&mut self, host: &L, t: S::Term) {
        self.index.add_term(host, t);
        self.sink.insert(host, t);
    }

    /// Open a scope on BOTH stores; the returned mark restores them together.
    pub fn checkpoint(&mut self) -> LedgerMark<B::Mark> {
        LedgerMark {
            index_frontier: self.index.frontier(),
            sink_mark: self.sink.checkpoint(),
        }
    }

    /// THE SOLE ROLLBACK. Restores BOTH stores to the checkpoint — neither can be
    /// left holding a term the other forgot.
    pub fn rollback_to(&mut self, mark: LedgerMark<B::Mark>) {
        self.index.rollback_to(mark.index_frontier);
        self.sink.rollback_to(mark.sink_mark);
    }

    /// Read-only access to the ground index (the engine's candidate source).
    pub fn index(&self) -> &GroundIndex<S> {
        &self.index
    }

    /// Read-only access to the congruence sink.
    pub fn sink(&self) -> &B {
        &self.sink
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ground::GroundIndex;
    use crate::toy::{Toy, ToySig};

    /// A toy sink that mirrors the ground-term set in a SECOND, independent
    /// `GroundIndex`. The two indices stay byte-identical only because the ledger
    /// funnels every register/checkpoint/rollback to both — if it ever let them
    /// diverge, the `assert_eq!`s below would catch it.
    struct MirrorSink {
        idx: GroundIndex<ToySig>,
    }
    impl MirrorSink {
        fn new() -> Self {
            MirrorSink { idx: GroundIndex::new() }
        }
        fn index(&self) -> &GroundIndex<ToySig> {
            &self.idx
        }
    }
    impl CongruenceSink<ToySig> for MirrorSink {
        type Mark = u32;
        fn insert<L: TermLang<Sig = ToySig>>(&mut self, host: &L, t: u32) {
            self.idx.add_term(host, t);
        }
        fn checkpoint(&mut self) -> u32 {
            self.idx.frontier()
        }
        fn rollback_to(&mut self, m: u32) {
            self.idx.rollback_to(m);
        }
    }

    #[test]
    fn register_and_rollback_keep_both_stores_in_lockstep() {
        let mut h = Toy::new();
        let s = 0; // the only sort
        let a = h.konst(1, s);
        let b = h.konst(2, s);
        let fa = h.app(10, &[a], s);
        let fb = h.app(10, &[b], s);
        let gfa = h.app(11, &[fa], s);

        let mut led = GroundLedger::new(MirrorSink::new());
        led.register(&h, fa); // registers a, f(a)
        led.register(&h, fb); // registers b, f(b)

        let mark = led.checkpoint();
        led.register(&h, gfa); // registers g(f(a))
        assert!(led.index().contains(gfa));
        assert!(led.sink().index().contains(gfa));

        led.rollback_to(mark);

        // Both stores forgot g(f(a)) ...
        assert!(!led.index().contains(gfa));
        assert!(!led.sink().index().contains(gfa));
        // ... and both kept everything registered before the checkpoint ...
        for &t in &[a, b, fa, fb] {
            assert!(led.index().contains(t), "index lost {t}");
            assert!(led.sink().index().contains(t), "sink lost {t}");
        }
        // ... and the two stores AGREE on every term (the desync invariant) ...
        for &t in &[a, b, fa, fb, gfa] {
            assert_eq!(
                led.index().contains(t),
                led.sink().index().contains(t),
                "stores disagree on {t}"
            );
        }
        // ... and the frontier is restored exactly on both.
        assert_eq!(led.index().frontier(), led.sink().index().frontier());
        assert_eq!(led.index().frontier(), mark.index_frontier);
    }

    #[test]
    fn nested_checkpoints_roll_back_both() {
        let mut h = Toy::new();
        let s = 0;
        let a = h.konst(1, s);
        let b = h.konst(2, s);
        let c = h.konst(3, s);

        let mut led = GroundLedger::new(MirrorSink::new());
        led.register(&h, a);
        let m1 = led.checkpoint();
        led.register(&h, b);
        let m2 = led.checkpoint();
        led.register(&h, c);

        // Roll back to the inner mark: c gone on both, b kept on both.
        led.rollback_to(m2);
        assert!(!led.index().contains(c) && !led.sink().index().contains(c));
        assert!(led.index().contains(b) && led.sink().index().contains(b));

        // Roll back to the outer mark: b gone on both, a kept on both.
        led.rollback_to(m1);
        assert!(!led.index().contains(b) && !led.sink().index().contains(b));
        assert!(led.index().contains(a) && led.sink().index().contains(a));
        assert_eq!(led.index().frontier(), led.sink().index().frontier());
    }

    #[test]
    fn re_register_after_rollback_works() {
        // A rolled-back term can be cleanly re-registered (no stale state).
        let mut h = Toy::new();
        let s = 0;
        let a = h.konst(1, s);

        let mut led = GroundLedger::new(MirrorSink::new());
        let m = led.checkpoint();
        led.register(&h, a);
        assert!(led.index().contains(a));
        led.rollback_to(m);
        assert!(!led.index().contains(a) && !led.sink().index().contains(a));
        // re-register: both pick it up again at the same frontier
        led.register(&h, a);
        assert!(led.index().contains(a) && led.sink().index().contains(a));
        assert_eq!(led.index().frontier(), led.sink().index().frontier());
    }
}
