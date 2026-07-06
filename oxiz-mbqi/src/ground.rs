//! The ground-term index — the ONLY source of instantiation candidates.
//!
//! Invariant #1 (see `DESIGN.md`) is enforced structurally here: candidates
//! are exactly the terms that occur in the asserted formulas and in prior
//! valid instances, grouped by sort. There is no path that adds a fabricated
//! witness or a bound variable to this index, so any substitution drawn from
//! it has a ground, in-problem range by construction.
//!
//! The index is keyed by the lifetime-free [`Sig`], so it lives on the engine
//! across rounds; its term-walking methods take the borrowing host `&L` per
//! call (`L: TermLang<Sig = S>`).

use crate::term::{Sig, TermLang, TermView};
use rustc_hash::{FxHashMap, FxHashSet};

/// Ground terms seen so far, indexed for candidate lookup.
pub struct GroundIndex<S: Sig> {
    /// All ground terms, deduplicated.
    all: FxHashSet<S::Term>,
    /// Ground terms grouped by sort (candidate domains for instantiation).
    by_sort: FxHashMap<S::Sort, Vec<S::Term>>,
    /// Ground applications grouped by head symbol (candidates for e-matching
    /// a trigger whose top symbol is `sym`).
    by_head: FxHashMap<S::Sym, Vec<S::Term>>,
    /// Monotonic insertion index per term — the frontier watermark. A
    /// quantifier remembers how many terms existed when it last scanned; new
    /// candidates are those with `idx >= watermark`. Purely an efficiency
    /// device (the `seen` dedup already guarantees correctness); it turns
    /// per-round matching from "all ground terms" into "the delta".
    idx: FxHashMap<S::Term, u32>,
    next_idx: u32,
    /// Registration order: `order[i]` is the term registered with index `i`.
    /// Lets [`rollback_to`](Self::rollback_to) identify exactly the terms added
    /// since a frontier checkpoint. Additive — the live (monotone) engine never
    /// rolls back; only a [`GroundLedger`](crate::ledger::GroundLedger) does, to
    /// keep the index in lock-step with a scoped congruence store (design §10).
    order: Vec<S::Term>,
    /// **Instantiation generation** per term (design `FUEL_AWARE_COST_SCHEDULER.md`
    /// E1): input (assertion) terms are generation 0; a term first registered while
    /// minting an instance carries `1 + max(generation of that instance's binding
    /// terms)` (see [`add_term_gen`](Self::add_term_gen)). This is the well-founded
    /// depth measure the cost-scheduler prices on — distinct from the insertion-order
    /// `idx` above. Write-once (a term keeps the generation of its FIRST registration,
    /// like `idx`); read-only thereafter. **Additive: nothing consumes it yet
    /// (P0.5); verdicts are unchanged.**
    term_gen: FxHashMap<S::Term, u32>,
    /// The maximum generation registered so far (cached; recomputed on rollback).
    max_gen: u32,
}

impl<S: Sig> Default for GroundIndex<S> {
    fn default() -> Self {
        Self::new()
    }
}

impl<S: Sig> GroundIndex<S> {
    pub fn new() -> Self {
        GroundIndex {
            all: FxHashSet::default(),
            by_sort: FxHashMap::default(),
            by_head: FxHashMap::default(),
            idx: FxHashMap::default(),
            next_idx: 0,
            order: Vec::new(),
            term_gen: FxHashMap::default(),
            max_gen: 0,
        }
    }

    /// The instantiation generation of a term (E1): 0 for an input/assertion term
    /// or one never registered; `1 + max binding generation` for an instance-minted
    /// term. See [`add_term_gen`](Self::add_term_gen).
    pub fn gen_of(&self, t: S::Term) -> u32 {
        self.term_gen.get(&t).copied().unwrap_or(0)
    }

    /// The largest generation registered so far.
    pub fn max_gen(&self) -> u32 {
        self.max_gen
    }

    /// Total ground terms registered so far — the current frontier watermark.
    pub fn frontier(&self) -> u32 {
        self.next_idx
    }

    /// The insertion index of a term (0 if somehow absent).
    pub fn idx_of(&self, t: S::Term) -> u32 {
        self.idx.get(&t).copied().unwrap_or(0)
    }

    /// Candidate terms of a given sort.
    pub fn of_sort(&self, sort: S::Sort) -> &[S::Term] {
        self.by_sort.get(&sort).map(Vec::as_slice).unwrap_or(&[])
    }

    /// Ground applications whose head is `sym` (e-matching candidates).
    pub fn with_head(&self, sym: S::Sym) -> &[S::Term] {
        self.by_head.get(&sym).map(Vec::as_slice).unwrap_or(&[])
    }

    pub fn contains(&self, t: S::Term) -> bool {
        self.all.contains(&t)
    }

    /// Recursively register every GROUND subterm of `t`. A subterm under a
    /// quantifier (which would contain that quantifier's bound vars) is NOT
    /// descended into — its bound variables are not ground, so it never
    /// becomes a candidate. This is the structural guarantee behind
    /// invariant #1: the index can only hold variable-free, in-problem terms.
    pub fn add_term<L: TermLang<Sig = S>>(&mut self, lang: &L, t: S::Term) {
        self.add_rec(lang, t, 0);
    }

    /// Register the ground subterms of an INSTANCE-minted term `t` at generation
    /// `g` (E1). Newly-registered subterms take generation `g`; already-known terms
    /// keep their existing generation (write-once, like `idx`). The caller computes
    /// `g = 1 + max(generation of the instance's binding terms)`. Same registration
    /// path / same structural guarantees as [`add_term`] — the only difference is
    /// the generation tag on fresh terms.
    pub fn add_term_gen<L: TermLang<Sig = S>>(&mut self, lang: &L, t: S::Term, g: u32) {
        self.add_rec(lang, t, g);
    }

    /// Returns `true` if `t` is ground (contains no variables) — and as a
    /// side effect registers its ground subterms at generation `g`.
    fn add_rec<L: TermLang<Sig = S>>(&mut self, lang: &L, t: S::Term, g: u32) -> bool {
        match lang.view(t) {
            TermView::Var { .. } => {
                // A `Var` REACHED by the index is a free / declared constant,
                // not a bound variable: the index never descends into a `Quant`
                // (below) and emitted lemmas are bound-var-free, so a bound
                // variable is never visited here. Treat it as a ground term so
                // it becomes a candidate. Hosts that model constants as nullary
                // `App` (the toy) never hit this arm; hosts that model declared
                // constants as `Var` (OxiZ) rely on it. e-matching still
                // distinguishes bound variables via the quantifier's bound set,
                // so this is sound.
                self.register(lang, t, g);
                true
            }
            TermView::Quant { .. } => {
                // Do not descend: the body holds bound variables. The
                // quantifier node itself is not a ground first-order term.
                false
            }
            TermView::Opaque => {
                self.register(lang, t, g);
                true
            }
            TermView::App { sym } => {
                let args = lang.children(t);
                let mut all_ground = true;
                for &a in &args {
                    if !self.add_rec(lang, a, g) {
                        all_ground = false;
                    }
                }
                if all_ground {
                    self.register(lang, t, g);
                    self.by_head.entry(sym).or_default().push(t);
                }
                all_ground
            }
        }
    }

    fn register<L: TermLang<Sig = S>>(&mut self, lang: &L, t: S::Term, g: u32) {
        if self.all.insert(t) {
            self.by_sort.entry(lang.sort_of(t)).or_default().push(t);
            self.idx.insert(t, self.next_idx);
            self.order.push(t);
            self.next_idx += 1;
            self.term_gen.insert(t, g);
            if g > self.max_gen {
                self.max_gen = g;
            }
        }
    }

    /// Roll the index back to a `frontier` previously read from
    /// [`frontier`](Self::frontier): every term registered at or after it is
    /// removed from ALL buckets (`all` / `by_sort` / `by_head` / `idx`), exactly
    /// inverting the registrations done since. A no-op if `frontier` is already
    /// current or ahead.
    ///
    /// Additive scoped capability used by [`GroundLedger`](crate::ledger::GroundLedger):
    /// the live monotone engine never calls it, so the structural invariant #1
    /// and the cross-round candidate accumulation are unaffected. It is what lets
    /// the index move in lock-step with a scoped congruence store so the two can
    /// never desync (design §10).
    pub fn rollback_to(&mut self, frontier: u32) {
        if frontier >= self.next_idx {
            return;
        }
        // Exactly the terms registered at index ≥ frontier (`order[i]` has idx i).
        let removed = self.order.split_off(frontier as usize);
        for t in &removed {
            self.all.remove(t);
            self.idx.remove(t);
            self.term_gen.remove(t);
        }
        // Drop the removed terms from the sort/head buckets (split borrow: `all`
        // and the bucket maps are disjoint fields).
        let all = &self.all;
        self.by_sort.values_mut().for_each(|b| b.retain(|t| all.contains(t)));
        self.by_head.values_mut().for_each(|b| b.retain(|t| all.contains(t)));
        self.next_idx = frontier;
        // Recompute the generation high-water mark over the surviving terms.
        self.max_gen = self.term_gen.values().copied().max().unwrap_or(0);
    }
}
