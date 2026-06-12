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
        }
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
        self.add_rec(lang, t);
    }

    /// Returns `true` if `t` is ground (contains no variables) — and as a
    /// side effect registers its ground subterms.
    fn add_rec<L: TermLang<Sig = S>>(&mut self, lang: &L, t: S::Term) -> bool {
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
                self.register(lang, t);
                true
            }
            TermView::Quant { .. } => {
                // Do not descend: the body holds bound variables. The
                // quantifier node itself is not a ground first-order term.
                false
            }
            TermView::Opaque => {
                self.register(lang, t);
                true
            }
            TermView::App { sym } => {
                let args = lang.children(t);
                let mut all_ground = true;
                for &a in &args {
                    if !self.add_rec(lang, a) {
                        all_ground = false;
                    }
                }
                if all_ground {
                    self.register(lang, t);
                    self.by_head.entry(sym).or_default().push(t);
                }
                all_ground
            }
        }
    }

    fn register<L: TermLang<Sig = S>>(&mut self, lang: &L, t: S::Term) {
        if self.all.insert(t) {
            self.by_sort.entry(lang.sort_of(t)).or_default().push(t);
            self.idx.insert(t, self.next_idx);
            self.next_idx += 1;
        }
    }
}
