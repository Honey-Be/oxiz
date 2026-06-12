//! The solver-agnostic term interface.
//!
//! The engine is generic over the host's term representation via [`TermLang`].
//! It is developed and z3-cross-checked against the in-crate toy host
//! ([`crate::toy`]); the OxiZ port (M4) implements [`TermLang`] for
//! `oxiz_core::ast::TermManager` with no engine change.

use core::hash::Hash;

/// A function/predicate symbol (host-defined opaque identity).
pub trait Symbol: Copy + Eq + Hash {}
impl<T: Copy + Eq + Hash> Symbol for T {}

/// A shallow, one-level view of a term — what the engine needs to match
/// triggers, collect ground terms, and rebuild instantiated bodies.
///
/// Crucially there is **no** "fresh witness" or "model value" constructor:
/// the engine never invents domain elements, so an instantiation range can
/// only ever be a real problem term (invariant #1, see `DESIGN.md`).
pub enum TermView<'a, L: TermLang + ?Sized> {
    /// A bound or free variable. `bound` is true iff this variable is bound
    /// by an enclosing quantifier currently being instantiated.
    Var { name: L::VarName },
    /// An application `f(args)` — uninterpreted (`f` an SMT function) OR a
    /// structured connective/operator (And/Eq/Add/Implies/…) presented under
    /// a reserved `sym`. The engine treats `f` opaquely (EUF-style) and reads
    /// the arguments via [`TermLang::children`] (an accessor, not an inline
    /// slice — host structured ops like `Eq(a,b)` have no contiguous args
    /// array). Nullary ⇒ a constant.
    App { sym: L::Sym },
    /// A first-order quantifier. `body` is the matrix; the `:pattern` trigger
    /// groups are fetched on demand via [`TermLang::patterns`] (an allocating
    /// accessor, called once per registration — avoids a `&[&[Term]]`
    /// borrow in the view).
    Quant {
        forall: bool,
        vars: &'a [(L::VarName, L::Sort)],
        body: L::Term,
    },
    /// A leaf the engine does not destructure (numeric/string/bool literal,
    /// or any node it should treat as an opaque ground atom).
    Opaque,
}

/// The host term language the engine is generic over.
///
/// All methods are pure except the `mk_*` constructors and [`substitute`],
/// which intern into the host's (hash-consed) term store.
///
/// [`substitute`]: TermLang::substitute
pub trait TermLang {
    type Term: Copy + Eq + Hash;
    type Sort: Copy + Eq + Hash;
    type VarName: Copy + Eq + Hash;
    type Sym: Symbol;

    /// One-level structural view.
    fn view(&self, t: Self::Term) -> TermView<'_, Self>;

    /// The argument terms of an `App` node (empty for non-apps / constants).
    /// An accessor rather than an inline slice so hosts whose structured ops
    /// (`Eq(a,b)`, `Implies`, …) lack a contiguous args array can still serve
    /// them. Allocates a small `Vec`; the caching milestones memoize hot
    /// walks.
    fn children(&self, t: Self::Term) -> Vec<Self::Term>;

    /// The `:pattern` trigger groups of a quantifier term (each group is a
    /// multi-trigger tuple). Empty ⇒ trigger-free. Called once at
    /// registration. Returns `Vec` to sidestep nested-slice borrows.
    fn patterns(&self, quant: Self::Term) -> Vec<Vec<Self::Term>>;

    /// The sort of a term.
    fn sort_of(&self, t: Self::Term) -> Self::Sort;

    /// **The only substitution entry point.** Capture-free; the binding's
    /// range MUST be ground (the engine guarantees this before calling — it
    /// only ever binds to ground-index terms). Returns the instantiated body.
    fn substitute(&mut self, body: Self::Term, binding: &Binding<Self>) -> Self::Term;

    /// Build `a ⇒ b` (used to attach a quantifier's boolean literal as the
    /// guard of its instance lemma, so the SAT layer carries the polarity
    /// context automatically — invariant #3).
    fn mk_implies(&mut self, a: Self::Term, b: Self::Term) -> Self::Term;
}

/// A capture-free substitution: bound-variable name → ground replacement.
pub struct Binding<'a, L: TermLang + ?Sized> {
    pub(crate) pairs: &'a [(L::VarName, L::Term)],
}

impl<'a, L: TermLang + ?Sized> Binding<'a, L> {
    pub fn new(pairs: &'a [(L::VarName, L::Term)]) -> Self {
        Binding { pairs }
    }
    pub fn get(&self, name: L::VarName) -> Option<L::Term> {
        self.pairs.iter().find(|(n, _)| *n == name).map(|(_, t)| *t)
    }
    pub fn pairs(&self) -> &[(L::VarName, L::Term)] {
        self.pairs
    }
}
