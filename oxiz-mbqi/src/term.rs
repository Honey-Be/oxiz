//! The solver-agnostic term interface.
//!
//! The engine is generic over the host's term representation via two traits:
//!
//!  * [`Sig`] — the **lifetime-free identity signature**: the four associated
//!    types (`Term`/`Sort`/`VarName`/`Sym`). It carries no borrow, so the
//!    engine's persistent state ([`crate::engine::Engine`],
//!    [`crate::ground::GroundIndex`], [`crate::instantiate::Quant`]) is
//!    parameterized by `S: Sig` and can **outlive any single borrow of the
//!    host** — it can sit on the solver across `check()` rounds.
//!  * [`TermLang`] — the **behavior**: `view`/`children`/`substitute`/… . A
//!    host impls it on a short-lived wrapper that borrows the term arena
//!    (`OxizHost<'a> { tm: &'a mut TermManager }`). Each round re-borrows the
//!    manager for a fresh `'a`; the methods take `&self`/`&mut self`, so the
//!    borrow lives only for that round.
//!
//! This split is the fix for the M4e lifetime blocker: `Engine<OxizHost<'a>>`
//! would have been `'a`-typed (uninstantiable across rounds) even though it
//! only ever stores `TermId`s; `Engine<OxizSig>` is lifetime-free.
//!
//! Developed and z3-cross-checked against the in-crate toy host
//! ([`crate::toy`]); the OxiZ port (M4) implements [`TermLang`] for a wrapper
//! over `oxiz_core::ast::TermManager` with no engine change.

use core::hash::Hash;

/// A function/predicate symbol (host-defined opaque identity).
pub trait Symbol: Copy + Eq + Hash {}
impl<T: Copy + Eq + Hash> Symbol for T {}

/// The lifetime-free identity signature of a host term language: just the four
/// opaque identity types the engine keys its state on.
///
/// Separating these from [`TermLang`]'s behavior is what lets `Engine<S>`,
/// `GroundIndex<S>`, and `Quant<S>` be lifetime-free and persist across solver
/// rounds. A host provides a zero-sized marker (`struct OxizSig;`) implementing
/// this, and impls [`TermLang`] (the borrowing behavior) separately with
/// `type Sig = OxizSig`.
///
/// `'static` documents the intent: these are owned identities (a `TermId`, a
/// `Spur`), never borrows. Every real host's ids are plain `Copy` PODs, so the
/// bound is free.
pub trait Sig: 'static {
    type Term: Copy + Eq + Hash;
    type Sort: Copy + Eq + Hash;
    type VarName: Copy + Eq + Hash;
    type Sym: Symbol;
}

/// A shallow, one-level view of a term — what the engine needs to match
/// triggers, collect ground terms, and rebuild instantiated bodies.
///
/// Parameterized by the lifetime-free [`Sig`] (not the host), with a borrow
/// `'a` only for the quantifier's bound-var slice. Crucially there is **no**
/// "fresh witness" or "model value" constructor: the engine never invents
/// domain elements, so an instantiation range can only ever be a real problem
/// term (invariant #1, see `DESIGN.md`).
pub enum TermView<'a, S: Sig> {
    /// A bound or free variable. Whether it is a *hole* (bound by the
    /// quantifier currently being instantiated) is decided by the caller
    /// against that quantifier's bound set, never by this view.
    Var { name: S::VarName },
    /// An application `f(args)` — uninterpreted (`f` an SMT function) OR a
    /// structured connective/operator (And/Eq/Add/Implies/…) presented under
    /// a reserved `sym`. The engine treats `f` opaquely (EUF-style) and reads
    /// the arguments via [`TermLang::children`] (an accessor, not an inline
    /// slice — host structured ops like `Eq(a,b)` have no contiguous args
    /// array). Nullary ⇒ a constant.
    App { sym: S::Sym },
    /// A first-order quantifier. `body` is the matrix; the `:pattern` trigger
    /// groups are fetched on demand via [`TermLang::patterns`] (an allocating
    /// accessor, called once per registration — avoids a `&[&[Term]]`
    /// borrow in the view).
    Quant {
        forall: bool,
        vars: &'a [(S::VarName, S::Sort)],
        body: S::Term,
    },
    /// A leaf the engine does not destructure (numeric/string/bool literal,
    /// or any node it should treat as an opaque ground atom).
    Opaque,
}

/// The structural role of a symbol in the recursion-**fuel** encoding
/// (Dafny/F★/Verus; design `FUEL_AWARE_COST_SCHEDULER.md` E2). The fuel argument
/// of a recursive-definition axiom is a unary Peano counter `succ(succ(…zero))`;
/// recognizing its two constructors lets the engine read the fuel-unfolding depth
/// (`succ`-nesting) of a term — the gradient the cost-scheduler discounts. A host
/// that does not use fuel returns `None` from [`TermLang::fuel_role`], degrading
/// the scheduler to a pure `weight + generation` cost (Z3 parity).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FuelRole {
    /// The `succ` fuel constructor (`succ(fuel)` — one more unfold available).
    Succ,
    /// The `zero` fuel constant (no fuel — the unfolding floor).
    Zero,
}

/// The host term language *behavior* the engine drives. Its identity types
/// live in [`Sig`] (lifetime-free); `Self` may borrow the host arena.
///
/// All methods are pure except the `mk_*` constructors and [`substitute`],
/// which intern into the host's (hash-consed) term store.
///
/// [`substitute`]: TermLang::substitute
pub trait TermLang {
    /// The lifetime-free identity signature (term/sort/name/sym types).
    type Sig: Sig;

    /// One-level structural view.
    fn view(&self, t: <Self::Sig as Sig>::Term) -> TermView<'_, Self::Sig>;

    /// The argument terms of an `App` node (empty for non-apps / constants).
    /// An accessor rather than an inline slice so hosts whose structured ops
    /// (`Eq(a,b)`, `Implies`, …) lack a contiguous args array can still serve
    /// them. Allocates a small `Vec`; the caching milestones memoize hot
    /// walks.
    fn children(&self, t: <Self::Sig as Sig>::Term) -> Vec<<Self::Sig as Sig>::Term>;

    /// The `:pattern` trigger groups of a quantifier term (each group is a
    /// multi-trigger tuple). Empty ⇒ trigger-free. Called once at
    /// registration. Returns `Vec` to sidestep nested-slice borrows.
    fn patterns(&self, quant: <Self::Sig as Sig>::Term) -> Vec<Vec<<Self::Sig as Sig>::Term>>;

    /// `true` iff `t` is an application of an UNINTERPRETED function symbol —
    /// a head the ground index buckets and the CCFV matcher can fire on.
    /// Structured/interpreted operators (`=`, `and`, `+`, `-`, `select`, …)
    /// must return `false`: a trigger headed by one never matches a ground
    /// congruence class, so inferring it would silently disable a quantifier.
    /// Consulted ONLY by trigger inference ([`crate::Engine`] registration);
    /// parsed `:pattern` groups are taken as-is.
    fn matchable_head(&self, t: <Self::Sig as Sig>::Term) -> bool;

    /// The sort of a term.
    fn sort_of(&self, t: <Self::Sig as Sig>::Term) -> <Self::Sig as Sig>::Sort;

    /// **The only substitution entry point.** Capture-free; the binding's
    /// range MUST be ground (the engine guarantees this before calling — it
    /// only ever binds to ground-index terms). Returns the instantiated body.
    fn substitute(
        &mut self,
        body: <Self::Sig as Sig>::Term,
        binding: &Binding<Self::Sig>,
    ) -> <Self::Sig as Sig>::Term;

    /// Build `a ⇒ b` (used to attach a quantifier's boolean literal as the
    /// guard of its instance lemma, so the SAT layer carries the polarity
    /// context automatically — invariant #3).
    fn mk_implies(
        &mut self,
        a: <Self::Sig as Sig>::Term,
        b: <Self::Sig as Sig>::Term,
    ) -> <Self::Sig as Sig>::Term;

    /// Build the disjunction `⋁ args` (used to discharge a BOUNDED existential
    /// soundly: `∃x̄∈D. φ` is exactly `⋁_{t̄∈D} φ[x̄↦t̄]`, a finite disjunction
    /// over the guard's literal domain). An empty `args` is `false`; a singleton
    /// is itself.
    fn mk_or(&mut self, args: Vec<<Self::Sig as Sig>::Term>) -> <Self::Sig as Sig>::Term;

    /// **Bounded-guard finite domains.** For each bound variable of `quant`,
    /// return `Some(literals)` when the quantifier body has the guarded shape
    /// `∀x̄. (guard ⇒ φ)` and `guard` pins that variable to a CONCRETE integer
    /// range `lo ≤ x ≤ hi` — `literals` is then exactly the ground terms
    /// `mk_int(lo), …, mk_int(hi)`. `None` for a variable with no such finite
    /// range (the engine then enumerates it over the full ground index, as
    /// before).
    ///
    /// Restricting enumeration to this finite set is SOUND and loses no
    /// completeness: for `x ∉ [lo,hi]` the guard is false so the instance is
    /// vacuous, and `∀x∈ℤ. (lo≤x≤hi ⇒ φ)` is exactly `⋀_{v=lo}^{hi} φ(v)`; a
    /// term instance `φ(t)` whose model value lands in `[lo,hi]` follows from the
    /// corresponding literal instance by congruence. It defuses the classic
    /// guarded-quantifier matching loop (a `∀m,n` over `Int` instantiated across
    /// every ground `Int` term — including the function's own applications —
    /// explodes; the guard says only finitely many tuples matter).
    ///
    /// Default: `Vec::new()` (no host support ⇒ no restriction anywhere). The
    /// returned vector, when non-empty, is aligned with the quantifier's bound
    /// variable list.
    fn bounded_var_domains(
        &mut self,
        _quant: <Self::Sig as Sig>::Term,
    ) -> Vec<Option<Vec<<Self::Sig as Sig>::Term>>> {
        Vec::new()
    }

    /// **E2 — the fuel-role accessor** (design `FUEL_AWARE_COST_SCHEDULER.md` §2.5).
    /// `Some(Succ)`/`Some(Zero)` iff `sym` is the recursion-fuel `succ`/`zero`
    /// constructor of the Dafny/F★/Verus fuel encoding; `None` for any other symbol
    /// (and for hosts with no fuel encoding). Read-only and pure. The fuel sort is
    /// otherwise opaque at this trait surface (`succ` is indistinguishable from any
    /// unary uninterpreted function), so the cost-scheduler's fuel gradient is
    /// unreadable without this hook; with it, the engine computes a term's
    /// fuel-unfolding depth as the `succ`-nesting of its fuel argument.
    ///
    /// Default: `None` everywhere ⇒ the scheduler degrades to `weight + generation`
    /// (Z3 parity) on any non-fuel host.
    fn fuel_role(&self, _sym: <Self::Sig as Sig>::Sym) -> Option<FuelRole> {
        None
    }

    /// **E3 — the content-key accessor** (design `FUEL_AWARE_COST_SCHEDULER.md` §2.5,
    /// R7 shuffle-invariance). A stable hash of `sym`'s CONTENT (its name/definition),
    /// NOT its interner/construction-order id. The scheduler's tie-break key
    /// (`FUEL_AWARE_COST_SCHEDULER.md` §5.2) must be a function of E-graph content so
    /// the release order — and hence the verdict — is invariant under an
    /// assertion-shuffle (Mariposa R7); the raw `Sym` id is order-variant and cannot
    /// serve. `None` ⇒ no stable content key available, and the engine falls back to
    /// the raw id (today's order-variant behaviour — acceptable only for
    /// non-shuffle-sensitive / toy hosts).
    fn content_key(&self, _sym: <Self::Sig as Sig>::Sym) -> Option<u64> {
        None
    }
}

/// A capture-free substitution: bound-variable name → ground replacement.
/// Keyed by the lifetime-free [`Sig`] so the engine can build one without
/// naming the host's borrow lifetime.
pub struct Binding<'a, S: Sig> {
    pub(crate) pairs: &'a [(S::VarName, S::Term)],
}

impl<'a, S: Sig> Binding<'a, S> {
    pub fn new(pairs: &'a [(S::VarName, S::Term)]) -> Self {
        Binding { pairs }
    }
    pub fn get(&self, name: S::VarName) -> Option<S::Term> {
        self.pairs.iter().find(|(n, _)| *n == name).map(|(_, t)| *t)
    }
    pub fn pairs(&self) -> &[(S::VarName, S::Term)] {
        self.pairs
    }
}
