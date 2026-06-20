//! The **congruence oracle** — the one new capability CCFV needs behind the
//! [`Sig`]/[`TermLang`](crate::term::TermLang) boundary (design
//! `CCFV_UNIFIED_INSTANTIATION.md` §5/§10, Phase **P0**).
//!
//! A read-only view of the ground E-graph's congruence `E`: the representative
//! of a class, congruence of two ground terms, class enumeration, and the
//! `E^cc` application index (every ground `f(t̄)` grouped by argument class).
//! These are exactly the queries CCFV's E-ground (dis)unification core makes to
//! match *modulo congruence* — the inference a purely syntactic matcher cannot
//! make. (CCFV with the trivial [`NoCong`] degenerates back to syntactic
//! matching, which is how the engine's flag-off path stays byte-identical.)
//!
//! The host implements it by delegating to its EUF solver (the `E^cc` index is
//! already maintained there). **Pure addition in P0**: this trait has no
//! consumer yet — CCFV (Phase P1+) is the sole future caller — so adding it
//! changes no behaviour. The soundness firewall is untouched: a congruence
//! oracle only *reads* the ground congruence; it produces no verdict and binds
//! no variable (that stays the engine's `instantiate`/`emit` gate).
use crate::term::Sig;

/// One ground application `f(t̄)` as the congruence sees it: a representative
/// ground term per argument position plus a representative of the result class.
/// Re-exports the host EUF's `E^cc` signature-class entry into the engine's
/// term space (`S::Term`), dropping the EUF-internal node indices CCFV does not
/// need.
pub struct FuncApp<S: Sig> {
    /// A representative ground term of each argument's congruence class, in order.
    /// `arg_reps.len()` is the application's arity.
    pub arg_reps: Vec<S::Term>,
    /// A representative ground term of the application's result class.
    pub result: S::Term,
}

/// A read-only congruence oracle over the ground E-graph `E`.
///
/// Every method takes `&self`: the oracle never mutates the congruence (the EUF
/// solver maintains it; CCFV only queries). A host implements it over its EUF —
/// `find` / `are_equal` / `class_members` / `function_application_entries` — so
/// CCFV gets congruence-aware candidate lookup without a second congruence
/// engine.
pub trait Congruence<S: Sig> {
    /// Canonical representative ground term of `t`'s congruence class (a member
    /// term, not a fresh internal node). Returns `t` itself when `t` is not yet
    /// in the congruence.
    fn rep(&self, t: S::Term) -> S::Term;

    /// `E ⊨ a ≃ b` — are the two ground terms congruent in `E`?
    fn equal(&self, a: S::Term, b: S::Term) -> bool;

    /// The ground terms in `t`'s congruence class (`[t]` when `t` is not yet in
    /// the congruence). One representative per congruent node.
    fn class(&self, t: S::Term) -> Vec<S::Term>;

    /// The `E^cc` index for the head of `app`: every ground application in `E`
    /// sharing `app`'s function symbol, each as a [`FuncApp`]. **Keyed by a
    /// witness application term** (`app = f(t̄)`), not a bare symbol id, so the
    /// implementation stays entirely in term space — no host-symbol ↔ EUF-func-id
    /// bridge is needed at P0 (that mapping is a P2 concern when trigger
    /// e-matching is re-expressed through CCFV). Empty when `app` is not an
    /// interned application.
    fn apps_like(&self, app: S::Term) -> Vec<FuncApp<S>>;

    /// Total-model default value `ξ_f(args)` for an under-specified application —
    /// CCFV's MBQI / model-completion mode (design §3). `None` ⇒ fall back to the
    /// real ground congruence. Default `None`; only a model-completing host
    /// overrides it. (Soundness-gated by the host's accounting gate before any
    /// completion is trusted — see design §6.)
    fn default_value(&self, _f: S::Sym, _args: &[S::Term]) -> Option<S::Term> {
        None
    }

    /// Are `a` and `b` **provably disequal** in `E` (`E ⊨ a ≄ b`)? A sound,
    /// conservative test (`false` when undetermined) — the disequality dual of
    /// [`equal`](Self::equal), needed by the complete E-ground *dis*unification
    /// core (design §2.3 `R_*` rules). NOTE: for the model-completion verdict-flip
    /// the decision primitive is the *total* view's "distinct class reps are
    /// distinct by construction" (via [`class_reps_of_sort`](Self::class_reps_of_sort)),
    /// NOT this asserted-disequality query — `disequal` is a building block.
    /// Default `false`.
    fn disequal(&self, _a: S::Term, _b: S::Term) -> bool {
        false
    }

    /// Every ground term of sort `s` known to `E` — the domain the complete
    /// solver enumerates output/disequality witnesses over (maps to the engine's
    /// `GroundIndex::of_sort`, threaded in by the host). Default empty.
    fn ground_of_sort(&self, _s: S::Sort) -> Vec<S::Term> {
        Vec::new()
    }

    /// One representative ground term per congruence **class** of sort `s` — the
    /// disjoint witness set for the disequality / `R_GEN` enumeration (a dedup of
    /// [`ground_of_sort`](Self::ground_of_sort) by [`rep`](Self::rep)). On a total
    /// view its members are pairwise distinct by construction, which is what makes
    /// `!equal` over them a genuine `≄`. Default empty.
    fn class_reps_of_sort(&self, _s: S::Sort) -> Vec<S::Term> {
        Vec::new()
    }
}

/// The trivial (empty) congruence: every term is its own class, equality is
/// syntactic identity. Used as the placeholder oracle on the non-CCFV path
/// (`Engine::round_with`), where the congruence is never queried — so it costs
/// nothing and keeps the default behaviour byte-identical. Matching through CCFV
/// with `NoCong` is exactly syntactic matching.
pub struct NoCong;

impl<S: Sig> Congruence<S> for NoCong {
    fn rep(&self, t: S::Term) -> S::Term {
        t
    }
    fn equal(&self, a: S::Term, b: S::Term) -> bool {
        a == b
    }
    fn class(&self, t: S::Term) -> Vec<S::Term> {
        vec![t]
    }
    fn apps_like(&self, _app: S::Term) -> Vec<FuncApp<S>> {
        Vec::new()
    }
}

/// Which of the three CCFV instantiation strategies a search is running — the
/// design's §3 parameterization (`CCFV_UNIFIED_INSTANTIATION.md`). All three are
/// `ccfv::solve(cong, C)` over the SAME unification core, differing only in the
/// constraint `C` and the congruence *view*:
///
/// | mode         | constraint `C`        | congruence view |
/// |--------------|-----------------------|-----------------|
/// | `Trigger`    | `⋀ pattern ≃ out-var` | [`ground`](Mode::view) — the real `E` |
/// | `Conflict`   | `¬ψ` (CDQI)           | `ground` — the real `E` |
/// | `ModelCompl` | `¬ψ` (MBQI)           | [`total`](Mode::view) — `E_TOT` |
///
/// `Trigger` is the e-matcher ([`crate::ccfv::match_trigger`]); `Conflict` is
/// CDQI ([`crate::cdqi::find_conflicts`], landed). `ModelCompl` solves `¬ψ`
/// against the **total** view [`TotalView`] (`E_TOT`): if CCFV finds *no*
/// conflict, the completed model satisfies `∀x̄.ψ` → the host may answer
/// `Some(true)` from `eval_forall`. That verdict-producing flip is **gated**
/// (design §6, [`TotalView`]) and is NOT yet live — it needs the complete
/// disequality CCFV (`R_VAR`/`R_FAPP`/`R_GEN`) so "no conflict" is sound, plus
/// the verus pre-verification the project's `[선검증→구현→후검증]` discipline
/// requires. The structure lands here ready for that step.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Mode {
    /// E-matching: ground the `:pattern` terms in the real congruence `E`.
    Trigger,
    /// CDQI: every `σ` with `E ⊨ ¬ψσ` — a conflicting ground instance.
    Conflict,
    /// MBQI / model-completion: `¬ψ` against the total view `E_TOT`.
    ModelCompl,
}

impl Mode {
    /// Whether this mode solves against the **total** model view `E_TOT`
    /// (default-extended congruence) rather than the real ground congruence `E`.
    /// Only `ModelCompl` does; `Trigger`/`Conflict` use the real `E`.
    #[must_use]
    pub fn total_view(self) -> bool {
        matches!(self, Mode::ModelCompl)
    }
}

/// The **total-model view** `E_TOT` (design §3/§6): the real ground congruence
/// `E` (the wrapped `base`) extended with default values `ξ_f` for
/// under-specified applications, for CCFV's model-completion (`Mode::ModelCompl`)
/// mode. `rep`/`equal`/`class`/`apps_like` are exactly the base congruence — a
/// completion never merges or splits real classes — so the ONLY added capability
/// is `default_value`, supplied by the wrapped closure `xi`.
///
/// SOUNDNESS (the reason this is structure-only until the gated flip): `E_TOT`
/// may be trusted as a model witness — i.e. "CCFV finds no conflict in `E_TOT`"
/// concluded as `∀x̄.ψ` holding — ONLY when it is a *conservative extension* of
/// `E` (the defaults contradict no asserted ground fact), which the host's
/// accounting gate (`global_occ[f] == body_occ + |ground_apps[f]|`, design §6)
/// must confirm first, AND when the conflict search is *complete* (the
/// disequality rules, not yet implemented). The wrapper itself makes no verdict;
/// it only routes `ξ_f` to CCFV, so adding it changes nothing on its own.
pub struct TotalView<'a, S: Sig, C: Congruence<S>, F>
where
    F: Fn(S::Sym, &[S::Term]) -> Option<S::Term>,
{
    base: &'a C,
    xi: F,
    _marker: core::marker::PhantomData<S>,
}

impl<'a, S: Sig, C: Congruence<S>, F> TotalView<'a, S, C, F>
where
    F: Fn(S::Sym, &[S::Term]) -> Option<S::Term>,
{
    /// Wrap a base congruence `E` with a default-value function `xi` to form the
    /// total view `E_TOT`. `xi(f, args)` returns the completion's value `ξ_f` for
    /// an under-specified `f`-application, or `None` to defer to the real `E`.
    pub fn new(base: &'a C, xi: F) -> Self {
        TotalView {
            base,
            xi,
            _marker: core::marker::PhantomData,
        }
    }
}

impl<S: Sig, C: Congruence<S>, F> Congruence<S> for TotalView<'_, S, C, F>
where
    F: Fn(S::Sym, &[S::Term]) -> Option<S::Term>,
{
    fn rep(&self, t: S::Term) -> S::Term {
        self.base.rep(t)
    }
    fn equal(&self, a: S::Term, b: S::Term) -> bool {
        self.base.equal(a, b)
    }
    fn class(&self, t: S::Term) -> Vec<S::Term> {
        self.base.class(t)
    }
    fn apps_like(&self, app: S::Term) -> Vec<FuncApp<S>> {
        self.base.apps_like(app)
    }
    fn default_value(&self, f: S::Sym, args: &[S::Term]) -> Option<S::Term> {
        (self.xi)(f, args)
    }
    /// On the TOTAL view, two ground terms are disequal iff they fall in DIFFERENT
    /// base classes — `E_TOT`'s all-pairs separation among distinct class reps
    /// makes "not congruent" a genuine `≄`. This is precisely what lets the
    /// complete `solve`'s disequality gate (`cong.disequal`) be sound for the
    /// model-completion conflict search (whereas the bare ground congruence's
    /// `disequal` is the weaker asserted-only query, unsound for the flip).
    fn disequal(&self, a: S::Term, b: S::Term) -> bool {
        !self.base.equal(a, b)
    }
    /// The witness enumeration domain is unchanged by the completion — `E_TOT`
    /// adds default *values*, not new classes — so delegate to the base.
    fn ground_of_sort(&self, s: S::Sort) -> Vec<S::Term> {
        self.base.ground_of_sort(s)
    }
    fn class_reps_of_sort(&self, s: S::Sort) -> Vec<S::Term> {
        self.base.class_reps_of_sort(s)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::term::Sig;

    // A minimal `Sig` for unit-testing the congruence wrappers in isolation
    // (Term/Sort/VarName/Sym are all `u32` — the trait only needs Copy+Eq+Hash).
    #[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
    struct TestSig;
    impl Sig for TestSig {
        type Term = u32;
        type Sort = u32;
        type VarName = u32;
        type Sym = u32;
    }

    #[test]
    fn nocong_is_syntactic_identity() {
        let c = NoCong;
        assert!(<NoCong as Congruence<TestSig>>::equal(&c, 7, 7));
        assert!(!<NoCong as Congruence<TestSig>>::equal(&c, 7, 8));
        assert_eq!(<NoCong as Congruence<TestSig>>::rep(&c, 7), 7);
        assert_eq!(<NoCong as Congruence<TestSig>>::class(&c, 7), vec![7]);
        assert_eq!(<NoCong as Congruence<TestSig>>::default_value(&c, 1, &[2]), None);
    }

    #[test]
    fn total_view_delegates_congruence_and_adds_defaults() {
        // E_TOT over the trivial base: rep/equal/class are the base (NoCong),
        // but default_value returns ξ_f from the wrapped closure — the one new
        // capability the model-completion mode needs.
        let base = NoCong;
        let view: TotalView<TestSig, _, _> =
            TotalView::new(&base, |f: u32, args: &[u32]| if f == 10 { Some(args[0] + 100) } else { None });

        // Congruence delegated to the base (no class merges/splits).
        assert!(view.equal(5, 5));
        assert!(!view.equal(5, 6));
        assert_eq!(view.rep(5), 5);
        assert_eq!(view.class(5), vec![5]);

        // The completion value ξ_f is supplied for the covered symbol only.
        assert_eq!(view.default_value(10, &[7]), Some(107));
        assert_eq!(view.default_value(11, &[7]), None);
    }

    #[test]
    fn mode_total_view_only_for_model_completion() {
        assert!(!Mode::Trigger.total_view());
        assert!(!Mode::Conflict.total_view());
        assert!(Mode::ModelCompl.total_view());
    }
}
