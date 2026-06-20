//! The **congruence oracle** — the one new capability CCFV needs behind the
//! [`Sig`]/[`TermLang`](crate::term::TermLang) boundary (design
//! `CCFV_UNIFIED_INSTANTIATION.md` §5/§10, Phase **P0**).
//!
//! A read-only view of the ground E-graph's congruence `E`: the representative
//! of a class, congruence of two ground terms, class enumeration, and the
//! `E^cc` application index (every ground `f(t̄)` grouped by argument class).
//! These are exactly the queries CCFV's E-ground (dis)unification core makes to
//! match *modulo congruence* — the inference the current syntactic matcher
//! (`trigger::match_term`) cannot make.
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
