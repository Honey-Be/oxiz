//! Model-evaluation oracle.
//!
//! CDQI (M2) and model-based verification (M3) need to ask the host "is this
//! ground boolean term true/false under your current candidate model?". The
//! host (which owns the SAT assignment + theory state) answers; the engine
//! never builds a model itself. `None` means "the model does not determine
//! it" (a symbolic residual) — the engine treats that conservatively (it is
//! never grounds for a refutation).
//!
//! The oracle is parameterized by the borrowing host `L: TermLang` (it needs
//! `view`/`children` to fold connectives), and references the host's term type
//! through the lifetime-free signature as `<L::Sig as Sig>::Term`.

use crate::term::{Sig, TermLang};

pub trait ModelEval<L: TermLang> {
    /// Evaluate a GROUND boolean term under the current model.
    /// `Some(true/false)` if determined, `None` if symbolic/unknown.
    fn eval_bool(&self, lang: &L, t: <L::Sig as Sig>::Term) -> Option<bool>;

    /// **M3 model-based verification.** Does the model satisfy this
    /// universally-quantified term? `Some(true)` = the host checked it over
    /// ITS completed model (universe + function interpretations) and it
    /// holds; `Some(false)` = it is violated; `None` = the host cannot tell.
    ///
    /// Crucially, the host evaluates internally — any synthetic universe
    /// witnesses it uses to do so **never cross into the engine**, so they
    /// can never be turned into hard lemmas. That firewall is exactly what
    /// the old OxiZ D bug lacked (it enumerated the body over fabricated
    /// witnesses and added the grid as clauses). Here a trigger-free
    /// definitional axiom is confirmed `Some(true)` and contributes to a
    /// `Sat` verdict with zero fabricated lemmas.
    ///
    /// Default `None` (engine then reports the quantifier unverified →
    /// `Unknown`, never a guess).
    fn eval_forall(&self, _lang: &L, _quant: <L::Sig as Sig>::Term) -> Option<bool> {
        None
    }

    /// **M3.5 relevance gating.** Is the quantifier's boolean literal `Q`
    /// assigned **true** in the current model? A `∀` under `(=> g ψ)` with
    /// `g` false has `Q` false, so it constrains nothing — skip it entirely
    /// (instantiation AND verification). This both slashes work on
    /// guard-heavy preludes (verus fuel) and is the precise way to *respect
    /// the guard* the old OxiZ fuel bug dropped.
    ///
    /// Sound: skipping `Q=false` cannot lose a refutation — the instance
    /// `Q ⇒ φ[..]` is vacuously true, and an inactive quantifier is trivially
    /// satisfied. If the model later flips `Q` true (after lemmas re-solve),
    /// the next round instantiates it.
    ///
    /// Default `true` (conservative: if the host can't say, treat as active —
    /// never skip something that might constrain).
    fn is_active(&self, _lang: &L, _quant: <L::Sig as Sig>::Term) -> bool {
        true
    }
}

/// The empty model — determines nothing. With it, CDQI finds no conflict and
/// model-based verification is inconclusive, so the engine falls back to
/// e-matching / enumeration. Used for pure-syntactic rounds and in tests.
pub struct NoModel;

impl<L: TermLang> ModelEval<L> for NoModel {
    fn eval_bool(&self, _lang: &L, _t: <L::Sig as Sig>::Term) -> Option<bool> {
        None
    }
}
