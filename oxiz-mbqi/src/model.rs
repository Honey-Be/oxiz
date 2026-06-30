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

use crate::congruence::Congruence;
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
    /// `cong` is the SAME congruence oracle the engine solves with this round, so
    /// a recognizer can verify its completion against the LIVE ground congruence
    /// `E` (e.g. a definitional axiom `∀x̄.f(x̄)=rhs` is only soundly `Some(true)`
    /// once every ground `f`-point is already `≃` its definitional value — see the
    /// host impl). Generic over `C` (never a trait object), zero-cost when unused.
    ///
    /// Default `None` (engine then reports the quantifier unverified →
    /// `Unknown`, never a guess).
    fn eval_forall<C: Congruence<L::Sig>>(
        &self,
        _lang: &L,
        _cong: &C,
        _quant: <L::Sig as Sig>::Term,
    ) -> Option<bool> {
        None
    }

    /// **M3+ / P4 model-completion verdict-flip (design §3 `Mode::ModelCompl`).**
    /// The fallback the engine consults (only when [`crate::engine::Config::ccfv_model_compl`]
    /// is set) for a trigger-free universal that [`eval_forall`](Self::eval_forall)
    /// left unverified (`None`). The host lowers `¬ψ` to a (dis)equality DNF
    /// [`Constraint`](crate::ccfv::Constraint) and runs the brute-force CCFV
    /// [`solve`](crate::ccfv::solve) against the **total view** `E_TOT` it builds
    /// from `cong` (a [`TotalView`](crate::congruence::TotalView), whose
    /// `disequal = !equal` makes "distinct class reps are distinct" a genuine
    /// `≄`): if the conflict set is EMPTY, the completed model satisfies `∀x̄.ψ`,
    /// so the host returns `Some(true)` (a `Sat` contribution).
    ///
    /// SOUNDNESS (why this is gated, not on by default): a `Some(true)` here is a
    /// model witness, so it is only sound when (i) the conflict search is
    /// COMPLETE (a missed `σ` is a spurious `sat`, the cardinal sin), (ii) the
    /// host's accounting gate has confirmed `E_TOT` is a conservative extension of
    /// `E` (the completion defaults contradict no asserted ground fact, design
    /// §6), and (iii) the witness domain is inhabited. The contract is strictly
    /// one-sided: any conflict found, undecidable lowering, or unmet gate ⇒
    /// `None` (the engine then yields the sound `Unknown`) — this method NEVER
    /// returns `Some(false)`, because "found a conflict over the *sampled* domain"
    /// is not "the axiom is violated in every model" (a different completion might
    /// satisfy it). Default `None` (no host completion).
    ///
    /// `cong` is the SAME congruence oracle the engine solves with this round
    /// (e.g. the host's live EUF view), carrying the by-sort witness index
    /// ([`Congruence::class_reps_of_sort`]) the brute-force enumeration ranges
    /// over. Generic over `C` (never used as a trait object), so the method stays
    /// zero-cost when the flag is clear.
    fn model_completion<C: Congruence<L::Sig>>(
        &self,
        _lang: &L,
        _cong: &C,
        _quant: <L::Sig as Sig>::Term,
    ) -> Option<bool> {
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
