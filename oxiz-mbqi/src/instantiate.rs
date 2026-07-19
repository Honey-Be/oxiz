//! Sound, guarded instantiation — the central enforcement point for the
//! soundness invariant (see `DESIGN.md`).
//!
//! Given a registered quantifier and a substitution, produce the lemma
//! `Q ⇒ φ[x̄ ↦ t̄]` where `Q` is the boolean term standing for the quantifier
//! node (so the SAT layer carries the polarity context: the instance only
//! fires when the quantifier itself is asserted — invariant #3).
//!
//! Three conditions are checked HERE, centrally, rather than trusted at each
//! call site (the old OxiZ code trusted them and was wrong in four places):
//!  1. every bound variable is assigned;
//!  2. every replacement is a GROUND term registered in the ground index
//!     (no fabricated witness, no foreign bound variable — invariant #1);
//!  3. capture-freedom is the host `substitute`'s contract.

use crate::ground::GroundIndex;
use crate::term::{Binding, Sig, TermLang};

/// A registered quantifier the engine instantiates. Keyed by the lifetime-free
/// [`Sig`] so it lives on the engine across rounds.
pub struct Quant<S: Sig> {
    /// The quantifier term itself (used as the guard literal `Q`).
    pub term: S::Term,
    /// Bound variables and their sorts.
    pub vars: Vec<(S::VarName, S::Sort)>,
    /// `:pattern` trigger groups (flattened); empty ⇒ trigger-free.
    pub triggers: Vec<Vec<S::Term>>,
    /// `triggers` were INFERRED from the body (no parsed `:pattern`). An
    /// inferred trigger drives e-matching exactly like a parsed one, but it is
    /// NOT a user contract: at saturation the quantifier must still be
    /// model-verified (`eval_forall`) like a trigger-free one — trigger
    /// semantics may only justify `Sat` for patterns the AUTHOR supplied.
    pub inferred: bool,
    /// Trigger inference already ran (it runs LAZILY on the quantifier's
    /// first active round — it needs `bounded_var_domains`, which requires
    /// `&mut` host access registration does not have; and a FULLY-bounded
    /// quantifier must keep its complete finite-box enumeration instead).
    pub inference_tried: bool,
    /// E1 ever-fired gate (#425): the quantifier's trigger e-match has yielded
    /// at least one binding at some point. A parsed `:pattern` justifies the
    /// trigger-semantics saturation exemption ONLY once it has actually fired:
    /// a dead-symbol / ill-arity / never-matching pattern (not statically
    /// decidable behind the `TermLang` view) otherwise silences its quantifier
    /// forever and turns `Saturated` into a spurious `Sat`. Set at the
    /// `ematch_all` call site (any non-empty binding set, even from an aborted
    /// e-match); CDQI conflicts do NOT set it (they bypass the trigger, so
    /// they say nothing about the pattern's matchability).
    pub matched: bool,
    /// E1 additive-patterns mode (#425): inferred trigger groups were APPENDED
    /// to this quantifier's parsed ones (`Engine::augment_parsed_triggers`).
    /// Set unconditionally once augmentation was attempted (so the additive
    /// outer loop terminates), and — like `inferred` — it removes the
    /// trigger-semantics saturation exemption: the author's `:pattern`
    /// contract no longer describes the full trigger set, so the quantifier
    /// must be model-verified at saturation.
    pub augmented: bool,
    /// The matrix.
    pub body: S::Term,
    /// Universal? (Existentials are skolemized by the host before reaching us.)
    pub universal: bool,
    /// Per-bound-variable FINITE enumeration domain from a bounded-int guard
    /// (`TermLang::bounded_var_domains`), computed lazily on first enumeration.
    /// `None` = not yet computed; once `Some`, each entry is `Some(literals)`
    /// (restrict to that finite set) or `None` (enumerate over the ground index).
    pub var_domains: Option<Vec<Option<Vec<S::Term>>>>,
}

/// Outcome of attempting one instantiation.
pub enum InstResult<T> {
    /// A sound guarded lemma `Q ⇒ φ[x̄↦t̄]`.
    Lemma(T),
    /// The substitution was rejected (a replacement was not ground / not in
    /// the index). This must never happen if candidates come only from the
    /// ground index; it is a defensive backstop, counted in stats.
    Rejected,
}

/// Build the guarded instance lemma for `quant` under `binding`, enforcing
/// the soundness conditions. `binding` maps each bound var to a candidate.
pub fn instantiate<S, L>(
    lang: &mut L,
    ground: &GroundIndex<S>,
    quant: &Quant<S>,
    binding: &[(S::VarName, S::Term)],
) -> InstResult<S::Term>
where
    S: Sig,
    L: TermLang<Sig = S>,
{
    // (1) every bound variable assigned exactly once.
    if binding.len() != quant.vars.len() {
        return InstResult::Rejected;
    }
    for (name, _) in &quant.vars {
        if !binding.iter().any(|(n, _)| n == name) {
            return InstResult::Rejected;
        }
    }
    // (2) every replacement is a registered ground term. This is the single
    // structural check that kills the whole spurious-`unsat` bug class:
    // a fabricated witness, a bound variable, or a sibling quantifier's
    // variable is, by construction, NOT in the ground index.
    for (_, t) in binding {
        if !ground.contains(*t) {
            return InstResult::Rejected;
        }
    }
    // (3) capture-free substitution (host contract).
    let b = Binding::<S>::new(binding);
    let instance = lang.substitute(quant.body, &b);
    // Guard with the quantifier literal so the instance inherits the
    // quantifier's polarity context (e.g. a `∀` under `(=> g …)` only fires
    // when `g` holds, because `Q` does).
    let lemma = lang.mk_implies(quant.term, instance);
    InstResult::Lemma(lemma)
}
