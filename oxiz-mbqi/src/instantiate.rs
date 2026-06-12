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
use crate::term::{Binding, TermLang};

/// A registered quantifier the engine instantiates.
pub struct Quant<L: TermLang> {
    /// The quantifier term itself (used as the guard literal `Q`).
    pub term: L::Term,
    /// Bound variables and their sorts.
    pub vars: Vec<(L::VarName, L::Sort)>,
    /// `:pattern` trigger groups (flattened); empty ⇒ trigger-free.
    pub triggers: Vec<Vec<L::Term>>,
    /// The matrix.
    pub body: L::Term,
    /// Universal? (Existentials are skolemized by the host before reaching us.)
    pub universal: bool,
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
pub fn instantiate<L: TermLang>(
    lang: &mut L,
    ground: &GroundIndex<L>,
    quant: &Quant<L>,
    binding: &[(L::VarName, L::Term)],
) -> InstResult<L::Term> {
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
    let b = Binding::<L>::new(binding);
    let instance = lang.substitute(quant.body, &b);
    // Guard with the quantifier literal so the instance inherits the
    // quantifier's polarity context (e.g. a `∀` under `(=> g …)` only fires
    // when `g` holds, because `Q` does).
    let lemma = lang.mk_implies(quant.term, instance);
    InstResult::Lemma(lemma)
}
