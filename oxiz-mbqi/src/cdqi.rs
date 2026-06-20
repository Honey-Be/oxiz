//! Conflict-driven quantifier instantiation (Reynolds, Tinelli, de Moura,
//! FMCAD'14), re-derived inside the soundness invariant — now expressed
//! **through the CCFV congruence oracle** (design `CCFV_UNIFIED_INSTANTIATION.md`
//! §3, Phase **P3**).
//!
//! Among the ground-index tuples for a quantifier, find the ones whose
//! instantiated body is **false** under the current model — *conflicting*
//! instances that refute the candidate model. It fabricates nothing (candidates
//! are ground-index terms), so each lemma is just an ordinary valid instance; it
//! only differs in being chosen because it prunes. The engine emits them FIRST
//! (before e-match/enumerate), since a conflicting instance is the strongest,
//! most relevant lemma.
//!
//! **P3 — CCFV congruence in two ways, both verdict-preserving:**
//!  1. *Congruence-deduped candidate domains.* The per-sort domain is collapsed
//!     by congruence class via the [`Congruence`] oracle (`rep`): syntactically
//!     distinct but congruent ground terms evaluate IDENTICALLY under the
//!     congruence-consistent model, so one representative per class is enough —
//!     fewer redundant body evaluations (the design's (a) congruence-aware
//!     lookup). The kept representative is always an INDEX term (the first of its
//!     class encountered), never a fresh `rep(t)` node, so `instantiate`'s
//!     ground-membership check can never reject it. With the trivial `NoCong`
//!     (the non-congruence path) `rep` is the identity, so the domain — and hence
//!     the behaviour — is exactly the old odometer.
//!  2. *All conflicts, not the first.* The CCFV formulation yields **every**
//!     conflicting `σ` (`C = ¬ψ`), replacing the odometer's finds-one. The engine
//!     emits them together; each is an independent valid instance, so the verdict
//!     is unchanged (more conflict lemmas only converge faster).
//!
//! Soundness is independent of the choices: a conflicting tuple is still a tuple
//! of ground terms, so each emitted `Q ⇒ φ[x̄↦t̄]` is valid. (If the model
//! misjudged a body, we have merely added a redundant valid lemma — never a
//! spurious refutation.)

use crate::congruence::Congruence;
use crate::ground::GroundIndex;
use crate::instantiate::{InstResult, Quant, instantiate};
use crate::model::ModelEval;
use crate::term::{Sig, TermLang};
use rustc_hash::FxHashSet;

/// Collapse `terms` by congruence class: keep the FIRST term of each class (an
/// index term — never a synthesised `rep` node), so the result is a subset of
/// `terms` with one member per `cong`-class. With `NoCong` (`rep` = identity)
/// this is the input unchanged (the index already holds no duplicates).
fn dedup_by_class<S, C>(cong: &C, terms: &[S::Term]) -> Vec<S::Term>
where
    S: Sig,
    C: Congruence<S>,
{
    let mut seen: FxHashSet<S::Term> = FxHashSet::default();
    let mut out = Vec::new();
    for &t in terms {
        if seen.insert(cong.rep(t)) {
            out.push(t);
        }
    }
    out
}

/// Search for the conflicting instances of `quant` under the current model.
/// Returns every conflicting binding `x̄↦t̄` found within the `max_tuples`
/// evaluation budget; the engine emits them through the same sound `emit` path
/// as every other strategy (so dedup/guard/indexing stay uniform). Empty when
/// there is no real candidate of some sort, or no tuple falsifies the body.
pub fn find_conflicts<S, L, M, C>(
    lang: &mut L,
    ground: &GroundIndex<S>,
    model: &M,
    cong: &C,
    quant: &Quant<S>,
    max_tuples: usize,
) -> Vec<Vec<(S::VarName, S::Term)>>
where
    S: Sig,
    L: TermLang<Sig = S>,
    M: ModelEval<L>,
    C: Congruence<S>,
{
    let sorts: Vec<S::Sort> = quant.vars.iter().map(|(_, s)| *s).collect();
    // Congruence-deduped per-sort candidate domains (one index term per class).
    let domains: Vec<Vec<S::Term>> = sorts
        .iter()
        .map(|s| dedup_by_class(cong, ground.of_sort(*s)))
        .collect();
    if domains.iter().any(|d| d.is_empty()) {
        return Vec::new(); // no real candidates → no conflict to find
    }
    let k = domains.len();
    let mut idx = vec![0usize; k];
    let mut tried = 0usize;
    let mut conflicts = Vec::new();
    loop {
        if tried >= max_tuples {
            break;
        }
        tried += 1;
        let tuple: Vec<S::Term> = (0..k).map(|i| domains[i][idx[i]]).collect();
        let binding: Vec<(S::VarName, S::Term)> = quant
            .vars
            .iter()
            .map(|(n, _)| *n)
            .zip(tuple.iter().copied())
            .collect();
        // Confirm the binding is sound (range ground) before evaluating, then
        // ask the model whether the bare instantiated body is false.
        if let InstResult::Lemma(_) = instantiate(lang, ground, quant, &binding) {
            let bare = {
                let b = crate::term::Binding::<S>::new(&binding);
                lang.substitute(quant.body, &b)
            };
            if model.eval_bool(lang, bare) == Some(false) {
                conflicts.push(binding);
            }
        }
        // odometer
        let mut carry = true;
        for i in 0..k {
            if carry {
                idx[i] += 1;
                if idx[i] >= domains[i].len() {
                    idx[i] = 0;
                } else {
                    carry = false;
                }
            }
        }
        if carry {
            break; // exhausted all tuples
        }
    }
    conflicts
}
