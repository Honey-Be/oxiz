//! Conflict-driven quantifier instantiation (Reynolds, Tinelli, de Moura,
//! FMCAD'14), re-derived inside the soundness invariant.
//!
//! Among the ground-index tuples for a quantifier, find one whose
//! instantiated body is **false** under the current model — a *conflicting*
//! instance that refutes the candidate model in one step. It fabricates
//! nothing (candidates are ground-index terms), so its lemma is just an
//! ordinary valid instance; it only differs in being chosen because it
//! prunes. The engine emits it FIRST (before e-match/enumerate), since a
//! conflicting instance is the strongest, most relevant lemma.
//!
//! Soundness is independent of the choice: a conflicting tuple is still a
//! tuple of ground terms, so the emitted `Q ⇒ φ[x̄↦t̄]` is valid. (If the
//! model misjudged the body, we have merely added a redundant valid lemma —
//! never a spurious refutation.)

use crate::ground::GroundIndex;
use crate::instantiate::{InstResult, Quant, instantiate};
use crate::model::ModelEval;
use crate::term::TermLang;

/// Search for one conflicting instance of `quant`. On success returns the
/// conflicting binding `x̄↦t̄`; the engine emits it through the same sound
/// `emit` path as every other strategy (so dedup/guard/indexing are uniform).
/// Bounded by `max_tuples` evaluations.
pub fn find_conflict<L: TermLang, M: ModelEval<L>>(
    lang: &mut L,
    ground: &GroundIndex<L>,
    model: &M,
    quant: &Quant<L>,
    max_tuples: usize,
) -> Option<Vec<(L::VarName, L::Term)>> {
    let sorts: Vec<L::Sort> = quant.vars.iter().map(|(_, s)| *s).collect();
    let domains: Vec<Vec<L::Term>> = sorts.iter().map(|s| ground.of_sort(*s).to_vec()).collect();
    if domains.iter().any(|d| d.is_empty()) {
        return None; // no real candidates → no conflict to find
    }
    let k = domains.len();
    let mut idx = vec![0usize; k];
    let mut tried = 0usize;
    loop {
        if tried >= max_tuples {
            return None;
        }
        tried += 1;
        let tuple: Vec<L::Term> = (0..k).map(|i| domains[i][idx[i]]).collect();
        let binding: Vec<(L::VarName, L::Term)> = quant
            .vars
            .iter()
            .map(|(n, _)| *n)
            .zip(tuple.iter().copied())
            .collect();
        // Confirm the binding is sound (range ground) before evaluating, then
        // ask the model whether the bare instantiated body is false.
        if let InstResult::Lemma(_) = instantiate(lang, ground, quant, &binding) {
            let bare = {
                let b = crate::term::Binding::<L>::new(&binding);
                lang.substitute(quant.body, &b)
            };
            if model.eval_bool(lang, bare) == Some(false) {
                return Some(binding);
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
            return None; // exhausted all tuples, no conflict
        }
    }
}
