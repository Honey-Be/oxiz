//! The instantiation round loop.
//!
//! The engine's contract — and the whole point of the rewrite — is that it
//! **never returns `Unsat`**. It only ever hands the host new, sound,
//! guarded lemmas (or reports saturation / budget). The host adds the lemmas
//! to its ground SAT+theory core and re-solves; any `Unsat` is the core's,
//! hence real. See `DESIGN.md`.
//!
//! Per quantifier, per round, the strategy order is **CDQI → e-matching →
//! enumeration** (the cvc5 order). All three funnel through the single sound
//! `emit` path (dedup + guard + index), so soundness is enforced in one
//! place regardless of which strategy proposed the tuple.
//!
//! The engine is keyed by the lifetime-free [`Sig`] (`Engine<S>`), so it lives
//! on the solver across `check()` rounds; each round passes a freshly-borrowed
//! host `&mut L` (`L: TermLang<Sig = S>`).

use crate::cdqi;
use crate::ground::GroundIndex;
use crate::instantiate::{InstResult, Quant, instantiate};
use crate::model::{ModelEval, NoModel};
use crate::term::{Sig, TermLang, TermView};
use crate::trigger;
use rustc_hash::FxHashSet;

/// What a round produced. Note the absence of an `Unsat` variant — by design.
pub enum Verdict<T> {
    /// New sound lemmas to assert before the next solve.
    NewLemmas(Vec<T>),
    /// No new instances AND every quantifier is satisfied by the model:
    /// triggered ones are e-match-saturated (standard trigger semantics) and
    /// every trigger-free one was model-verified `Some(true)` (M3). If the
    /// ground core is still SAT here, the host may report **`Sat`**.
    Saturated,
    /// No new instances, but at least one trigger-free quantifier could NOT
    /// be model-verified (`None`, or violated with no real-ground witness to
    /// refute it). The host must report **`Unknown`** — never a guessed
    /// `Sat`, never a fabricated `Unsat`.
    Inconclusive,
    /// The per-check instantiation budget was hit → host reports `Unknown`.
    BudgetExhausted,
}

pub struct Config {
    pub max_instances: usize,
    pub max_tuples_per_quant: usize,
}

impl Default for Config {
    fn default() -> Self {
        Config {
            max_instances: 100_000,
            max_tuples_per_quant: 4_096,
        }
    }
}

pub struct Engine<S: Sig> {
    quants: Vec<Quant<S>>,
    ground: GroundIndex<S>,
    seen: FxHashSet<(usize, Vec<S::Term>)>,
    /// Per-quantifier frontier watermark: ground-index insertion indices below
    /// this were already scanned for this quantifier (mod-time e-matching).
    scanned: Vec<u32>,
    emitted: usize,
    rejected: usize,
    cfg: Config,
}

impl<S: Sig> Engine<S> {
    pub fn new(cfg: Config) -> Self {
        Engine {
            quants: Vec::new(),
            ground: GroundIndex::new(),
            seen: FxHashSet::default(),
            scanned: Vec::new(),
            emitted: 0,
            rejected: 0,
            cfg,
        }
    }

    pub fn rejected(&self) -> usize {
        self.rejected
    }

    /// Register an asserted top-level term: index its ground subterms and
    /// register any quantifiers it (top-level) contains.
    pub fn assert<L: TermLang<Sig = S>>(&mut self, lang: &L, t: S::Term) {
        self.ground.add_term(lang, t);
        self.collect_quants(lang, t);
    }

    fn collect_quants<L: TermLang<Sig = S>>(&mut self, lang: &L, t: S::Term) {
        match lang.view(t) {
            TermView::Quant { forall, vars, body } => {
                let vars = vars.to_vec();
                let triggers = lang.patterns(t);
                self.quants.push(Quant {
                    term: t,
                    vars,
                    triggers,
                    body,
                    universal: forall,
                    var_domains: None, // computed lazily on first enumeration
                });
                self.scanned.push(0); // new quantifier: scan the whole index once
            }
            TermView::App { .. } => {
                for a in lang.children(t) {
                    self.collect_quants(lang, a);
                }
            }
            _ => {}
        }
    }

    /// One round with no model (pure syntactic: e-match + enumerate).
    pub fn round<L: TermLang<Sig = S>>(&mut self, lang: &mut L) -> Verdict<S::Term> {
        self.round_with(lang, &NoModel)
    }

    /// One round with a model oracle. Per quantifier (relevance-gated to
    /// those whose `Q` is true in the model): CDQI → e-matching (frontier) →
    /// enumeration. Watermarks advance so the next round only scans the delta.
    pub fn round_with<L, M>(&mut self, lang: &mut L, model: &M) -> Verdict<S::Term>
    where
        L: TermLang<Sig = S>,
        M: ModelEval<L>,
    {
        let mut lemmas = Vec::new();
        let round_start = self.ground.frontier();
        let n = self.quants.len();
        let mut active = vec![false; n];
        let mut budget_hit = false;
        for qi in 0..n {
            if self.emitted >= self.cfg.max_instances {
                budget_hit = true;
                break;
            }
            // Relevance gating: skip quantifiers whose `Q` is not asserted true
            // in the current model (respects the guard; vacuously satisfied).
            if !model.is_active(lang, self.quants[qi].term) {
                continue;
            }
            active[qi] = true;

            // 1. CDQI — a conflicting instance, if the model reveals one.
            if let Some(binding) = cdqi::find_conflict(
                lang,
                &self.ground,
                model,
                &self.quants[qi],
                self.cfg.max_tuples_per_quant,
            ) {
                self.emit(lang, qi, &binding, &mut lemmas);
                continue;
            }

            // 2. E-matching (frontier-filtered) — triggered quantifiers.
            if !self.quants[qi].triggers.is_empty() {
                let bindings = self.ematch_all(lang, qi);
                for b in bindings {
                    if self.emitted >= self.cfg.max_instances {
                        budget_hit = true;
                        break;
                    }
                    self.emit(lang, qi, &b, &mut lemmas);
                }
                continue;
            }

            // 2.5. Model-completion short-circuit (M3, #260). If the host can
            //    verify this trigger-free quantifier in a COMPLETED model, it
            //    needs no ground instances — and enumerating it could DIVERGE: a
            //    body like `∀a. f(a) > 0` instantiates `a := f(t)` (an `Int`
            //    ground term), yielding `f(f(t))`, a fresh ground term enumerated
            //    next round → an unbounded `f`-tower that never saturates (so the
            //    saturation check below never runs). The host's `eval_forall`
            //    returns `Some(true)` only via a recognizer that has VERIFIED the
            //    existing pinned ground points (definitional / pure-polarity need
            //    none; the arithmetic function-completion recognizer scans the
            //    model's `f`-applications and arith-folds the body). So a
            //    model-falsified existing instance (e.g. `f(7) = -3`) is NOT
            //    certified — it falls through to enumeration, where the
            //    arithmetic theory refutes it. Skipping here is therefore sound:
            //    the completion's witness never crosses into the engine.
            if model.eval_forall(lang, self.quants[qi].term) == Some(true) {
                continue;
            }

            // 3. Enumeration — trigger-free, REAL ground index only (no
            //    fabricated witness ⇒ D bug impossible). Completeness over the
            //    ground universe; the model-based check below decides Sat vs
            //    Unknown once it saturates.
            self.enumerate(lang, qi, &mut lemmas);
        }
        // Advance the frontier watermark for every quantifier scanned this
        // round: terms that existed at round start are now "old" for them.
        for qi in 0..n {
            if active[qi] {
                self.scanned[qi] = round_start;
            }
        }
        if !lemmas.is_empty() {
            return Verdict::NewLemmas(lemmas);
        }
        if budget_hit {
            return Verdict::BudgetExhausted;
        }
        // Saturated. A triggered quantifier is satisfied by trigger semantics
        // once e-matching adds nothing; a trigger-free, ACTIVE one must be
        // model-verified (inactive ones are vacuously satisfied). The host's
        // synthetic witnesses never cross into the engine → nothing fabricated.
        for q in &self.quants {
            if q.triggers.is_empty() && model.is_active(lang, q.term) {
                // Bounded-guard FINITE quantifier (`∀x̄. (lo≤x̄≤hi ⇒ φ)`): every
                // bound var has a finite literal domain whose product fits the
                // per-quant enumeration cap, so ALL its non-vacuous instances were
                // emitted (saturation ⇒ none new this round ⇒ all in `seen`) and
                // the model satisfies them (Saturated ⇒ the ground solve is
                // consistent); everything outside the guard is vacuous. Hence the
                // quantifier holds — no model-completion needed, sound by finite
                // exhaustion. (The cap guard is essential: if the product exceeded
                // the cap, enumeration would truncate and "saturate" without
                // covering the tail, so we must NOT claim satisfaction then.)
                let finitely_exhausted = q.var_domains.as_ref().is_some_and(|vds| {
                    !vds.is_empty()
                        && vds.iter().all(|d| d.is_some())
                        && vds
                            .iter()
                            .map(|d| d.as_ref().map_or(0, Vec::len))
                            .fold(1usize, usize::saturating_mul)
                            <= self.cfg.max_tuples_per_quant
                });
                if finitely_exhausted {
                    continue;
                }
                match model.eval_forall(lang, q.term) {
                    Some(true) => {}
                    Some(false) | None => return Verdict::Inconclusive,
                }
            }
        }
        Verdict::Saturated
    }

    fn ematch_all<L: TermLang<Sig = S>>(
        &self,
        lang: &L,
        qi: usize,
    ) -> Vec<Vec<(S::VarName, S::Term)>> {
        let q = &self.quants[qi];
        let watermark = self.scanned[qi];
        let mut out = Vec::new();
        for group in &q.triggers {
            let bs = if group.len() == 1 {
                // Frontier filter: only match against ground terms (with the
                // trigger head) that are NEW since this quantifier last scanned.
                // Matches whose candidate is old were already found in a prior
                // round (mod-time e-matching).
                let head = match lang.view(group[0]) {
                    TermView::App { sym, .. } => sym,
                    _ => continue,
                };
                let cands: Vec<S::Term> = self
                    .ground
                    .with_head(head)
                    .iter()
                    .copied()
                    .filter(|&c| self.ground.idx_of(c) >= watermark)
                    .collect();
                trigger::match_single(lang, &cands, group[0], &q.vars)
            } else {
                trigger::match_multi(lang, &self.ground, group, &q.vars)
            };
            out.extend(bs);
        }
        out
    }

    fn enumerate<L: TermLang<Sig = S>>(
        &mut self,
        lang: &mut L,
        qi: usize,
        out: &mut Vec<S::Term>,
    ) {
        // Lazily compute the per-variable bounded-guard finite domains (the host
        // parses the `∀x̄. (lo≤x≤hi ⇒ φ)` guard once); cache on the quantifier.
        if self.quants[qi].var_domains.is_none() {
            let vd = lang.bounded_var_domains(self.quants[qi].term);
            self.quants[qi].var_domains = Some(vd);
        }
        let sorts: Vec<S::Sort> = self.quants[qi].vars.iter().map(|(_, s)| *s).collect();
        // Cloned to release the `self.quants` borrow before touching `self.ground`.
        let vd = self.quants[qi].var_domains.clone().unwrap_or_default();
        let domains: Vec<Vec<S::Term>> = sorts
            .iter()
            .enumerate()
            .map(|(i, s)| match vd.get(i).and_then(|o| o.as_ref()) {
                // Bounded-int guard → only the finite literal set matters.
                Some(finite) => finite.clone(),
                // Otherwise enumerate over the real ground index (unchanged).
                None => self.ground.of_sort(*s).to_vec(),
            })
            .collect();
        if domains.iter().any(|d| d.is_empty()) {
            return; // no real candidate of some sort → emit nothing (no fabrication)
        }
        let k = domains.len();
        let mut idx = vec![0usize; k];
        let mut tuples = 0usize;
        loop {
            if tuples >= self.cfg.max_tuples_per_quant || self.emitted >= self.cfg.max_instances {
                break;
            }
            tuples += 1;
            let binding: Vec<(S::VarName, S::Term)> = self.quants[qi]
                .vars
                .iter()
                .map(|(n, _)| *n)
                .zip((0..k).map(|i| domains[i][idx[i]]))
                .collect();
            self.emit(lang, qi, &binding, out);
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
                break;
            }
        }
    }

    /// The single sound emit path used by every strategy: dedup by
    /// (quantifier, tuple), run the central invariant-enforcing `instantiate`,
    /// index the new ground subterms, and collect the guarded lemma.
    fn emit<L: TermLang<Sig = S>>(
        &mut self,
        lang: &mut L,
        qi: usize,
        binding: &[(S::VarName, S::Term)],
        out: &mut Vec<S::Term>,
    ) {
        let tuple: Vec<S::Term> = binding.iter().map(|(_, t)| *t).collect();
        if !self.seen.insert((qi, tuple)) {
            return; // already emitted
        }
        match instantiate(lang, &self.ground, &self.quants[qi], binding) {
            InstResult::Lemma(l) => {
                self.ground.add_term(lang, l); // chained triggers next round
                out.push(l);
                self.emitted += 1;
            }
            InstResult::Rejected => self.rejected += 1,
        }
    }
}
