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

use crate::ccfv;
use crate::cdqi;
use crate::congruence::{Congruence, NoCong};
use crate::ground::GroundIndex;
use crate::instantiate::{InstResult, Quant, instantiate};
use crate::model::{ModelEval, NoModel};
use crate::term::{Binding, Sig, TermLang, TermView};
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
    /// Whether trigger e-matching runs **modulo congruence**. CCFV is the sole
    /// matcher either way; this flag only selects the *oracle* `ematch_all`
    /// passes it: the real congruence (congruence-aware — fires modulo `E`) when
    /// `true`, or the trivial [`NoCong`] (syntactic-equivalent) when `false`.
    /// It is only meaningful when a real congruence is supplied via
    /// [`Engine::round_with_cong`]; `round_with` passes [`NoCong`], so the flag is
    /// moot there. CCFV-with-congruence is a *superset* of syntactic matching (it
    /// adds matches holding modulo `E`), and every match still flows through the
    /// unchanged `instantiate`/`emit` firewall — so enabling it can only add sound
    /// instances. The engine's own [`Config::default`] leaves it `false` (the
    /// `oxiz-mbqi` unit tests exercise the syntactic-equivalent path); the live
    /// solver sets it from `SolverConfig::ccfv_ematch`, which defaults `true`.
    pub ccfv_ematch: bool,
    /// **CCFV model-completion verdict-flip (P4, design §3 `Mode::ModelCompl`).**
    /// When set, a trigger-free universal that the host's structural recognizers
    /// (`eval_forall`) leave unverified is given one more chance: the host runs
    /// CCFV `¬ψ` against the **total view** `E_TOT` ([`crate::congruence::TotalView`])
    /// via [`ModelEval::model_completion`]; *no* conflict ⇒ the completed model
    /// satisfies `∀x̄.ψ` ⇒ `Some(true)` (a `Sat` contribution). This is the
    /// completeness half of CCFV — but it is **SOUNDNESS-CRITICAL**: a missed
    /// conflict is a spurious `sat`, so it stays **default `false`** until the
    /// disequality search is complete + verus-pre-verified + corpus-0-spurious
    /// gated (design §6). With the flag clear the backstop is never consulted, so
    /// the path is byte-identical. Set by the live solver from
    /// `SolverConfig::ccfv_model_compl`.
    pub ccfv_model_compl: bool,
    /// **The fuel-aware cost scheduler (design `FUEL_AWARE_COST_SCHEDULER.md`).**
    /// When `false` (default) the round loop fires every discovered instance
    /// immediately, exactly as before — byte-identical. When `true`, discovered
    /// candidates are SCORED and routed through a [`CostScheduler`], drained
    /// cheapest-first within an intra-round discover⇄drain fixpoint (§5.3). The
    /// scheduler only reorders/defers sound instances; the `instantiate`/`emit`
    /// firewall and the never-conclude-unsat verdict are unchanged. Off until the
    /// corpus A/B gate (P2) validates 0 regressions.
    pub cost_schedule: bool,
    /// Cost-function parameters (default = Z3 parity: `cost = weight + generation`).
    pub cost_params: crate::cost::CostParams,
    /// AWR age:weight pulse ratio for the scheduler. `awr_age_ratio = 0` (default)
    /// is single-min-tier mode; a positive age share is the fairness pulse (P3).
    pub awr_age_ratio: u32,
    pub awr_weight_ratio: u32,
}

impl Default for Config {
    fn default() -> Self {
        Config {
            max_instances: 100_000,
            max_tuples_per_quant: 4_096,
            ccfv_ematch: false,
            ccfv_model_compl: false,
            cost_schedule: false,
            cost_params: crate::cost::CostParams::default(),
            awr_age_ratio: 0,
            awr_weight_ratio: 1,
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
    /// The cost-scheduler priority queue (built lazily on the first scheduled
    /// round; `None` when `cfg.cost_schedule` is off). Monotone — accumulates
    /// within a solve, never rolled back.
    scheduler: Option<crate::cost_scheduler::CostScheduler<S>>,
    /// Set only during a scheduled discovery pass: routes [`emit`](Self::emit) to
    /// [`collect_candidate`](Self::collect_candidate) instead of firing. Off in
    /// the fire-all (flag-off) path, so that path is byte-identical.
    scheduling: bool,
    /// Count of NEW candidates the scheduler accepted (dedup-passing inserts) —
    /// used to detect a stalled fixpoint pass.
    sched_inserts: usize,
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
            scheduler: None,
            scheduling: false,
            sched_inserts: 0,
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
                let mut vars = vars.to_vec();
                let mut triggers = lang.patterns(t);
                let mut body = body;
                let mut inferred = false;
                if triggers.is_empty() {
                    // Flatten a same-polarity nested chain (`∀x.∀y.φ ≡ ∀x,y.φ`,
                    // `∃∃` likewise) so inference sees the true matrix and one
                    // instantiation grounds the whole chain (the two-level
                    // dance — outer enumerated, inner re-registered from the
                    // lemma — is what blew up the trigger-less Int-domain
                    // definitional axioms). Stop at an inner quantifier that
                    // flips polarity, carries its own parsed patterns (its
                    // author scoped them to THAT level), or shadows an
                    // accumulated variable name (binding would be ambiguous).
                    loop {
                        match lang.view(body) {
                            TermView::Quant { forall: f2, vars: v2, body: b2 }
                                if f2 == forall
                                    && lang.patterns(body).is_empty()
                                    && v2.iter().all(|(n, _)| {
                                        vars.iter().all(|(m, _)| m != n)
                                    }) =>
                            {
                                vars.extend_from_slice(v2);
                                body = b2;
                            }
                            _ => break,
                        }
                    }
                }
                // Trigger INFERENCE itself runs LAZILY on the first active
                // round (see the round loop): it must consult
                // `bounded_var_domains` (a FULLY-bounded quantifier keeps its
                // complete finite-box enumeration — inference there would
                // mask a jointly-unsat box, the pigeonhole), and that needs
                // the `&mut` host access registration does not have.
                let inferred = false;
                self.quants.push(Quant {
                    term: t,
                    vars,
                    triggers,
                    inferred,
                    inference_tried: false,
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
        // Default path: the trivial congruence (never queried when
        // `cfg.ccfv_ematch` is false), so behaviour is byte-identical.
        self.round_with_cong(lang, model, &NoCong)
    }

    /// As [`round_with`](Self::round_with), but threading a congruence oracle so
    /// single-pattern trigger e-matching can run **modulo congruence** via
    /// [`ccfv::match_trigger`] when `cfg.ccfv_ematch` is set (design
    /// `CCFV_UNIFIED_INSTANTIATION.md` §3, Phase P2). With `cfg.ccfv_ematch ==
    /// false` (the default) the oracle is ignored and this is exactly
    /// `round_with`. CCFV matching only *adds* matches over the syntactic path,
    /// and every match still passes the `instantiate`/`emit` firewall, so enabling
    /// it can never introduce an unsound instance.
    pub fn round_with_cong<L, M, C>(
        &mut self,
        lang: &mut L,
        model: &M,
        cong: &C,
    ) -> Verdict<S::Term>
    where
        L: TermLang<Sig = S>,
        M: ModelEval<L>,
        C: Congruence<S>,
    {
        // Cost-schedule dispatch (design §7). Default OFF ⇒ the fire-all body
        // below runs unchanged (byte-identical). The scheduled path is a separate
        // method so this one is provably untouched when the flag is clear.
        if self.cfg.cost_schedule {
            return self.round_cost_scheduled(lang, model, cong);
        }
        let mut lemmas = Vec::new();
        let round_start = self.ground.frontier();
        let n = self.quants.len();
        let mut budget_hit = false;
        if std::env::var_os("OXIZ_MBQI_DBG").is_some() {
            eprintln!(
                "[mbqi-dbg] round: quants={n} frontier={round_start} emitted={} rejected={}",
                self.emitted, self.rejected,
            );
        }
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

            // 0. EXISTENTIALS are never ground-instantiated like universals —
            //    asserting `Q ⇒ φ[x̄↦t̄]` for an arbitrary ground `t̄` is UNSOUND
            //    (a `t̄` outside the guard makes `φ` false, so `Q ⇒ false` = `¬Q`
            //    refutes the asserted `∃` → spurious `unsat`). A BOUNDED `∃` is
            //    discharged SOUNDLY by its finite disjunction `Q ⇒ ⋁_{t̄∈D} φ[t̄]`
            //    (exactly the existential over its guard's integer domain — the
            //    guard inside each disjunct self-excludes out-of-range tuples).
            //    An UNBOUNDED `∃` emits nothing and reports the sound `Unknown`
            //    at saturation (host-side skolemization, forbidden by the
            //    no-fabrication firewall inside the engine, would be needed).
            if !self.quants[qi].universal {
                self.emit_existential_disjunction(lang, qi, &mut lemmas);
                continue;
            }

            // 0.5. LAZY trigger inference (z3's auto-pattern parity), once per
            //    quantifier: a trigger-less universal otherwise falls to
            //    ground-index enumeration, which DIVERGES on definitional
            //    axioms over infinite sorts (`∀x,y:Int. Sub(x,y) = x−y`
            //    instantiates over every ground Int pair, each instance
            //    minting fresh `x−y` terms for the next round — the measured
            //    300 s churn → 3 ms on the verus fuel prelude). A
            //    FULLY-bounded quantifier is EXEMPT: its finite-box
            //    enumeration is complete (a jointly-unsat box — pigeonhole —
            //    needs every box instance, which a trigger would mask).
            if self.quants[qi].triggers.is_empty() && !self.quants[qi].inference_tried {
                self.quants[qi].inference_tried = true;
                if self.quants[qi].var_domains.is_none() {
                    let vd = lang.bounded_var_domains(self.quants[qi].term);
                    self.quants[qi].var_domains = Some(vd);
                }
                let fully_bounded = self.quants[qi]
                    .var_domains
                    .as_ref()
                    .is_some_and(|vd| !vd.is_empty() && vd.iter().all(|d| d.is_some()));
                if !fully_bounded {
                    let trg =
                        infer_triggers(lang, &self.quants[qi].vars, self.quants[qi].body);
                    if std::env::var_os("OXIZ_MBQI_DBG").is_some() {
                        let shapes: Vec<usize> = trg.iter().map(Vec::len).collect();
                        eprintln!(
                            "[mbqi-dbg] quant {qi}: vars={} inferred {} group(s), sizes {shapes:?}",
                            self.quants[qi].vars.len(),
                            trg.len(),
                        );
                    }
                    if !trg.is_empty() {
                        self.quants[qi].triggers = trg;
                        self.quants[qi].inferred = true;
                    }
                }
            }

            // 1. CDQI — every conflicting instance the model reveals (P3: CCFV
            //    `C = ¬ψ`, congruence-deduped candidates). A non-empty conflict
            //    set is the strongest, most relevant lemma, so it short-circuits
            //    e-matching/enumeration for this quantifier this round.
            let conflicts = cdqi::find_conflicts(
                lang,
                &self.ground,
                model,
                cong,
                &self.quants[qi],
                self.cfg.max_tuples_per_quant,
            );
            if !conflicts.is_empty() {
                for b in &conflicts {
                    if self.emitted >= self.cfg.max_instances {
                        budget_hit = true;
                        break;
                    }
                    self.emit(lang, qi, b, &mut lemmas);
                }
                continue;
            }

            // 2. E-matching (frontier-filtered) — triggered quantifiers.
            // NOTE: an INFERRED-trigger quantifier deliberately does NOT get
            // the M3 `eval_forall` short-circuit here: a structural
            // recognizer can certify the CURRENT model while the ground core
            // still needs the (bounded, trigger-confined) instances to
            // progress toward `unsat` — skipping starved the fuel-prelude
            // chain. E-matching is frontier-filtered and terminates, so the
            // divergence-defusing role of the short-circuit is not needed.
            if !self.quants[qi].triggers.is_empty() {
                let bindings = self.ematch_all(lang, qi, cong);
                // #404 — the frontier watermark advances HERE, in the branch
                // that actually CONSUMED the frontier, not in a blanket
                // end-of-round sweep. The old sweep advanced `scanned[qi]`
                // even on rounds where a `continue` (a CDQI conflict, an
                // existential, a model-completion short-circuit) skipped this
                // e-match — so a trigger inferred in such a round never saw
                // the PRE-watermark ground seeds again, permanently starving
                // the quantifier (the corpus decreases-check wall: CDQI emits
                // one conflict instance in the inference round, the watermark
                // sweeps past the seed terms, every later `ematch_all` sees
                // an empty frontier). Re-scans after a skipped round are
                // idempotent — `emit` dedups by `(qi, tuple)`.
                self.scanned[qi] = round_start;
                if std::env::var_os("OXIZ_MBQI_DBG").is_some() {
                    eprintln!(
                        "[mbqi-dbg] quant {qi}: ematch_all -> {} binding(s), emitted so far {}",
                        bindings.len(),
                        self.emitted,
                    );
                }
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
            if model.eval_forall(lang, cong, self.quants[qi].term) == Some(true) {
                continue;
            }

            // 2.6. Model-completion short-circuit (P4, `Mode::ModelCompl`). When
            //    the verdict-flip is enabled, give an unverified trigger-free
            //    universal a CCFV `¬ψ` conflict search over the total view
            //    `E_TOT` BEFORE enumerating it: no conflict ⇒ the completed model
            //    satisfies it ⇒ skip (the same divergence-defusing role as the
            //    `eval_forall` short-circuit above, for the cases the structural
            //    recognizers miss). Gated (default off) so the path is unchanged
            //    unless the flip is on; `Some(true)` only — any conflict /
            //    undecidable lowering ⇒ fall through to sound enumeration.
            if self.cfg.ccfv_model_compl
                && model.model_completion(lang, cong, self.quants[qi].term) == Some(true)
            {
                continue;
            }

            // 3. Enumeration — trigger-free, REAL ground index only (no
            //    fabricated witness ⇒ D bug impossible). Completeness over the
            //    ground universe; the model-based check below decides Sat vs
            //    Unknown once it saturates.
            self.enumerate(lang, qi, &mut lemmas);
        }
        // #404 — NO blanket end-of-round watermark sweep: `scanned[qi]`
        // advances inside the e-match branch, exactly when the frontier was
        // consumed (see the comment there). `enumerate` ignores the
        // watermark (full ground-index rescan, `emit`-deduped) and the
        // `continue` branches must NOT age the frontier they never read.
        if std::env::var_os("OXIZ_MBQI_DBG").is_some() {
            eprintln!(
                "[mbqi-dbg] round end: lemmas={} emitted={} rejected={} budget_hit={budget_hit}",
                lemmas.len(),
                self.emitted,
                self.rejected,
            );
        }
        if !lemmas.is_empty() {
            return Verdict::NewLemmas(lemmas);
        }
        if budget_hit {
            return Verdict::BudgetExhausted;
        }
        self.saturation_verdict(lang, model, cong)
    }

    /// The per-quantifier saturation verdict (shared by the fire-all and the
    /// cost-scheduled rounds). Reached only when a round emitted no lemma and did
    /// not hit the budget; returns `Saturated` (host may report `Sat`) unless some
    /// active quantifier is unverified → `Inconclusive` (host reports `Unknown`).
    ///
    /// A triggered quantifier is satisfied by trigger semantics once e-matching
    /// adds nothing; a trigger-free, ACTIVE one must be model-verified (inactive
    /// ones are vacuously satisfied). The host's synthetic witnesses never cross
    /// into the engine → nothing fabricated.
    ///
    /// NOTE: a bounded-guard FINITE quantifier (`∀x̄. (lo≤x̄≤hi ⇒ φ)`) is NOT
    /// auto-satisfied just because all its instances were emitted — the earlier
    /// "finite exhaustion ⇒ sat" shortcut was the #277 spurious-sat (the
    /// incremental CDCL(T) can miss a GLOBAL conflict, e.g. pigeonhole); the
    /// verdict now defers to `eval_forall` (a bounded quantifier it cannot verify
    /// yields the sound `Unknown`, never a guessed `Sat`).
    fn saturation_verdict<L, M, C>(&mut self, lang: &mut L, model: &M, cong: &C) -> Verdict<S::Term>
    where
        L: TermLang<Sig = S>,
        M: ModelEval<L>,
        C: Congruence<S>,
    {
        for qi in 0..self.quants.len() {
            let q = &self.quants[qi];
            // An INFERRED trigger drives e-matching but is not a user
            // contract — trigger semantics may only justify `Sat` for parsed
            // `:pattern`s, so an inferred-trigger quantifier must still be
            // model-verified here exactly like a trigger-free one.
            if !((q.triggers.is_empty() || q.inferred) && model.is_active(lang, q.term)) {
                continue;
            }
            // A BOUNDED-FINITE quantifier emitted ALL its instances over the
            // guard's box, so it is FULLY captured; the `∀`-direction re-solve is
            // sound (the incremental `Saturated`→`Sat` alone was #277).
            if self.bounded_finite(qi) {
                continue;
            }
            // An UNBOUNDED existential emitted nothing and is unverified → the
            // sound `Unknown`, NEVER a guessed `Sat`. `eval_forall` is a
            // `∀`-only recognizer and must not run on an `∃`.
            if !q.universal {
                return Verdict::Inconclusive;
            }
            match model.eval_forall(lang, cong, q.term) {
                Some(true) => {}
                Some(false) => return Verdict::Inconclusive,
                None => {
                    // P4 model-completion backstop (gated, default off): CCFV `¬ψ`
                    // over the total view `E_TOT` gets the final word — no conflict
                    // ⇒ satisfied; any conflict / undecidable ⇒ sound `Unknown`.
                    if self.cfg.ccfv_model_compl
                        && model.model_completion(lang, cong, q.term) == Some(true)
                    {
                        continue;
                    }
                    return Verdict::Inconclusive;
                }
            }
        }
        Verdict::Saturated
    }

    /// E-match every trigger group of quantifier `qi` against the ground index,
    /// returning the full bound-variable bindings (in `q.vars` order) to emit.
    ///
    /// CCFV is the **sole** matcher (the syntactic `trigger` module was deleted in
    /// the P2 follow-up). The `cfg.ccfv_ematch` flag selects the *oracle*: the
    /// real congruence `cong` (congruence-aware — fires modulo `E`) when set, or
    /// the trivial [`NoCong`] (syntactic-equivalent) when clear, so the flag-off
    /// path is byte-identical to the old `trigger::match_*`. Every raw CCFV
    /// substitution is normalised into `q.vars` order and dropped unless it binds
    /// EVERY bound variable (an instance must be fully ground — the same fullness
    /// filter the syntactic matcher applied; the canonical order also keeps the
    /// `seen` dedup tuple aligned with CDQI/enumeration).
    fn ematch_all<L: TermLang<Sig = S>, C: Congruence<S>>(
        &self,
        lang: &L,
        qi: usize,
        cong: &C,
    ) -> Vec<Vec<(S::VarName, S::Term)>> {
        let q = &self.quants[qi];
        let watermark = self.scanned[qi];
        let holes: Vec<S::VarName> = q.vars.iter().map(|(n, _)| *n).collect();
        let mut out = Vec::new();
        for group in &q.triggers {
            let raw: Vec<ccfv::Subst<S>> = if group.len() == 1 {
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
                // CCFV with the real oracle is a *superset* of syntactic matches —
                // it also fires when the pattern matches a candidate *modulo
                // congruence*; with `NoCong` it is exactly syntactic.
                if self.cfg.ccfv_ematch {
                    ccfv::match_trigger(cong, lang, group[0], &holes, &cands)
                } else {
                    ccfv::match_trigger(&NoCong, lang, group[0], &holes, &cands)
                }
            } else {
                // Multi-pattern join: per-pattern candidate seeds (the ground
                // applications sharing each pattern's head — no frontier filter,
                // the joint match re-scans every round as `match_multi` did). A
                // non-App pattern makes the whole group unmatchable.
                let mut seeds: Vec<Vec<S::Term>> = Vec::with_capacity(group.len());
                let mut ok = true;
                for &p in group {
                    match lang.view(p) {
                        TermView::App { sym, .. } => seeds.push(self.ground.with_head(sym).to_vec()),
                        _ => {
                            ok = false;
                            break;
                        }
                    }
                }
                if !ok {
                    continue;
                }
                if self.cfg.ccfv_ematch {
                    ccfv::match_trigger_multi(cong, lang, group, &holes, &seeds)
                } else {
                    ccfv::match_trigger_multi(&NoCong, lang, group, &holes, &seeds)
                }
            };
            // Normalise to `q.vars` order; drop any binding that is not fully ground.
            for s in &raw {
                let mut binding: Vec<(S::VarName, S::Term)> = Vec::with_capacity(q.vars.len());
                let mut full = true;
                for (n, _) in &q.vars {
                    match s.iter().find(|(m, _)| m == n) {
                        Some(&(_, t)) => binding.push((*n, t)),
                        None => {
                            full = false;
                            break;
                        }
                    }
                }
                if full {
                    out.push(binding);
                }
            }
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
        // Cost-schedule routing (design §7): during a scheduled discovery pass,
        // a discovered candidate is SCORED and queued rather than fired now; the
        // fixpoint drains it (through `emit_bound`) in cost order. The fire-all
        // path never sets `scheduling`, so it is unaffected (byte-identical).
        if self.scheduling {
            self.collect_candidate(lang, qi, binding);
            return;
        }
        let tuple: Vec<S::Term> = binding.iter().map(|(_, t)| *t).collect();
        if !self.seen.insert((qi, tuple)) {
            return; // already emitted
        }
        match instantiate(lang, &self.ground, &self.quants[qi], binding) {
            InstResult::Lemma(l) => {
                // E1 (design FUEL_AWARE_COST_SCHEDULER.md): the minted lemma's fresh
                // ground terms carry generation `1 + max(generation of the binding
                // terms)` — the well-founded instantiation-depth measure the
                // cost-scheduler prices on. Binding terms are ground-index terms
                // whose generation is already recorded; an empty binding (nullary /
                // existential sentinel) yields generation 1. Additive: nothing reads
                // `gen` yet, so verdicts are unchanged.
                let g = 1 + binding
                    .iter()
                    .map(|(_, t)| self.ground.gen_of(*t))
                    .max()
                    .unwrap_or(0);
                self.ground.add_term_gen(lang, l, g); // chained triggers next round
                out.push(l);
                self.emitted += 1;
            }
            InstResult::Rejected => {
                if std::env::var_os("OXIZ_MBQI_DBG").is_some() {
                    eprintln!("[mbqi-dbg] quant {qi}: instance REJECTED");
                }
                self.rejected += 1;
            }
        }
    }

    // ===== Cost-scheduled path (design `FUEL_AWARE_COST_SCHEDULER.md` §5.3, §8) =====
    // Reached only when `cfg.cost_schedule` is set; the fire-all path above is
    // untouched, so it stays byte-identical when the flag is clear.

    /// The cost-scheduled round: an intra-round **discover⇄drain fixpoint** (§5.3).
    /// Each pass discovers candidates (routing them into the scheduler), then
    /// drains a cheapest-first batch and fires it — the mints land in the ground
    /// index immediately, so the next pass re-discovers on the grown frontier and
    /// the within-round cascade the deep-closers need is reconstructed. The §8
    /// gate: a sound candidate still queued ⇒ `BudgetExhausted` (→ `Unknown`),
    /// never `Saturated`.
    fn round_cost_scheduled<L, M, C>(&mut self, lang: &mut L, model: &M, cong: &C) -> Verdict<S::Term>
    where
        L: TermLang<Sig = S>,
        M: ModelEval<L>,
        C: Congruence<S>,
    {
        if self.scheduler.is_none() {
            self.scheduler = Some(crate::cost_scheduler::CostScheduler::new(
                self.cfg.awr_age_ratio,
                self.cfg.awr_weight_ratio,
            ));
        }
        let mut lemmas = Vec::new();
        let mut budget_hit = false;
        // Per-CALL emit budget: the intra-round fixpoint cascades a few
        // generations (so a deep-closer reaches its fuel depth within the round),
        // then RETURNS to the host so it can re-solve — which lets an `unsat`
        // close early (the fire-all path gets this for free by emitting one pass
        // per round) and lets the between-round MBQI wall-clock guard bound total
        // time. Without this cap the fixpoint drains the whole cascade before the
        // host ever re-solves → it over-instantiates to `max_instances` on a
        // large prelude (a 20 s+ hang), never seeing the early conflict.
        let call_start = self.emitted;
        loop {
            let before = self.sched_inserts;
            let bh = self.discover_collect(lang, model, cong, &mut lemmas);
            budget_hit |= bh;
            let inserted = self.sched_inserts > before;
            // Drain a cheapest-first batch; fire each → mints grow the frontier.
            let batch = self
                .scheduler
                .as_mut()
                .unwrap()
                .drain(self.cfg.max_tuples_per_quant);
            let drained = !batch.is_empty();
            for (qi, sigma) in batch {
                if self.emitted >= self.cfg.max_instances {
                    budget_hit = true;
                    break;
                }
                self.emit_bound(lang, qi as usize, &sigma, &mut lemmas);
            }
            if self.emitted >= self.cfg.max_instances {
                budget_hit = true;
            }
            // Fixpoint end: budget hit, per-call cap reached (yield to the host),
            // or nothing new discovered AND nothing left to drain.
            if budget_hit
                || self.emitted - call_start >= self.cfg.max_tuples_per_quant
                || (!inserted && !drained)
            {
                break;
            }
        }
        if !lemmas.is_empty() {
            return Verdict::NewLemmas(lemmas);
        }
        // §8 — DEFER never DROP: a sound candidate still queued (budget-deferred
        // this check) forbids `Saturated` (which would license the host to report
        // `Sat` while a refuter is withheld). Route to `Unknown`.
        let queued = self.scheduler.as_ref().is_some_and(|s| !s.is_empty());
        if budget_hit || queued {
            return Verdict::BudgetExhausted;
        }
        self.saturation_verdict(lang, model, cong)
    }

    /// One scheduled DISCOVERY pass: the same per-quantifier strategy sequence as
    /// the fire-all loop, but with `self.scheduling` set so every `emit` routes to
    /// [`collect_candidate`](Self::collect_candidate) (universal candidates are
    /// queued + scored, not fired). Existentials fire directly into `lemmas` (they
    /// bypass the scheduler, like CDQI conflicts). Returns whether the budget hit.
    fn discover_collect<L, M, C>(
        &mut self,
        lang: &mut L,
        model: &M,
        cong: &C,
        lemmas: &mut Vec<S::Term>,
    ) -> bool
    where
        L: TermLang<Sig = S>,
        M: ModelEval<L>,
        C: Congruence<S>,
    {
        let round_start = self.ground.frontier();
        let n = self.quants.len();
        let mut budget_hit = false;
        // Bound how many candidates ONE discovery pass queues before yielding to a
        // drain: without this a single enumeration flood (up to `max_tuples` PER
        // quantifier × hundreds of quantifiers) balloons the scheduler, and the
        // whole point of the fixpoint is to interleave discover with drain. Bounded
        // via the O(1) insert counter (not an O(n) live scan).
        let pass_start = self.sched_inserts;
        for qi in 0..n {
            if self.emitted >= self.cfg.max_instances {
                budget_hit = true;
                break;
            }
            if self.sched_inserts - pass_start >= self.cfg.max_tuples_per_quant {
                break; // pass collection cap → go drain, then re-discover
            }
            if !model.is_active(lang, self.quants[qi].term) {
                continue;
            }
            // Existentials fire directly (scheduling off around this call so the
            // disjunction is emitted, not queued).
            if !self.quants[qi].universal {
                self.emit_existential_disjunction(lang, qi, lemmas);
                continue;
            }
            // Lazy trigger inference (identical to the fire path).
            if self.quants[qi].triggers.is_empty() && !self.quants[qi].inference_tried {
                self.quants[qi].inference_tried = true;
                if self.quants[qi].var_domains.is_none() {
                    let vd = lang.bounded_var_domains(self.quants[qi].term);
                    self.quants[qi].var_domains = Some(vd);
                }
                let fully_bounded = self.quants[qi]
                    .var_domains
                    .as_ref()
                    .is_some_and(|vd| !vd.is_empty() && vd.iter().all(|d| d.is_some()));
                if !fully_bounded {
                    let trg = infer_triggers(lang, &self.quants[qi].vars, self.quants[qi].body);
                    if !trg.is_empty() {
                        self.quants[qi].triggers = trg;
                        self.quants[qi].inferred = true;
                    }
                }
            }
            // 1. CDQI — fire conflicts IMMEDIATELY (bypass the scheduler, §5.1):
            //    a conflicting instance is the strongest lemma and drives the
            //    ground core to `unsat`; queuing it by cost would delay the
            //    refutation behind cheaper non-conflict instances and the host
            //    would never re-solve to the conflict. `scheduling` stays off, so
            //    `emit` fires into `lemmas` (and reserves `seen`, so the cost path
            //    won't re-queue it). Short-circuits e-match/enumerate this round,
            //    exactly like the fire-all path.
            let conflicts = cdqi::find_conflicts(
                lang,
                &self.ground,
                model,
                cong,
                &self.quants[qi],
                self.cfg.max_tuples_per_quant,
            );
            if !conflicts.is_empty() {
                for b in &conflicts {
                    self.emit(lang, qi, b, lemmas);
                }
                continue;
            }
            // 2. E-matching — collect (queue + score) into the scheduler.
            if !self.quants[qi].triggers.is_empty() {
                let bindings = self.ematch_all(lang, qi, cong);
                self.scanned[qi] = round_start;
                self.scheduling = true;
                for b in &bindings {
                    self.emit(lang, qi, b, lemmas);
                }
                self.scheduling = false;
                continue;
            }
            // 2.5/2.6 Model-completion short-circuits (identical to the fire path).
            if model.eval_forall(lang, cong, self.quants[qi].term) == Some(true) {
                continue;
            }
            if self.cfg.ccfv_model_compl
                && model.model_completion(lang, cong, self.quants[qi].term) == Some(true)
            {
                continue;
            }
            // 3. Enumeration — collect into the scheduler.
            self.scheduling = true;
            self.enumerate(lang, qi, lemmas);
            self.scheduling = false;
        }
        self.scheduling = false;
        budget_hit
    }

    /// Score a discovered universal candidate and queue it (design §3/§5.2). No
    /// instantiation here — the drain does that in cost order via `emit_bound`.
    fn collect_candidate<L: TermLang<Sig = S>>(
        &mut self,
        lang: &L,
        qi: usize,
        binding: &[(S::VarName, S::Term)],
    ) {
        let tuple: Vec<S::Term> = binding.iter().map(|(_, t)| *t).collect();
        // Unified dedup on the engine's `seen` (design fix #6): a candidate that a
        // fire-first CDQI conflict / existential already emitted is NOT re-queued,
        // and once queued it is not re-collected — so a drained candidate is never
        // double-emitted (`emit_bound` does not re-check `seen`; this reservation is
        // its dedup).
        if !self.seen.insert((qi, tuple.clone())) {
            return;
        }
        // generation = 1 + max binding generation (E1) — the candidate's depth.
        let generation = 1 + tuple.iter().map(|t| self.ground.gen_of(*t)).max().unwrap_or(0);
        // P2: Z3-parity cost = weight + generation (default CostParams zero the
        // fuel gradient + class penalty; those are wired at P3). weight is 0 until
        // the host supplies a per-quantifier `:weight`.
        let cost = crate::cost::cost_of(
            &self.cfg.cost_params,
            0,
            generation,
            0,
            crate::cost::GenClass::Unknown,
        );
        // Content sort-key (§5.2): the quantifier's content then each tuple term's;
        // `(q, σ)` is unique so this totally orders within a cost tier.
        let qterm = self.quants[qi].term;
        let mut key: Vec<u64> = Vec::with_capacity(tuple.len() + 1);
        key.push(crate::cost::term_content_key(lang, qterm));
        for t in &tuple {
            key.push(crate::cost::term_content_key(lang, *t));
        }
        let sched = self.scheduler.as_mut().unwrap();
        if sched.insert(qi as u32, tuple, cost, key.into_boxed_slice()) {
            self.sched_inserts += 1;
        }
    }

    /// Fire a drained candidate `(qi, σ)`: reconstruct the binding from the
    /// quantifier's variable names and run the same `instantiate`/`emit` firewall
    /// + generation-tagged indexing. The scheduler already deduped, so no `seen`.
    fn emit_bound<L: TermLang<Sig = S>>(
        &mut self,
        lang: &mut L,
        qi: usize,
        sigma: &[S::Term],
        out: &mut Vec<S::Term>,
    ) {
        let binding: Vec<(S::VarName, S::Term)> = self.quants[qi]
            .vars
            .iter()
            .map(|(n, _)| *n)
            .zip(sigma.iter().copied())
            .collect();
        match instantiate(lang, &self.ground, &self.quants[qi], &binding) {
            InstResult::Lemma(l) => {
                let g = 1 + sigma.iter().map(|t| self.ground.gen_of(*t)).max().unwrap_or(0);
                self.ground.add_term_gen(lang, l, g);
                out.push(l);
                self.emitted += 1;
            }
            InstResult::Rejected => {
                self.rejected += 1;
            }
        }
    }

    /// Discharge a BOUNDED existential by its exact finite disjunction
    /// `Q ⇒ ⋁_{t̄∈D} φ[x̄↦t̄]` over the guard's integer domain `D`. Emitted at
    /// most ONCE per quantifier (deduped via the empty-tuple `seen` sentinel).
    /// For an UNBOUNDED existential (a bound var with no finite domain, or a
    /// product exceeding the cap) nothing is emitted — the saturation check
    /// then reports the sound `Unknown`.
    ///
    /// SOUND + COMPLETE: `∃x̄. (guard ∧ φ)` is exactly `⋁_{t̄∈D} (guard[t̄] ∧
    /// φ[t̄])`, where `D` is the integer box the guard pins. Each disjunct
    /// substitutes the FULL body (guard included), so a tuple outside the guard
    /// has a false guard and contributes nothing — no need for `D` to be exactly
    /// the guard's support. Unlike the universal verdict, this is the EASY
    /// satisfiability direction (find ONE true disjunct), so it is immune to the
    /// incremental conflict-miss that forced `∀` to the sound `Unknown` (#277).
    fn emit_existential_disjunction<L: TermLang<Sig = S>>(
        &mut self,
        lang: &mut L,
        qi: usize,
        out: &mut Vec<S::Term>,
    ) {
        // Once per quantifier (the bound-var list is never empty, so the empty
        // tuple is a free sentinel that never collides with a real instance).
        if !self.seen.insert((qi, Vec::new())) {
            return;
        }
        if self.quants[qi].var_domains.is_none() {
            let vd = lang.bounded_var_domains(self.quants[qi].term);
            self.quants[qi].var_domains = Some(vd);
        }
        if !self.bounded_finite(qi) {
            return; // unbounded ∃ ⇒ no lemma ⇒ sound Unknown at saturation
        }
        let vd = self.quants[qi].var_domains.clone().unwrap_or_default();
        let domains: Vec<Vec<S::Term>> = vd.iter().map(|o| o.clone().unwrap_or_default()).collect();
        if domains.iter().any(|d| d.is_empty()) {
            return;
        }
        let vars: Vec<S::VarName> = self.quants[qi].vars.iter().map(|(n, _)| *n).collect();
        let body = self.quants[qi].body;
        let k = domains.len();
        let mut idx = vec![0usize; k];
        let mut disjuncts: Vec<S::Term> = Vec::new();
        loop {
            let binding: Vec<(S::VarName, S::Term)> = vars
                .iter()
                .copied()
                .zip((0..k).map(|i| domains[i][idx[i]]))
                .collect();
            let b = Binding::<S>::new(&binding);
            disjuncts.push(lang.substitute(body, &b));
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
        let disj = lang.mk_or(disjuncts);
        let lemma = lang.mk_implies(self.quants[qi].term, disj);
        self.ground.add_term(lang, lemma);
        out.push(lemma);
        self.emitted += 1;
    }

    /// Whether `qi`'s bound vars ALL have a finite literal domain whose product
    /// fits the per-quant cap (computed via `bounded_var_domains`, cached on the
    /// quantifier). For a bounded `∃` this means it was (or can be) discharged by
    /// its finite disjunction; for anything else it is `false`.
    fn bounded_finite(&self, qi: usize) -> bool {
        self.quants[qi].var_domains.as_ref().is_some_and(|vds| {
            !vds.is_empty()
                && vds.iter().all(|d| d.is_some())
                && vds
                    .iter()
                    .map(|d| d.as_ref().map_or(0, Vec::len))
                    .fold(1usize, usize::saturating_mul)
                    <= self.cfg.max_tuples_per_quant
        })
    }
}

/// Infer `:pattern`-style trigger groups for a trigger-less UNIVERSAL — the
/// z3 auto-pattern parity that keeps definitional axioms off the divergent
/// ground-index enumeration path (see the registration comment).
///
/// Candidates are the body's app subterms with an e-matchable head
/// ([`TermLang::matchable_head`]) that contain at least one bound variable
/// and no nested quantifier. Selection:
///  * every MINIMAL candidate covering ALL bound variables becomes its own
///    single-trigger group (groups are a union — more groups, more matches);
///  * if no single candidate covers, a greedy multi-trigger group is built
///    from the largest-coverage candidates; if even their union cannot cover
///    every bound variable, NO trigger is inferred (empty ⇒ the quantifier
///    keeps today's enumeration path — never a silent disable).
///
/// Inference is a heuristic for INSTANTIATION only; the `Quant::inferred`
/// flag keeps the saturation verdict on the model-verified path, so a poor
/// inference can cost completeness (a sound `Unknown`), never soundness.
pub(crate) fn infer_triggers<S: Sig, L: TermLang<Sig = S>>(
    lang: &L,
    vars: &[(S::VarName, S::Sort)],
    body: S::Term,
) -> Vec<Vec<S::Term>> {
    use rustc_hash::FxHashMap;
    if vars.is_empty() || vars.len() > 64 {
        return Vec::new(); // mask-based cover; >64 bound vars is not a real case
    }
    let var_bit: FxHashMap<S::VarName, u64> =
        vars.iter().enumerate().map(|(i, (n, _))| (*n, 1u64 << i)).collect();
    let full: u64 = if vars.len() == 64 { u64::MAX } else { (1u64 << vars.len()) - 1 };

    // Post-order walk: per-subterm bound-var mask + contains-a-quantifier
    // flag, memoized (terms are hash-consed on the host side, so sharing is
    // common). Iterative to keep deep bodies off the stack.
    #[derive(Clone, Copy)]
    struct Info {
        mask: u64,
        has_quant: bool,
    }
    let mut info: FxHashMap<S::Term, Info> = FxHashMap::default();
    let mut candidates: Vec<S::Term> = Vec::new();
    // Heads the axiom FEEDS: the body contains an app of this head with a
    // STRUCTURED bound-var-carrying argument, so every instance mints a NEW
    // ground term with that head — a trigger on such a head re-matches the
    // axiom's own output and loops (the `has_type(as_type(x,t),t)` tower:
    // trigger `has_type(x,t)` matches the instance's own conclusion with the
    // strictly larger `as_type(p,T)`, forever). Simplify's classic static
    // matching-loop test.
    let mut feeding_heads: FxHashSet<S::Sym> = FxHashSet::default();
    let mut stack: Vec<(S::Term, bool)> = vec![(body, false)];
    while let Some((t, expanded)) = stack.pop() {
        if info.contains_key(&t) {
            continue;
        }
        if !expanded {
            match lang.view(t) {
                TermView::Var { name } => {
                    let mask = var_bit.get(&name).copied().unwrap_or(0);
                    info.insert(t, Info { mask, has_quant: false });
                }
                TermView::Quant { .. } => {
                    // Do not descend: a nested quantifier's own bound vars are
                    // not ours, and a trigger containing a binder never
                    // matches a ground term.
                    info.insert(t, Info { mask: 0, has_quant: true });
                }
                TermView::App { .. } => {
                    stack.push((t, true));
                    for c in lang.children(t) {
                        stack.push((c, false));
                    }
                }
                TermView::Opaque => {
                    info.insert(t, Info { mask: 0, has_quant: false });
                }
            }
        } else {
            let mut acc = Info { mask: 0, has_quant: false };
            let mut structured_var_arg = false;
            for c in lang.children(t) {
                if let Some(ci) = info.get(&c) {
                    acc.mask |= ci.mask;
                    acc.has_quant |= ci.has_quant;
                    // a child that carries a bound var AND is itself an app —
                    // instantiating builds a strictly-larger term under this
                    // head.
                    if ci.mask != 0 && matches!(lang.view(c), TermView::App { .. }) {
                        structured_var_arg = true;
                    }
                }
            }
            if acc.mask != 0 && !acc.has_quant && lang.matchable_head(t) {
                candidates.push(t);
                if structured_var_arg {
                    if let TermView::App { sym } = lang.view(t) {
                        feeding_heads.insert(sym);
                    }
                }
            }
            info.insert(t, acc);
        }
    }
    // Drop candidates on a feeding head (loop risk) — but only if the
    // filtered pool can still COVER every bound variable. When the ONLY
    // covering candidates sit on feeding heads (the bit-op invariant
    // preservation axioms: `iInv(t, %I(x)) ∧ … ⇒ iInv(t, bitand(…))` — the
    // premise `iInv(t, %I(x))` is the natural trigger yet `iInv` also heads
    // the conclusion), keep them: a structured trigger argument (`%I(x)`)
    // does not re-match the axiom's own conclusion shape, and the
    // alternative — no trigger, ground-index enumeration over
    // Poly×Poly×Int — is the divergence this inference exists to prevent.
    let keep = |c: &S::Term| match lang.view(*c) {
        TermView::App { sym } => !feeding_heads.contains(&sym),
        _ => true,
    };
    // Decide FIRST whether the feeding-filtered pool still covers, then
    // apply the filter only if it does — no clone-and-restore.
    let filtered_covers = {
        let mut m = 0u64;
        for c in candidates.iter().filter(|c| keep(c)) {
            m |= info.get(c).map(|i| i.mask).unwrap_or(0);
        }
        m == full
    };
    if filtered_covers {
        candidates.retain(keep);
    }
    if candidates.is_empty() {
        return Vec::new();
    }

    // `a` occurs strictly inside `b`?
    fn is_strict_subterm<S: Sig, L: TermLang<Sig = S>>(
        lang: &L,
        a: S::Term,
        b: S::Term,
    ) -> bool {
        let mut stack: Vec<S::Term> = lang.children(b);
        let mut seen: FxHashSet<S::Term> = FxHashSet::default();
        while let Some(t) = stack.pop() {
            if t == a {
                return true;
            }
            if seen.insert(t) {
                stack.extend(lang.children(t));
            }
        }
        false
    }

    let mask_of = |t: &S::Term| info.get(t).map(|i| i.mask).unwrap_or(0);
    let mut full_covers: Vec<S::Term> =
        candidates.iter().copied().filter(|t| mask_of(t) == full).collect();
    if !full_covers.is_empty() {
        // keep the MINIMAL full covers (drop any that strictly contains
        // another full cover — the smaller pattern matches strictly more).
        let all = full_covers.clone();
        full_covers.retain(|&t| {
            !all.iter().any(|&o| o != t && is_strict_subterm(lang, o, t))
        });
        full_covers.truncate(4); // cap: each group is a full ground-index scan
        return full_covers.into_iter().map(|t| vec![t]).collect();
    }

    // Greedy multi-trigger: largest new coverage first (ties: first seen).
    let mut group: Vec<S::Term> = Vec::new();
    let mut covered = 0u64;
    while covered != full {
        let mut best: Option<(S::Term, u32)> = None;
        for &c in &candidates {
            let gain = (mask_of(&c) & !covered).count_ones();
            if gain > 0 && best.is_none_or(|(_, g)| gain > g) {
                best = Some((c, gain));
            }
        }
        match best {
            Some((c, _)) => {
                covered |= mask_of(&c);
                group.push(c);
                if group.len() > 4 {
                    return Vec::new(); // joint match would be too wide — give up
                }
            }
            None => return Vec::new(), // bound vars not coverable
        }
    }
    vec![group]
}
