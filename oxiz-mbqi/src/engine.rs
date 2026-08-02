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
    /// No new instances AND every ACTIVE quantifier is POSITIVELY justified:
    /// model-verified `Some(true)` (M3), or fully captured by its finite
    /// guard box (`bounded_finite`). Since #426 there is no longer a purely
    /// syntactic "its `:pattern` stopped firing" justification. If the ground
    /// core is still SAT here, the host may report **`Sat`**.
    Saturated,
    /// **Confirm-but-never-sat** (#425 phase 2, widened by #426). E-matching
    /// is closed and no OBLIGATION was model-REFUTED, but ≥ 1 active
    /// universal could not be positively justified:
    ///  * #425 — a parsed `:pattern` that NEVER fired, or an augmented /
    ///    inferred trigger set, that `eval_forall` left `None`;
    ///  * #426 — a parsed `:pattern` that DID fire but is INSUFFICIENT: it
    ///    matched something, just not enough to close the problem, and the
    ///    model neither certifies (`None`) nor is trusted to refute
    ///    (`Some(false)`) the quantifier.
    ///
    /// The caller MAY confirm the accumulated ground instance set — the
    /// instances are sound ground consequences, so a ground **UNSAT** over
    /// them is a real `unsat` — but must **NEVER conclude `sat`**: the
    /// unjustified quantifier may still be violated. This is the sound half
    /// of the pre-#425 early-stop (`Saturated`'s confirm-then-unsat path)
    /// without its `sat` half.
    SaturatedUnverified,
    /// No new instances, but at least one quantifier was model-REFUTED
    /// (`eval_forall` = `Some(false)`) with no real-ground witness to make
    /// progress on, or an unbounded existential could not be discharged. The
    /// host must report **`Unknown`** — never a guessed `Sat`, never a
    /// fabricated `Unsat`.
    Inconclusive,
    /// The per-check instantiation budget was hit → host reports `Unknown`.
    BudgetExhausted,
}

pub struct Config {
    pub max_instances: usize,
    pub max_tuples_per_quant: usize,
    /// Per-`ematch_all`-call cap on the raw CCFV substitution set (passed to
    /// [`ccfv::match_trigger`]/[`ccfv::match_trigger_multi`] as `max_substs`).
    /// A multi-pattern join over a large ground index is a PRODUCT of seed
    /// sets, so its match set can dwarf `max_instances` before a single lemma
    /// is emitted; this bounds that memory/time blow-up at the source. Hitting
    /// the cap truncates the match set and ABORTS the e-match (the abort flag
    /// routes into `budget_hit` → `Verdict::BudgetExhausted` → the host's
    /// `Unknown`) — it never silently drops matches, which could otherwise
    /// surface as a spurious `Saturated`/`Sat`.
    pub max_match_substs: usize,
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
    /// **E1 additive-patterns mode (#425).** After a pass that would conclude
    /// `Saturated`/`Inconclusive`, AUGMENT each parsed-trigger universal with
    /// inferred trigger groups (a UNION — the author's groups are kept) and
    /// re-pass, at most once per quantifier (`Quant::augmented`). This is the
    /// z3-auto-config parity lever for under-triggered axioms (dead `:pattern`
    /// symbols, ill-arity patterns): the parsed trigger alone never fires, and
    /// the ever-fired gate then yields the sound `Unknown` — augmentation can
    /// recover the real `unsat` instead. Augmented quantifiers LOSE the
    /// trigger-semantics saturation exemption (model-verified like
    /// inferred-trigger ones), so the mode only ever adds sound instances or
    /// moves a verdict in the sound direction. **Default `false`** pending the
    /// corpus A/B; set by the live solver from
    /// `SolverConfig::mbqi_additive_patterns` / `OXIZ_MBQI_ADDITIVE`.
    pub additive_patterns: bool,
    /// **Strict pattern saturation (#426).** When set (the DEFAULT), a parsed
    /// `:pattern` that has FIRED no longer buys an unconditional saturation
    /// exemption — it is only *provisionally* exempt, and must still be
    /// corroborated by `eval_forall` (`Some(true)`) or by its finite guard box
    /// before the pass may conclude [`Verdict::Saturated`]. Anything else
    /// demotes the pass to [`Verdict::SaturatedUnverified`]
    /// (confirm-but-never-sat), NEVER to `Inconclusive`.
    ///
    /// #425 closed the NEVER-fired half of the exemption; #426 is the residual
    /// FIRED-BUT-INSUFFICIENT half — a trigger that matches *something* but
    /// not enough to derive the contradiction still bought the exemption, so
    /// the engine reported `Saturated` → the host `sat` on unsat problems
    /// (23/2000 seeds in the E1 randomized pattern differential's `undertrig`
    /// class; z3 answers `unsat` via MBQI and cvc5 answers `unknown` on the
    /// same inputs — neither reference solver ever answers `sat`).
    ///
    /// Clearing it restores the pre-#426 lax exemption **and the spurious
    /// `sat`** — it exists only as a no-recompile A/B kill-switch, armed by
    /// `OXIZ_MBQI_LAX_PATTERN_SAT=1` in [`Engine::new`] (the
    /// `OXIZ_MBQI_GUARD_MS` / `OXIZ_MBQI_ADDITIVE` convention).
    pub strict_pattern_saturation: bool,
}

impl Default for Config {
    fn default() -> Self {
        Config {
            max_instances: 100_000,
            max_tuples_per_quant: 4_096,
            max_match_substs: 100_000,
            ccfv_ematch: false,
            ccfv_model_compl: false,
            additive_patterns: false,
            // #426: sound-by-default. `Default` stays a PURE function — the
            // env kill-switch is applied once in `Engine::new`, not here, so
            // an explicitly-built `Config` means exactly what it says.
            strict_pattern_saturation: true,
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
    /// Wall-clock deadline for round work (set by the host per round via
    /// [`set_deadline`](Self::set_deadline); `None` = unbounded). Checked at
    /// the per-quant loop head and threaded into the CCFV matchers so a
    /// pathological e-match aborts instead of overshooting the host's guard.
    /// Any deadline abort routes into `budget_hit` →
    /// [`Verdict::BudgetExhausted`] — NEVER a silent skip, which could
    /// surface as a spurious `Saturated`/`Sat` (a parsed-trigger quantifier's
    /// saturation rests entirely on "e-matching added nothing").
    deadline: Option<std::time::Instant>,
    cfg: Config,
}

impl<S: Sig> Engine<S> {
    pub fn new(mut cfg: Config) -> Self {
        // #426 kill-switch, read ONCE per engine (never in `saturation_verdict`,
        // which runs per pass): `OXIZ_MBQI_LAX_PATTERN_SAT=1` restores the
        // pre-#426 unconditional fired-trigger exemption for a no-recompile
        // A/B. It can only ever move a verdict in the UNSOUND direction, so it
        // is opt-in and never consulted unless explicitly set.
        if std::env::var("OXIZ_MBQI_LAX_PATTERN_SAT")
            .ok()
            .is_some_and(|v| v == "1" || v.eq_ignore_ascii_case("true"))
        {
            cfg.strict_pattern_saturation = false;
        }
        Engine {
            quants: Vec::new(),
            ground: GroundIndex::new(),
            seen: FxHashSet::default(),
            scanned: Vec::new(),
            emitted: 0,
            rejected: 0,
            deadline: None,
            cfg,
        }
    }

    pub fn rejected(&self) -> usize {
        self.rejected
    }

    /// Set (or clear) the wall-clock deadline the next round(s) honour. The
    /// host should call this before EVERY round — the engine persists across
    /// rounds (and potentially across check-sats), so a stale deadline from an
    /// earlier check would otherwise linger (the assert-time-populated-cache /
    /// stale-state bug class). Idempotent and cheap.
    pub fn set_deadline(&mut self, d: Option<std::time::Instant>) {
        self.deadline = d;
    }

    #[inline]
    fn deadline_hit(&self) -> bool {
        self.deadline
            .is_some_and(|d| std::time::Instant::now() >= d)
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
                // E1 STATIC `:pattern` validation (#425). A parsed group is
                // dropped only when PROVABLY unusable: a bare-`Var` member
                // can never head an e-match, and a fully-ANALYZABLE group
                // (every member and reached subterm classified by the view)
                // whose union of covered bound vars falls short of `vars`
                // can never yield an instance (`ematch_all`'s fullness
                // filter drops partial bindings) — its ONLY effect was
                // making `triggers` non-empty, which EXEMPTED the quantifier
                // from model-verified saturation → spurious `Sat`; dropping
                // it removes exactly that unsound exemption. Anything the
                // view does NOT classify (`Opaque` — e.g. Dt constructor/
                // selector applications under the OxiZ bridge) makes the
                // group UNANALYZABLE and it is KEPT conservatively (never
                // drop what the gate cannot reason about; a never-firing
                // kept group loses its exemption at the dynamic ever-fired
                // gate instead) — see `valid_pattern_group`. If EVERY group
                // drops, `triggers` is empty and
                // the existing lazy-inference path takes over unmodified
                // (inference sets `inferred = true`, which keeps the
                // quantifier model-verified at saturation). Dead symbols and
                // ill-arity patterns are NOT statically decidable behind the
                // `TermLang` view (no declaration table) — the dynamic
                // ever-fired gate (`Quant::matched`) covers those.
                if !triggers.is_empty() {
                    let before = triggers.len();
                    triggers.retain(|g| valid_pattern_group(lang, &vars, g));
                    if triggers.len() < before && std::env::var_os("OXIZ_MBQI_DBG").is_some() {
                        eprintln!(
                            "[mbqi-dbg] collect_quants: dropped {} invalid :pattern group(s), {} kept",
                            before - triggers.len(),
                            triggers.len(),
                        );
                    }
                }
                let mut body = body;
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
                    matched: false,
                    augmented: false,
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
        // E1 (#425) pass loop. Each iteration is ONE full instantiation pass
        // (the pre-E1 round body). With `additive_patterns` OFF (the default)
        // the loop body runs exactly once — byte-identical behaviour. With it
        // ON, a pass that would conclude `Saturated`/`SaturatedUnverified`/
        // `Inconclusive` (the no-progress verdicts) first gets its
        // parsed-trigger universals AUGMENTED with inferred groups
        // (once per quantifier — `augment_parsed_triggers` returns `false`
        // once nothing new can be appended, so the loop terminates).
        //
        // INVARIANT (checked EVERY pass, BEFORE saturation): a pass that hit
        // any budget (instance cap, deadline, e-match abort) must return
        // `BudgetExhausted` — falling through to the saturation verdict with
        // a PARTIAL pass would read "added nothing" as saturation → spurious
        // `Sat`.
        loop {
            let (lemmas, budget_hit) = self.instantiation_pass(lang, model, cong);
            if !lemmas.is_empty() {
                return Verdict::NewLemmas(lemmas);
            }
            if budget_hit {
                return Verdict::BudgetExhausted;
            }
            let v = self.saturation_verdict(lang, model, cong);
            if self.cfg.additive_patterns
                && matches!(
                    v,
                    Verdict::Saturated | Verdict::SaturatedUnverified | Verdict::Inconclusive
                )
                && self.augment_parsed_triggers(lang)
            {
                continue; // re-pass: the appended groups rescan from zero
            }
            return v;
        }
    }

    /// One full instantiation pass over every quantifier (CDQI → e-matching →
    /// enumeration per quantifier — the pre-E1 `round_with_cong` body).
    /// Returns the pass's `(lemmas, budget_hit)`; the caller owns the verdict
    /// decision (see the pass-loop invariant in
    /// [`round_with_cong`](Self::round_with_cong)).
    fn instantiation_pass<L, M, C>(
        &mut self,
        lang: &mut L,
        model: &M,
        cong: &C,
    ) -> (Vec<S::Term>, bool)
    where
        L: TermLang<Sig = S>,
        M: ModelEval<L>,
        C: Congruence<S>,
    {
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
            // Wall-clock guard at the loop head: bounds the between-quant work
            // (CDQI, enumeration, lazy trigger inference) as well as the
            // e-match itself. MUST route through `budget_hit` — a bare `break`
            // with zero lemmas would fall through to the saturation verdict
            // and a parsed-trigger quantifier that never got its e-match this
            // round would be read as saturated → spurious `Sat`.
            if self.deadline_hit() {
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
                let (bindings, ematch_aborted) = self.ematch_all(lang, qi, cong);
                // E1 ever-fired gate (#425): record that this quantifier's
                // trigger has matched at least once. Any non-empty binding
                // set counts — even from an ABORTED e-match (a match is a
                // match; the abort only says the set is partial). CDQI
                // conflict hits deliberately do NOT set this: they bypass
                // the trigger entirely, so they say nothing about the
                // pattern's matchability. A quantifier whose parsed trigger
                // NEVER fires loses the trigger-semantics saturation
                // exemption (see `saturation_verdict`).
                if !bindings.is_empty() {
                    self.quants[qi].matched = true;
                }
                // Deadline/`max_match_substs` abort: the match set is PARTIAL.
                // Route it into `budget_hit` (→ `BudgetExhausted` when the
                // round yields no lemmas) so an aborted e-match can never be
                // read as "added nothing ⇒ saturated" — THE spurious-Sat risk
                // (parsed-trigger quantifiers are exempt from the per-quant
                // saturation verify loop below, and the host's
                // `verify_clean_saturated` re-solve does not re-run
                // e-matching, so nothing downstream would catch it).
                if ematch_aborted {
                    budget_hit = true;
                }
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
                //
                // On an ABORTED e-match the watermark must NOT advance: the
                // frontier was only PARTIALLY consumed, and sweeping past the
                // unscanned seeds would lose their matches forever — a later
                // round (same check, e.g. after a `max_match_substs` abort
                // whose lemmas kept the solve alive) would then see an empty
                // frontier, add nothing, and saturate with a violating
                // instance still undiscovered → spurious `Sat`. Re-scanning
                // the whole span next round is idempotent (`emit` dedups).
                if !ematch_aborted {
                    self.scanned[qi] = round_start;
                }
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
        (lemmas, budget_hit)
    }

    /// The saturation verdict for a pass that emitted nothing and hit no
    /// budget — NEVER anything that mints lemmas or a `Sat`/`Unsat`:
    ///  * `Saturated` iff every non-exempt ACTIVE quantifier is
    ///    model-verified (`Some(true)`);
    ///  * `Inconclusive` (dominates) if any obligation is model-REFUTED
    ///    (`Some(false)`) or an unbounded existential is undischargeable;
    ///  * `SaturatedUnverified` (#425 phase 2) otherwise, when ≥ 1 obligation
    ///    is merely UNVERIFIABLE (`eval_forall` = `None`) — nothing failed,
    ///    but the exemption/verification ledger has a hole, so the host may
    ///    confirm the accumulated ground set (trusting only a ground UNSAT)
    ///    and must never conclude `sat`.
    ///
    /// Every ACTIVE quantifier must be POSITIVELY justified — since #426 there
    /// is no purely syntactic "its `:pattern` stopped firing" justification
    /// left (inactive ones are vacuously satisfied). The host's synthetic
    /// witnesses never cross into the engine → nothing fabricated.
    ///
    /// NOTE: a bounded-guard FINITE quantifier (`∀x̄. (lo≤x̄≤hi ⇒ φ)`) is NOT
    /// auto-satisfied just because all its instances were emitted. The earlier
    /// "finite exhaustion ⇒ sat" shortcut trusted that `Saturated` implied the
    /// ground solve had a CONSISTENT model of those instances — but the
    /// incremental CDCL(T) can MISS a conflict that is GLOBAL across the
    /// instances (e.g. pigeonhole: `n+1` holes pairwise-distinct in `[1,n]` is
    /// unsat, yet the incremental model stays `sat`), so the shortcut reported
    /// a spurious `sat`. The bounded enumeration still defuses the
    /// `f`-tower (no hang); the VERDICT defers to `eval_forall`, which is
    /// sound (a bounded quantifier it cannot verify yields the sound
    /// `Unknown`, never a guessed `Sat`).
    fn saturation_verdict<L, M, C>(&self, lang: &L, model: &M, cong: &C) -> Verdict<S::Term>
    where
        L: TermLang<Sig = S>,
        M: ModelEval<L>,
        C: Congruence<S>,
    {
        // #425 phase 2: an `eval_forall` `None` no longer short-circuits into
        // `Inconclusive` — it is RECORDED and the scan continues, so a later
        // model-REFUTED obligation (`Some(false)`) still dominates with
        // `Inconclusive`. Only at the end does "unverified but nothing
        // failed" become `SaturatedUnverified`.
        let mut unverified_seen = false;
        for qi in 0..self.quants.len() {
            let q = &self.quants[qi];
            // An INACTIVE quantifier (`Q` not asserted true in the model) is
            // vacuously satisfied — the ONLY unconditional exemption left.
            if !model.is_active(lang, q.term) {
                continue;
            }
            // #426 — the trigger-semantics exemption is now PROVISIONAL.
            //
            // A PARSED, UNAUGMENTED trigger that has actually FIRED used to be
            // exempt from model verification outright: "e-matching added
            // nothing" was read as "trigger semantics satisfy this". #425
            // closed the NEVER-fired half of that (a dead / ill-arity /
            // shape-unmatched pattern justifies nothing, since its quantifier
            // was never instantiated even once). #426 is the residual half: a
            // trigger that fires but is INSUFFICIENT — it matches *something*,
            // just not enough to derive the contradiction — is equally no
            // justification, and the engine reported `Saturated` → the host
            // `sat` on genuinely UNSAT problems.
            //
            // SMT-LIB `:pattern` is a heuristic annotation, not semantics:
            // `(! φ :pattern p)` IS `φ`. So an e-match fixpoint is only ever
            // evidence that the INSTANTIATION HEURISTIC is exhausted, never
            // that `φ` holds. Both references agree — on the #426 repro z3
            // falls through to MBQI and answers `unsat`, cvc5 answers
            // `unknown`; neither ever answers `sat`.
            //
            // So the quantifier stays in the scan and must earn `Saturated`
            // POSITIVELY (finite guard box, or `eval_forall`/model-completion
            // `Some(true)`). What it keeps over a true obligation is only the
            // FAILURE handling: a `Some(false)` here does NOT dominate into
            // `Inconclusive` (see the `provisional` arm below).
            let provisional =
                !q.triggers.is_empty() && !q.inferred && !q.augmented && q.matched && q.universal;
            if provisional && !self.cfg.strict_pattern_saturation {
                // Pre-#426 lax exemption (`OXIZ_MBQI_LAX_PATTERN_SAT=1`
                // A/B kill-switch only — this is the unsound direction).
                continue;
            }
            // A BOUNDED-FINITE quantifier emitted ALL its instances over the
            // guard's box, so it is FULLY captured: a `∀`'s box conjunction
            // (`⋀_{t̄∈D} φ[t̄]`) or a `∃`'s box disjunction (`⋁_{t̄∈D} φ[t̄]`,
            // emitted as one lemma). Both defer the verdict to the ground solver
            // via `Saturated` — and for the `∀` direction the SOLVER confirms
            // that `Saturated` with a single-shot re-solve (the incremental
            // `Saturated`→`Sat` alone was the #277 spurious-sat; the re-solve is
            // sound now that it carries the logic). The `∃` disjunction is the
            // easy satisfiability direction and needs no re-solve.
            if self.bounded_finite(qi) {
                continue;
            }
            // An UNBOUNDED existential emitted nothing and is unverified → the
            // sound `Unknown`, NEVER a guessed `Sat`. `eval_forall` is a
            // `∀`-only recognizer and must not run on an `∃`.
            if !q.universal {
                return Verdict::Inconclusive;
            }
            let ev = model.eval_forall(lang, cong, q.term);
            if provisional && ev != Some(true) && std::env::var_os("OXIZ_MBQI_DBG").is_some() {
                eprintln!(
                    "[mbqi-dbg] quant {qi}: #426 provisional parsed-trigger exemption WITHDRAWN \
                     (eval_forall={ev:?}) -> SaturatedUnverified"
                );
            }
            match ev {
                Some(true) => {}
                // #426 — a model-REFUTED PROVISIONAL quantifier must NOT
                // dominate into `Inconclusive`. `Inconclusive` is the host's
                // bare `Unknown`: it skips the accumulated-instance ground
                // confirm that `SaturatedUnverified` runs, and that confirm is
                // exactly what rescues the under-triggered UNSAT rows (E1
                // measured the corpus depending on it). Demoting instead to
                // `SaturatedUnverified` is equally sound — every emitted
                // instance is a guarded ground consequence `Q ⇒ φ[t̄]`, so a
                // single-shot ground UNSAT over them proves the input unsat
                // regardless of what any model claims — and strictly more
                // complete. `Some(false)` on a real OBLIGATION keeps its
                // pre-#426 dominating `Inconclusive`.
                Some(false) if provisional => unverified_seen = true,
                Some(false) => return Verdict::Inconclusive,
                None => {
                    // P4 model-completion backstop: the structural recognizers
                    // could not verify this saturated universal — give CCFV `¬ψ`
                    // over the total view `E_TOT` the final word. No conflict ⇒
                    // the completed model satisfies it (`Some(true)`) → this
                    // quantifier is satisfied. Any conflict / undecidable
                    // lowering / unmet gate ⇒ `None` here too → the unverified
                    // bucket below. Gated (default off): with the flip disabled
                    // this is exactly the plain `None ⇒ unverified` path.
                    if self.cfg.ccfv_model_compl
                        && model.model_completion(lang, cong, q.term) == Some(true)
                    {
                        continue;
                    }
                    // Could be neither exempted nor verified — but nothing
                    // FAILED either. Record and keep scanning (a later
                    // `Some(false)` must still dominate with `Inconclusive`).
                    unverified_seen = true;
                }
            }
        }
        if unverified_seen {
            Verdict::SaturatedUnverified
        } else {
            Verdict::Saturated
        }
    }

    /// E1 additive-patterns augmentation (#425): for each PARSED-trigger
    /// universal not yet augmented (and not inferred — inference already owns
    /// those groups), run [`infer_triggers`] over its `(vars, body)` and
    /// APPEND the groups not already present (dedup by exact term-vec
    /// equality — hash-consed terms make that structural). The parsed groups
    /// are never touched: the mode is strictly additive.
    ///
    /// `augmented` is set UNCONDITIONALLY (once per quantifier), even when
    /// inference finds nothing or only duplicates — that bounds the
    /// `round_with_cong` pass loop (a pass in which nothing was appended
    /// returns `false`, and no quantifier is ever re-augmented).
    ///
    /// On any actual append, `scanned[qi]` is reset to 0 (MANDATORY): the
    /// frontier watermark advanced past the ground seeds while only the
    /// parsed (non-firing) groups were scanned, so the appended groups must
    /// see the WHOLE index. The rescan is idempotent via `emit`'s
    /// `(qi, tuple)` dedup.
    fn augment_parsed_triggers<L: TermLang<Sig = S>>(&mut self, lang: &L) -> bool {
        let mut appended_any = false;
        let dbg = std::env::var_os("OXIZ_MBQI_DBG").is_some();
        for qi in 0..self.quants.len() {
            {
                let q = &self.quants[qi];
                if !q.universal || q.triggers.is_empty() || q.inferred || q.augmented {
                    continue;
                }
            }
            let trg = infer_triggers(lang, &self.quants[qi].vars, self.quants[qi].body);
            self.quants[qi].augmented = true; // unconditionally — once per quant
            let mut appended = 0usize;
            for g in trg {
                if !self.quants[qi].triggers.contains(&g) {
                    self.quants[qi].triggers.push(g);
                    appended += 1;
                }
            }
            if appended > 0 {
                self.scanned[qi] = 0;
                appended_any = true;
            }
            if dbg {
                eprintln!(
                    "[mbqi-dbg] quant {qi}: additive augmentation appended {appended} inferred group(s)"
                );
            }
        }
        appended_any
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
    ///
    /// The second return value is the ABORT flag: `true` when any group's CCFV
    /// match was cut short by the engine deadline or `cfg.max_match_substs`
    /// (the bindings are then a PARTIAL match set). The caller MUST fold it
    /// into `budget_hit` and, on abort, must NOT advance the frontier
    /// watermark — see the call site in [`round_with_cong`](Self::round_with_cong).
    fn ematch_all<L: TermLang<Sig = S>, C: Congruence<S>>(
        &self,
        lang: &L,
        qi: usize,
        cong: &C,
    ) -> (Vec<Vec<(S::VarName, S::Term)>>, bool) {
        let q = &self.quants[qi];
        let watermark = self.scanned[qi];
        let holes: Vec<S::VarName> = q.vars.iter().map(|(n, _)| *n).collect();
        let mut out = Vec::new();
        let mut aborted = false;
        for group in &q.triggers {
            let (raw, group_aborted): (Vec<ccfv::Subst<S>>, bool) = if group.len() == 1 {
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
                    ccfv::match_trigger(
                        cong,
                        lang,
                        group[0],
                        &holes,
                        &cands,
                        self.deadline,
                        self.cfg.max_match_substs,
                    )
                } else {
                    ccfv::match_trigger(
                        &NoCong,
                        lang,
                        group[0],
                        &holes,
                        &cands,
                        self.deadline,
                        self.cfg.max_match_substs,
                    )
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
                    ccfv::match_trigger_multi(
                        cong,
                        lang,
                        group,
                        &holes,
                        &seeds,
                        self.deadline,
                        self.cfg.max_match_substs,
                    )
                } else {
                    ccfv::match_trigger_multi(
                        &NoCong,
                        lang,
                        group,
                        &holes,
                        &seeds,
                        self.deadline,
                        self.cfg.max_match_substs,
                    )
                }
            };
            aborted |= group_aborted;
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
        (out, aborted)
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
            InstResult::Rejected => {
                if std::env::var_os("OXIZ_MBQI_DBG").is_some() {
                    eprintln!("[mbqi-dbg] quant {qi}: instance REJECTED");
                }
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

/// E1 static `:pattern` validation (#425): drop `group` only when it is
/// PROVABLY unmatchable / provably useless for instantiation. Per-member
/// classification, by one-level view:
///
///  * `Var` — a bare variable (a bound var of this quantifier, or a host
///    constant modelled as a `Var` node) can never head an e-match
///    (`ematch_all` fires only on `App`-viewing patterns), so the member is
///    provably unmatchable → the GROUP is invalid (as before). A bare
///    literal is equally unmatchable, but the generic view cannot
///    distinguish a literal from an unclassified host node — both present as
///    `Opaque` — so literals land in the conservative bucket below.
///  * `App` — ANALYZABLE: its bound-var coverage is computed by the walk.
///  * anything else (`Opaque` / unclassified — e.g. the datatype
///    constructor/selector/tester applications the OxiZ bridge does not yet
///    classify, which view as `Opaque` with no visible children) —
///    UNANALYZABLE: the gate must NEVER drop what it cannot reason about.
///    The group is KEPT, and the union-coverage requirement below is
///    enforced ONLY when every member (and every subterm the walk reaches)
///    is analyzable — an unanalyzable member/subterm may cover bound vars
///    through children the bridge cannot see (the dm3 misdrop: 3 live
///    Dt-headed groups viewed as `Opaque` leaves and were dropped).
///    A kept-but-actually-unmatchable group costs NO soundness: it never
///    fires, so the dynamic ever-fired gate (`Quant::matched`) strips its
///    trigger-semantics saturation exemption → `SaturatedUnverified`, never
///    a spurious `Sat`. The cost is completeness only (a kept group blocks
///    the lazy-inference fallback; the additive mode recovers it).
///
/// When every member is fully analyzable, the group is retained iff the
/// union of bound vars covered across the group equals the full `vars` set.
/// An under-covering all-analyzable group can never yield an instance
/// (`ematch_all`'s fullness filter drops partial bindings), so dropping it
/// only removes its unsound saturation exemption. NOTE: an individual member
/// MAY be hole-free (a ground `App` matches via the empty substitution) — a
/// multipattern group is matchable as long as its UNION covers, so a
/// per-member bound-var requirement would drop live groups and lose their
/// instances (a soundness regression, not a conservative narrowing). Dead
/// symbols and ill-arity patterns are NOT statically decidable here (no
/// declaration table); the dynamic ever-fired gate covers those.
///
/// FOLLOW-UP (the principled upgrade): classify Dt constructor / selector /
/// tester applications as `App` views WITH children in the OxiZ bridge
/// (`clean_mbqi.rs` `view`/`children`) — real e-match capability for
/// Dt-headed triggers instead of this conservative keep. That is a separate
/// slice with its own corpus gate: the blast radius is the whole MBQI
/// traversal (every `view`/`children` consumer — ground index, CCFV,
/// inference, CDQI), not just this gate.
fn valid_pattern_group<S: Sig, L: TermLang<Sig = S>>(
    lang: &L,
    vars: &[(S::VarName, S::Sort)],
    group: &[S::Term],
) -> bool {
    if group.is_empty() {
        return false;
    }
    let bound: FxHashSet<S::VarName> = vars.iter().map(|(n, _)| *n).collect();
    let mut covered: FxHashSet<S::VarName> = FxHashSet::default();
    let mut all_analyzable = true;
    for &p in group {
        match lang.view(p) {
            // A bare variable can never head a match — provably unmatchable.
            TermView::Var { .. } => return false,
            TermView::App { .. } => {}
            // Opaque / unclassified (incl. a pattern-level binder): the gate
            // cannot reason about this member — conservative keep.
            _ => {
                all_analyzable = false;
                continue;
            }
        }
        let mut seen: FxHashSet<S::Term> = FxHashSet::default();
        let mut stack: Vec<S::Term> = vec![p];
        while let Some(t) = stack.pop() {
            if !seen.insert(t) {
                continue;
            }
            match lang.view(t) {
                TermView::Var { name } if bound.contains(&name) => {
                    covered.insert(name);
                }
                TermView::Var { .. } => {}
                // A pattern containing a binder never matches a ground term;
                // do not descend (mirrors `infer_triggers`).
                TermView::Quant { .. } => {}
                TermView::App { .. } => stack.extend(lang.children(t)),
                // An unclassified SUBTERM taints the member too: `children`
                // returns nothing for it, so bound vars may hide beneath
                // (e.g. `(f (Cons x y))` under the OxiZ bridge — the `App`
                // head is visible but the Dt-constructor child is an opaque
                // wall). Coverage cannot be decided → do not enforce it.
                _ => all_analyzable = false,
            }
        }
    }
    !all_analyzable || covered.len() == bound.len()
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
