# CCFV — a unified instantiation core for the clean-MBQI engine

*Design sketch. Adopt E-ground (dis)unification (Barbosa–Fontaine–Reynolds,
TACAS 2017, "Congruence Closure with Free Variables") as the single candidate
source behind the clean-MBQI engine, so trigger e-matching, conflict-driven
instantiation, and model-based instantiation all become **parameterizations of
one calculus**. This closes both open fronts at once: (a) prelude-scale
saturation and (b) the completeness recognizers.*

Companion to `REAL_MODEL_CONSTRUCTION.md` (the recognizers this generalizes) and
to the MBQI research library (`<adsmt root>/.claude-research-library/`,
CCFV = `2017-Barbosa-Fontaine-Reynolds-TACAS-…CCFV.pdf`).

---

## 0. Thesis

The engine has **three** instantiation strategies that each do the same three
things (enumerate candidates → unify/substitute → gate for soundness) with
separate code:

| strategy | candidate source | matching | file |
|---|---|---|---|
| trigger e-matching | `ground.with_head(f)` (syntactic) | `trigger::match_term` (recursive, **congruence-blind**) | `oxiz-mbqi/src/trigger.rs` |
| CDQI (conflict) | `ground.of_sort(s)` odometer | model `eval_bool` per tuple | `oxiz-mbqi/src/cdqi.rs` |
| enumeration | `ground.of_sort(s)` | — (direct substitution) | `oxiz-mbqi/src/engine.rs:307` |

CCFV solves the single problem **E-ground (dis)unification**: *given the ground
congruence `E` and a constraint `C` with free (bound) variables, find every
substitution `σ` with `E ⊨ Cσ`.* All three strategies are then **what `C` you
hand it**:

- triggers → `C = ⋀ᵢ (pᵢ ≃ yᵢ)` (the `:pattern` terms), all `yᵢ` ground;
- conflict → `C = ¬ψ` (the negated matrix) — and CCFV finds **all** conflicting
  instances, not the one the odometer happens to hit first;
- MBQI / model-completion → `C = ¬ψ` solved against the **total** model
  extension `E_TOT` (default values + all-pairs disequalities), lazily.

One core, three call sites. The soundness firewall (`instantiate` →
`emit`) is **unchanged**: CCFV is a smarter *source* of bindings behind the same
gate, and the engine still `Verdict`s `NewLemmas | Saturated | Inconclusive |
BudgetExhausted` — **never `Unsat`**.

---

## 1. Where we are

### 1.1 The abstraction boundary is already right
`oxiz-mbqi` is split (`term.rs`):
- **`Sig`** — lifetime-free identity: `Term, Sort, VarName, Sym` (all `Copy+Eq+Hash`).
- **`TermLang`** — behavioural: `view / children / patterns / sort_of /
  substitute / mk_implies / mk_or / bounded_var_domains`.

The engine (`Engine<S>`) is generic over `Sig`; the host (`OxizHost<'a>` in
`oxiz-solver/src/clean_mbqi.rs`) provides `TermLang` + `ModelEval` per round.
CCFV slots in **behind this boundary** — it needs exactly one new capability the
boundary does not yet expose: a **congruence oracle**.

### 1.2 The gap CCFV fills
The MBQI engine's `GroundIndex` (`ground.rs`: `by_head`, `by_sort`, `idx`
frontier) is **syntactic and decoupled from EUF**. So today's "e-matching" is
`match_term` over `with_head(f)` candidates — it does **not** match modulo the
congruence. Two terms in the same EUF class but syntactically distinct are
invisible to it. That is both an incompleteness (missed matches) and, more
importantly for (a), the reason we cannot do the CCFV **entailed-instance
discard** (`E ∪ E_σ ⊨ ℓ`) that stops re-deriving already-satisfied prelude
axioms.

### 1.3 The congruence infrastructure already exists
`oxiz-theories/src/euf/solver.rs` already has the `E^cc` index CCFV's paper
calls for:
- `sig_table: (func, [canonical_args]) → node` — the signature class.
- `function_application_entries(f) -> Vec<FuncAppEntry>` — every `f`-application
  in congruence-closed form (`arg_reps`, `arg_class_terms`, `result_rep`,
  `result_class_terms`), single O(nodes) pass.
- `class_members(rep)`, `find(t)`, `are_equal(a,b)`, `all_func_symbols()`.

CCFV does **not** need a new congruence engine — it needs a thin oracle that
re-exports these to the `oxiz-mbqi` side.

---

## 2. The CCFV core

### 2.1 Problem (paper Def. / Thm 1)
`E` is a set of ground equalities (the EUF congruence); `C` is a DNF of
(dis)equality literals over free variables `x̄`. **E-ground (dis)unification**:
enumerate substitutions `σ` (grounding `x̄` to terms in `E`) with `E ⊨ Cσ`.
NP-complete; the solution set is finitely representable. Sound, complete,
terminating.

### 2.2 State
A search state is `E_σ ⊩_E C`:
- `E_σ` — the partial solution so far (a conjunctive substitution / set of
  `x ≃ t` bindings, normalised through congruence representatives `rep`).
- `C` — the remaining DNF constraint, rewritten under `E_σ`.

### 2.3 Rules (paper Table 1, condensed)
Decompose `C` top-down, accumulate into `E_σ`:

- **ASSIGN** — move a forced binding `x ≃ s` into `E_σ`; renormalise `C` by
  rewriting to congruence representatives `rep`.
- **U_VAR / U_COMP / U_GEN** (equality branches) — enumerate the ways
  `f(s̄) ≃ y` can be entailed: by syntactic unification of args, or by matching a
  different `f`-application in the **same signature class** (via
  `function_application_entries(f)`), bit-mask-filtered for fast candidate retrieval.
- **R_VAR / R_FAPP / R_GEN** (disequality duals) — the same for `≄`.
- **SPLIT** — branch a disjunction.
- **FAIL** — eagerly discard a branch that can no longer be entailed (e.g. an
  `f`-application whose ground args fail congruence) — the key pruning.
- **YIELD** — close a branch as a solution when `E ∪ E_σ ⊨ C`.

Termination: a well-founded measure on the decreasing variable-depth `d(C)`.

### 2.4 The signature-class index `E^cc`
`function_application_entries(f)` *is* `E^cc` for symbol `f`. CCFV's
U_COMP/U_GEN ask "which `f(t̄)` live in `E`, grouped by arg-class?" — answered in
one pass. The bit-mask pre-filter (paper) maps onto EUF's `fingerprint_table`
(already a 64-bit pre-filter before the sig-table lookup). **No new index.**

---

## 3. The three strategies as parameterizations

```
fn instantiate_quant(q, mode) -> impl Iterator<Item = Binding> {
    let C = match mode {
        Mode::Trigger     => conj(q.triggers.map(|p| Eq(p, fresh_out_var()))),
        Mode::Conflict    => negate(q.body),          // all conflicting instances
        Mode::ModelCompl  => negate(q.body),          // solved against E_TOT
    };
    let cong = match mode {
        Mode::ModelCompl  => CongruenceView::Total(default_values, all_pairs_diseq),
        _                 => CongruenceView::Ground,  // the real EUF congruence
    };
    ccfv::solve(cong, C)            // yields every σ with E ⊨ Cσ
        .filter(|σ| mode != Mode::Trigger || !cong.entails(q.body, σ))  // discard
}
```

- **Trigger** — `C` is the conjunction of `:pattern` terms equated to fresh
  ground output variables; CCFV grounds them by matching in `E^cc`. The
  **discard** post-filter (`E ∪ E_σ ⊨ ℓ`) is the (a) lever: drop instances the
  model already satisfies before they re-enter the loop.
- **Conflict (CDQI)** — `C = ¬ψ`. CCFV returns **all** conflicting `σ`, replacing
  `cdqi::find_conflict`'s odometer-finds-one. (The 2014 CDQI flat-form
  `µ ⇒ ϕ` falsify/match split *is* CCFV's ASSIGN+branch structure — we already
  ported a special case in #229; this generalises it.)
- **Model-completion (MBQI)** — `C = ¬ψ` against `E_TOT`: extend each `f` with a
  lazy default value `ξ_f` and add all-pairs disequalities among representatives.
  If CCFV finds **no** `σ` with `E_TOT ⊨ ¬ψσ`, the completed model satisfies
  `∀x̄.ψ` → the host may return `Some(true)` from `eval_forall`. This is the
  principled, **complete** version of the hand-written recognizers in
  `REAL_MODEL_CONSTRUCTION.md`.

---

## 4. How (a) and (b) both fall out

### (a) prelude-scale saturation
1. **Congruence-aware lookup** — candidates come from `E^cc` (sig classes), not
   syntactic `with_head`, so redundant syntactic variants collapse to one class.
2. **Entailed-instance discard** — `E ∪ E_σ ⊨ ℓ` drops instances already true in
   the model *before* they are emitted; the prelude stops re-deriving its
   thousands of satisfied frame axioms each round. This is the single biggest
   saturation lever (paper: the `cvc+d`/`cvc+e` gains).
3. **Conflict-first stays, now complete** — the engine already runs CDQI before
   e-matching; with CCFV it finds all conflicts in one decision procedure, so a
   goal-relevant refutation is reached without first saturating.
4. Layer the 2007 e-matching **code-tree + inverted-path index** *on the
   sig-class lookup* (separate follow-up) for O(query-delta) re-match — composes
   with the AOT prelude reuse already shown to give 37× on the abduce path.

### (b) completeness recognizers
The `Mode::ModelCompl` parameterization is a **general model-completion
backstop**: where a hand recognizer in `eval_forall` does not fire, CCFV against
`E_TOT` either (i) finds a conflicting `σ` → emit it (refine the model), or (ii)
finds none → the completed model is a witness → sound `Some(true)`. The existing
recognizers stay as **fast paths**; CCFV is the principled fallback that turns
their gaps (current `Unknown`) into sound `Sat` whenever the completion has no
conflict. The MBP / CEGMS lineage (`REAL_MODEL_CONSTRUCTION.md` §1) supplies the
default-value `ξ_f` choices for arithmetic sorts.

---

## 5. Integration boundary — one new trait

Add a congruence oracle to the `oxiz-mbqi` abstraction; `OxizHost` implements it
by delegating to `EufSolver`. Nothing else in the boundary changes.

```rust
/// Congruence oracle over the ground E-graph. Read-only; the host implements
/// it via EufSolver. CCFV is the sole consumer.
pub trait Congruence<S: Sig> {
    /// Canonical representative of a ground term's class.
    fn rep(&self, t: S::Term) -> S::Term;
    /// Are two ground terms congruent? (E ⊨ a ≃ b)
    fn equal(&self, a: S::Term, b: S::Term) -> bool;
    /// Every application of `f` in E, grouped by argument class — the E^cc index.
    /// (Maps to EufSolver::function_application_entries.)
    fn apps_of(&self, f: S::Sym) -> &[FuncApp<S>];
    /// Members of a class (for disequality / output enumeration).
    fn class(&self, rep: S::Term) -> &[S::Term];
    /// Total-model view for MBQI mode: default value ξ_f for an under-specified
    /// app, lazily; None ⇒ use the real ground congruence. Soundness-gated by
    /// the host (must be a conservative extension — see §6).
    fn default_value(&self, f: S::Sym, args: &[S::Term]) -> Option<S::Term>;
}
```

`ccfv::solve(cong: &impl Congruence<S>, c: Constraint<S>) -> impl Iterator<Item =
Binding<S>>` is the core. The engine's three call sites (`round_with`) replace
`trigger::match_*`, `cdqi::find_conflict`, and `enumerate` with `ccfv::solve(..,
mode)`; every yielded `Binding` still flows through the **unchanged**
`emit`→`instantiate` gate.

> The frontier watermark (`scanned[qi]`, `GroundIndex::idx`) moves into the
> oracle as an "only classes touched since round N" filter, preserving the
> O(delta) re-match the syntactic index gives today.

---

## 6. Soundness — never-conclude-unsat is preserved

CCFV produces **candidate bindings**, never verdicts. The firewall is intact:

1. Every binding still passes `instantiate` (`instantiate.rs:51`), which
   **requires every replacement to be a registered ground term** — CCFV grounds
   `x̄` only to terms in `E`, so this holds by construction.
2. `Mode::ModelCompl` returns `Some(true)` **only when CCFV finds no conflict in
   `E_TOT`**, and `E_TOT` must be a *conservative extension* of `E` (default
   values do not contradict any asserted ground fact). The host enforces this
   with the existing **accounting gate** (`global_occ[f] == body_occ +
   |ground_apps[f]|`) before trusting the completion — same discipline as the
   recognizers. A non-conservative completion ⇒ fall back to `Unknown`.
3. CCFV never asserts `Unsat`; a refutation is the host SAT/ground core's job, as
   today. The `Verdict` enum is unchanged.

This is the same firewall the recognizers already rely on; CCFV moves the
candidate search inside it, it does not move the wall.

---

## 7. Phasing (each gated: `clean_mbqi_corpus --ignored` + `cargo test
--workspace` + verus full-prelude smoke; all user `!` gates)

| phase | scope | risk |
|---|---|---|
| **P0** ✅ **LANDED** (2026-06-20) | `Congruence` trait + `FuncApp` in `oxiz-mbqi/src/congruence.rs`; impl'd by a **new `EufCongruence<'a>` wrapper** in `oxiz-solver/src/clean_mbqi.rs` (NOT on `OxizHost` — it holds no EUF; a borrow-wrapper over `&EufSolver` is non-invasive) delegating to `find_immutable`/`are_equal_immutable`/`class_members`/`function_application_entries`. Keyed off a **witness term** (`apps_like(app)`) so no host-`Sym`(u64) ↔ EUF-func-id(u32) bridge is needed yet (that's P2). Pure addition, no consumer, no behaviour change; 2 delegation tests green (incl. the `f(a)=f(b)`-by-congruence read-back). | low |
| **P1** ✅ **LANDED** (2026-06-20, matching-modulo-congruence half) | `oxiz-mbqi/src/ccfv.rs` — the E-ground **unification** core as `match_trigger(cong, host, pat, holes, seeds) -> Vec<Subst>`: `unify`/`unify_args` recurse a trigger pattern against ground terms through the P0 [`Congruence`] oracle (`rep`/`equal`/`class`). The executable refinement of the verus model — hole bind = ASSIGN (grounded, (ii)); arg recursion = DECOMPOSE (depth-bounded, (iii)); class-member branch = SPLIT; full unify = YIELD, sound because every leaf goes through `equal` ((i)). 5 unit tests incl. **the congruence match the syntactic `trigger::match_term` cannot make** (`f(g(x))` ~ `f(c)` when `c≡g(a)`) + control, non-linear consistency, SPLIT multiplicity, head mismatch. **Behaviour-isolated**: seed enumeration is the caller's (P2) job, so no host-`Sym`↔EUF-func-id concern; produces only candidate `Subst`s (firewall unchanged). **Deferred:** the disequality rules (R_*), full-DNF disjunction SPLIT, and the conflict/MBQI parameterizations (`C = ¬ψ`, `E_TOT`) — those are P3/P4. | med |
| **P2a** ✅ **LANDED** (2026-06-20, engine-side, opt-in) | `engine.rs`: `round_with` now delegates to a new `round_with_cong<L,M,C>(lang, model, cong)` (body moved, +`Congruence` oracle), so the 5 existing callers are untouched; `ematch_all` takes the oracle and, when the new `Config::ccfv_ematch` flag is set, routes **single-pattern** triggers through `ccfv::match_trigger` (congruence-aware) instead of `trigger::match_single`. Flag **default false** + `NoCong` placeholder ⇒ default path **byte-identical** (all existing tests green). New `tests/ccfv_ematch.rs` (3 tests): with the flag on + a real congruence `c≡g(a)`, `f(g(x))` matches `f(c)` (x↦a) where the syntactic path finds nothing; controls confirm it's the congruence, not the code path; firewall holds (rejected=0). Multi-pattern stays syntactic (follow-up). | med |
| **P2b** ✅ **CODE-COMPLETE** (2026-06-20, opt-in; default-flip pending the corpus gate) | Driver wiring landed: `SolverConfig::ccfv_ematch` (new, **default false**, all 4 presets); `(set-option :oxiz.ccfv-ematch true)` SMT-LIB switch (`context.rs`); `mod.rs` builds the engine with the flag and, at the round call, `EufCongruence::new(&self.euf)` (the live post-solve congruence, restored by `restore_theory_manager`) → `round_with_cong`. Default off ⇒ byte-identical (quant-soundness 71 + wiring suites green). **ccfv-on end-to-end smoke** green: `:oxiz.ccfv-ematch true` + `∀a.f(a)=a :pat(f a)` derives `f(3)=4 → unsat` and the consistent `f(3)=3 → sat` through the full live path. **REMAINING (user `!` gate):** run the z3-parity corpus with `:oxiz.ccfv-ematch true` (`clean_mbqi_corpus --ignored`) → confirm no spurious + matches ≥ old, then flip the default + delete `trigger::match_term`. | med |
| **P3** | Re-express **CDQI** as `ccfv::solve(Ground, ¬ψ)` (all conflicts). Delete `cdqi`'s odometer. Validate: #229 regressions hold; conflict count ≥ old. | med |
| **P4** | Add **`Mode::ModelCompl`** (`E_TOT`) as the general `eval_forall` backstop behind the recognizers. Target: ≥1 current corpus `Unknown` → sound `Sat`, **0 spurious**. | high (soundness) |
| **P5** | **Entailed-instance discard** + (separately) the 2007 code-tree/inverted-path index on the sig-class lookup. Measure the full-prelude `(abduce)` wall (target: < 75 s; combine with AOT). | med |

Each phase is independently shippable and independently revertible. P0–P3 are
**refactors** (same verdicts, less code, congruence-correct); P4 is the (b)
completeness win; P5 is the (a) performance win.

---

## 8. Pre-verification hook (선검증)

CCFV is sound + complete + terminating *in the paper*. The
`[선검증 → 구현 → 후검증]` discipline (see `oxiz_redesign_verification_pipeline`)
applies: before P1 lands, pre-verify in the `oxiz-sat-redesign-verification`
Verus project the three CCFV invariants we actually depend on — **(i)
YIELD-soundness** (`E ∪ E_σ ⊨ C` at every yield), **(ii) grounding** (every
yielded `σ` maps `x̄` into `T(E)`), **(iii) termination** (the `d(C)` measure
strictly decreases). (i)+(ii) are what keep the never-conclude-unsat firewall
intact under the new candidate source; (iii) bounds the inner search (the
*outer* MBQI loop's termination is a separate concern — the 2024
non-generative/generative/nested classification, a P5+ follow-up).

---

## 9. Open questions

1. **GroundIndex vs EUF sync.** The engine indexes ground subterms of asserted +
   *emitted* lemmas; EUF indexes asserted ground terms. Confirm EUF observes every
   emitted instance's ground terms before the next CCFV round (it should — emitted
   lemmas are asserted), else CCFV's `E` lags the engine's candidate set. Likely a
   "re-assert emitted lemmas into EUF before round" ordering constraint.
2. **`E_TOT` cost.** All-pairs disequalities among class representatives is O(n²);
   keep it **lazy** (materialise a diseq only when a branch needs it) per the paper.
3. **Default-value choice for arithmetic.** `ξ_f` for Int/Real sorts wants the
   MBP/`REAL_MODEL_CONSTRUCTION.md` defaults (constant / sup-of-guard / identity),
   not a single sentinel — wire the recognizers' `δ` as `default_value`.
4. **Perf vs the syntactic matcher.** CCFV's branching + congruence bookkeeping is
   heavier per match than `match_term`; the FAIL eager-prune + fingerprint
   pre-filter must carry it. Bench P2 against the current matcher before deleting it.
5. **Existential / nested quantifiers.** ∃ are host-skolemised before the engine;
   confirm CCFV's free-variable scope aligns with the existing
   `emit_existential_disjunction` path (CCFV handles the matrix, not the prefix).

---

---

## 10. Open question §9.1 resolved — the `GroundLedger` (desync made unrepresentable)

> **Status (2026-06-20): the GroundLedger SPIKE is LANDED** (data structure +
> invariant, tested in isolation; pure addition, no live wiring yet — the *port*
> onto EUF follows the project's spike→port precedent). `oxiz-mbqi/src/ledger.rs`:
> `trait CongruenceSink<S>` (store B: `insert`/`checkpoint`/`rollback_to`) +
> `GroundLedger<S, B>` (owns `GroundIndex` + the sink **privately**; sole writer
> `register`, sole rollback `rollback_to`, each touches both) + `LedgerMark`.
> `GroundIndex` gained an **additive scoped rollback** (`order` field +
> `rollback_to(frontier)`; the live monotone engine never calls it). 3 tests prove
> the lock-step invariant via a `MirrorSink` (a second independent `GroundIndex`
> that stays byte-identical only because the ledger funnels both): register +
> rollback, nested checkpoints, re-register-after-rollback. `cargo test -p
> oxiz-mbqi` green; `oxiz-solver` (the `GroundIndex` consumer) builds + tests
> green. **Deferred to the port:** the live `EufSink` impl of `CongruenceSink`
> (interning is entangled with the theory manager), and hanging the ledger off the
> CDCL trail spine (§10.3 ②). The spike establishes the desync-proof structure;
> P1+ consumes it.

### 10.1 Why a special data structure is needed
The two indices CCFV bridges are **not** two views over one event stream — they
are owned by two subsystems, fed by two drivers, at two phases, with **opposite
backtracking semantics**:

| | `GroundIndex` (oxiz-mbqi) | EUF `term_to_node` (oxiz-theories) |
|---|---|---|
| owner / driver | MBQI `Engine` | `TheoryManager` (CDCL theory callback) |
| keyed on | `TermId` identity + sort + head bucket | structural congruence signature `(func, arg-class-reps)`; many TermIds collapse to one node |
| seeded | whole `assertions` at engine build (`oxiz-solver/.../mod.rs:610`) + per emitted lemma (`engine.rs:383,458`) | per literal *assigned* during search (`theory_manager.rs:1263…`) |
| backtracking | **monotone — no pop** (only grows) | **full push/pop**; `pop` does `term_to_node.retain(idx < num_nodes)` (`euf/solver.rs:1121`) |

The sharpest desync: an EUF `pop` *removes* a term from `term_to_node` while it
stays permanently in `GroundIndex` — so CCFV, querying a candidate from the
ground side, can match against a congruence class EUF has already discarded.
Guarding each call site cannot fix a *class* of desync; the structure must.

### 10.2 The design — one funnel, two private stores, one scoped log
Borrow Pattern A (ScopedRollback single-append + truncate-that-yields,
`portable-collection-primitives/.../scoped_log.rs` + `vec_scoped_stack.rs`) and
Pattern B (the four-writer spine — one growth writer, one shrink spine, all
writers route through it, invariant by construction, `oxiz-sat/src/trail.rs`).

```rust
/// THE single registration funnel. GroundIndex and the EUF term→node map are
/// private behind it — no solver code can mutate one without the other,
/// because there is no other mutator (Pattern B: "no second writer").
pub struct GroundLedger {
    index: GroundIndex,                       // store A (sort/head buckets, frontier idx)
    euf:   EufView,                           // store B (intern → node/class)
    log:   VecScopedStack<GroundEntry>,       // Pattern A undo ledger
}
struct GroundEntry { term: TermId, node: u32 } // both undo handles, captured together

impl GroundLedger {
    /// SOLE WRITER. One call = append A + intern B + log, fired together.
    pub fn register(&mut self, lang: &impl TermLang, t: TermId) -> TermId {
        self.index.add_term(lang, t);                       // A
        let node = self.euf.intern(t);                      // B (atomic with A)
        self.log.push(GroundEntry { term: t, node });       // ledger
        t
    }
    pub fn checkpoint(&self) -> Checkpoint { self.log.checkpoint() }   // = one length
    /// SOLE ROLLBACK. drain_since yields each undone entry LIFO; the loop drops
    /// it from BOTH stores in lock-step — neither can outlive the other.
    pub fn rollback_to(&mut self, m: Checkpoint) {
        for e in self.log.drain_since(m) { self.euf.retract(e.node); self.index.remove(e.term); }
    }
}
```

### 10.3 The three decisions that make it correct
1. **Canonical key = `TermId`** (GroundIndex's identity). EUF's node-collapse is
   recorded as a *derived* relation (`TermId → node/class`), **not** as identity
   merge — so congruence collapse (`f(a)≡f(b)`) is a value-level equivalence the
   CCFV oracle reads off the class, never an index desync. (Resolves R1's "must
   decide which identity is canonical.")
2. **Hang the ledger off the CDCL trail spine, don't be a fifth writer**
   (Pattern B's lesson — the `backtrack_to_size`/`clear` bypass bug). `register`
   fires from `assign_hook`/the assertion seed; `rollback_to` fires from
   `pop_frame`/`unassign_hook`. The ground-term scope then tracks decision level
   **by construction**, exactly as `|theory frames| == decision_level+1` holds.
   This *removes* the monotone-vs-scoped asymmetry: GroundIndex stops being
   independently monotone — it inherits EUF's scope through the shared log.
3. **The MBQI engine's "candidates accumulate across rounds" is preserved**
   because MBQI rounds happen at a *fixed* scope (no decision-level push between
   instantiation rounds); the ledger only rolls back on an actual `(pop)` /
   backjump — which is exactly when EUF rolls back too. So the within-check-sat
   monotonicity the engine relies on and the across-scope retraction EUF needs
   are the *same* ledger, not two policies.

**Invariant gained by construction:** `GroundIndex` and EUF always hold the same
ground-term set at every scope — the cross-store desync class is unreachable, not
guarded. This *is* the substance of P0: the `Congruence` trait (§5) is backed by
`GroundLedger`, so OxizHost delegates to **one** scoped store, not two.

> Anchors: funnel chokepoints `ground.rs:127` (`register`) and `euf/solver.rs:369/385`
> (`intern`/`intern_app`); EUF pop `euf/solver.rs:1065-1149`; spine `trail.rs:326-365`;
> ScopedStack `vec_scoped_stack.rs:76-111`.

---

## 11. Open question §9.4 resolved — AOT + algebraic-JIT acceleration of CCFV

The prelude's congruence backbone is **goal-independent and monotone**: a query
goal only *adds* ground terms / congruences on top of the fixed prelude E-graph.
That is exactly the "prelude = method, query = trace" shape the AOT/JIT machinery
already exploits for the SAT core (`adsmt-engine/src/solver.rs`,
`portable-algebraic-aotjit`). Four reuse layers, each mapping onto an existing
mechanism:

1. **Bake the prelude E^cc + ground-term set** — add a trailing **v1.4
   `prelude_ccfv_index: Option<…>`** field to `CdclSection`
   (`adsmt-aot/src/cdcl.rs:144`), written by a new `dump_ccfv_state` (analogous to
   `dump_cdcl_state`, `solver.rs:700`) with atoms interned through the v0 pool;
   reconstructed **once** at `--aot-load` into a solver field `aot_prelude_ccfv`
   (beside `aot_prelude_clause_fold`, `solver.rs:281`). Trailing-`Option`
   discipline keeps banks back-compatible (the v1.2 `had_opaque` / v1.3
   `prelude_clause_fold` template).
2. **Compile the prelude CCFV search as a `Method<TermId>`** (`method.rs:51`):
   `clause_fold` = the AdHash fold (`clause_set_fold`, `solver.rs:155`) of the
   prelude's ground-equality / E-node-literal set keyed by **atom name** — so
   `region_key = compose_digest(prelude_fold, EMPTY_FOLD)` (`method.rs:79`) **is
   the prelude congruence signature**. It gates whether a baked CCFV search may be
   reused for the query in front of us.
3. **Replay per-query instantiation deltas via `replay_hybrid`** (`replay.rs:169`):
   record each query's CCFV round as a `CdclTraceEvent` stream led by
   `MethodInvoke{region_key}`. Atoms in prelude classes resolve through
   `method.resolve`; query-new atoms through `query_resolve`, chained
   `query_resolve(h).or_else(|| method.resolve(h).cloned())` (`replay.rs:189`) —
   **O(query-instantiation delta)**, never re-walking the prelude E-graph. This is
   the layer that composes with the measured **37× AOT win** on the full-prelude
   `(abduce)` path: the prelude search is reused, only the heavy-cut delta is
   replayed.
4. **Guard CCFV trace re-fire with `Guard::EquivClass{a,b}`** (`guard.rs:25`): a
   recorded instantiation re-fires only when its triggering congruence invariant
   ("the two trigger terms still share a class") still holds, checked O(#classes)
   against a host `ClassesView`. FF-free; the natural CCFV invariant.

**Discard ((a) lever) becomes a digest membership test:** an instance whose
clause-fold contribution is already in the prelude method's `clause_fold` is
already E-entailed by the baked prelude → skip it before emit, via the same
homomorphic `combine_fold` (`digest.rs:88`, exact multiset — not probabilistic).

**Soundness — two-gate independence carries over unchanged** (`method.rs:74-81`):
`region_key` gates **reuse** (cheap, recoverable — a mismatch just falls through
to a full CCFV round, never a verdict); `compose_digest(prelude_fold,
query_delta_fold)` gates the **verdict** (the §3.5.J exact-match cert that a
replayed level-0 `root_conflict` is trustworthy). CCFV still never concludes
`Unsat` itself — the replay yields candidate bindings + a possible root conflict
that is only trusted under exact digest match. `S::Atom` (the E-node handle) must
be `Clone`-cheap (an interned id), per `replay_hybrid`'s bound.

> This makes CCFV's prelude cost a **one-time bake**, its per-query cost a
> **delta replay gated by the prelude congruence signature** — the same lever
> that already gave 37×, now applied to the unified instantiation core.

---

## 12. Pre-verification with upstream verus (§9 / 선검증)

System `verus` is installed and works end-to-end: **`Verus 0.2026.06.07.cd03505`**
at `/usr/bin/verus`. Confirmed invocations:
- single file: **`verus --crate-type=lib <file>.rs`** (the bare form errors
  `main function not found`; `--crate-type=lib` is required for a spec/proof-only
  file) — smoke verified 6/0;
- project form (recommended, mirrors the existing scaffold): a **sibling
  standalone crate** with `[workspace]` (empty, to stay out of AD1's cargo
  workspace) + `vstd = "=0.0.0-2026-05-31-0205"` + `[package.metadata.verus]
  verify = true`, run with **`cargo verus verify`**. The existing
  `external/oxiz-sat-redesign-verification` (a git submodule, **not** in AD1's
  workspace; re-verified **28/0**) is the precedent for layout and style.

Per the `[선검증 → 구현 → 후검증]` discipline, pre-verify CCFV's three invariants
**before P1 lands** — they are precisely what keeps the never-conclude-unsat
firewall intact (i, ii) and bounds the inner search (iii):

```rust
use vstd::prelude::*;
verus! {
    // semantic layer — concrete enough to be NON-VACUOUS (mirror spec.rs entails/formula_sat)
    pub type EVar = nat; pub type GTerm = nat; pub type Subst = spec_fn(EVar) -> GTerm;
    pub open spec fn term_universe(e: Set<GTerm>) -> Set<GTerm>;          // T(E)
    pub open spec fn bound_vars(c: Clause) -> Set<EVar>;                  // fv(C)
    pub open spec fn entails_inst(e: Set<GTerm>, esig: Set<GTerm>, c: Clause, s: Subst) -> bool; // E∪E_σ ⊨ Cσ

    // (i) YIELD-SOUNDNESS — every yield is entailed (keeps the firewall sound)
    pub proof fn ccfv_yield_is_sound(e: Set<GTerm>, esig: Set<GTerm>, c: Clause, s: Subst)
        requires yield_guard(e, esig, c, s) ensures entails_inst(e, esig, c, s) {}
    // (ii) GROUNDING — σ maps every bound var into T(E) (keeps `instantiate` gate satisfiable by construction)
    pub open spec fn grounded_into(e: Set<GTerm>, c: Clause, s: Subst) -> bool {
        forall|v: EVar| #[trigger] bound_vars(c).contains(v) ==> term_universe(e).contains(s(v)) }
    pub proof fn ccfv_yield_is_grounded(..) requires .. ensures grounded_into(e, c, s) {}
    // (iii) TERMINATION — a well-founded d(C) strictly decreases per step (bounds the inner search)
    pub open spec fn d_measure(c: Clause) -> nat;
    pub proof fn ccfv_step_decreases(c: Clause)
        requires d_measure(c) > 0 ensures d_measure(ccfv_step(c)) < d_measure(c) decreases d_measure(c) {}
}
```

Each invariant follows the scaffold's established shape — `open spec fn`
predicate + `proof fn requires <guard> / ensures <invariant>` (the
`*_preserves_lockstep` pattern), with `decreases` for (iii) (the smoke file's
`sum_to` confirms the mechanism). The semantic layer must stay concrete (like
`entails`/`formula_sat` in `spec.rs`) or the three theorems are vacuous. The
*outer* MBQI-loop termination is a separate, later concern (the 2024
non-generative/generative/nested classification — a P5+ follow-up).

**Status (2026-06-20): the scaffold is LANDED, VERIFIED, and STRENGTHENED.**
Written as the sibling crate **`external/ccfv-verification/`** (standalone
workspace, mirrors `oxiz-sat-redesign-verification`; pins `vstd =
"=0.0.0-2026-05-31-0205"`). Verifies on system verus `0.2026.06.07.cd03505` —
**`29 verified, 0 errors`** by both `verus --crate-type=lib src/lib.rs` (bundled
vstd) and `cargo verus verify` (vstd 1690 + crate 29). Modules: `spec.rs` (i)
equality YIELD-soundness + the sound rules (refl/member/sym/trans/mono);
**`congruence.rs` (i+) the STRENGTHENING — function congruence is now MODELLED, not
assumed: `respects_cong` makes the interpretation a congruence, `entails_cong`
proves the `x≃y ⟹ f(x)≃f(y)` rule sound, and `cong_proof_sound` proves the whole
congruence-closure discharge sound by structural induction over a `CongProof`
derivation (`cong_yield_sound`)** — so matching modulo congruence is verified;
`ground.rs` (ii) grounding (`assign_preserves_grounding`, `yield_is_grounded`);
`terminate.rs` (iii) the strictly-decreasing `d_measure` + well-founded
`solve_depth`; `capstone.rs` the firewall theorem (admissible YIELD ⟹ grounded ∧
sound). Remaining honest scope (crate README): the abstract one-variable-per-step
search model; building the congruence closure *incrementally with backtracking* is
the EUF solver's job (verified separately, desync-proofed by §10's `GroundLedger`);
ghost-only. The P1 obligation is to *refine* these abstract states/steps in the
`ccfv.rs` implementation (the 후검증).

---

*Sketch v1 — 2026-06-20. The bet: one E-ground (dis)unification core behind the
existing Sig/TermLang firewall makes trigger/conflict/model-based three call
sites instead of three subsystems. §10 makes the GroundIndex⇄EUF desync class
structurally unreachable via the `GroundLedger` funnel; §11 reuses the AOT/JIT
"prelude=method, query=trace" machinery so CCFV's prelude cost is a one-time bake
and its per-query cost a signature-gated delta replay; §12 pre-verifies the three
firewall-preserving invariants on upstream verus before any code lands. CCFV is
the only single structural change that touches both (a) and (b).*
