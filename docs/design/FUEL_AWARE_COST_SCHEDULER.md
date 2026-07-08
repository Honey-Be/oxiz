# A fuel-aware cost-scheduler for the clean-MBQI engine

*Design. Replace the failed hard **generation cap** with a **cost-scheduled**
instantiation loop whose priority is a fuel/generativity-aware function of each
candidate — so the fuel-recursion corpus's shallow-closers and deep-closers both
close, without the zero-sum a static depth bound forces. The engine stays
**monotone** (never-conclude-unsat) and the scheduler sits entirely behind the
`instantiate`/`emit` soundness firewall.*

Companion to `CCFV_UNIFIED_INSTANTIATION.md` (the calculus this schedules) and to
the research synthesis `<adsmt root>/.claude-research-library/FUEL_AWARE_INSTANTIATION_RESEARCH.md`.
Memory: `[[mbqi-term-growth-throttle]]`, `[[oxiz_mbqi_rewrite]]`.

> **⛔ STATUS (2026-07-08) — BUILT, MEASURED, SHELVED. Do NOT re-implement on this
> branch.** This design was implemented in full (P0.5→P3) and corpus-measured on
> branch `0.2.4-feat/fuel-cost-scheduler`, then found **NET-NEGATIVE** on the
> 213-row verus lukb corpus and **not merged here except the `OXIZ_MBQI_GUARD_MS`
> guard knob**. A 7-config sweep spanning the whole parameter space (from Z3-parity
> `(0,0)` to CAP-saturated `(48,48)` to age-dominant) was **verdict-invariant**:
> `GAIN=0 / REGRESS=8 / spurious=0`, every config byte-identical to `(0,0)`.
> Raising the guard 3 s→4 s made it *worse* (net loss 8→15): the budget-scaling
> closures fire-all captures, the scheduled path's per-instance overhead loses to
> the guard. Root cause: closure on this corpus is decided by **budget-fit, not
> instance order**, so reordering opens nothing; and the corpus's "fuel" is mostly
> `fuel_bool_default` boolean gating, not a `succ`-peel the cost gradient can read.
> Like the hard generation cap before it, the scheduler is **strictly dominated by
> fire-all** here — the verified baseline is Pareto-optimal (`[[mbqi-term-growth-throttle]]`).
> Full method + tables live on the feature branch's copy of this doc (§10/§11).
> Revisit only for a genuinely `succ`-peel-heavy corpus (Dafny/F★). The rest of
> this document is the (sound, flag-off-safe, but unhelpful-here) design as built.

> **Revision 2 (2026-07-06)** — incorporates the 3-lens adversarial design review
> (`#404-D`, workflow `wehgar69d`), which ground-truthed the doc against the code
> and found the v1 draft would *reproduce the cap-0 stall* it exists to kill. The
> key corrections: (M1) the engine does **not** track instantiation generation
> today — `GroundIndex.idx` is insertion order; generation is **new** state; (M2)
> the fuel sort is **opaque** at the `TermLang` surface — a fuel-role accessor is
> a **new host extension**, not a free read; (M3) the classifier reconciliation
> is **inverted** (static-authoritative, live-only-downgrades) or the zero-sum
> relocates into it; (M4) discovery and draining must **interleave within a round**
> or the within-round cascade dies; (M5/M6) `§8` is the sole firewall and the R7
> key needs a host content-key accessor. **⇒ this is NOT "just a scheduler on top";
> it needs a small, pre-verified host/engine extension slice (P0.5) first.**

---

## 0. Thesis

The clean-MBQI round loop draws candidate instances (CDQI → e-match → enumeration)
and today fires **every** candidate it finds each round (bounded only by
`max_instances`). A hard generation cap was tried and **shelved as zero-sum**: it
recovers the shallow-closing obligations (`fuel-recursion-1/ob06`) only by starving
the deep-closing siblings (`fuel-recursion-2/ob01`, `fr3/*`), because it converts
the *fast within-round multi-generation cascade* the deep proofs need into a slow
one-generation-per-stall climb, and because the divergence it fights is
**distributed across ~50 quantifiers** with no single culprit.

The field's answer (Z3, Simplify, Vampire/E, the 2024 generativity theory) is a
**cost-priority schedule**: generation is one *term in a cost*, not a *gate*; cheap
candidates fire eagerly, expensive ones defer (never drop); a mandatory *fairness
pulse* guarantees deep candidates eventually fire; and the genuinely-divergent
axioms are distinguished **structurally** (fuel-ascending) from the safe deep
cascades (fuel-decreasing) so only the former are throttled. This design ports that
discipline, specialized to the corpus's fuel encoding.

It rests on **one scheduler + three pre-verified host/engine extensions** (the P0.5
slice — none exists today):
1. **Generation tracking** on `GroundIndex` (a `term→gen` map, distinct from the
   insertion-order `idx`).
2. A **fuel-role accessor** on the host (`TermLang`), so the engine can see the
   `succ`/`zero` fuel structure that is otherwise an opaque symbol.
3. A **content-key accessor** on the host, so the schedule's ordering key is
   assertion-shuffle-invariant (Mariposa R7).

**Invariant preserved:** the scheduler only reorders/defers *which sound candidate
fires when*. It never fabricates an instance and never concludes Unsat.

---

## 1. Where we are, and why the cap failed

Measured (adsmtc `-p adsmtc`, corpus 209 rows; `[[mbqi-term-growth-throttle]]`):

- Baseline (uncapped) closes `fr2/ob01` in **2 rounds / 265 instances** via a
  within-round cascade: `emit` calls `ground.add_term` **immediately**
  (`engine.rs:653`), so a later `qi` in the same round e-matches a term an earlier
  `qi` just minted.
- Cap-0 blocks that cascade, emits **117**, and iterative deepening raises the cap
  one generation per *stalled* host-round — too slow within the 3 s guard.
- fr1/ob06 (shallow-closer) is the mirror: its cascade *diverges*, so blocking it
  saves it. Full-cap: fr1 recovers, **7 siblings regress**. Enumerate-only: strict
  loss. Per-quant throttle-on-count: inapplicable (distributed divergence).

The corpus is a **fuel encoding** (Dafny/F★; `2014-Amin-Leino-Rompf`,
`2023-Lattuada-et-al`): `sort FuelId; const zero: Fuel; fn succ(Fuel):Fuel`,
recursive-definition axioms triggered on `f(succ(fuel),…)` with the recursive call
at `f(fuel,…)` — one `succ` peeled per unfold; self-bounding (a `f(zero,…)` matches
nothing). Required depth = nested body-exposures before an IH/base-case (fr1: 1,
fr2/fr3: 2). Divergence comes from *other* (fuel-flat/ascending, non-fuel)
quantifiers, not the fuel axioms.

**Engine model (verified `solver/mod.rs`; corrected):** monotone — a per-solve local
`CleanEngine` (`solver/mod.rs:685/858`) accumulating across MBQI *rounds* (frontier
watermark `scanned`), never retracting, **rebuilt per top-level solve**. No backtrack
surface, and needs none. **⇒ the scheduler is monotone; no incremental spine.**

**Two premises the v1 draft got wrong (verified):**
- **Generation is NOT tracked.** `GroundIndex` stores `idx: FxHashMap<Term,u32>`,
  `next_idx += 1` per `register` (`ground.rs:30-31,134-140`) — **insertion order,
  not instantiation depth**. `grep -riE 'generation|fuel|generativ' oxiz-mbqi/src`
  = comments only. Generation is new state (M1).
- **Fuel is opaque.** `OxizHost::view` maps `Apply{func}` → `App{sym: spur_sym(func)}`
  (`clean_mbqi.rs:643`), an opaque `u64`; `succ` is indistinguishable from any unary
  uninterpreted fn. `TermLang` (`term.rs:96-120`) has no name resolution / fuel
  accessor (`resolve_str` is a `TermManager` method, off the trait). Reading the fuel
  gradient requires a new host accessor (M2).

---

## 2. Design decisions (LOCKED)

1. **Cost = `f(weight, generation, fuel_gradient)`** (§3).
2. **Generativity classifier = static fuel-shape (authoritative) + live `g_out`
   (corroborator only)** (§4).
3. **Root-throttling = Cazamariposas causal-graph fixed point** — but respecified on
   an engine-local signal (§6); demoted to a P3 enhancement, not the keystone.
4. **Pre-verification = all three invariants** (§9), plus the P0.5 accessor
   extensions are themselves pre-verified sound/monotone.
5. **Architecture = monotone Age-Weight-Ratio (AWR) two-queue** with an **intra-round
   discover⇄drain fixpoint** (§5, §7); single-min-tier is `age-ratio = 0`.

---

## 2.5. The P0.5 host/engine extension slice (pre-verified, gates everything)

Three small, read-only, monotone extensions — sequenced first, each pre-verified
(§9) because the scheduler's correctness rests on them:

- **E1 — generation.** `GroundIndex` gains `gen: FxHashMap<Term,u32>` (seed 0 for
  assertion terms in `assert`; `gen(child) = 1 + max(gen of σ's bound terms)`
  computed at `emit` when the minted term is added, `engine.rs:653`). This is
  genuine engine surgery, not a free reuse.
- **E2 — fuel-role accessor.** A `TermLang` extension `fuel_role(sym) ->
  Option<FuelRole>` (`FuelRole ∈ {Succ, Zero}`) — or, equivalently, a `Config`
  carrying the resolved `succ`/`zero` sym-ids the host fills once. Lets the engine
  compute `fuel_depth(t)` (the `succ`-nesting of `t`'s fuel argument) and hence the
  real `Δfuel`. Pre-verified: read-only, returns `None` for non-fuel hosts (so the
  scheduler degrades to `weight+generation` — Z3 parity — on any non-fuel problem).
- **E3 — content-key accessor.** A host `content_key(sym) -> u64` (a stable hash of
  the symbol's *name*/definition, not its interner id) + literal content, so the R7
  ordering key (§5.2) is assertion-shuffle-invariant. Bundled with E2 (same host
  round-trip). Without it the §11.3 shuffle differential cannot pass.

E2/E3 return `Option`/degrade gracefully, so a host that supplies neither yields
exactly today's `weight+generation` Z3-parity schedule — the flag-off / non-fuel
baseline.

---

## 3. The cost function `f(weight, generation, fuel_gradient)`

Per candidate `ι = (q, σ)`, trigger term `τ` matched against ground `g`:

```
cost(ι) : Cost = clamp_0_CAP(
      weight(q)                       // per-quantifier :weight (default 0)
    + generation(ι)                   // E1: 1 + max gen of σ's bound terms
    + fuel_penalty(ι)                 // the fuel_gradient (needs E2)
    + gen_class_penalty(q)            // 0 if Decreasing; +Δg if Ascending (§4)
    + root_penalty(q) )               // §6 causal-root throttle; 0 normally, P3+
```

- `generation(ι)` (E1) is the base *soft* shallow-first pressure (deeper ⇒ later,
  never blocked). NB it counts **all** instantiation depth, not only fuel unfolds —
  so it is **not** interchangeable with fuel-depth (see M3/§4).
- **`fuel_penalty` = the fuel_gradient (E2).** `Δfuel(ι) = fuel_depth(minted) −
  fuel_depth(matched τ-term)`. Fuel-**decreasing** (`Δfuel < 0`, the `succ`-peel):
  **discount** — these self-bounding unfolds must stay cheap so a needed depth-2
  cascade fires within a round. Fuel-**flat/ascending** (`Δfuel ≥ 0`): `0` / positive.
  `fuel_penalty = k_fuel · Δfuel` clamped so decreasing edges get a bounded discount
  (constants tuned by the sweep). A fuel-flat cascade has `Δfuel = 0` and cannot spoof
  the discount — the discount is *only* for genuine `succ`-peels, which are terminating.
- **`gen_class_penalty`** applies §4: `Decreasing → 0`, `Ascending → +Δg`. The
  selective throttle the uniform cap could not express.
- `clamp_0_CAP`: `cost = CAP` (≈48–64) ⇒ **DEFER** (overflow bucket), never DROP (§8).

`new_generation(child) = max(parent_gen + 1, cost)`.

**Threshold/drain semantics (reconciled — was §3-vs-§5.1 inconsistent).** There is
**one** rule: the scheduler drains in ascending `cost` order (cheapest bucket first);
`EAGER`/`LAZY` are not a separate gate but the **AWR budget shape** — within a round
the weight side drains buckets while `cost ≤ EAGER` freely, buckets in `(EAGER,LAZY]`
drain subject to the age-ratio interleave, `> LAZY` only if the round is otherwise
empty (still queued, never dropped). Defaults `EAGER=10, LAZY=20` (Z3), corpus-tunable.

---

## 4. The generativity classifier — static authoritative, live corroborator (M3)

Each quantifier gets `GenClass ∈ {Decreasing, Ascending, Unknown}`.

**Static (authoritative for `Decreasing`), computed at trigger-fix using E2.** For
trigger group `τ → body`: **Decreasing** iff every term the body mints under a match
of `τ` is (a) a subterm of `τ`, (b) Bool-sorted, or (c) at strictly smaller
`fuel_depth` than `τ`'s bound fuel (the `succ`-peel). **Ascending** iff the body mints
a fresh-class term (new Skolem/function application, or a fuel-flat/ascending
recursive call). This is the `2024-instantiation-termination` non-generative test on
the **real** fuel structure (E2) — the actual discriminator.

**Live `g_out(q)` — a weak corroborator that may only *escalate an Unknown*, never
override a static `Decreasing` (the M3 inversion).** `g_out(q) = max_recent(
generation(minted) − generation(matched))`. Because `generation` counts *all*
instantiation depth, `g_out ≥ 1` for essentially every active quantifier —
**including** the fuel-decreasing deep-closers (their early instances match gen-0
seeds and mint gen-1 offspring). So a `Decreasing OR live` rule would brand fr2/fr3
Ascending and penalize exactly the cascade that must run uncapped — **the zero-sum
relocated into the classifier.** Therefore: static `Decreasing` is final; `g_out` may
only push an `Unknown`/not-yet-classified quantifier toward `Ascending`. `g_out` is a
generation-delta, **not** fuel-succ-depth (the two diverge both ways), so it is never
the discriminator.

**Inferred-trigger quantifiers:** `Unknown` until the trigger is inferred, then run
the static test on it; `g_out` governs in the interim (base `generation` cost only —
neither over- nor under-throttled).

---

## 5. The scheduler — monotone AWR over a bucket queue

### 5.1 Structure (research §5; adversarial fixes folded)

Flat Dial bucket queue over an append-only arena + a FIFO age cursor — an AWR
two-queue. Monotone: accumulates within a solve, rebuilt per solve, **never rolled
back** (drops the R6 machinery; the dormant `GroundLedger` is *not* used).

```
type Cost=u16; type ArenaIx=u32; const CAP=48;   // cost>CAP → overflow (DEFER)
struct Cand<S:Sig>{ q:u32, sigma:SmallVec<[S::Term;4]>, cost:Cost, born:u32,
                    fired:bool, superseded:bool }  // born = generation (E1) = AGE key
struct CostScheduler<S:Sig>{
    arena:Vec<Cand<S>>, buckets:Vec<Vec<ArenaIx>>, age:Vec<ArenaIx>, age_cursor:usize,
    seen:FxHashSet<(u32,SmallVec<[S::Term;4]>)>,   // EXACT (q,σ) dedup — NOT a lossy hash (fix #3)
    cursor:usize, tick:u32 }
```

- **`insert`** — exact-key dedup; push arena/bucket/age; lower `cursor`.
- **`drain_step`** (called by the round fixpoint, §5.3) — AWR pulse: `tick%(a+w)<a` ?
  pop oldest un-fired age entry : pop cheapest non-empty weight tier. A weight tier is
  **sorted by the §5.2 key**, each dispatched through the unchanged `instantiate`/`emit`
  firewall (**move** `σ` out — no clone, fix #6). `tick += 1`.
- **`promote(ix,new_cost)`** — explicit (fix #4): append fresh entry at
  `buckets[new_cost]`, set old `superseded`; if `new_cost < cursor` reset cursor
  (fires this round). No decrease-key, no 2nd `seen` insert.
- CDQI conflicts are **not** queued — emit first out-of-band (`engine.rs:299`); they
  `seen.insert((q,σ))` so the cost path won't re-emit.

### 5.2 Determinism (fix #2 — R7; needs E3)

Sort each tier by the **content-derived total** key
`( cost, content_key(q), [ (content_key(t_i), …) for i in binding-position order ] )`
using E3's stable content keys — **not** `qi`/`Spur`/`TermId` (all interner/order
variant). `(q,σ)` unique ⇒ no residual ties ⇒ order is a pure function of content.
The **age key `born`** is the E1 generation (content-derived), not `idx` (order-
variant) — this is why age uses generation, not insertion index. Acceptance gate:
the §11.3 assertion-shuffle differential (identical verdict + schedule) — **cannot
pass without E3.**

### 5.3 The intra-round discover⇄drain fixpoint (M4 — load-bearing)

The within-round cascade is the whole game for the deep-closers. `emit` adds the
minted term to the ground index **immediately** (`engine.rs:653`), so draining a
tier *creates new frontier* that later discovery must see **in the same round**. A
discover-all-then-drain-once loop runs `qi=k+1`'s discovery before `qi≤k`'s mints
exist → one generation per host round → **precisely the cap-0 stall** (fr2 at 117 vs
baseline 265/2-rounds). So each host round is a **fixpoint**:

```
loop {                                   // one host round_with_cong call
  discover candidates over the CURRENT frontier (CDQI→e-match→enumerate), insert scored
  if no new candidate inserted { break }         // real saturation for this round (M5)
  drain the cheapest admissible tier (AWR)       // mints land in ground index
  if round budget / deadline hit { break }
}                                        // → return NewLemmas / verdict
```

so a decreasing cascade pops several generations in one round (matching baseline),
while cost-ordering + the age pulse bound the fan-out. This **replaces** §7's v1
"discovery unchanged / minimal surgery" — Z3 likewise interleaves matching and
instantiation within a search epoch.

### 5.4 Why AWR not a single cost order

A single cost order with a hard `LAZY` cutoff *is* a soft generation-cap and would
reproduce the zero-sum. The age pulse (ratio `a:w`, default ≈1:4, optionally decaying
toward age as budget is spent — LRS) *defers* deep candidates rather than suppressing
them: weight queue → fuel/seq cheapest-first; age pulse → fr1/ob06's deep terms
eventually fire. **AWR-vs-single is empirical** (`[[feedback_empirical_adversarial_review]]`):
both behind one flag, default + ratio picked by an idle-machine sweep
(`[[feedback_scripted_tallies]]`); no paper-chosen constant.

---

## 6. Causal-root throttle — respecified, demoted to P3 (SHOULD-FIX)

The Cazamariposas signal `EXCESS = #made − #entered conflict/prop/merge` **is not
implementable on this engine**: `round_with_cong` returns only a fresh model;
per-lemma productivity is host-side (`clean_instances`, `solver/mod.rs:1001`) and
never reaches the engine; `emit` records no producing-`qi` provenance. So §6 is
respecified two ways, and **demoted from keystone to a P3 enhancement** (the core
resolution — `gen_class_penalty` + age pulse — stands without it):

- **Engine-local signal (default):** replace EXCESS with the Axiom-Profiler
  "additional structure" + frontier-stall marker, computable from E1 generation +
  term-size growth: a root is a quantifier whose instances keep minting
  strictly-deeper, strictly-larger terms (divergence) without the frontier stalling.
  Causal edges still need term→producing-quant provenance — **net-new plumbing** at
  `emit` (record the `qi` that minted each term) if §6 survives its P3 measurement.
- **Or** an explicit host→engine conflict-attribution channel (heavier; only if the
  engine-local signal proves too weak).

Gate at P3 with an explicit "does it earn its keep vs per-quantifier `gen_class_penalty`
alone?" measurement.

---

## 7. Integration into the round loop

- **`Config`** gains cost params (`k_fuel`, `gen_class_delta`, `weight` source),
  `eager`/`lazy`, `awr_ratio` (0 = single-tier), `cap`, and the E2/E3 accessor hooks
  — all with degrade-to-Z3-parity defaults; env-overridable for the sweep.
- **The round becomes the §5.3 fixpoint.** Candidate discovery (CDQI→e-match→enumerate)
  is unchanged *per pass* but now **re-runs on the new frontier within the round**.
  Each discovered `(q,σ)` is **scored** (E1 generation + E2 Δfuel + §4 class) and
  **inserted**; CDQI conflicts still fire first out-of-band.
- **`emit` funnel untouched** (`instantiate` ground-membership + capture-free, then
  dedup); the scheduler calls it on drain. **`seen` respec (SHOULD-FIX):** removing
  the engine's `seen` (`engine.rs:90`) must (a) keep a home for the existential
  empty-tuple sentinel (`engine.rs:688` — if lost, the bounded-∃ disjunction re-emits
  every round → `lemmas` never empties → **livelock**, not unsoundness), and (b) reap
  the cross-round CDQI zombie (a prior-round deferred `(q,σ)` that CDQI later fires
  out-of-band → double-emit). Route both through the scheduler's single `seen`.

---

## 8. Soundness — the Saturated gate is the SOLE firewall (M5)

The structural firewall is intact and untouched: `Verdict` has no `Unsat` variant
(`engine.rs:35`); `instantiate` enforces ground-membership (`instantiate.rs:86`);
`emit` calls it unconditionally. The scheduler only reorders/defers sound candidates.

**But there is no defense-in-depth:** `verify_clean_saturated`→`fresh_ground_resolve`
re-solves only the *emitted* `clean_instances` (`solver/mod.rs:1001`), so a
*withheld* refuter never reaches the re-solve — the Saturated gate is the only thing
standing between a deferred sound refuter and a spurious `Sat`. Therefore:

1. **DEFER, never DROP.** `cost > CAP`, budget-hit, deadline, promote, CDQI-zombie —
   every path **queues**, never discards (`[[feedback_soundness_opaque_fallback]]`:
   withholding preserves Unsat-freedom but must never manufacture Sat).
2. **The gate, stated exactly.** `Saturated` (→ host may report `Sat`) is legal only
   when: **the scheduler queue is empty (all buckets + overflow + age drained)** ∧
   **no candidate was budget-deferred this check** ∧ **the round fixpoint inserted no
   new candidate** (the real "saturation" — NOT "frontier empty": the frontier is the
   monotone `next_idx`, never zero) ∧ **every trigger-free quantifier model-verified**
   (existing M3). Otherwise → `Inconclusive`/`BudgetExhausted` → **`Unknown`**
   (`solver/mod.rs:1095`). This strictly *shrinks* the `Sat`-license → no spurious
   Sat; and never introduces Unsat.
3. **Boundary note:** the enumerate/CDQI per-quant caps (`engine.rs:609`,
   `cdqi.rs:94`) generate-and-drop *outside* the queue, so DEFER-not-DROP does not
   cover them; their soundness is carried by `eval_forall`/the model-verification
   condition, not the queue. This boundary is unchanged by this design.

**Regression required:** *a deferred sound refuter present ⇒ the engine returns
Inconclusive/BudgetExhausted, never Saturated* — tested through the real producer
(`[[feedback_roundtrip_through_real_producer]]`).

---

## 9. Pre-verification (선검증 — all three + the accessors)

`oxiz-sat-redesign-verification`-style harness; agents **execute**, not paper-reason
(`[[feedback_empirical_adversarial_review]]`):

- **(0) The P0.5 accessors are sound read-only extensions.** E1 generation is
  write-once-at-emit and read-only thereafter; E2 `fuel_role`/E3 `content_key` are
  pure functions returning `Option`/a hash, never mutating host or engine state, and
  `None` ⇒ Z3-parity degrade. (Cheapest to discharge; unblocks the rest.)
- **(i) Fairness ⇒ termination-on-UNSAT.** Model the AWR drain (with `a > 0` and the
  DEFER no-drop invariant) as a fair enumeration over the monotone-growing candidate
  set ⇒ every candidate eventually drained ⇒ Reynolds 2018 Cor. 2 ⇒ terminates on
  UNSAT. (The per-solve rebuild does not weaken this: each solve is its own fair run.)
- **(ii) Never-conclude-unsat firewall.** No `drain` path yields a non-ground /
  not-all-bound term; `Verdict` has no `Unsat`; and the §8 gate property: `Saturated
  ⇒ queue-empty ∧ no-deferral-this-check ∧ no-new-candidate ∧ model-verified`.
- **(iii) Cost monotonicity — split by `GenClass` (M-shouldfix).** For the
  **Ascending** class, `cost` is non-decreasing in `generation` (holding other inputs)
  ⇒ deferred-set cost cannot fall unboundedly ⇒ (with (i)) divergence bounded. For the
  **Decreasing** class `fuel_penalty` is *negative*, so cost can fall as generation
  rises — its termination rests instead on the **succ→zero floor** (a calculus
  property: finitely many `succ`-peels to `zero`, seen via E2), NOT on cost
  monotonicity. State both branches; do not claim monotonicity for the discounted class.

---

## 10. Phasing (each gated: `clean_mbqi_corpus --ignored` + `cargo test --workspace`)

- **P0.5 — firewall/host-extension slice (pre-verified; gates P2).** E1 generation on
  `GroundIndex`; E2 fuel-role accessor; E3 content-key accessor. Discharge §9(0).
  No behaviour change yet (nothing consumes them) — differential-clean by construction.
- **P0 — substrate.** `CostScheduler` (AWR bucket queue, monotone, exact dedup,
  content-key sort, promote, DEFER overflow) unit-tested: insert/drain order, AWR
  ratio, promote, overflow, **shuffle-determinism differential** (needs E3).
- **P1 — cost + classifier (flag OFF = queue BYPASSED).** `cost_fn` (E1+E2), `GenClass`
  static+live (M3 direction), `g_out`. `cost_schedule=false` must **bypass insert/drain
  entirely** (drain reorders ≠ discovery order, so "off" cannot route through the queue)
  → byte-identical verdicts (differential gate).
- **P2 — flip on, single-tier first (`awr_ratio=0`) + the §5.3 fixpoint + §8 gate.**
  Corpus A/B vs b4518db: **0 regressions** + ground-DT z3+cvc5 differential **0
  spurious-unsat** + the §8 deferred-refuter regression. Expect deep-closers to hold
  (no cap); measure fr1/ob06.
- **P3 — AWR + causal-root.** Age pulse + the §6 engine-local root signal (with
  `emit` provenance if kept); sweep the ratio; "does §6 earn its keep?" Target: fr1/ob06
  **and** the fuel/seq siblings both closed, 0 regressions.
- **P4 — 선검증 (i)(ii)(iii) discharged; DEFICIT-re-run decision (§12); docs/comments
  sweep (`[[feedback_per_slice_doc_sweep]]`); verus-fork reply; memory.**

Scoped suites only; full `cargo test --workspace` + `-- --ignored` to the user via `!`
(`[[feedback_long_test_runs]]`, `[[feedback_test_ignored_pass]]`); guarded sweeps solo
on an idle machine (`[[feedback_scripted_tallies]]`).

---

## 11. Validation gate (v1.0.0 verdict-trust)

Per `[[lu_vs_z3_disagreement_analysis]]` + `[[feedback_z3_differential_for_unsat_trust]]`:
1. **Full corpus A/B vs b4518db, 0 regressions** (the discipline that shelved the cap).
2. **Randomized ground-DT z3+cvc5 differential, 0 spurious-unsat** (the schedule only
   reorders sound instances; a non-clean result is a real bug, not a completeness trade).
3. **Assertion-shuffle differential** (R7) — needs E3; identical verdict across mutants.
4. The §9 (0)(i)(ii)(iii) obligations green.

---

## 12. Open questions (carry into implementation)

- **DEFICIT-targeted re-run (SHOULD-FIX).** Research §2.5 made it load-bearing for
  completeness; a deferred-needed instance that misses the 3 s guard yields `Unknown`
  with no escalation. Decide: add the F★-ladder "bump *that* quantifier's budget and
  re-run", or explicitly accept "no escalation; rely on the correct classifier keeping
  needed instances cheap." (Lean: measure at P2 whether it's needed before building it.)
- Exact `fuel_penalty` shape + `k_fuel`, `gen_class_delta` — the sweep's job; start
  Z3-parity (`fuel_penalty=0` ⇒ pure `weight+generation`) and add the fuel discount
  incrementally, watching the net sign of `fuel_penalty + gen_class_penalty` (a wrong
  net sign re-introduces the additive-CAP starvation the review flagged).
- Which axioms deserve `weight > 0` a priori (fuel-free `Lit`-computation; known
  loopers) vs the live classifier.
- §6: full causal fixed point vs engine-local frontier-growth signal — the P3
  measurement decides; is the `emit` provenance plumbing worth it?
- `children()` allocates a `Vec` per call (`term.rs:101`); the content-key / structural
  walk at prelude scale needs a per-`TermId` hash memo (`[[feedback_hashcons_hot_paths]]`).
