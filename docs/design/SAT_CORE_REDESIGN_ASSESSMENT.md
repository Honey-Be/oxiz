# OxiZ SAT Core — Redesign Scope Assessment

**Status:** Design recommendation (no code in this document)
**Date:** 2026-06-13 · **Revised:** 2026-06-13 post-Phase-0 (HEAD `5527290`)
**Branch:** `0.2.4-feat/cdqi`
**Audience:** OxiZ maintainer / sign-off holder
**Inputs:** three structured audit findings (pure-SAT differential-fuzz soundness audit; architecture/feature map; engine-trust + minimal-sound-API + lock-step-invariant design probe).

> **REVISION NOTE (post-Phase-0).** This document was first written *before* its own proposed Phase 0
> (§5) was executed. Phase 0 has since been run and landed (commit `5527290`); the theory-callback fuzz it
> prescribed found **two additional soundness defects beyond the one this document anticipated** — both in the
> conflict-analysis surface the early draft called "the sound nucleus": a degenerate-conflict spurious-SAT in the
> Boolean `analyze()` (BUG 2) and a missing post-theory-conflict BCP-settle in `solve_with_theory` (BUG 3) — plus
> the placeholder leak this document *did* predict. All three are fixed and regression-pinned. **The bottom-line
> recommendation is unchanged (and is now empirically vindicated): integration-layer clean-room on the reused
> engine, not a full rewrite, not keep-patching.** What changed is the *evidence narrative and effort sizing*:
> the trusted-core precondition is not "one few-line `analyze()` fix" but "a bounded, single-class conflict-
> analysis hardening track" (~270 net LoC, landed across `cc3872c`+`4419298`+`5527290`). Sections below are
> annotated inline; see the companion `SAT_CORE_REDESIGN_ASSESSMENT_REVIEW.md` for the full review.
>
> Line anchors cited below reference the pre-Phase-0 code; the most decision-relevant ones have been refreshed to
> `5527290`. Where an anchor still shows an old number, the underlying claim was re-verified and holds; the line
> may be off by up to ~150 lines after the Phase-0 edits (`conflict.rs` +211/−2, `mod.rs` +199).

---

## 1. Executive summary and bottom-line recommendation

This session fixed **6 soundness bugs** (spurious `unsat`/`sat`), and the post-mortem question is: do we clean-room rewrite the SAT core the way the quantifier engine was rewritten (`~/oxiz-mbqi`), or is a narrower scope correct?

We then did the thing the user asked for first: we **audited the pure ~38k-line SAT engine** — which had never been differential-fuzzed *as pure SAT*, only ever exercised through the SMT path — to learn whether the engine itself harbors soundness bugs, before recommending a redesign scope.

### Bottom-line recommendation

> **Integration-layer clean-room + one minimal trusted-core fix.**
>
> Rewrite the **CDCL(T) theory-integration layer** (the ~6,800-line glue: the `TheoryCallback` contract in `oxiz-sat` + the advisory `theory_manager.rs` in `oxiz-solver`) clean-room, oxiz-mbqi-style, built **on top of the existing `oxiz-sat` engine reused unchanged** — *except* for the two surgical engine edits the new contract structurally requires (move theory push/pop **inside** the trail's level-mutating functions; make `Reason` typed and delete the sentinel-`0` placeholder). **In addition**, the trusted core needs a **bounded, single-class conflict-analysis hardening track** before it can be trusted standalone — *not* a single few-line fix as the first draft assumed. Phase 0 (now executed, §5) showed the always-on conflict-analysis surface harboured a *cluster* of defects sharing one root: **two `analyze()` defects** (a `lits[0]` positional assumption → spurious-UNSAT; a no-current-level *degenerate conflict* → spurious-SAT under CDCL(T)), a positional + placeholder defect in `analyze_theory_conflict`, and a missing post-conflict BCP-settle in `solve_with_theory`. All are now landed (`cc3872c` + `4419298` + `5527290`, ~270 net LoC, regression-pinned). This is **not** a full 38k-line rewrite and **not** keep-patching.

### One-paragraph reason

The *desync* bug class (frame-stack desync, stale theory bounds, sentinel reason literal) lives in the **theory-integration glue** — the glue keeps a *parallel* level stack synced to the trail only *advisorily* (`on_new_level` even has an empty default body), so desync is the default failure mode. The pure-SAT audit confirms the engine's propagation, restarts, clause-DB, and LBD machinery are sound and that the big risky engines (XOR/Gauss, cube, GPU, ML-branching, inprocessing) are **dead code with respect to the solve path** — so rewriting 38k trustworthy lines is the wrong leverage (the oxiz-mbqi precedent rewrote the *unsound* layer and reused the sound core). **The post-Phase-0 correction:** there is a *second*, distinct soundness-defect class — **conflict-analysis robustness under CDCL(T)-induced states** — and it lives in the *shared* always-on conflict analyzers (`analyze`, `analyze_theory_conflict`) and the `solve_with_theory` driver, *not* in the glue. These defects arise because textbook-CDCL invariants ("the implied literal sits at `lits[0]`"; "every conflict has a current-level literal"; "BCP has run to fixpoint before the next decision") are violated **only** by the CDCL(T) calling pattern. Crucially they form **one root-cause cluster**, not multi-subsystem rot: propagate, watched-lits, clause-DB, restarts and LBD remained unflagged across 8k pure-SAT + 6k DRAT-verified instances at 0 unsound. So the right response is a **bounded conflict-analysis hardening track plus permanent fuzz gates** (both landed), **not** an escalation to a full rewrite. The `analyze()` 1-UIP loop must therefore be treated as a *soundness-sensitive shared surface*, not as part of an assumed-sound nucleus.

---

## 2. Empirical pure-SAT soundness verdict

### 2.1 Headline numbers

| Metric | Value |
|---|---|
| CNF instances checked | **106,693** across **78 runs** |
| Wall time | ~12 min, release-mode |
| `agree` (oxiz == cadical, 3-oracle confirmed) | 106,652 |
| `oxiz_unknown` | **0** |
| `model_invalid` / fake-SAT | **0** |
| **UNSOUND (spurious-UNSAT)** | **41** |
| Unsound rate | **0.0384%** |

Every one of the 41 unsound results was `oxiz = unsat` while **cadical = sat AND z3 = sat AND cryptominisat5 = sat** (and `minisat = sat` on the minimal case). The three-oracle consensus exonerates cadical on every disagreement. The direction is **uniform**: all 41 are spurious-UNSAT (the engine over-prunes / learns an unsound clause). There were **zero fake-SAT** results across 106k instances despite the runner re-validating every claimed model, and **zero unknowns**.

> ⚠️ **POST-PHASE-0 SCOPING.** "Zero fake-SAT / uniform spurious-UNSAT-only" is true **for this pure-SAT campaign**, and it remains a meaningful signal that the *pure-SAT* calling pattern is targeted-buggy, not pervasively rotten. It is **not** a property of the engine under *all* calling patterns: Phase 0's CDCL(T) theory-callback campaign DID surface **spurious-SAT** (BUG 2, BUG 3 — §5). Those spurious-SATs are confined to the CDCL(T) calling pattern and are *provably inert in pure SAT* (a pure-Boolean conflict always has a current-level literal, so the BUG-2 degenerate-conflict guard cannot fire — `mod.rs:778-782`). Read the "zero fake-SAT" boast as scoped to the pure-SAT path, not as engine-wide.

### 2.2 Distribution and features exercised

Per-distribution split:

| Config slice | Instances | Unsound |
|---|---|---|
| default config | 30k + 40k | ~29 |
| preset matrix (industrial / aggressive / conservative / cadical / random / glucose / ...) | 16k+ | 12 |
| minisat preset (`random_polarity_prob = 0.0`) | — | **0** |

CNF families fed (semantics independently validated): random 3-SAT near phase transition, k-SAT, dense 2-SAT, small + larger pigeonhole, **XOR/parity systems** (Tseitin expansion brute-force-checked; ~26% of every campaign was XOR-structured — xor-system + parity-chain + 3sat+xor-mix), **graph k-colouring + clique-colouring** (K_{k+1} guaranteed-UNSAT, resolution-hard, stresses learning).

Engine features active on the **default `solve()` path** (read out of `SolverConfig::default` + the `solve()` loop): two-watched-literal propagation, 1-UIP conflict analysis + clause minimization, LBD, Luby restarts, clause-DB reduction/vivification, phase saving, random polarity (p=0.02), VSIDS/CHB/LRB decay, lazy-hyper-binary-resolution (`enable_lazy_hyper_binary = true`), chronological backtracking (`enable_chronological_backtrack = true`). The preset sweep (via `OXIZ_SAT_PRESET`) additionally turned on inprocessing, LRB/CHB branching, and Glucose/geometric restarts; per-flag env knobs (`OXIZ_LHB / CHRONO / INPROC / RANDPOL / LRB / CHB`) isolated the trigger.

**The XOR/inprocessing machinery, though exercised by the inputs, was ruled OUT as the cause.** `grep` shows `solver/mod.rs` has zero references to `Xor`; the XOR/Gauss, cube, GPU, ML-branching, and preprocessing engines are **never called from `solve()`**. The bug is in the always-on CDCL core.

### 2.3 Root cause and minimal CNF

> ⚠️ **Critical harness correction.** The committed harness's earlier "300 instances, unsound = 0" smoke was a **false negative**. `oxiz --dimacs` does **not** exercise `oxiz-sat`; it converts the CNF to QF_UF SMT-LIB2 and runs the *separate* `oxiz-solver` SMT CDCL (which returns the correct `sat`). A new `pure_sat_runner` example was built to drive `oxiz_sat::Solver` directly (`DimacsParser` + `solve()`), and the bug was reconfirmed by a pure-Rust unit test (`oxiz-sat/tests/soundness_repro.rs::minimal_spurious_unsat_default_config`) that calls `Solver::new()` + `add_clause()` + `solve()` — no Python, no example — proving it is **not** a harness artifact. **STATUS (post-Phase-0): FIXED.** The `analyze()` 1-UIP defect was corrected in `cc3872c`; the repro test is now a plain `#[test]` (no longer `#[ignore]`d) and **passes** on HEAD. (The test file's in-file docstring was likewise updated to past tense — `soundness_repro.rs:12-16` now reads "STATUS: FIXED".)

**Minimal CNF (6 vars, 7 clauses):**

```
p cnf 6 7
 6 -5 0
-4 -3 0
 2 -1 0
 2  4 0
 3  5 0
 4 -2 0
-6 -2 0
```

- `oxiz` (default config) = **UNSATISFIABLE** (wrong).
- `cadical = SAT`, `z3 = SAT`, `cryptominisat5 = SAT`, `minisat = SAT`.
- **Unique model:** `v1=F v2=F v3=F v4=T v5=T v6=T` (hand-verified against all 7 clauses). The certificate is a **MODEL**, not a DRAT proof, because the unsound direction is spurious-UNSAT, not fake-UNSAT.

**Mechanism (traced by instrumenting `solve()` + `analyze()`, since reverted):** with random-polarity picking `v1 = TRUE`, propagation forces `v2=T, v4=T, v6=F, v3=F, v5=F` (all level 1), yielding a **real** conflict on clause `[3,5]`. But `analyze()` in `oxiz-sat/src/solver/conflict.rs` computes the **wrong 1-UIP**: it learns the unit `[-4]` (`v4 = false`) instead of `[-1]`. `v4` is TRUE in the only model, so the learned unit is unsound; asserted at level 0 it then conflicts with `[4,-2]` via `v2` → spurious level-0 conflict → UNSAT. The 1-UIP trail-walk terminates at a **non-dominating** literal (`v4`): the loop's `counter` accounting (the `start = if p.is_some() {1} else {0}` skip + `counter`/`seen` bookkeeping) stops before reaching the true unique implication point `v1`; `v4` does not dominate the `v6 → v5` path, so resolving on it omits the `v2 → v4` and `v1 → v2` antecedents.

**Feature / file:** pure-SAT 1-UIP conflict analysis, `oxiz-sat/src/solver/conflict.rs::analyze`.

### 2.4 Trigger gating

- **Config-gated on `random_polarity_prob > 0`.** `OXIZ_RANDPOL=0` makes the minimal instance return `SAT` (correct). The shipped Default and 9/10 presets (all `randpol > 0`) are unsound; only the **minisat** preset (`randpol = 0.0`) is correct.
- Random polarity only flips the **first** decision phase — it cannot itself make a SAT instance unsound; it merely **exposes** the latent `analyze()` defect by steering search into the buggy implication-graph shape.
- `OXIZ_LHB=0` and `OXIZ_CHRONO=0` do **not** fix it → lazy-hyper-binary and chronological backtracking are ruled out as causes.

### 2.5 Coverage gaps — what was NOT exercised

Be explicit: this is a **necessary-but-not-sufficient** audit of the *default pure-SAT path*. Specifically NOT exercised:

1. **The theory-only engine surfaces.** Two pure-engine code paths are reached **only** by the theory loop and the pure-SAT fuzzer never touches them:
   - `add_theory_reason_clause` (`learn.rs:135`→`141`) — builds learned reason clauses on the fly with manual watch setup.
   - `analyze_theory_conflict` (`conflict.rs:381`→`538`) — a **separate** conflict analyzer from the Boolean `analyze()`, which carries a **latent** bug: the `Lit::from_code(0)` placeholder (`conflict.rs:386`→top of the function) is only overwritten when a UIP is found; if the trail walk terminates with `p == None`, a spurious literal (var 0, positive) leaks into the learned clause.

   > ✅ **CLOSED by Phase 0 (§5).** A theory-callback fuzz with a synthetic *provably-sound* theory (z3/cadical-cross-checked, model-validated) now exercises both surfaces. **The placeholder leak this document predicted was confirmed reachable** (via a `theory-probe` cargo feature: `no_uip` fired, `placeholder_in_clause`>0 pre-fix) and fixed by dropping the placeholder in the `p==None` branch (`conflict.rs:654-695`). The fuzz *also* found two defects this section did **not** anticipate — a degenerate-conflict spurious-SAT in the *Boolean* `analyze()` (BUG 2) and a missing post-conflict BCP-settle in `solve_with_theory` (BUG 3). **Prediction scorecard: 1 of 3 Phase-0 findings anticipated** (the placeholder leak); the two `analyze()`/`solve_with_theory` spurious-SAT defects were missed and are the reason this document's "one single-site defect" framing (§2.5) needed correction — a measured correction to the thesis, not a refutation of the narrow-scope conclusion (§6.3).
2. **DRAT-verified UNSAT.** The campaign cross-checked verdicts by *differential agreement* with 4 oracles, not by replaying oxiz's own UNSAT proofs through `drat-trim`. `oxiz-sat` ships DRAT emission (`proof.rs`, `drat_inprocessing.rs`, `parallel/proof_check.rs`); a proper soundness gate should *replay* UNSAT verdicts through `drat-trim` (a far stronger oracle than agreement — a spurious-UNSAT would surface as a `drat-trim` rejection).
3. **The advanced engines as live solvers.** XOR/Gauss, cube, GPU, ML-branching, inprocessing were exercised only as *inputs hitting a core that does not call them*. They were never driven as the answer-producing path because the solve loops never construct them. Their soundness is therefore **untested** (but also **dormant** — see §3).
4. **Long-horizon / large industrial CNF.** The campaign is near-phase-transition + structured-hard but small; no multi-hour single-instance or large real-world industrial run.
5. **Incremental / assumptions paths.** `solve_with_assumptions()` and the incremental add-after-solve path were not the focus of the differential campaign.

**Empirical verdict:** the default pure-SAT engine is **UNSOUND on the shipped Default config** — the pure-SAT defect is **localized, deterministic** (the `analyze()` 1-UIP `lits[0]` loop), present in Default and 9/10 presets, absent under `randpol=0`. **Post-Phase-0 refinement:** it is not a *single-site* bug but the pure-SAT representative of a **single-CLASS, multi-SITE conflict-analysis cluster** (two `analyze()` sites + `analyze_theory_conflict` + the `solve_with_theory` BCP-settle), all sharing one root (CDCL invariants the theory cycle violates). It remains a **targeted cluster, not pervasive rot** — propagate/watched-lits/clause-DB/restart/LBD stayed clean across the pure-SAT and DRAT campaigns.

---

## 3. Architecture map: core CDCL vs advanced features

### 3.1 Shape

`oxiz-sat` (~38k lines, 75 modules) is a **"mono-struct + standalone-toolbox"** layout, *not* a plugin pipeline. The `Solver` struct (`solver/mod.rs:327-398`) embeds **only** the core CDCL state: `config`, `num_vars`, `clauses: ClauseDatabase`, `trail: Trail`, `watches: WatchLists`, the `vsids/chb/lrb` heuristics, `learnt`/`seen`/`analyze_stack`, restart bookkeeping (Luby index, thresholds, recent/global LBD sums), `binary_graph: BinaryImplicationGraph`, `chrono_backtrack: ChronoBacktrack`, `memory_optimizer`.

**Every advanced module** (`xor` / `cube` / `gpu` / `ml_branching` / `proof` / `resolution_graph` / `symmetry` / `lookahead` / `local_search` / `backbone` / `maxsat` / `allsat` / `preprocessing`) is a **separate top-level struct** exported from `lib.rs` — **none** is a field of `Solver`. A `grep` for `self.{xor,cube,gpu,ml,resolution,proof,symmetry,lookahead,local_search}` over `solver/*.rs` returns **empty**. The advanced toolbox is architecturally decoupled from the solve loops. *(Post-Phase-0 footnote: Phase 0 added one optional `drat: Option<DratWriter>` field to `Solver` (`mod.rs:409`) + ~25 `self.drat*` call sites for proof emission. It defaults to `None`, is a no-op on the hot path, and is soundness-neutral — emission produces a wrong **certificate**, never a wrong **verdict** (§3.5 rank 7). The `proof.rs` reasoning module and the eight standalone reasoning engines remain un-fielded.)*

### 3.2 Trusted nucleus (~3.5k–5k lines)

| Concern | Location |
|---|---|
| Main loops | `solve()` `mod.rs:668-818` · `solve_with_assumptions()` `mod.rs:830-927` · `solve_with_theory()` `mod.rs:937-1137` (the CDCL(T) loop the SMT path uses) |
| Unit propagation / watched lits | `solver/propagate.rs` (~210L) + `watched.rs` |
| Conflict analysis / 1-UIP / minimization | `solver/conflict.rs` — `analyze()` :35, `minimize_learnt_clause()` :249, `lit_is_redundant()` :338, `analyze_theory_conflict()` :381 |
| Clause learning / LBD / DB reduction | `solver/learn.rs` — `reduce_clause_database()` :165 (tier-based, always-on), `handle_clause_deletion_and_restart()` :280 |
| Decision / branching | `solver/decide.rs` + `solver/heuristic.rs` (`pick_branch_var`); `vsids.rs/chb.rs/lrb.rs/vmtf.rs` heaps |
| Backtrack / restart | `backtrack_with_phase_saving` (`decide.rs`), `restart()`, Luby; `chronological_backtrack.rs` |
| Leaf data | `literal.rs`, `clause.rs`, `trail.rs`, `big.rs`, `memory_opt.rs` |
| Theory protocol (thin — the *desync*-bug surface is on the *theory* side, not here) | `TheoryCallback` trait `mod.rs:73-86`→`78-91` (`on_new_level` has a **default empty body** :82→:87); result enum `mod.rs:60-69` |

> ⚠️ **POST-PHASE-0 CORRECTION to the "Trusted nucleus" label.** The conflict-analysis row above is in the always-on nucleus but was **not** defect-free. `analyze()` carried **two** soundness defects — the pure-SAT `lits[0]` spurious-UNSAT *and* a CDCL(T) degenerate-conflict spurious-SAT (BUG 2) — and `analyze_theory_conflict` carried the placeholder leak + a positional defect. Their shared root: the textbook invariant "every conflict has a current-level literal" / "the implied literal sits at `lits[0]`" is violated **only** by the CDCL(T) calling pattern (theory-propagated lower-level units falsifying an original clause at a higher level; watched-literal movement relocating a reason's implied literal). **Treat `analyze`/`analyze_theory_conflict`/`solve_with_theory`-propagation-sequencing as a soundness-sensitive *shared* surface**, not as part of an assumed-sound nucleus. All defects are now fixed (`cc3872c`+`4419298`+`5527290`) and regression-pinned.

### 3.3 Advanced features (standalone, ~34k lines, reachable only by directly constructing their structs)

`preprocessing_core.rs` (760L) + `preprocessing/{advanced, gate_extraction, variable_elimination}.rs`; `xor.rs` (1419L — GF(2) Gaussian elimination, **never referenced from `solver/*.rs`**); `cube.rs`/`cube_solver.rs`/`tactics/cube_improve.rs`; `gpu.rs` (1353L); `ml_branching.rs` (655L); `proof.rs` (865L) + `drat_inprocessing.rs` (590L) + `resolution_graph.rs` (727L); and the dormant rest (`symmetry`, `lookahead`, `local_search`, `backbone`, `maxsat`, `allsat`, `distillation`, `hyper_binary`, `vivification.rs`, community, autotuning, portfolio, parallel/). The **only** in-loop entry into preprocessing is `inprocess()` (`learn.rs:403-424`), gated by `config.enable_inprocessing` at `mod.rs:785`.

### 3.4 Default-on status (two config layers)

**(1) `oxiz-sat` `SolverConfig::default()` (`mod.rs:183-203`)** — the pure-SAT defaults: Luby restarts; `var_decay 0.95`; `random_polarity_prob 0.02`; `enable_lazy_hyper_binary = TRUE`; VSIDS (CHB/LRB off); **`enable_inprocessing = FALSE`**; `enable_chronological_backtrack = TRUE`; `external_branching = None` (ML off).

**(2) `oxiz-solver` `SolverConfig::default()` (`oxiz-solver/src/solver/types.rs:281-310`)** — what the actual SMT/verus delegation path uses. It builds the SAT config (`oxiz-solver mod.rs:161-166`) forwarding **only** `restart_strategy` + `enable_inprocessing` + `inprocessing_interval`: Geometric restarts, **inprocessing OFF**, `inprocessing_interval = 0`. So in the verus/SMT path: inprocessing OFF, XOR/cube/GPU/ML/proof/resolution-graph **all OFF (never constructed)**. SMT core entry is `self.sat.solve_with_theory(&mut theory_manager)` (`oxiz-solver mod.rs:492`).

**What actually runs in the default SMT (`solve_with_theory`) path:** propagate (BCP), `analyze`/1-UIP + minimization, `learn_clause`, `backtrack_with_phase_saving`, restart, `reduce_clause_database` (always-on tier deletion), chronological backtrack, lazy-hyper-binary, VSIDS, and the theory callbacks. **Neither inprocessing nor vivification runs here.**

**What runs in the default pure-SAT (`solve`) path additionally:** `vivify_clauses()` (`learn.rs:324`→`339`), invoked in `solve()` only (no config flag) at `mod.rs:771`→`875`, **triple-gated**: `conflicts_since_deletion >= clause_deletion_threshold` (`mod.rs:867`, i.e. on the clause-DB-reduction cadence) AND `restarts % 10 == 0` (`:872`) AND `decision_level == 0` (`:874`). This is the **one** always-on clause-mutating technique on the default pure-SAT loop, and the one the §2 audit's spurious-UNSAT campaign drives that the SMT verdicts never see — but it fires less often than "unconditional" implies.

### 3.5 Soundness-risk ranking (clause-mutating transforms are the dangerous ones)

| Rank | Feature | Intrinsic risk | Default-on (SMT path) |
|---|---|---|---|
| 1 | Inprocessing / preprocessing (BVE, blocked-clause, subsumption, pure-literal, on-the-fly strengthening) — `inprocess()`/`strengthen_clauses_inprocessing()` mutate `clause.lits` directly **without rebuilding watch lists** | **HIGHEST** | **NO** (`enable_inprocessing=false` both configs) |
| 2 | XOR reasoning (`xor.rs`, GF(2) Gauss) — notorious bug class; project's own §3.5 history hit GF(2) issues | **VERY HIGH** | **NO** — and **not wired** into either solve loop |
| 3 | Cube/cube-and-conquer + GPU accelerator | HIGH | NO; not wired |
| 4 | **Vivification (in-loop `vivify_clauses` `learn.rs:324`)** — the **only** clause-mutating advanced technique that is **default-ON in pure-SAT `solve()`** | MEDIUM-HIGH | **pure-SAT only** (NOT in `solve_with_theory`) |
| 5 | ML-branching + chronological backtracking — branching can't affect soundness; chrono only changes backtrack *target level* (perf), but a wrong level can corrupt trail/watch invariants | LOW-MEDIUM | chrono ON; ML off |
| 6 | Clause-DB reduction (`reduce_clause_database`) — deletes only **learned** clauses, skips reason clauses + binaries → soundness-preserving by construction | LOW | ON everywhere |
| 7 | `proof.rs` / `drat_inprocessing.rs` / `resolution_graph.rs` — emission/analysis only; a buggy proof is a wrong *certificate*, not a wrong *verdict* | LOWEST (latent) | off; not wired |

**Net:** the only soundness-relevant advanced code on the **default SMT path** is essentially **none**; on the **default pure-SAT path** the only extra is in-loop vivification. The big risky engines are dormant unless explicitly turned on — consistent with all 6 **DESYNC-class** bugs landing in the theory-integration glue. *(The post-Phase-0 conflict-analysis defects — BUG 2/BUG 3 — are a separate, **nucleus-side** class in the shared `analyze`/`solve_with_theory` surfaces, not in the glue; see the §3.2 correction.)*

### 3.6 Separability — strongly YES

1. The trusted nucleus is self-contained in `Solver` + `solver/{propagate,conflict,learn,decide,heuristic,incremental}.rs` + leaf data modules + branching heaps + chrono-backtrack + BIG — ~3.5–5k lines, **no compile-time or call dependency** on `xor/cube/gpu/ml_branching/proof/resolution_graph` (the `self.{...}` grep is empty).
2. Disabling the risky features needs **no surgery** — they are already off by default. A minimal-trusted-core build is: (a) use default `SolverConfig`, (b) feature-gate the one default-on clause-mutator in pure-SAT (`vivify_clauses` `mod.rs:771`) *or* restrict the trusted layer to `solve_with_theory` (which never vivifies), (c) integration layer calls `solve_with_theory` exclusively.
3. The cleanest integration boundary already exists: `TheoryCallback` + `solve_with_theory`. **Caveat for the redesign:** the desync bugs are in this **advisory protocol** (`on_new_level` empty default body; restart-notify is the caller's responsibility, a documented hazard at `learn.rs:269-279`) — so the redesign hardens the **protocol/contract**, it does **not** rewrite propagate/analyze/learn.

---

## 4. The recommended design

Goal, stated in the oxiz-mbqi idiom ("make the bug *unrepresentable*, don't guard it"): the desync bug **class** — not just the 6 instances — must become impossible **by construction**.

### 4.1 The structural lock-step invariant

> **INVARIANT.** The theory context stack and the SAT trail's decision-level boundaries are **two projections of the same data structure**, mutated by **one owner (the `Trail`)**, so
>
> `|theory frames| == trail.decision_level() + 1`
>
> holds **after every single trail mutation**, not merely at notification points.

**Who owns the trail today vs. the fix.** Today the theory keeps a **parallel** stack — `TheoryManager.level_stack: Vec<usize>` (`theory_manager.rs:51-52`) plus `euf/arith/bv` push/pop driven by `while`-loops comparing `level_stack.len()` to a passed-in `u32` (`on_new_level` `theory_manager.rs:1692-1697`, `on_backtrack` `:1702-1708`). **Two stacks, two owners, advisory sync → desync is the default.** The fix **deletes the parallel stack** and lets the trail drive frame transitions.

**Register the theory ON the trail; make push/pop atomic with the level move:**

```rust
struct Trail {
    // ... existing fields ...
    theory: Option<Box<dyn TheoryHooks>>,   // the theory lives ON the trail
}

impl Trail {
    fn new_decision_level(&mut self) {                 // trail.rs:114 — the ONLY level-up site
        self.current_level += 1;
        self.level_starts.push(self.assignments.len());
        if let Some(t) = &mut self.theory {
            t.push_frame(self.current_level);          // atomic with the level move
        }
    }

    fn backtrack_to_with_callback(&mut self, level: u32, cb: impl FnMut(Lit)) {
        // decide.rs:61 — the ONLY level-down site
        while self.current_level > level {
            if let Some(t) = &mut self.theory {
                t.pop_frame(self.current_level);       // atomic, per level
            }
            // ... pop assignments (firing unassign_hook), run cb ...
            self.current_level -= 1;
        }
    }
}
```

Because `push_frame`/`pop_frame` fire from **inside** the level-mutating functions, **every** caller is covered with **zero** per-call-site discipline: `solve()` (`mod.rs:795`), `solve_with_theory()` (`mod.rs:1074`), `restart()` (`decide.rs:119, 175`), `vivify` (`learn.rs:357`), incremental `push`/`pop` (`mod.rs:1180`), `solve_with_assumptions` (`mod.rs:868`). The restart-without-notify hazard (`learn.rs:270-278`) and the `LocalLbd`-restart bug (`decide.rs:175`) become **structurally impossible**: there is no path that moves the level without moving the frame.

> ⚠️ **CORRECTION — `current_level` has FOUR writers, not two.** Verified on `trail.rs`: `new_decision_level` (`:115`, `+= 1`), `backtrack_to_with_callback` (`:228`, `= level`), **`backtrack_to_size` (`:195`, `= 0`)**, and **`clear` (`:266`, `= 0`)**. The first two are the intended hook sites; the latter two **bypass** the hook. `backtrack_to_size` is reached by the incremental-SMT `pop()` path (`incremental.rs:99`, `mod.rs:1369`) — a legitimate level-down on exactly the push/pop surface §4.1 lists as "covered by construction," so frames *would* desync there. (`clear` is reached only from a full `reset()` at `mod.rs:1404`, where a frame desync is benign because the entire solver state is wiped; `backtrack_to` at `:201` delegates to `backtrack_to_with_callback` and is fine.) **For the by-construction guarantee to be literally true, re-implement `backtrack_to_size` (and `clear`) in terms of `backtrack_to_with_callback`, or enumerate all four writers and discharge each.** As written, "the *two* sole mutators" is the design's intent, not the current code.

### 4.2 The minimal sound SAT-engine API

The current `TheoryCallback` (`oxiz-sat/src/solver/mod.rs:73-86`) is **advisory** and structurally unsound in three ways:

- `on_assignment(lit)` fires per new trail literal over a **re-scanned slice**, deduped by a fragile `theory_processed` index hack (`mod.rs:950,965,985,999,1021`) hand-resynced after every backtrack via `.min(trail.len())`.
- `on_new_level(level)` has a **default empty body** (`mod.rs:82`) → a theory can silently skip frame pushes.
- `on_backtrack(level)` is called by the **solver loop** at 6+ distinct sites (`mod.rs:962,971,1018,1027,1053,1062,1113,1122`), each a separate hand-written call that can be (and was) forgotten — `restart()` and `LocalLbd` restart backtrack the trail **without** any `on_backtrack`; the loop only notifies if `handle_clause_deletion_and_restart` happens to return `true`.

**Replacement: a NARROWER but MANDATORY, trail-driven contract — 5 methods, two of them driven by the trail not the loop.**

```rust
/// Implemented by the theory; the engine OWNS the calling discipline.
trait TheoryHooks {
    // (1)+(2) DRIVEN BY THE TRAIL, not the solve loop — fired from inside
    //         Trail::assign / Trail::new_decision_level / Trail::backtrack_to_with_callback.
    fn assign_hook(&mut self, lit: Lit, level: u32) -> TheoryStep; // each assign, once, in trail order
    fn unassign_hook(&mut self, lit: Lit, level: u32);             // each unassign, once, in trail order
    fn push_frame(&mut self, level: u32);                          // atomic with level-up
    fn pop_frame(&mut self, level: u32);                           // atomic with level-down

    // (3) full theory check + SAT-side completeness oracle
    fn final_check(&mut self) -> TheoryStep;
    fn eval(&mut self, atom: AtomId) -> Option<bool>;             // model-eval oracle (mirrors oxiz-mbqi host eval)
}

/// The only ways a theory can talk back. No sentinel, no empty conflict.
enum TheoryStep {
    Ok,
    Propagate { lit: Lit, reason: TheoryReason },   // reason is NON-NULL by type
    Conflict  { reason: TheoryReason },             // the ONLY conflict channel; non-empty, level-tagged
}
```

Key consequences:
- `assign_hook`/`unassign_hook` are emitted by `Trail::assign` and `Trail::backtrack_to_with_callback` — **the engine already has the unassign callback-closure plumbing** (`decide.rs:61 backtrack_to_with_callback`), so we extend it to also drive the theory. This **eliminates the `theory_processed` re-scan/dedup entirely**: the theory sees exactly each assign once and each unassign once, in trail order, never a re-scanned slice.
- `Conflict { reason }` is the **only** conflict channel, so `analyze_theory_conflict` always receives a **well-formed, non-empty, level-tagged** literal set.

### 4.3 The typed `Reason`

Today `Reason` (verified at `trail.rs:8-17`) is exactly:

```rust
pub enum Reason {
    Decision,
    Propagation(ClauseId),
    Theory,                // opaque — no theory-lemma identity; explanation flattened into a synthesized clause at learn.rs:135
}
```

The new contract makes it **typed and non-nullable**:

```rust
pub enum Reason {
    Decision,
    Propagation(ClauseId),
    TheoryLemma(TheoryReasonId),   // stable handle; the theory is asked to EXPLAIN lazily
}

/// First-class explanation carried by value, not flattened into a synthesized clause.
struct TheoryReason {
    asserting: Lit,        // the implied/asserting literal — an INPUT, never a discovered output
    explanation: SmallVec<[Lit; 8]>,   // the false literal set
}
```

`assign_propagation` **requires** a non-null reason, so a theory propagation with no explanation is **unrepresentable**.

### 4.4 How each of the 6 fixed integration bugs becomes impossible by construction

| # | Bug (this session) | Today's mechanism | Made impossible by |
|---|---|---|---|
| 1 | **Frame-stack desync** (atom asserted both polarities at one level) | parallel `level_stack` synced advisorily to the trail | §4.1: one owner; `push_frame`/`pop_frame` fire **inside** the sole level-mutators → `|frames| == level+1` always |
| 2 | **Restart not notifying the theory** | `restart()`/`LocalLbd` backtrack the trail without `on_backtrack` (`learn.rs:270-278` hazard) | §4.1: restart routes through `backtrack_to_with_callback` → `pop_frame` fires by construction |
| 3 | **Stale theory bound** (retracted atom still asserts a bound) | suppression heuristics `last_conflict_is_stale_bound()` at `theory_manager.rs:616, 1092, 1500, 1654` (FOUR sites) | §4.2: `unassign_hook` retracts the bound the instant its literal leaves the trail → a stale bound cannot exist; the **four suppression heuristics get DELETED** |
| 4 | **Sentinel reason literal leak** | `Lit::from_code(0)` placeholder (`conflict.rs:386`→`:546`) only overwritten if a UIP is found; `p==None` → var-0 leaks (`conflict.rs:479`→fixed at `:654-695`) | §4.3: the asserting literal is an **input** carried in `TheoryReason`, not a discovered output → placeholder slot removed; `p==None` leak cannot occur. *(Phase 0 already closed this at runtime by dropping the placeholder — §5; §4.3 is the stronger structural kill.)* |
| 5 | **Re-scan/dedup desync** (`theory_processed.min()` resyncs) | `theory_processed` index hack hand-resynced after each backtrack (`mod.rs:965,1021`) | §4.2: `assign_hook`/`unassign_hook` deliver each event exactly once in trail order → the re-scan index is **gone** |
| 6 | **Spurious-unsat-needing re-verification** (`verify_clean_unsat`, `oxiz-solver mod.rs:494-503` — re-solves a single-shot ground check because incremental CDCL(T) can report spurious unsat) | advisory protocol lets frames/bounds desync across lemma rounds | §4.1+§4.2 together remove the desync class → the defensive re-verify becomes unnecessary (keep it as a belt-and-braces CI assertion, not a correctness crutch) |

> ⚠️ **The table above is correctly scoped to the 6 DESYNC-class bugs and holds for them — but it is NOT exhaustive over all soundness defects.** Phase 0 found two more that this design does **NOT** make impossible by construction, because they are **conflict-analysis robustness** defects orthogonal to theory-frame-sync:
>
> | # | Bug (Phase 0) | Why §4 does NOT kill it | Required fix (landed) |
> |---|---|---|---|
> | **B2** | **Degenerate conflict in `analyze()`** — a conflict clause with *no* literal at the current decision level (a theory-propagated lower-level unit falsifies an original clause while at a higher level). 1-UIP fabricates garbage → spurious SAT. | §4.1's lock-step invariant constrains frame *depth*, not the *level* a theory-propagated literal occupies. Perfect frame sync still admits a no-current-level conflict. **Orthogonal to theory-sync.** | A degenerate-conflict guard in `analyze()`: learn the (deduped) conflict clause itself, place highest-level lit at `[0]` / 2nd-highest at `[1]`, backtrack below the highest level (`conflict.rs:140-211`). |
> | **B3** | **Missing BCP-settle after a theory-conflict learn** in `solve_with_theory` — a level-0 contradiction created by the learned unit went undetected before the next decision → spurious SAT. | A loop-ordering invariant ("BCP runs to fixpoint before any decision / `final_check`"), which the `TheoryStep::Conflict` channel (§4.2) does not by itself enforce. | `propagate()` + re-analyze (level-0/empty ⇒ UNSAT) immediately after the theory-conflict learn (`mod.rs:1138-1160`). |
>
> **These two are PRECONDITIONS of the redesign, not consequences of it.** The design should adopt them as explicit conflict-analysis invariants (see §4.5), and a sound CDCL(T) port MUST preserve them — `analyze()`/`analyze_theory_conflict` must never assume a current-level literal exists, and no decision/`final_check` may run with BCP pending.

### 4.5 Invariant check (debug-assert, runs in CI/fuzz)

After every assign/backtrack:

```rust
debug_assert!(theory.frame_depth() == trail.decision_level() + 1);
debug_assert!(theory.asserted_atoms().is_subset(&trail.live_literals()));
```

Cheap, and would have caught **all 6 DESYNC-class bugs** **at the mutation site** rather than as a downstream spurious verdict — exactly the oxiz-mbqi move of one central invariant replacing four ad-hoc checks.

**But these two asserts would NOT have caught Phase 0's BUG 2 / BUG 3** — a degenerate conflict has correct frame depth and a correct atom-subset, and a skipped propagation leaves the trail consistent. The conflict-analysis robustness invariants (§4.4 addendum) need their own asserts:

```rust
// At pick_branch_var() / final_check() entry — catches BUG 3 (BCP must be at fixpoint before deciding):
debug_assert!(!trail.has_pending_propagation());
// At analyze()/analyze_theory_conflict() entry — catches BUG 2 (a non-empty conflict either has a
// current-level literal, or is routed to the degenerate-conflict path, never to the textbook UIP walk):
debug_assert!(conflict.is_empty()
    || conflict.lits().any(|l| trail.level(l.var()) == trail.decision_level())
    || handling_degenerate_conflict);
```

---

## 5. Phased plan (oxiz-mbqi playbook: standalone + differential-fuzz gate, then port)

### Phase 0 — Trusted-core soundness gate — ✅ EXECUTED (commit `5527290`)

This phase decided whether the engine can be reused or whether scope must escalate. **It has been run.** Its four steps and outcomes:

1. ✅ **Fixed `conflict.rs::analyze()`** (the §2 bug): the 1-UIP traversal now processes every reason literal and never relies on a reason clause's `lits[0]` being the implied literal (`cc3872c`; sibling `[1..]` fix in `analyze_theory_conflict` `4419298`). `oxiz-sat/tests/soundness_repro.rs::minimal_spurious_unsat_default_config` is now a plain `#[test]` and **passes**.
2. ✅ **Wired the pure-SAT differential fuzz to drive `pure_sat_runner`** (the pure engine, not `oxiz --dimacs`): `oxiz-sat/tests/sat_diff_fuzz_pure.py` (vs cadical/z3/cryptominisat5). *(The original `sat_diff_fuzz.py` — the false-negative harness — was removed.)*
3. ✅ **DRAT-verified fuzz** — `DratWriter` wired into the pure `solve()` loop behind `Option<DratWriter>` (default `None`, hot path untouched); `oxiz-sat/tests/sat_diff_fuzz_pure_drat.py` replays every oxiz UNSAT through `drat-trim`. **8,938 UNSAT proofs verified, 0 drat-trim rejections.** Closes coverage gap §2.5(2). *(Caveat: certifies the **pure-SAT** path only — see §6.2.)*
4. ✅ **Theory-callback fuzz** — `oxiz-sat/tests/theory_callback_fuzz.rs` exercises `add_theory_reason_clause` and `analyze_theory_conflict` against a synthetic **provably-sound** theory (secret model `a*` + rejection-sampled 2-lit axioms), brute-force + z3/cadical-cross-checked, every SAT model independently re-validated. Closes coverage gap §2.5(1).

**Gate verdict — the engine was NOT clean on first pass, but is reusable after a bounded surgical fix-set.** The theory-callback fuzz found **three** real soundness defects (all reproduced, all z3/cadical-cross-checked, all regression-pinned):

| Defect | Site | Direction | Regression (`theory_callback_fuzz.rs`) |
|---|---|---|---|
| Placeholder leak (predicted, §2.5(1)) | `analyze_theory_conflict` `p==None` | latent | `regress_theory_conflict_reason_position_unsat:1047` + `theory_conflict_placeholder_leak_targeted:608` |
| **BUG 2** — degenerate conflict (no current-level lit) | `analyze()` `conflict.rs:140-211` | spurious-SAT | `regress_bool_analyze_all_level0_sat:1062` |
| **BUG 3** — missing post-conflict BCP-settle | `solve_with_theory` `mod.rs:1138-1160` | spurious-SAT | `regress_post_theory_conflict_propagation_sat:1077` |

All three share **one root cause** — CDCL invariants the CDCL(T) cycle violates — and all were fixed surgically (`5527290`, ~270 net LoC) without touching propagate/watched-lits/clause-DB/restart. **Post-fix validation:** >2.2M theory-callback differential instances (0 unsound), SMT-vs-z3 EUF 4500 + arith 6000 (fatal=0), pure-SAT 8k + DRAT 6k (0 unsound); oxiz-sat lib 609 / oxiz-theories 1172 / oxiz-solver 526 green.

**Conclusion: engine reusable (beyond the two §4 structural edits + the landed conflict-analysis hardening) → proceed to Phase 1.** No repros clustered across *independent* core subsystems, so scope stays NARROW (§6.3); the gate's "stays clean on first pass" wording is superseded by "reusable after a bounded, single-class conflict-analysis hardening track."

### Phase 1 — Standalone `TheoryHooks` contract + toy theory (no real EUF/arith yet)

- Land the `TheoryHooks` trait (§4.2), typed `Reason` (§4.3), and the trail-driven hooks (§4.1) in `oxiz-sat`, behind the new contract — analogous to oxiz-mbqi's standalone `TermLang`.
- Build a **toy in-crate theory** for unit + corpus testing.
- Add the §4.5 debug-assert invariant.
- **Validate as CDCL(T)** against z3/cvc5 on QF_UF / QF_LIA / QF_BV using the existing **`ground_soundness_fuzz.rs`** harness as the gate.

### Phase 2 — Port the real theories onto the new contract

- Re-implement `theory_manager.rs`'s advisory callbacks as a clean trail-driven manager over the real EUF/arith/simplex (`oxiz-theories`).
- **DELETE** the parallel `level_stack`, the three `last_conflict_is_stale_bound()` suppression heuristics, and the `theory_processed` re-scan index — they are now unrepresentable, not guarded.
- Keep `verify_clean_unsat` initially as a CI assertion; remove the *dependence* on it once the invariant holds across the full QF_UF/LIA/BV corpus.

### Phase 3 — Re-run the full differential gate + bake into CI

- All four harnesses wired as permanent CI gates: `sat_diff_fuzz_pure.py` (pure SAT vs cadical), `sat_diff_fuzz_pure_drat.py` (DRAT-verified), `theory_callback_fuzz.rs` (CDCL(T) synthetic-theory differential), and `ground_soundness_fuzz.rs` (CDCL(T) vs z3).
- Re-run the §2 campaign at scale; confirm `unsound = 0` on the pure path AND the theory path. *(Phase 0 already established this baseline on the current engine; Phase 3 re-confirms it on the rewritten contract.)*

**Validation gates (existing harnesses):** `oxiz-sat/tests/sat_diff_fuzz_pure.py` + `sat_diff_fuzz_pure_drat.py` (pure engine via `pure_sat_runner`, agreement + DRAT-verified), `oxiz-sat/tests/theory_callback_fuzz.rs` (CDCL(T) vs a synthetic provably-sound theory; `theory-probe` feature), and `ground_soundness_fuzz.rs` (CDCL(T) vs z3/cvc5). The bisection oracle that was unsound for MBQI is unsound here for the same reason (advisory two-stack sync) until Phase 2 lands — so do not rely on delta-debugging for regressions before the invariant holds.

---

## 6. Risks, effort, and the scope-width decision

### 6.1 Effort (rough)

| Work item | Rough effort |
|---|---|
| Phase 0: conflict-analysis hardening + DRAT gate + theory-callback fuzz — **DONE** (`5527290`) | small-medium **(LANDED)**: not "a few lines" — the realized trusted-core hardening is ~270 net LoC (`conflict.rs` +211/−2: degenerate-conflict guard + placeholder-drop branch; `mod.rs` +199: 5 new empty-clause-as-UNSAT guards + BUG-3 propagate-and-reanalyze block + DRAT wiring), plus `cc3872c`+`4419298`. Harness wiring + fuzz campaigns were the bulk of the cost. |
| Phase 1: standalone `TheoryHooks` + typed `Reason` + trail-driven hooks + toy theory | medium (the two §4 engine edits + contract design + toy-theory corpus) |
| Phase 2: port EUF/arith/simplex; delete parallel stack + suppression heuristics | medium-large (~6.8k glue lines re-architected, but mechanically constrained by the new contract) |
| Phase 3: full differential gate + CI | small-medium |

**Total: bounded — re-architect ~6,800 lines of glue + two surgical engine edits + a bounded conflict-analysis hardening sub-track (~270 LoC, already landed).** This is still roughly an order of magnitude less than a 38k-line full rewrite. *(The first draft estimated "one localized `analyze()` fix"; Phase 0's actual conflict-analysis hardening was an order of magnitude larger than that single line item, though still small in absolute terms and now complete.)*

### 6.2 Risks

- **The two §4 engine edits touch the trail's hot path** (`new_decision_level`, `backtrack_to_with_callback`). Mitigation: they are *additive* (one `if let Some(t)` per level move); the existing unassign callback plumbing already proves the closure path is viable; the §2 fuzz gate guards against regressions.
- **Phase-0 escalation risk — RESOLVED (did not escalate).** The theory-only surfaces (`add_theory_reason_clause`, `analyze_theory_conflict`) and the Boolean `analyze()` under CDCL(T) have now been fuzzed; they yielded a *bounded, single-root* cluster (placeholder + BUG 2 + BUG 3), all fixed without touching other subsystems, so scope did **not** widen (see §6.3).
- **Conflict-analysis / watched-literal fragility (NEW, demonstrated in Phase 0).** The conflict analyzers rely on textbook CDCL invariants the CDCL(T) cycle breaks, and the fixes carry their own fragility: the BUG-2 degenerate-conflict guard returns *before* the normal path's common second-watch arrangement, so it must **re-implement** two-watched-literal placement by hand (`conflict.rs:188-205`: *"the second watch must be the highest-level literal among the rest … without this the clause could later be fully falsified without a watch firing — a missed conflict ⇒ unsound SAT"* — a manual `swap(1, second_idx)`). This per-site duplication is exactly the kind of representable-bad-state the §4 "make-it-unrepresentable" philosophy should absorb. **Recommendation:** route *all* learned-clause finalization (normal + degenerate + theory) through ONE function that enforces empty-clause-as-UNSAT and the two-watched-literal placement — apply the §4 discipline to conflict analysis, not only to theory-sync.
- **DRAT gate does not cover the CDCL(T) path.** The DRAT self-certification (§2.5(2), §6.3) certifies the **pure-SAT** path only: `pure_sat_runner` bypasses the theory layer, and theory lemmas are theory-justified, not propositional RUP/RAT, so they are deliberately not logged. DRAT therefore cannot catch the spurious-**SAT** defects (BUG 2/BUG 3) — DRAT certifies UNSAT, not SAT. The CDCL(T)-path soundness gate is `theory_callback_fuzz.rs` + `ground_soundness_fuzz.rs`, not DRAT.
- **Performance:** the lock-step hooks add per-level/per-assign work; must profile against the existing wall budgets (the §3.5 JIT/AOT work in the broader project is wall-sensitive). Mitigation: hooks are `Option`-gated and no-op in the pure-SAT path.
- **Dead-code latent risk:** XOR/Gauss, cube, GPU, ML-branching inflate the line count and expose a **dead-but-public** API. Recommend **quarantining/feature-gating** them (out of the default build surface) so they cannot be accidentally wired into a sound path later. This is a maintenance/hygiene item, not a soundness fix.

### 6.3 What would make us choose a BROADER vs NARROWER scope

**Stay NARROWER (the recommendation — integration-layer clean-room + the conflict-analysis hardening) when:**
- the conflict-analysis / CDCL(T)-driver defects share **one root cause** (a fixed set of CDCL invariants the theory cycle breaks), AND
- they are surgically repairable **without** touching propagate / watched-lits / clause-DB / restart, AND
- post-fix DRAT (pure-SAT) + theory-callback fuzz + SMT-vs-z3 return **0 unsound**.

> *(Original draft's gate — "Phase 0 stays clean after the `analyze()` rewrite" and "the theory-callback fuzz finds nothing beyond the `conflict.rs:386` sentinel" — was **falsified** by Phase 0: the fuzz found BUG 2 + BUG 3 + the reason-position defect beyond the placeholder. But the narrow **conclusion** survives via the common-single-root criterion above, which the original gate text did not encode. Phase 0 landed in the MIDDLE escalation branch below, and that branch's surgical fix sufficed — validated by >2.2M theory-callback instances + 6k DRAT proofs at 0 unsound.)*

This is the evidence we have: the engine is DRAT-self-certifying **on the pure-SAT path**, the advanced engines are dormant, and the conflict-analysis defects are a single-root cluster, not multi-subsystem rot.

**Escalate to integration-layer + minimal trusted core when (THIS is the branch Phase 0 landed in):**
- the theory-callback fuzz surfaces a real defect in the **conflict-analysis surface** — `analyze`, `analyze_theory_conflict`, or `solve_with_theory` propagation-sequencing (broadened from the original "the two theory-only surfaces", because BUG 2 fell in the *shared Boolean* `analyze()`, which the original trigger did not cover) → harden **just** that surface + the reason-clause machinery (still short of a full rewrite), or
- the corrected pure-SAT fuzzer, **after** the `analyze()` fixes, keeps producing **distinct** minimal repros in *other* core subsystems (propagate/learn/backtrack) → the conflict/trail/watch invariants are systemically under-specified. **(Did NOT occur — those subsystems stayed clean across 8k pure-SAT + 6k DRAT instances.)**

**Escalate to a FULL SAT rewrite only when:**
- repros cluster across *multiple independent* core subsystems **with no common cause** — i.e. the 38k engine is pervasively under-specified, not locally buggy. **Nothing in the current evidence points here.** Even after Phase 0, all defects (the two `analyze()` bugs, the `analyze_theory_conflict` placeholder/positional, the `solve_with_theory` BCP-settle) share **one** root cause — CDCL invariants the theory cycle violates — and confine to the conflict-analysis surface; propagate / watched-lits / clause-DB / restart / LBD stayed clean across the pure-SAT + DRAT campaigns. That is the signature of a *single-class cluster*, not systemic rot.

**Never: keep-patching.** This session's fixes (`last_conflict_is_stale_bound` suppression; `theory_processed.min()` resyncs; the documented-but-unenforced restart hazard) are exactly the whack-a-mole the oxiz-mbqi `DESIGN.md` calls out — guards that mask symptoms while the bug class (two parallel stacks synced advisorily) stays representable. Each new theory or restart strategy can reopen it.

---

## Appendix — Anchors (branch `0.2.4-feat/cdqi`)

> **Note.** Line numbers below were captured on the pre-Phase-0 tree; after commit `5527290` (`conflict.rs` +211/−2, `mod.rs` +199) many shifted by up to ~150 lines. Each underlying claim was **re-verified** on HEAD `5527290`; refreshed anchors are shown as `old`→`new`.

- `Reason` enum = `Decision | Propagation(ClauseId) | Theory` (untyped) — `oxiz-sat/src/trail.rs:8-17` (`enum` at `:10`). ✔ (still untyped — §4.3 not yet applied)
- `analyze_theory_conflict` pushes `Lit::from_code(0)` placeholder — `oxiz-sat/src/solver/conflict.rs:386`→`538` (fn). ✔ **LANDED-FIX:** the leak is now closed — when the UIP walk ends `p==None` the placeholder is dropped (`conflict.rs:654-695`, `5527290`).
- `analyze()` 1-UIP — `oxiz-sat/src/solver/conflict.rs:35`→`110`. ✔ **LANDED-FIX:** `lits[0]` spurious-UNSAT fixed (`cc3872c`); degenerate-conflict spurious-SAT guard added (`conflict.rs:140-211`, `5527290`).
- `TheoryCallback::on_new_level` has empty default body; `on_backtrack` mandatory — `oxiz-sat/src/solver/mod.rs:73-86`→`78-91` (`on_new_level` at `:87`, `on_backtrack` at `:90`). ✔
- `vivify_clauses()` invoked in `solve()` only, triple-gated (`conflicts_since_deletion ≥ clause_deletion_threshold` AND `restarts%10==0` AND `level==0`) — call at `oxiz-sat/src/solver/mod.rs:768-778`→`875` (fn `learn.rs:324`→`339`). ✔ (NOT "unconditional" — see §3.4)
- `last_conflict_is_stale_bound()` suppression sites: **FOUR**, not three — `oxiz-solver/src/solver/theory_manager.rs:616, 1092, 1500, 1654` (the original §4.4 row 3 cited only three: 616/654/1654; "654" was never a stale-bound site — now corrected in §4.4 to all four). ✔
- `add_theory_reason_clause` — `oxiz-sat/src/solver/learn.rs:135`→`141`. ✔
- Pure-SAT differential harness present — `oxiz-sat/tests/sat_diff_fuzz_pure.py` (+ DRAT-verified `sat_diff_fuzz_pure_drat.py`). ✔ *(the originally-cited `sat_diff_fuzz.py` was the false-negative harness and was removed.)*
- Theory-callback differential harness present — `oxiz-sat/tests/theory_callback_fuzz.rs` (`theory-probe` feature). ✔ (new in Phase 0)
- `drat: Option<DratWriter>` field on `Solver` (default `None`, no-op hot path) — `oxiz-sat/src/solver/mod.rs:409`; `enable_drat` `:484`. ✔ (new in Phase 0; soundness-neutral, §3.5 rank 7)
