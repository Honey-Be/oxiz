# OxiZ SAT Core — Redesign Scope Assessment

**Status:** Design recommendation (no code in this document)
**Date:** 2026-06-13
**Branch:** `0.2.4-feat/cdqi`
**Audience:** OxiZ maintainer / sign-off holder
**Inputs:** three structured audit findings (pure-SAT differential-fuzz soundness audit; architecture/feature map; engine-trust + minimal-sound-API + lock-step-invariant design probe).

---

## 1. Executive summary and bottom-line recommendation

This session fixed **6 soundness bugs** (spurious `unsat`/`sat`), and the post-mortem question is: do we clean-room rewrite the SAT core the way the quantifier engine was rewritten (`~/oxiz-mbqi`), or is a narrower scope correct?

We then did the thing the user asked for first: we **audited the pure ~38k-line SAT engine** — which had never been differential-fuzzed *as pure SAT*, only ever exercised through the SMT path — to learn whether the engine itself harbors soundness bugs, before recommending a redesign scope.

### Bottom-line recommendation

> **Integration-layer clean-room + one minimal trusted-core fix.**
>
> Rewrite the **CDCL(T) theory-integration layer** (the ~6,800-line glue: the `TheoryCallback` contract in `oxiz-sat` + the advisory `theory_manager.rs` in `oxiz-solver`) clean-room, oxiz-mbqi-style, built **on top of the existing `oxiz-sat` engine reused unchanged** — *except* for the two surgical engine edits the new contract structurally requires (move theory push/pop **inside** the trail's level-mutating functions; make `Reason` typed and delete the sentinel-`0` placeholder). **In addition**, because the pure-SAT audit found a real, reproducible soundness defect in the always-on `analyze()` 1-UIP loop, the trusted core needs **one localized fix to `conflict.rs::analyze()`** (a few-line, textbook 1-UIP rewrite) before it can be trusted standalone. This is **not** a full 38k-line rewrite and **not** keep-patching.

### One-paragraph reason

All 6 of this session's bugs, and the entire bug *class* (frame-stack desync, stale theory bounds, sentinel reason literal), live in the **theory-integration glue**, not in the SAT nucleus — the glue keeps a *parallel* level stack synced to the trail only *advisorily* (`on_new_level` even has an empty default body), so desync is the default failure mode. The pure-SAT audit confirms the engine's propagation, restarts, clause-DB, and LBD machinery are sound and that the big risky engines (XOR/Gauss, cube, GPU, ML-branching, inprocessing) are **dead code with respect to the solve path** — so rewriting 38k trustworthy lines to fix a 6.8k-line integration defect is exactly the wrong leverage (the oxiz-mbqi precedent rewrote the *unsound* layer and reused the sound core). The audit's *one* caveat — a localized, reproducible spurious-UNSAT in `analyze()` — is a targeted single-site bug, not systemic rot, so it warrants a focused fix plus a permanent fuzz gate, **not** an escalation of scope.

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

> ⚠️ **Critical harness correction.** The committed harness's earlier "300 instances, unsound = 0" smoke was a **false negative**. `oxiz --dimacs` does **not** exercise `oxiz-sat`; it converts the CNF to QF_UF SMT-LIB2 and runs the *separate* `oxiz-solver` SMT CDCL (which returns the correct `sat`). A new `pure_sat_runner` example was built to drive `oxiz_sat::Solver` directly (`DimacsParser` + `solve()`), and the bug was reconfirmed by a pure-Rust unit test (`oxiz-sat/tests/soundness_repro.rs`, currently `#[ignore]`/failing) that calls `Solver::new()` + `add_clause()` + `solve()` — no Python, no example — proving it is **not** a harness artifact.

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
   - `add_theory_reason_clause` (`learn.rs:135`) — builds learned reason clauses on the fly with manual watch setup.
   - `analyze_theory_conflict` (`conflict.rs:381`) — a **separate** conflict analyzer from the Boolean `analyze()`, which carries a **latent** bug: the `Lit::from_code(0)` placeholder at `conflict.rs:386` is only overwritten when a UIP is found; if the trail walk terminates with `p == None`, a spurious literal (var 0, positive) leaks into the learned clause.
2. **DRAT-verified UNSAT.** The campaign cross-checked verdicts by *differential agreement* with 4 oracles, not by replaying oxiz's own UNSAT proofs through `drat-trim`. `oxiz-sat` ships DRAT emission (`proof.rs`, `drat_inprocessing.rs`, `parallel/proof_check.rs`); a proper soundness gate should *replay* UNSAT verdicts through `drat-trim` (a far stronger oracle than agreement — a spurious-UNSAT would surface as a `drat-trim` rejection).
3. **The advanced engines as live solvers.** XOR/Gauss, cube, GPU, ML-branching, inprocessing were exercised only as *inputs hitting a core that does not call them*. They were never driven as the answer-producing path because the solve loops never construct them. Their soundness is therefore **untested** (but also **dormant** — see §3).
4. **Long-horizon / large industrial CNF.** The campaign is near-phase-transition + structured-hard but small; no multi-hour single-instance or large real-world industrial run.
5. **Incremental / assumptions paths.** `solve_with_assumptions()` and the incremental add-after-solve path were not the focus of the differential campaign.

**Empirical verdict:** the default pure-SAT engine is **UNSOUND on the shipped Default config** — but the defect is **localized, deterministic, single-site** (the `analyze()` 1-UIP loop), present in Default and 9/10 presets, absent under `randpol=0`. It is a **targeted bug, not pervasive rot.**

---

## 3. Architecture map: core CDCL vs advanced features

### 3.1 Shape

`oxiz-sat` (~38k lines, 75 modules) is a **"mono-struct + standalone-toolbox"** layout, *not* a plugin pipeline. The `Solver` struct (`solver/mod.rs:327-398`) embeds **only** the core CDCL state: `config`, `num_vars`, `clauses: ClauseDatabase`, `trail: Trail`, `watches: WatchLists`, the `vsids/chb/lrb` heuristics, `learnt`/`seen`/`analyze_stack`, restart bookkeeping (Luby index, thresholds, recent/global LBD sums), `binary_graph: BinaryImplicationGraph`, `chrono_backtrack: ChronoBacktrack`, `memory_optimizer`.

**Every advanced module** (`xor` / `cube` / `gpu` / `ml_branching` / `proof` / `resolution_graph` / `symmetry` / `lookahead` / `local_search` / `backbone` / `maxsat` / `allsat` / `preprocessing`) is a **separate top-level struct** exported from `lib.rs` — **none** is a field of `Solver`. A `grep` for `self.{xor,cube,gpu,ml,resolution,proof,drat,symmetry,lookahead,local_search}` over `solver/*.rs` returns **empty**. The advanced toolbox is architecturally decoupled from the solve loops.

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
| Theory protocol (thin — the 6-bug surface is on the *theory* side, not here) | `TheoryCallback` trait `mod.rs:73-86` (`on_new_level` has a **default empty body** :82); result enum `mod.rs:60-69` |

### 3.3 Advanced features (standalone, ~34k lines, reachable only by directly constructing their structs)

`preprocessing_core.rs` (760L) + `preprocessing/{advanced, gate_extraction, variable_elimination}.rs`; `xor.rs` (1419L — GF(2) Gaussian elimination, **never referenced from `solver/*.rs`**); `cube.rs`/`cube_solver.rs`/`tactics/cube_improve.rs`; `gpu.rs` (1353L); `ml_branching.rs` (655L); `proof.rs` (865L) + `drat_inprocessing.rs` (590L) + `resolution_graph.rs` (727L); and the dormant rest (`symmetry`, `lookahead`, `local_search`, `backbone`, `maxsat`, `allsat`, `distillation`, `hyper_binary`, `vivification.rs`, community, autotuning, portfolio, parallel/). The **only** in-loop entry into preprocessing is `inprocess()` (`learn.rs:403-424`), gated by `config.enable_inprocessing` at `mod.rs:785`.

### 3.4 Default-on status (two config layers)

**(1) `oxiz-sat` `SolverConfig::default()` (`mod.rs:183-203`)** — the pure-SAT defaults: Luby restarts; `var_decay 0.95`; `random_polarity_prob 0.02`; `enable_lazy_hyper_binary = TRUE`; VSIDS (CHB/LRB off); **`enable_inprocessing = FALSE`**; `enable_chronological_backtrack = TRUE`; `external_branching = None` (ML off).

**(2) `oxiz-solver` `SolverConfig::default()` (`oxiz-solver/src/solver/types.rs:281-310`)** — what the actual SMT/verus delegation path uses. It builds the SAT config (`oxiz-solver mod.rs:161-166`) forwarding **only** `restart_strategy` + `enable_inprocessing` + `inprocessing_interval`: Geometric restarts, **inprocessing OFF**, `inprocessing_interval = 0`. So in the verus/SMT path: inprocessing OFF, XOR/cube/GPU/ML/proof/resolution-graph **all OFF (never constructed)**. SMT core entry is `self.sat.solve_with_theory(&mut theory_manager)` (`oxiz-solver mod.rs:492`).

**What actually runs in the default SMT (`solve_with_theory`) path:** propagate (BCP), `analyze`/1-UIP + minimization, `learn_clause`, `backtrack_with_phase_saving`, restart, `reduce_clause_database` (always-on tier deletion), chronological backtrack, lazy-hyper-binary, VSIDS, and the theory callbacks. **Neither inprocessing nor vivification runs here.**

**What runs in the default pure-SAT (`solve`) path additionally:** `vivify_clauses()` (`learn.rs:324`), invoked **unconditionally** at `mod.rs:771` (no config flag — gated only on `restarts % 10 == 0 && decision_level == 0`). This is the **one** always-on clause-mutating technique on the default pure-SAT loop, and the one the §2 audit's spurious-UNSAT campaign drives that the SMT verdicts never see.

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

**Net:** the only soundness-relevant advanced code on the **default SMT path** is essentially **none**; on the **default pure-SAT path** the only extra is in-loop vivification. The big risky engines are dormant unless explicitly turned on — consistent with all 6 of this session's soundness bugs landing in the theory-integration glue.

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

Because `push_frame`/`pop_frame` fire from **inside** the two functions that are the **sole** mutators of `current_level`, **every** caller is covered with **zero** per-call-site discipline: `solve()` (`mod.rs:795`), `solve_with_theory()` (`mod.rs:1074`), `restart()` (`decide.rs:119, 175`), `vivify` (`learn.rs:357`), incremental `push`/`pop` (`mod.rs:1180`), `solve_with_assumptions` (`mod.rs:868`). The restart-without-notify hazard (`learn.rs:270-278`) and the `LocalLbd`-restart bug (`decide.rs:175`) become **structurally impossible**: there is no path that moves the level without moving the frame.

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
| 3 | **Stale theory bound** (retracted atom still asserts a bound) | suppression heuristics `last_conflict_is_stale_bound()` at `theory_manager.rs:616,654,1654` | §4.2: `unassign_hook` retracts the bound the instant its literal leaves the trail → a stale bound cannot exist; the **three suppression heuristics get DELETED** |
| 4 | **Sentinel reason literal leak** | `Lit::from_code(0)` placeholder (`conflict.rs:386`) only overwritten if a UIP is found; `p==None` → var-0 leaks (`conflict.rs:479`) | §4.3: the asserting literal is an **input** carried in `TheoryReason`, not a discovered output → placeholder slot removed; `p==None` leak cannot occur |
| 5 | **Re-scan/dedup desync** (`theory_processed.min()` resyncs) | `theory_processed` index hack hand-resynced after each backtrack (`mod.rs:965,1021`) | §4.2: `assign_hook`/`unassign_hook` deliver each event exactly once in trail order → the re-scan index is **gone** |
| 6 | **Spurious-unsat-needing re-verification** (`verify_clean_unsat`, `oxiz-solver mod.rs:494-503` — re-solves a single-shot ground check because incremental CDCL(T) can report spurious unsat) | advisory protocol lets frames/bounds desync across lemma rounds | §4.1+§4.2 together remove the desync class → the defensive re-verify becomes unnecessary (keep it as a belt-and-braces CI assertion, not a correctness crutch) |

### 4.5 Invariant check (debug-assert, runs in CI/fuzz)

After every assign/backtrack:

```rust
debug_assert!(theory.frame_depth() == trail.decision_level() + 1);
debug_assert!(theory.asserted_atoms().is_subset(&trail.live_literals()));
```

Cheap, and would have caught **all 6** bugs **at the mutation site** rather than as a downstream spurious verdict — exactly the oxiz-mbqi move of one central invariant replacing four ad-hoc checks.

---

## 5. Phased plan (oxiz-mbqi playbook: standalone + differential-fuzz gate, then port)

### Phase 0 — Trusted-core soundness gate (PRECONDITION for "reuse engine unchanged")

This phase decides whether the engine can be reused or whether scope must escalate. **Do this before writing any new glue.**

1. **Fix `conflict.rs::analyze()`** (the §2 bug): rewrite the 1-UIP traversal to the textbook MiniSat/Glucose form — walk the trail strictly in reverse, decrement `counter` only on `seen` current-level vars, stop when `counter == 1`, **never** rely on a reason clause's `lits[0]` being the implied literal. Un-`#[ignore]` `oxiz-sat/tests/soundness_repro.rs`; it must pass.
2. **Wire the corrected `sat_diff_fuzz.py` to drive `pure_sat_runner`** (the pure engine, not `oxiz --dimacs`) and make it a **permanent CI soundness gate**.
3. **Run a 10k-instance overnight DRAT-verified fuzz** — replay every oxiz UNSAT through `drat-trim`, not just differential agreement. This closes coverage gap §2.5(2).
4. **Add a theory-callback fuzz mode** exercising `add_theory_reason_clause` (`learn.rs:135`) and `analyze_theory_conflict` (`conflict.rs:381`) with **random SOUND theory lemmas** (closes coverage gap §2.5(1)). Apply the one-line defensive fix to `conflict.rs:386` as part of the new contract.

**Gate:** if Phase 0 stays clean after the `analyze()` fix, the engine is reusable unchanged (beyond the two §4 structural edits) → proceed to Phase 1. **If new distinct minimal repros keep surfacing in other subsystems, escalate scope** (see §6).

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

- Both harnesses (`sat_diff_fuzz.py` driving the pure engine + `ground_soundness_fuzz.rs`) wired as permanent CI gates.
- Re-run the §2 campaign at scale; confirm `unsound = 0` on the pure path AND the theory path.

**Validation gates (existing harnesses):** `oxiz-sat/tests/sat_diff_fuzz.py` (corrected to drive `pure_sat_runner` + DRAT-verified mode) and `ground_soundness_fuzz.rs` (CDCL(T) vs z3/cvc5). The bisection oracle that was unsound for MBQI is unsound here for the same reason (advisory two-stack sync) until Phase 2 lands — so do not rely on delta-debugging for regressions before the invariant holds.

---

## 6. Risks, effort, and the scope-width decision

### 6.1 Effort (rough)

| Work item | Rough effort |
|---|---|
| Phase 0: `analyze()` fix + DRAT gate + theory-callback fuzz | small (the fix is a few lines; most cost is the overnight fuzz + harness wiring) |
| Phase 1: standalone `TheoryHooks` + typed `Reason` + trail-driven hooks + toy theory | medium (the two §4 engine edits + contract design + toy-theory corpus) |
| Phase 2: port EUF/arith/simplex; delete parallel stack + suppression heuristics | medium-large (~6.8k glue lines re-architected, but mechanically constrained by the new contract) |
| Phase 3: full differential gate + CI | small-medium |

**Total: bounded — re-architect ~6,800 lines of glue + two surgical engine edits + one localized `analyze()` fix.** This is roughly an order of magnitude less than a 38k-line full rewrite.

### 6.2 Risks

- **The two §4 engine edits touch the trail's hot path** (`new_decision_level`, `backtrack_to_with_callback`). Mitigation: they are *additive* (one `if let Some(t)` per level move); the existing unassign callback plumbing already proves the closure path is viable; the §2 fuzz gate guards against regressions.
- **Phase-0 escalation risk:** the theory-only engine surfaces (`add_theory_reason_clause`, `analyze_theory_conflict`) have never been fuzzed; a defect there is the one thing that could widen scope (see §6.3).
- **Performance:** the lock-step hooks add per-level/per-assign work; must profile against the existing wall budgets (the §3.5 JIT/AOT work in the broader project is wall-sensitive). Mitigation: hooks are `Option`-gated and no-op in the pure-SAT path.
- **Dead-code latent risk:** XOR/Gauss, cube, GPU, ML-branching inflate the line count and expose a **dead-but-public** API. Recommend **quarantining/feature-gating** them (out of the default build surface) so they cannot be accidentally wired into a sound path later. This is a maintenance/hygiene item, not a soundness fix.

### 6.3 What would make us choose a BROADER vs NARROWER scope

**Stay NARROWER (the recommendation — integration-layer clean-room + the `analyze()` fix) when:**
- Phase 0 stays clean after the `analyze()` rewrite (no new distinct minimal repros), and
- the theory-callback fuzz of `add_theory_reason_clause`/`analyze_theory_conflict` finds nothing beyond the known `conflict.rs:386` sentinel.

This is the evidence we have: the engine is DRAT-self-certifying, the advanced engines are dormant, and the lone pure-SAT defect is single-site.

**Escalate to integration-layer + minimal trusted core when:**
- the theory-callback fuzz surfaces a real defect in `analyze_theory_conflict` or `add_theory_reason_clause` → rewrite **just** those two surfaces + the reason-clause machinery (still short of a full rewrite), or
- the corrected pure-SAT fuzzer, **after** the `analyze()` fix, keeps producing **distinct** minimal repros in *other* core subsystems (propagate/learn/backtrack) → the conflict/trail/watch invariants are systemically under-specified.

**Escalate to a FULL SAT rewrite only when:**
- repros cluster across *multiple independent* core subsystems with no common single-site cause — i.e. the 38k engine is pervasively under-specified, not locally buggy. **Nothing in the current evidence points here.** The audit found exactly one localized defect and uniform spurious-UNSAT-only behavior with zero fake-SAT, which is the signature of a *targeted* bug, not systemic rot.

**Never: keep-patching.** This session's fixes (`last_conflict_is_stale_bound` suppression; `theory_processed.min()` resyncs; the documented-but-unenforced restart hazard) are exactly the whack-a-mole the oxiz-mbqi `DESIGN.md` calls out — guards that mask symptoms while the bug class (two parallel stacks synced advisorily) stays representable. Each new theory or restart strategy can reopen it.

---

## Appendix — Anchors verified for this document (branch `0.2.4-feat/cdqi`)

- `Reason` enum = `Decision | Propagation(ClauseId) | Theory` (untyped) — `oxiz-sat/src/trail.rs:8-17`. ✔
- `analyze_theory_conflict` pushes `Lit::from_code(0)` placeholder — `oxiz-sat/src/solver/conflict.rs:386`. ✔
- `TheoryCallback::on_new_level` has empty default body; `on_backtrack` mandatory — `oxiz-sat/src/solver/mod.rs:73-86`. ✔
- `vivify_clauses()` invoked unconditionally (level-0 + `restarts % 10` only) — `oxiz-sat/src/solver/mod.rs:768-778`. ✔
- `sat_diff_fuzz.py` present — `oxiz-sat/tests/sat_diff_fuzz.py`. ✔
