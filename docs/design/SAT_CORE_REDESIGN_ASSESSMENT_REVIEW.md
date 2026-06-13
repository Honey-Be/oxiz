# OxiZ SAT Core Redesign — Final Review

**Target document:** `/home/ybi/AD1/external/oxiz/docs/design/SAT_CORE_REDESIGN_ASSESSMENT.md`
**Branch:** `0.2.4-feat/cdqi` · **Code state reviewed:** HEAD `5527290` (Phase 0 committed)
**Reviewer role:** Lead reviewer, consolidating five dimension reviews against the post-Phase-0 code.

---

## 1. Verdict

**The document's bottom-line recommendation still stands — integration-layer clean-room on a reused `oxiz-sat` engine, NOT a full 38k rewrite, NOT keep-patching — but the document needs TARGETED REVISIONS before sign-off because its central *evidence narrative* has been overtaken by its own Phase 0.** The recommendation is, if anything, *vindicated*: the Phase-0 theory-callback fuzz the doc prescribed (§5 step 4) found three more soundness defects (BUG 2, BUG 3, the placeholder leak), all reproduced, all z3/cadical-cross-checked, all fixed surgically in `conflict.rs` + `solve_with_theory` and pinned by regression tests that **pass on HEAD** (I ran them: `regress_bool_analyze_all_level0_sat`, `regress_post_theory_conflict_propagation_sat`, `regress_theory_conflict_reason_position_unsat`, `soundness_repro::minimal_spurious_unsat_default_config` — all green). None of those defects cluster across independent subsystems; they are a single-class cluster in conflict analysis, exactly the kind of bounded, surgically-fixable evidence the doc's own §6.3 says keeps scope NARROW. **What is now false is the doc's rhetorical scaffolding** — "all 6 bugs in the glue, the nucleus is sound, exactly ONE localized single-site analyze() defect, zero fake-SAT, the gate stays clean." The nucleus harbored **two** `analyze()` soundness defects (one spurious-UNSAT, one spurious-SAT) plus a missing-propagation defect in the CDCL(T) driver, and the §6.3 "stay NARROWER" gate condition is, read literally, falsified by Phase 0. These are documentation-accuracy defects on a sign-off-quality artifact, not code-soundness holes — but a maintainer sizing scope reads exactly those sentences, so they must be corrected. **Apply the revisions in §6 below; the recommendation does not change.**

---

## 2. Load-bearing claims — consolidated status

De-duplicated across all five dimensions, verification-upheld only. Each row re-verified against HEAD `5527290`.

| # | Claim (doc location) | Status | Evidence |
|---|---|---|---|
| C1 | "All 6 bugs / the entire bug class live in the theory glue, not the SAT nucleus" (§1 L25) | **FALSIFIED** | BUG 2 lives in `analyze()` (the always-on Boolean 1-UIP), guard at `conflict.rs:140-211`; BUG 3 in `solve_with_theory` at `mod.rs:1146-1160`. Both in the nucleus the doc calls sound. |
| C2 | "Exactly ONE localized single-site defect in `analyze()`; spurious-UNSAT only" (§1 L25; §2.5 L104; §6.3 L370) | **FALSIFIED / PARTLY-FALSE** | TWO defects in `analyze()`: lits[0]-skip spurious-UNSAT (`cc3872c`, conflict.rs ~248-275) AND degenerate-conflict spurious-SAT (`5527290`, conflict.rs:140-211). Opposite directions, distinct sites. |
| C3 | "Zero fake-SAT across 106k; uniform spurious-UNSAT-only = targeted bug" (§2.1 L43; §6.3 L370) | **DRIFTED** | True for the **pure-SAT campaign** (BUG 2 provably inert there — `mod.rs:778-782`). The **CDCL(T)** theory-callback fuzz DID surface spurious-SAT (BUG 2/BUG 3). Scope the boast to pure-SAT. |
| C4 | §6.3 "Stay NARROWER" gate: fuzz finds "nothing beyond the known conflict.rs:386 sentinel" (§6.3 L361) | **FALSIFIED** | Fuzz found BUG 2 + BUG 3 + reason-position beyond the placeholder. Literal gate condition is false; narrow *conclusion* survives via common-root structure the gate text omits. |
| C5 | "the trusted core needs ONE localized few-line analyze() fix" (§1 L21; §6.1 L343) | **DRIFTED** | Realized trusted-core work = degenerate guard (74L) + placeholder branch (44L) + 5 new empty-clause-as-UNSAT guards + BUG-3 propagation block + DRAT wiring. `numstat`: conflict.rs +211/-2, mod.rs +199 in `5527290`. Order-of-magnitude understated. |
| C6 | Placeholder leak: `Lit::from_code(0)` leaks when UIP walk ends `p==None`; predicted by doc (§2.5(1); §4.4 row 4) | **HOLDS (credit)** | Pre-fix shape at `conflict.rs:546`; reachability confirmed via `theory-probe` (`theory_callback_fuzz.rs:608`); fix at conflict.rs:658-695. Doc predicted both mechanism and file. |
| C7 | §4.1 `new_decision_level` + `backtrack_to_with_callback` are the SOLE `current_level` mutators (§4.1) | **PARTLY-FALSE** | FOUR writers: `trail.rs:115` (+=), `:195` (=0, `backtrack_to_size`), `:228` (=level), `:266` (=0, `clear`). `backtrack_to_size` reached by incremental `pop()` (mod.rs:1369, incremental.rs:99) — bypasses the hook. |
| C8 | §4.4 table makes "each of the 6 bugs impossible by construction" (§4.4) | **HOLDS for the 6, but INCOMPLETE** | Table is correctly scoped to the 6 desync bugs and holds for them. BUG 2/BUG 3 are NOT desync bugs and §4 does not make them impossible — they need an orthogonal conflict-analysis robustness clause. |
| C9 | Reason enum = `Decision \| Propagation(ClauseId) \| Theory` (untyped) (§4.3; Appendix) | **HOLDS** | `trail.rs:8-17` exact match. |
| C10 | Engines dormant: XOR/cube/GPU/ML/symmetry/lookahead/local_search not `Solver` fields; `solve()` never calls XOR (§3.1; §3.3; §3.6) | **HOLDS** | `grep Xor solver/mod.rs` → 0; the eight-engine `self.{…}` grep is empty. |
| C11 | "`self.{…proof,drat…}` grep over `solver/*.rs` is EMPTY" (§3.1; §3.6) | **PARTLY-FALSE** | Phase 0 added `drat: Option<DratWriter>` (`mod.rs:409`) + 25 `self.drat*` sites (mod.rs 12, learn.rs 11, propagate.rs 1, incremental.rs 1). Only `drat` leaked; `proof` grep still empty. Soundness-neutral (default `None`, §3.5 rank-7). |
| C12 | Both configs `enable_inprocessing=false`; SMT path forwards only restart+inproc+interval; `solve_with_theory` never vivifies (§3.4) | **HOLDS** | `mod.rs:201` false; oxiz-solver forwards exactly those three; vivify only in `solve()`. |
| C13 | vivify "unconditional / gated only on `restarts%10 && level==0`" (§3.4; Appendix #4) | **PARTLY-FALSE** | Also nested under `if conflicts_since_deletion >= clause_deletion_threshold` (`mod.rs:867`), vivify call at `:875`. Fires less often than stated. |
| C14 | Three `last_conflict_is_stale_bound()` suppression sites at 616/654/1654 (§4.4 row 3) | **DRIFTED** | FOUR sites: `theory_manager.rs:616, 1092, 1500, 1654`. Strengthens the whack-a-mole argument; mechanism holds. |
| C15 | `sat_diff_fuzz.py` present (Appendix #5; §5) | **FALSIFIED (anchor)** | No such file. Actual: `sat_diff_fuzz_pure.py` + `sat_diff_fuzz_pure_drat.py`. Stale checkmark; self-correcting via `ls`. |
| C16 | DRAT-self-certifying: 8,938 UNSAT proofs, 0 drat-trim rejections (§2.5(2); §6.3 L363) | **HOLDS, with a scope gap** | DRAT wired (`mod.rs:484` region); certifies the **pure-SAT** path only (theory lemmas not RUP/RAT-logged; `pure_sat_runner` bypasses the theory layer). Cannot catch spurious-SAT BUG 2/BUG 3. |
| C17 | Pervasive Appendix/inline line drift post-`5527290` (claims hold) (Appendix; §3.2; §4.1) | **DRIFTED** | analyze_theory_conflict 381→538; placeholder 386→546; TheoryCallback 73-86→78-91; vivify 771→875; add_theory_reason_clause 135→141. Underlying claims hold. |

---

## 3. Central-thesis impact

The doc's load-bearing argument is a chain: **(a)** all 6 session bugs are in the glue → **(b)** the SAT nucleus is sound except for one localized `analyze()` spurious-UNSAT → **(c)** "zero fake-SAT, single-site" is the *signature* of a targeted bug, not systemic rot → **(d)** therefore stay NARROW (reuse the 38k engine, rewrite only the 6.8k glue + 2 edits + 1 analyze fix).

**Phase 0 breaks links (a), (b), and (c) but NOT the conclusion (d).**

- **Link (a) is false.** BUG 2 lives in `Solver::analyze()` (`conflict.rs:110`, guard at `:140-211`) — the always-on Boolean 1-UIP analyzer the doc itself files under "Trusted nucleus" (§3.2 L122) — reached from `solve_with_theory` at `mod.rs:1069/1151/1190`. BUG 3 lives in the `solve_with_theory` driver (`mod.rs:1146-1160`). Both are nucleus/driver defects, not glue.

- **Link (b) is false on two counts.** `analyze()` had **two** soundness defects, not one, and the new one is the *opposite* direction (spurious-SAT, not spurious-UNSAT). The guard's own comment states the un-guarded UIP walk "yields an UNSOUND verdict (spurious SAT/UNSAT, with the returned model violating an input clause)" (`conflict.rs:148-150`).

- **Link (c) is overgeneralized.** "Zero fake-SAT across 106k" is *literally true for the pure-SAT campaign* — and BUG 2 is provably inert there (`mod.rs:778-782`: "In the pure-Boolean path the analyze() degenerate-conflict guard cannot fire"). But the inference "zero fake-SAT ⇒ targeted bug, not systemic rot" (§6.3 L370) collapses the moment the CDCL(T) calling pattern of that same `analyze()` is included, because the theory-callback campaign *did* produce spurious-SAT.

- **Conclusion (d) survives — and is reinforced.** Apply the doc's own §6.3 decision tree to the *actual* Phase-0 evidence:
  - **Full-rewrite trigger** (§6.3 L370): "repros cluster across multiple *independent* core subsystems with no common single-site cause." **NOT MET.** All defects — the two `analyze()` bugs, the `analyze_theory_conflict` reason-position + placeholder, and the BUG-3 `solve_with_theory` settle — share ONE root cause: textbook CDCL invariants ("the implied literal sits at `lits[0]`"; "every conflict has a current-level literal"; "BCP has run to fixpoint before deciding") that **only the CDCL(T) cycle violates**. Propagate, watched-lits, clause-DB, restarts, LBD remain unflagged (8k pure-SAT + 6k DRAT, 0 unsound).
  - **Middle-escalation trigger** (§6.3 L366): "fuzz surfaces a real defect in `analyze_theory_conflict` / `add_theory_reason_clause` → rewrite just those surfaces, short of a full rewrite." **THIS is the branch Phase 0 landed in** — and the surgical fix sufficed (commit-message validation: >2.2M theory-callback instances, EUF 4500 + arith 6000 fatal=0, pure-SAT 8k + DRAT 6k, all 0 unsound).

**Corrected bottom line on scope:** *Integration-layer clean-room on the reused engine remains correct and is now empirically vindicated. The trusted-core precondition is NOT "one few-line analyze() fix" but "a bounded, single-class conflict-analysis hardening track (already landed in `cc3872c` + `4419298` + `5527290`, ~270 net LoC, regression-pinned)." Scope still points firmly AWAY from a full rewrite — the full-rewrite trigger is genuinely unmet.* The change is to the *evidence narrative and effort sizing*, not the decision.

---

## 4. Prioritized findings

Ordered critical → major → minor, upheld findings only, severities reconciled across dimension verifications (most "critical"/"major" items were corrected DOWN one notch on verification, because the code is fixed and the recommendation holds — these are doc-accuracy defects, not live soundness holes).

### MAJOR

**M1 — `analyze()` had TWO soundness defects, not one; the new one is spurious-SAT.** *(§1 L25; §2.5 L104; §6.3 L370)*
The doc's "ONE localized single-site spurious-UNSAT in analyze()" is wrong on both axes. Verified: lits[0]-skip spurious-UNSAT (`cc3872c`) and degenerate-conflict spurious-SAT (`5527290`, `conflict.rs:140-211`) are two distinct sites with opposite directions, both inside the function the doc calls trusted.
**Edit:** Rewrite those sentences to: *"the conflict-analysis surface harbored a single-CLASS, multi-SITE cluster — two `analyze()` defects (a `lits[0]` positional assumption → spurious-UNSAT; a no-current-level degenerate conflict → spurious-SAT under CDCL(T)), one positional defect + one placeholder leak in `analyze_theory_conflict`, and a missing post-conflict BCP-settle in `solve_with_theory` — all sharing one root: textbook-CDCL invariants the CDCL(T) cycle violates. A targeted cluster, not systemic rot."*

**M2 — §6.3 "Stay NARROWER" gate condition is falsified as written.** *(§6.3 L359-363)*
The gate keys "stay narrow" on the fuzz finding "nothing beyond the known `conflict.rs:386` sentinel." It found BUG 2 + BUG 3 + reason-position. Read literally the doc would escalate out of its own recommended branch; the narrow conclusion survives only via the common-root structure the gate text does not encode.
**Edit:** Replace with a common-single-root gate: *"Stay NARROWER when the conflict-analysis/CDCL(T)-driver defects share one root cause (a fixed set of CDCL invariants the theory cycle breaks) AND are surgically repairable without touching propagate/watched-lits/clause-DB/restart AND post-fix DRAT + theory-callback fuzz return 0 unsound. Phase 0 landed in the MIDDLE escalation branch (§6.3) and that branch's surgical fix sufficed — validated by >2.2M theory-callback instances and 6k DRAT proofs at 0 unsound."*

**M3 — §6.1 effort table understates the trusted-core fix by ~an order of magnitude.** *(§6.1 L343, L348)*
"small (the fix is a few lines)" / "+ one localized analyze() fix" vs realized: `numstat` conflict.rs +211/-2, mod.rs +199 (plus `cc3872c` +10, `4419298` +8). The conflict-analysis logic alone is a 74-line degenerate guard, a 44-line placeholder branch, 5 new empty-clause-as-UNSAT guards (mod.rs `is_empty()` guards now 7, verified), and the BUG-3 propagate-and-reanalyze block.
**Edit:** Add a dedicated row: *"Trusted-core conflict-analysis hardening (LANDED, Phase 0): degenerate-conflict guard + post-theory-conflict BCP settle + placeholder removal + uniform empty-clause-as-UNSAT across solve-loop callsites + DRAT wiring — ~270 net LoC, small-medium, DONE."* Change the total rider from "one localized analyze() fix" to "a conflict-analysis hardening sub-track (~270 LoC, landed)." Keep the ~1/10-of-38k headline.

**M4 — §3.2/§6.2/§6.3 mis-locate the defect risk: the escalation triggers point at the two theory-only surfaces, but the most consequential bug (BUG 2) is in the shared Boolean `analyze()`.** *(§3.2 L122; §6.2 L353; §6.3 L366)*
§6.2 bullet 2 and the §6.3 escalation trigger scope soundness risk to `add_theory_reason_clause` / `analyze_theory_conflict`. BUG 2 fell in the gap — it is in `analyze()`, which §6.3 L367 ("other core subsystems") omits and the single analyze() fix was assumed to close.
**Edit:** In §3.2/§3.5 add: *"The Boolean `analyze()` 1-UIP loop is in the always-on nucleus but was NOT defect-free — it harbored both the pure-SAT `lits[0]` spurious-UNSAT and the CDCL(T) degenerate-conflict spurious-SAT. Its textbook invariant (every conflict has a current-level literal) is violated by the CDCL(T) cycle, so treat `analyze()` as a soundness-sensitive shared surface."* Broaden the §6.2/§6.3 escalation trigger from "the two theory surfaces" to "the conflict-analysis surface (`analyze` + `analyze_theory_conflict` + `solve_with_theory` propagation sequencing)."

**M5 — §5 Phase 0 must be rewritten as EXECUTED (commit `5527290`), with its outcomes folded in.** *(§5 L304-313)*
The whole §5 is forward-looking ("Do this before writing any new glue"). Phase 0 is done; the gate did NOT "stay clean" — it found three defects, all now fixed and regression-pinned. The gate's true verdict — *engine reusable after a bounded set of surgical conflict-analysis fixes, NOT clean on first pass* — is the single most decision-relevant fact for sign-off and is currently absent.
**Edit:** Add a "Phase 0 — EXECUTED (commit `5527290`)" subsection: list the three defects, that all reproduced + z3/cadical-cross-checked, the regression names in `oxiz-sat/tests/theory_callback_fuzz.rs` (`regress_bool_analyze_all_level0_sat:1062`, `regress_post_theory_conflict_propagation_sat:1077`, `regress_theory_conflict_reason_position_unsat:1047`), the post-fix numbers, and the verdict: *"NOT clean on first pass; all repros shared the CDCL(T)-invariant root and were surgically fixed; engine reusable — proceed to Phase 1."* Mark §5 steps 1-4 DONE.

**M6 — §4.4 "impossible by construction" table is incomplete: BUG 2 and BUG 3 are conflict-analysis robustness fixes orthogonal to theory-frame-sync, and §4's design does NOT make them impossible.** *(§4.4; §4.5)*
§4's lock-step invariant constrains frame *depth*, not the *level* a theory-propagated literal occupies. A theory unit at a lower level can still falsify an original clause while at a higher level (the exact BUG-2 precondition) even with perfect frame sync. BUG 3 is a loop-ordering invariant (BCP-to-fixpoint after a theory-conflict learn) that the `TheoryStep::Conflict` channel does not address. The §4.5 debug-asserts (frame-depth + atom-subset) would NOT have caught either: a degenerate conflict has correct frame depth and atom subset; a skipped propagation leaves the trail consistent.
**Edit:** (1) Add an explicit clause: *"`analyze()` and `analyze_theory_conflict()` must never assume a current-level literal exists; a degenerate conflict (no current-level lit) is handled by learning C itself and backtracking below its highest level. This is a conflict-analysis robustness fix ORTHOGONAL to theory-sync, already landed in Phase 0 (`conflict.rs:140-211`), and a PRECONDITION of the redesign — not a consequence."* (2) Add a loop invariant + third debug-assert: *"No decision and no `final_check` may occur while `trail.has_pending_propagation()` is true; `debug_assert!(!trail.has_pending_propagation())` at `pick_branch_var`/`final_check` entry."* (3) Scope the §4.5 "would have caught all 6" claim to "all 6 DESYNC-class bugs."

**M7 — §6.2 risk list omits the demonstrated conflict-analysis / watched-literal fragility, and the DRAT gate does not cover the CDCL(T) path.** *(§6.2 L352-355)*
The BUG-2 fix itself re-implements second-watch placement by hand: `conflict.rs:188-205` carries the warning *"the second watch must be the highest-level literal among the rest … Without this the clause could later be fully falsified without a watch firing (a missed conflict ⇒ unsound SAT)"* and does a manual `swap(1, second_idx)` — because the degenerate-conflict guard returns early at `:209` BEFORE the normal path's common backtrack swap (`conflict.rs:730`). This per-site duplication is precisely the fragility the §4 "make-it-unrepresentable" philosophy should absorb. Separately, the DRAT gate certifies only the pure-SAT path (`pure_sat_runner` bypasses theory; theory lemmas are theory-justified, not propositional RAT), so it does NOT guard the CDCL(T) conflict-analysis invariants where BUG 2/BUG 3 live.
**Edit:** Add a §6.2 risk bullet on conflict-analysis/watched-literal fragility; recommend routing ALL learned-clause finalization through ONE function enforcing empty-clause-as-UNSAT + two-watched-literal placement (the §4 discipline applied to conflict analysis). Note the residual DRAT gap: DRAT certifies pure-SAT only, not CDCL(T) verdicts.

### MINOR

**m1 — §4.1 mis-identifies the sole `current_level` mutators.** *(§4.1)* FOUR writers, not two: `backtrack_to_size` (`trail.rs:195`, =0) and `clear` (`trail.rs:266`, =0) bypass `backtrack_to_with_callback`. `backtrack_to_size` is reached by incremental `pop()` (`mod.rs:1369`, `incremental.rs:99`) — a legitimate level-down on the incremental-SMT push/pop surface §4.1 lists as "covered by construction," so frames would desync there. *(Note: the design dimension's claim that `clear` is reached by `backtrack_to_root` is imprecise — `backtrack_to_root` at `mod.rs:1397` routes through `backtrack_with_phase_saving(0)` and is correctly covered; the `trail.clear()` at `mod.rs:1404` is inside a full `reset()` where a frame desync is benign. The `backtrack_to_size`/`pop()` half stands independently.)* **Edit:** Re-implement `backtrack_to_size`/`clear` in terms of `backtrack_to_with_callback`, or enumerate all FOUR writers and state how each preserves the invariant; make "sole mutator" literally true in code or the by-construction guarantee is unproven.

**m2 — `soundness_repro.rs` present-tense status is stale.** *(§2.3)* The doc says the repro is "`#[ignore]`/failing"; it is a plain `#[test]` and PASSES (verified: `minimal_spurious_unsat_default_config ... ok`). The test file's own header comment (lines 12-15) is also stale. **Edit:** "reproduced the spurious-UNSAT; now FIXED — `soundness_repro.rs` passes"; mark §5 step 1 DONE; fix the in-file docstring.

**m3 — §3.4 vivify gating is imprecise.** *(§3.4; Appendix #4)* Also nested under `conflicts_since_deletion >= clause_deletion_threshold` (`mod.rs:867`; vivify at `:875`). **Edit:** "vivify runs in `solve()` only, gated on (`conflicts_since_deletion ≥ clause_deletion_threshold`) AND `restarts%10==0` AND `decision_level==0` — no config flag, throttled by the clause-DB-reduction cadence." Line 771→875.

**m4 — §3.1/§3.6 "`self.{…proof,drat…}` grep is empty" is now false for `drat`.** *(§3.1; §3.6)* Phase 0 added `drat: Option<DratWriter>` (`mod.rs:409`) + 25 `self.drat*` sites. Only `drat` leaked — `proof` and the eight reasoning engines are still empty. Soundness-neutral (default `None`, §3.5 rank-7). **Edit:** Narrow the grep to exclude `drat` (only `drat`, not `proof`), or footnote the default-None emission field per §3.5 rank-7. Keep the decoupling claim for the eight standalone engines.

**m5 — Appendix anchor `sat_diff_fuzz.py present ✔` is a falsified checkmark.** *(Appendix #5; §5 L309/L330/L333)* File does not exist; renamed to `sat_diff_fuzz_pure.py`, with `sat_diff_fuzz_pure_drat.py` realizing the §5 step-3 DRAT gate. **Edit:** Replace every `sat_diff_fuzz.py` with `sat_diff_fuzz_pure.py`; cite `sat_diff_fuzz_pure_drat.py` as the DRAT gate.

**m6 — `last_conflict_is_stale_bound()` is FOUR sites, not three.** *(§4.4 row 3)* `theory_manager.rs:616, 1092, 1500, 1654` (doc cited 616/654/1654). Strengthens the whack-a-mole argument. **Edit:** Refresh the count and anchors.

**m7 — Pervasive line drift post-`5527290`.** *(Appendix; §3.2; §4.1)* `analyze_theory_conflict` 381→538; placeholder 386→546; `TheoryCallback` 73-86→78-91; vivify 771→875; `add_theory_reason_clause` 135→141. Claims hold. **Edit:** Add a one-line Appendix note ("line numbers reference pre-Phase-0 code before `5527290`; claims re-verified, anchors may be ±~150 lines"); optionally re-pin the most-cited anchors, and mark the placeholder + both analyze() fixes as LANDED rather than open hazards.

**m8 — Record the doc's prediction scorecard honestly.** *(§2.5)* It predicted ONE of three Phase-0 findings (the placeholder leak) and missed BUG 2 + BUG 3. **Edit:** "Of the three Phase-0 findings, the doc predicted one (the placeholder leak, §2.5(1)); the two `analyze()`/`solve_with_theory` spurious-SAT defects were not anticipated and contradict the §2.4 single-site claim — a measured correction to the thesis, not a refutation of the narrow-scope conclusion."

---

## 5. What the doc got right

Genuine credit, so the maintainer trusts the corrected remainder:

- **Predicted the placeholder leak precisely.** §2.5(1) + §4.4 row 4 named both the mechanism (`Lit::from_code(0)` leaks when the UIP walk ends `p==None`) and the file/line. Phase 0 confirmed it reachable via the `theory-probe` feature (`theory_callback_fuzz.rs:608`) and applied a defensive fix (`conflict.rs:658-695`). The §4.3 typed-`Reason` design is a *stronger* structural kill than the runtime drop (the asserting literal becomes an input, not a discovered output).
- **Prescribed exactly the gate that worked.** §5 step 4's theory-callback fuzz of `add_theory_reason_clause` / `analyze_theory_conflict` is the very harness that surfaced BUG 2/BUG 3. The doc's instinct to fuzz the never-exercised theory-only surfaces before committing to scope was correct and high-value.
- **Architecture map is overwhelmingly accurate.** The mono-struct + standalone-toolbox shape, the dead-engine map (XOR/cube/GPU/ML/symmetry/lookahead/local_search not `Solver` fields, never called from `solve()`), the two-config-layer analysis, the SMT-path forwarding, the clause-DB-deletes-only-learned soundness argument, the inprocessing-without-watch-rebuild highest-risk row, the parallel `level_stack` + suppression heuristics — all verify against current code.
- **DRAT-self-certifying framing is empirically *strengthened*.** §5 step 3 became real: `sat_diff_fuzz_pure_drat.py` + DRAT wiring, 8,938 oxiz-UNSAT proofs verified by drat-trim, 0 rejections. (Caveat: pure-SAT path only — see M7.)
- **The §6.3 decision tree's *structure* is sound.** Applied to the actual Phase-0 evidence, it correctly routes to the middle branch and keeps scope away from a full rewrite. Only the gate *conditions* (M2) need updating, not the tree.
- **The redesign spine (§4.1 lock-step invariant + §4.2 trail-driven `TheoryHooks` + §4.3 typed `Reason`) genuinely makes the six desync bugs unrepresentable** — the §4.4 table holds for the bugs it scopes. The "make-it-unrepresentable, don't guard it" philosophy is the right one; M6/M7 only ask to *extend* it to conflict analysis.

---

## 6. Recommended-revisions checklist (section-by-section)

- [ ] **§1 (L21):** Change "the trusted core needs **one localized fix to `conflict.rs::analyze()`** (a few-line, textbook 1-UIP rewrite)" → "a bounded, single-class conflict-analysis hardening track (two `analyze()` fixes + `analyze_theory_conflict` positional/placeholder fix + a `solve_with_theory` post-conflict BCP settle — all landed in `cc3872c`+`4419298`+`5527290`, ~270 net LoC, regression-pinned)." *(M3, M5)*
- [ ] **§1 (L25):** Replace "All 6 bugs … live in the theory-integration glue, not in the SAT nucleus" and "the audit's *one* caveat — a localized, reproducible spurious-UNSAT in analyze()" with the single-CLASS-multi-SITE cluster wording from **M1**.
- [ ] **§2.1 (L43) / §2.4 (L104):** Scope "zero fake-SAT" / "single-site, spurious-UNSAT-only" explicitly to the **pure-SAT campaign**; note the CDCL(T) theory-callback campaign surfaced spurious-SAT (BUG 2/BUG 3), benign-direction for a Verus backend but real defects, confined to the CDCL(T) calling pattern (inert in pure SAT, `mod.rs:778-782`). *(C3, M1)*
- [ ] **§2.3:** Past-tense the repro status; mark `soundness_repro.rs` PASSING; fix its stale in-file docstring (lines 12-15). *(m2)*
- [ ] **§3.1 / §3.6:** Narrow the `self.{…}` grep claim to exclude `drat` only; footnote the default-None `self.drat` emission field (soundness-neutral, §3.5 rank-7). Keep the eight-engine decoupling claim. *(m4)*
- [ ] **§3.2 / §3.5:** Add the "analyze() is a soundness-sensitive shared surface, not assumed sound" correction. *(M4)*
- [ ] **§3.4:** Fix vivify gating wording + line 771→875. *(m3)*
- [ ] **§4.1:** Enumerate ALL FOUR `current_level` writers; route `backtrack_to_size`/`clear` through the hook (or discharge each); make "sole mutator" literally true in code. *(m1)*
- [ ] **§4.4:** Add rows for BUG 2 and BUG 3, noting they are conflict-analysis robustness fixes **orthogonal to theory-sync**, already landed in Phase 0, and PRECONDITIONS of the redesign — and that §4's frame-sync invariant does NOT by itself make them impossible. *(M6)*
- [ ] **§4.5:** Scope "would have caught all 6" to "all 6 DESYNC-class bugs"; add the third assert `debug_assert!(!trail.has_pending_propagation())` at decision/final_check entry (catches BUG 3) and the degenerate-conflict guard assert in `analyze()` (catches BUG 2). *(M6)*
- [ ] **§5:** Rewrite as "Phase 0 — EXECUTED (commit `5527290`)"; list the three defects, cross-checks (z3/cadical), regression-test names + line numbers, post-fix validation numbers, and the gate verdict ("NOT clean on first pass; surgically fixed; engine reusable → Phase 1"). Mark steps 1-4 DONE. Replace `sat_diff_fuzz.py` → `sat_diff_fuzz_pure.py` everywhere; cite `sat_diff_fuzz_pure_drat.py` as the DRAT gate. *(M5, m5)*
- [ ] **§6.1:** Add the conflict-analysis-hardening effort row; amend the total rider; keep the ~1/10-of-38k headline. *(M3)*
- [ ] **§6.2:** Add the conflict-analysis/watched-literal-fragility risk bullet (cite the BUG-2 fix's own hand-rolled second-watch placement, `conflict.rs:188-205`); note DRAT certifies only the pure-SAT path, not CDCL(T). *(M7)*
- [ ] **§6.3:** Replace the "Stay NARROWER" gate condition with the common-single-root criterion; broaden the escalation trigger from the two theory surfaces to the whole conflict-analysis surface; record that Phase 0 landed in the MIDDLE branch and the surgical fix sufficed (validation numbers). *(M2, M4)*
- [ ] **§2.5:** Add the prediction scorecard (1 hit / 2 misses). *(m8)*
- [ ] **Appendix:** Add the "line numbers pre-Phase-0" note; re-pin top anchors; fix the `sat_diff_fuzz.py` falsified checkmark; correct `last_conflict_is_stale_bound` to FOUR sites (616/1092/1500/1654); mark the placeholder + both analyze() fixes as LANDED. *(m5, m6, m7, C14)*

---

**Sign-off guidance:** The recommendation (integration-layer clean-room, no full rewrite, no keep-patching) is correct and now empirically vindicated by its own Phase 0. The document is **actionable after the §6 revisions** — none of which change the decision, all of which correct an evidence narrative that a scope-sizing reader would otherwise be misled by. The three highest-priority edits for sign-off are **M5** (record Phase 0 as executed with its real verdict), **M1** (correct the two-defect / spurious-SAT reality of `analyze()`), and **M2** (fix the falsified gate condition).
