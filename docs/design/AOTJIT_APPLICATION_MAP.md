# AOT / Algebraic-JIT Application Map — OxiZ + oxiz-nl2

*Analysis 2026-06-30 (the standing pre-port gate). Discharges "a THOROUGH full
analysis of how AOT and the algebraic JIT can be applied to oxiz-nl2 AND the rest
of OxiZ's components." 7-agent fan-out over each subsystem + the existing
machinery, synthesized into a prioritized map.*

## The lever (established, not re-derived)

The 2026-06-13 prelude-scale profile
(`~/portable-algebraic-aotjit/docs/algebraic-aotjit-codegen-rejected.md`) found
**~75 % of a solve is term/type-DAG construction + hash-consing and <5 % is
SAT/theory solving**; on the DAG-heavy shape specifically 79.9 % is parser
`byte_offset_to_position` O(N²) + ~15 % intern/hash-cons + **0 % codegen-amenable**.
adsmt's `--aot-load` (bake prelude state) removes ~62 %. The win is **state
reuse** (bake the stable prelude once, pay O(query delta)) — never native codegen.

**Native-codegen verdict: REJECTED, REINFORCED.** The new oxiz-nl2 evidence cuts
*against* codegen: the dominant nonlinear cost is arbitrary-precision
BigInt/BigRational arithmetic in `Polynomial::resultant`/`bareiss_det`
(`oxiz-math/.../extended_ops.rs:907`) and `sturm_chain`
(`oxiz-nl2/src/univariate.rs:99`) — dynasm cannot speed a bignum multiply, and the
waste is **RECOMPUTE not interpreter dispatch**, so the lever is *memo*, not
codegen. OxiZ is itself the delegation target for the hard solves, so those are
exactly the cases with no prior trace to replay.

## The one soundness discipline

Every cached/reused artifact is **EXACT-MATCH gated**, and a miss/mismatch
**always falls through to a full sound solve** (Unknown-safe) — nothing can
fabricate a sat/unsat. The asymmetry rule (a skipped path may preserve unsat but
must never invent sat) holds by construction. Four gate shapes:

1. **Verdict memos** — exact 32-byte K12 AdHash clause-set multiset digest
   (`digest.rs::clause_set_fold`/`fold_to_digest`, order-independent) **++ a
   context fingerprint** (sorts/funs/datatypes/logic/soundness-options), with the
   projected literal name an *injective* `Printer::print_term` (sort + operator
   identity). Cache **only Definite Sat/Unsat**, store the key beside the entry,
   structural-verify on hit; the Sat arm may re-run `Model::checks`.
2. **State bakes** — sound-by-RE-ADMISSION: the artifact (term DAG / EUF e-graph /
   simplex tableau) is solver *input* re-checked downstream, not a trusted output;
   recompute the live prelude content-address and require byte-equality before
   reinstating, else cold-build. The e-graph/tableau bake **must be paired** with
   the term-DAG bake (same digest) — they key on TermId/VarId arena indices.
3. **Pure-kernel memos** — exact canonical-normal-form match = polynomial
   *identity*, explicitly **NOT** ideal-membership (reduction against a
   non-Gröbner basis is the rejected unsound shortcut). The verdict still flows
   through the un-memoized G-SAT/G-UNSAT gates.
4. **Monotone-reuse banks** — gated by an existing sound gate: a model bank by
   `Model::checks(live_atoms)` (subset-satisfaction ⇒ FALSE_SAT impossible
   regardless of provenance); an unsat-core bank by verified-minimal-core
   subset-containment under canonical renaming + unsat-monotonicity.

## Highest-leverage item

**Prelude term-DAG state bake/reuse** — the OxiZ analog of `--aot-load`, attacking
the one *measured* dominant cost (75 % front-end). In OxiZ the front-end is re-paid
in full on every beneficiary: `oxiz_inproc` (`adsmt-cli/src/main.rs:996`) re-feeds
the whole ~44 KB history through `Context::execute_script` →
`TermManager::intern` on each fresh Verus VC-group process, and `:abduct-theory`
re-pays it **once per subset** (`main.rs:1001`). Because `TermManager.terms` is
`Arc<Vec<Term>>`, the in-process realization is nearly free. Soundness contrast
that makes it the *safest* high-value item: OxiZ's TermManager encodes only
**syntax** (solver input, re-checked downstream) — unlike adsmt-ir kernel state
which encodes trusted type-checking conclusions and is "fatally unsound" to
raw-dump (`adsmt-ir/src/bank.rs`).

## Phased sequencing

**Phase 0 — soundness-free in-process wins (do now, no serialization, no digest):**
- **Warm-Context clone (rank 2)** for the `:abduct-theory` fan-out: build the
  prelude `Context` once, `let mut c = template.clone(); c.execute_script(subset)`
  per subset (Arc pointer-bump for the DAG; only cache/symbol maps reallocate).
  Needs `Context: Clone`. Hits the **one measured recurrence**.
- **Simplex warm-start (rank 5, phase 1)**: persist `(assignment, basic)` at the
  prelude base level, seed `crash_basis` (`simplex.rs:556`). Sound because
  `check()` always re-pivots/re-verifies.

**Phase 1 — cross-obligation digest verdict memo (rank 3):** `compose_digest(
prelude_fold frozen at Context::push, query_delta_fold) ++ context_fingerprint`
keys a `HashMap<[u8;32], SolverResult>` of Definite verdicts at the top of
`check_sat` (`context.rs:296`). Reuses the portable crate unchanged. **Use this
phase to MEASURE the abductive-subset recurrence rate — the missing profile that
gates everything downstream.**

**Phase 2 — on-disk OxiZ `--aot-load` (the full 62 % lever, cross-process):**
rank 4 (command-journal port of `adsmt-ir/src/bank.rs`, parse-skipping,
re-admission-sound stepping stone) → rank 1 (TermManager state-dump, skips
parse+intern) → rank 6/5-phase2 theory blobs (EUF e-graph + simplex structure,
new `Serialize`, paired with the term bake) → rank 12 level-0 fixpoint replay.

**Phase 3 — nl2 / algebraic memos (CONDITIONAL):** gated on first measuring that
the workload actually has recurring **nonlinear** preludes (nl2 fires only when
native delegates into its fragment; the Verus prelude is EUF/MBQI-bound, where nl2
never runs). Build `poly_digest` (rank 7, the shared enabler) → resultant/Sturm
memos (ranks 10/11) + nl2 whole-set verdict memo (rank 8) + G-SAT model bank
(rank 9) → `sign_of` memo (rank 14) / unsat-core bank (rank 13) → defer the
McCallum prelude bake (rank 15).

**Lowest priority:** the replay/recorder items (ranks 17–19, deegen anti-drift +
subprocess-oracle ReplayState) — **redundant with #263's persistent push/pop for
the in-process backend**, relevant only to the feature-off `ADSMT_OXIZ_PATH`
subprocess oracle. The hard part is the recorder (OxiZ's SAT loop has no event
sink; `TheoryHooks` lack the decide-vs-propagate split / learnt / restart).

## Ranked applications (19)

| # | subsystem | application | value | tract. |
|---|-----------|-------------|-------|--------|
| 1 | termdag | Prelude term-DAG state-dump bake (OxiZ `--aot-load`) | high | moderate |
| 2 | termdag | Warm-Context template clone (abduction fan-out) | medium | easy |
| 3 | sat/crate | Digest verdict-memo across delegation obligations | high | moderate |
| 4 | termdag | Prelude command-journal replay (`bank.rs` port) | medium | easy |
| 5 | theory | Simplex tableau bake + prelude warm-start basis | medium | moderate |
| 6 | theory | AOT-bake the prelude EUF congruence e-graph | medium | hard |
| 7 | nl2 | `poly_digest` canonical-polynomial content-digest primitive | medium | easy |
| 8 | nl2 | Exact-match verdict memo for `oxiz_nl2::check` | medium | easy |
| 9 | nl2 | G-SAT-gated model bank (sat-side subset reuse) | medium | easy |
| 10 | nl2 | Memoize resultant/discriminant on `(p,q,var)` | medium | easy |
| 11 | nl2 | Memoize Sturm chains + isolating intervals | medium | easy |
| 12 | theory/sat | Replay prelude level-0 closure (theory fixpoint + SAT lemmas) | medium | moderate |
| 13 | nl2 | Verified unsat-core subset bank (monotone reuse) | medium | moderate |
| 14 | nl2 | Memoize `AlgebraicReal::sign_of` | medium | moderate |
| 15 | nl2 | AOT-bake the prelude McCallum projection basis | medium | hard |
| 16 | nl2 | Prelude nonlinear fold baked via `compose_digest` | low | moderate |
| 17 | crate | deegen single-spec recorder/replay anti-drift | medium | moderate |
| 18 | crate/sat | `ReplayState` host-binding for subprocess-oracle cold-start | medium | hard |
| 19 | sat | Replay prelude-only learned lemmas across pop | low | hard |

## Bottom line

Do **Phase 0** now (warm-Context clone + simplex warm-start — soundness-free,
hits the measured recurrence). Then the **digest verdict memo** (Phase 1) *and use
it to measure* whether the abductive-subset recurrence justifies the on-disk bake
(Phase 2, the real 62 % lever). The nl2 algebraic memos (Phase 3) are real but
**conditional on a nonlinear-prelude recurrence the current Verus workload does
not exhibit** — measure before building. No finding alters the native-codegen
rejection.

## Addendum 2026-07-19 — the 2026-06-30 ranking is SUPERSEDED

The v2-era re-analysis measured the lukb per-obligation corpus end-to-end and
found **~0.1 % front-end (parse + term construction) / ~99.9 % search** — the
inverse of this map's core premise (the 2026-06-13 profile's ~75 % DAG
construction was a prelude-scale artifact; the corpus obligations are
search-bound, not construction-bound). The prioritized table above should not
drive further work.

**Surviving items:**
- Delegation-layer verdict memo (rows 3-ish) — LANDED adsmt-side as D1.
- Instantiation-trace replay (V1) — delegation-layer, planned.
- fgr simplex warm-start — measure-gated, not yet justified.

**Killed by the measurement:** prelude term-DAG bakes, command-journal replay,
EUF e-graph bake, warm-Context clone, CDCL trace replay (§3.5 remains a
delegation-layer mechanism, not an engine lever).

**The actual path to the z3 gap** is the engine-algorithmics campaign:
E1 instantiation selection (pattern validation / ever-fired gating / additive
patterns, #425), S simplex trail, E2 EUF. The native-codegen rejection stands.
