<!-- SPDX-License-Identifier: Apache-2.0 -->

# Comparative analysis — five MBQI acceleration approaches

Decision input for "apply the adopted option(s) inside OxiZ" (post-M4). The
constant constraint: **none may touch the never-conclude-`Unsat` invariant.**
The discriminator from `DESIGN.md` is *model-independence*: instances /
matches / substitutions are valid regardless of any model (cache freely);
model evaluations are not (version + invalidate).

Each is scored on: **payoff** for the adsmt/verus workload (prelude-heavy,
AOT-baked, SAT-dominant), **soundness risk**, **complexity**, **§3.5 reuse**.

## 1. Progress-aware instantiation caching
*Cache `(quantifier, trigger, frontier)` → already-processed, so re-solving
processes only the ground-term delta — the M3.5 frontier, persisted across
`(check-sat)` calls and keyed by solver progress (decision level / assertion
frontier).*
- **payoff: HIGH.** The prelude frontier is stable; only the goal advances
  it. Turns each `(check-sat)` into O(goal delta) e-matching.
- **soundness risk: NONE.** Instances are model-independent.
- **complexity: LOW.** We already have `seen` + the frontier watermark;
  this persists them across checks and keys on the host's push/pop level.
- **§3.5 reuse: HIGH** (same incremental-frontier idea as the clause-fold).

## 2. Lookaheads
*Speculatively instantiate / explore a candidate model branch to steer search
(pick the decision that reaches a conflict fastest; precompute matches for
terms about to enter the e-graph).*
- **payoff: LOW–MED for adsmt.** Lookahead mostly accelerates UNSAT-finding;
  the verus prelude is SAT-dominant (we want a model fast), so the speculative
  exploration largely doesn't pay back. Helps adversarial/abduction search
  more than verification.
- **soundness risk: NONE** (heuristic; reorders work, adds no lemma).
- **complexity: HIGH** (speculative branches, rollback, cost accounting).
- **§3.5 reuse: NONE.**

## 3. Lemma caching (the prelude bank)
*Cache the generated instance LEMMAS across checks. The prelude's lemmas are
identical every `(check-sat)`; bake them once at `--aot-bake`, replay the bank
+ instantiate only the goal delta.*
- **payoff: VERY HIGH.** This is the direct O(goal-delta) win and the
  natural home for the existing AOT-bake pipeline.
- **soundness risk: NONE.** A baked lemma is a valid consequence of the
  (fixed) prelude; replaying it is always sound.
- **complexity: LOW–MED.** Store lemma `TermId`s (stable across checks —
  `TermManager` is persistent hash-cons), re-assert at check start.
- **§3.5 reuse: VERY HIGH** — literally the `prelude_clause_fold` / trace
  bank, one layer up at the quantifier level.

## 4. Inverse function reuse
*For paired / injective functions (verus box/unbox, as_type/has_type,
%I/I…), use the inverse axiom to compute the needed instantiation term
directly instead of enumerating — e.g. `unbox(box(x))=x` gives `x` without an
e-match search.*
- **payoff: MED–HIGH for verus specifically.** The prelude is saturated with
  box/unbox and `has_type` pairs; trigger **E** was exactly the int-width /
  `has_type` instantiation class. Targets that class directly.
- **soundness risk: LOW.** Only sound when the inverse is backed by a real
  asserted axiom; the result is still `φ[x/t]` for a ground `t`, so it stays
  inside the invariant. Must guard: never "reuse" an inverse that isn't
  actually asserted (else an invalid instance — caught by the central
  `instantiate` ground-range check, which would `Reject` it).
- **complexity: MED** (detect invertible pairs from the axioms; maintain the
  inverse map; integrate as a candidate-selection strategy alongside CDQI).
- **§3.5 reuse: LOW.**

## 5. Model state caching
*Cache `eval_bool`/`eval_forall` results and the completed model across
rounds; invalidate only the parts touched by new lemmas (model generation +
atom-dependency tracking).*
- **payoff: MED.** Speeds the CDQI / model-based phase; but at the goal that
  phase is light relative to e-matching.
- **soundness risk: MED — the ONLY one needing care.** Model-dependent: a
  stale eval mis-picks a CDQI tuple or mis-verifies a forall. Never an
  *unsoundness* (the lemma is still valid; verification only gates
  `Sat`/`Unknown`, never `Unsat`), but a wrong verdict/efficiency call.
  Requires precise generation-versioning + invalidation.
- **complexity: MED–HIGH** (atom-dependency tracking for precise
  invalidation; coarse versioning is simpler but flushes more).
- **§3.5 reuse: LOW.**

## Verdict

| approach | payoff(adsmt) | soundness risk | complexity | adopt? |
|---|---|---|---|---|
| 3. Lemma caching (prelude bank) | very high | none | low–med | **YES — first** |
| 1. Progress-aware inst. caching | high | none | low | **YES** |
| 4. Inverse function reuse | med–high | low (guarded) | med | **YES — selective** |
| 5. Model state caching | med | **med (versioned)** | med–high | later, careful |
| 2. Lookaheads | low–med | none | high | defer/skip |

**Adopt (the "들"): 3 + 1 + 4.** All three are model-INDEPENDENT, so they
inherit the never-unsat invariant for free, and all three hit the verus
prelude where it lives (fixed axioms + box/unbox/has_type pairs). 3 and 1 are
the same incremental-frontier idea at the lemma vs trigger granularity and
fold into the §3.5 AOT-bake bank; 4 targets the trigger-E class specifically.
**Model state caching (5)** is added later only where the model-based phase
is measured hot, with strict generation-versioning — it is the one place a
mistake costs a wrong verdict (never an unsound `Unsat`, but still). **5 and
2** are explicitly deferred.

Application order inside OxiZ (post-M4): bake-time prelude lemma bank (3) →
per-check progress-aware frontier reuse (1) → inverse-pair strategy (4) →
(later) versioned model-eval cache (5).
