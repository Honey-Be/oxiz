<!-- SPDX-License-Identifier: Apache-2.0 -->

# oxiz-mbqi — a clean-room quantifier-instantiation engine

A solver-agnostic quantifier engine (e-matching + MBQI) built from scratch
around **one soundness invariant**, then ported into OxiZ to replace the
patched-but-still-unsound `oxiz-solver/src/mbqi/`.

## Why a rewrite

The existing OxiZ MBQI produces **spurious `unsat`** on real Verus preludes
through *multiple independent* defects, and they cannot be reliably
delta-debugged because the bisection oracle (OxiZ's own verdict on a subset)
is itself unsound — a superset can report `sat` while a subset reports
`unsat`. Patching is whack-a-mole. Observed defects, all the SAME class:

| tag | defect | really |
|-----|--------|--------|
| B | trigger matched the quantifier's OWN body → identity subst `{i↦i}` | invalid lemma (bound var left free) |
| E | trigger matched a SIBLING quantifier's body → `{i↦x_sibling}` | invalid lemma (foreign bound var) |
| D | enumeration over FABRICATED universe witnesses `u!0…u!7` | lemma over non-problem terms |
| fuel (susp.) | inner `∀` under `(=> g …)` instantiated without the guard | invalid lemma (guard dropped) |

Every one is **"the engine emitted a lemma that is not a valid universal
instantiation of the quantifier."**

## The invariant (what makes this tractable)

> **The quantifier engine NEVER concludes `Unsat`.**
> It only emits lemmas of the form `φ[x̄ ↦ t̄]` where
> 1. each `tᵢ` is a **ground** term that actually occurs in the problem
>    (or was produced by a prior valid instantiation) — never a fabricated
>    witness, never another quantifier's bound variable;
> 2. the substitution is **capture-free**;
> 3. the lemma is emitted **in the polarity context the quantifier occurs
>    in** — a `∀` under `(=> g ψ[∀])` yields `g ⇒ ψ[φ[x̄↦t̄]]`, i.e. the
>    instance inherits the guard (we encode `Q ⇒ φ[x̄↦t̄]` where `Q` is the
>    boolean literal of the quantifier node, so the SAT layer carries the
>    guard automatically).
>
> `Unsat` is then derived ONLY by the ground SAT+theory core from the
> accumulated lemmas. Because every lemma is a valid logical consequence of
> the input, **any `Unsat` the core finds is a real `Unsat`** — spurious
> `unsat` is impossible by construction.

Corollary: the engine's only verdicts are
- `Sat` — every quantifier is satisfied by the candidate model (checked, not
  guessed), or e-matching saturated with no new instances and the model
  is consistent;
- `Unknown` — instantiation budget/timeout hit before saturation;
- (refutation is the SAT core's job, never the engine's).

This is the discipline z3/cvc5 follow. The current code violates it in four
places; the rewrite enforces it centrally.

## Architecture (solver-agnostic)

The engine is generic over a host term language via a trait, so it is
developed and z3-cross-checked standalone, then ported to OxiZ by
implementing the trait for `oxiz_core` types (no engine changes at port).

```
trait TermLang {
    type Term: Copy + Eq + Hash;
    type Sort: Copy + Eq + Hash;
    type VarName: Copy + Eq + Hash;

    // structure
    fn view(&self, t: Self::Term) -> TermView<Self>;     // Var | App(f,args) | Quant{..} | Const..
    fn sort_of(&self, t: Self::Term) -> Self::Sort;

    // construction (hash-consed by the host)
    fn mk_app(&mut self, f: FnSym, args: &[Self::Term]) -> Self::Term;
    fn mk_eq(&mut self, a: Self::Term, b: Self::Term) -> Self::Term;
    fn mk_implies(&mut self, a: Self::Term, b: Self::Term) -> Self::Term;
    // … just enough to rebuild instantiated bodies …

    // the ONLY substitution entry point — capture-free, ground range enforced
    fn substitute(&mut self, body: Self::Term,
                  binding: &[(Self::VarName, Self::Term)]) -> Self::Term;
}
```

Modules:
- `term` — the `TermLang` trait + `TermView`.
- `ground` — the per-check ground-term index (terms occurring in assertions
  and prior instances), grouped by sort. The ONLY candidate source.
  **Fabricated witnesses are never added here.**
- `instantiate` — given (quantifier, substitution) produces the guarded
  lemma `Q ⇒ φ[x̄↦t̄]` via `TermLang::substitute`. Central enforcement of the
  three invariant conditions; rejects any substitution whose range escapes
  the ground index (defensive — should never happen).
- `engine` — the round loop, choosing a candidate-selection **strategy** per
  quantifier, emitting guarded lemmas, reporting Sat/Unknown. Hard budget →
  Unknown. Never Unsat.
- `toy` — a tiny in-crate `TermLang` impl (a toy term DAG) so the engine is
  unit- and corpus-tested without OxiZ.

### Candidate-selection strategies (all feed the same sound `instantiate`)

Every strategy only ever proposes a substitution whose range is drawn from
the ground index, so they ALL inherit the invariant. They differ only in
*which* ground tuples they pick and *why* — soundness is independent of the
choice; completeness and efficiency are not.

- `enumerate` (M1) — blind cartesian product of ground terms by sort. Sound,
  complete-in-the-limit over the ground universe, but redundant. The
  fallback / correctness baseline.
- `trigger` (M2) — `:pattern` e-matching against the ground index. A match
  binds the trigger's variables to subterms of an existing ground term, so
  the range is ground-index terms by construction. The efficient default for
  `:pattern`-annotated axioms (the z3/cvc5 discipline). Pure speed/relevance
  win over `enumerate`.
- `cdqi` (M2) — **conflict-driven quantifier instantiation** (Reynolds,
  Tinelli, de Moura, FMCAD'14). Given the host's current model (an
  evaluation oracle `eval(term)->Option<bool/value>`), search the
  ground-index tuples for one whose body is **false** under the model — a
  *conflicting* instance that refutes the candidate model in a single step.
  It fabricates nothing, so it is cheap and its lemma is the strongest /
  most relevant. Tried FIRST (before enumerate/model-based) per quantifier;
  on a hit, emit that guarded lemma and skip the constructing search this
  round. CDQI is **not** a separate soundness surface — a conflicting
  instance is still just `φ[x̄↦t̄]` over ground terms, hence a valid lemma;
  it only changes *which* tuple is chosen. (This replaces OxiZ's
  `generate_ground_conflicts`, re-derived inside the invariant.)
- `model_based` (M3) — for trigger-free quantifiers with no conflicting and
  no e-match instance: VERIFY the quantifier against the completed model.
  The completed model's universe witnesses are used **only to evaluate** the
  body; if every relevant evaluation holds, report the quantifier satisfied
  (→ host may say `Sat`). Witnesses are NEVER turned into hard lemmas — that
  was OxiZ's D bug. If a witness evaluation fails, the violating instance is
  re-expressed at a REAL ground term (or, absent one, the quantifier is left
  to `Unknown`). Ge & de Moura (2009), with the witnesses firewalled out of
  the lemma stream.

The host supplies a model-evaluation oracle (a trait method) that `cdqi` and
`model_based` consult; `enumerate`/`trigger` do not need it.

## Test corpus (the oracle is z3, never the engine)

Two corpora, both cross-checked against z3 (never against OxiZ's own — that
oracle is unsound, which is why delta-debugging OxiZ failed):

1. **Soundness triggers** — the shapes harvested while debugging OxiZ, each
   with the z3 ground-truth verdict:
   - `b_self_match`, `e_cross_capture`, `d_fabricated_universe`,
     `fuel_guarded_forall`, `partial_order_trigger_free`
   - `verus_prelude_full` (the 120-axiom prelude; z3 times out goal-free, so
     the gate is **not `unsat`**)
   The engine's verdict must be `Sat`/`Unknown` (never a spurious `Unsat`)
   and must match z3 wherever z3 decides.

2. **z3-parity regression** — import OxiZ's existing quantifier parity corpus
   (`oxiz/bench/regression` + `oxiz-solver/tests/{lia_*,uf_*,mbqi_*,
   quant_*}.rs` cases) so the rewrite is exercised on the SAME broad set the
   old engine passed, not only on the bug shapes. This guards completeness:
   the clean engine must keep deciding everything the old one decided (modulo
   the spurious unsats it deliberately turns into sat/unknown). Imported as
   SMT-LIB fixtures + expected z3 verdict; run through the OxiZ port (M4) and,
   where expressible, the toy host.

The harness records, per case: engine verdict, z3 verdict, agreement, and the
`rejected` counter (must stay 0 — a non-zero means a candidate escaped the
ground index and wants investigation, though it is never an unsoundness).

## Progressive refinement & caching (M3.5, discuss before M4)

The naive engine (M1–M3) re-scans the whole ground index and re-enumerates
every round. That is correct but quadratic. The refinements below speed it up
**without ever touching soundness** — the trick is to classify what is safe
to cache:

- **Model-INDEPENDENT facts are always cacheable** and never need
  invalidation: emitted instances (`seen`), e-match substitutions, and
  `substitute(body, tuple)` results. They are valid logical consequences of
  the input regardless of any model, so a stale one is at worst redundant.
- **Model-DEPENDENT facts must be invalidated when the model changes:**
  `eval_bool`/`eval_forall` results (tagged by a model generation counter).
  A stale eval could mis-pick a CDQI tuple or mis-verify a forall — never an
  *unsoundness* (the lemma is still valid), but a wrong *efficiency/verdict*
  call, so we invalidate on each new SAT assignment.

This is the whole safety story: cache sound syntactic work freely; version
the model-eval cache. The never-conclude-`Unsat` invariant is untouched.

### Refinement mechanisms (in payoff order)

1. **Relevance gating (likely fixes the fuel trigger).** Only instantiate a
   quantifier whose boolean literal `Q` is **assigned true** in the current
   model. A `∀` under `(=> g ψ)` with `g` false has `Q` false → skip it
   entirely. Verus fuel preludes are dozens of *guarded* quantifiers, most
   inactive in any given model; gating both slashes work and is the precise
   way to *respect the guard* that the old OxiZ fuel bug dropped. Sound:
   skipping an irrelevant quantifier cannot lose a real refutation (if `Q` is
   false the instance `Q ⇒ φ[..]` is vacuously true anyway).
2. **Frontier / mod-time e-matching.** Tag each ground term with the round it
   entered the index. Per `(quantifier, trigger)`, remember the last frontier
   scanned; next round, only match against terms newer than that. Turns
   per-round e-matching from "all ground terms" into "the delta", which is
   what makes incremental solving cheap.
3. **Incremental enumeration.** Same frontier idea for the trigger-free
   enumerator: only emit tuples containing ≥1 new ground term.
4. **Match / substitution caches.** `(quantifier, trigger) → matched ground
   terms` and `(body, tuple) → instance term`. Pure speed; never invalidated.

### The adsmt big win: a prelude instantiation bank (ties to §3.5)

For `-V adsmt` the prelude axioms are FIXED across every `(check-sat)`; only
the goal changes. So the prelude's e-match/CDQI instances are largely stable.
Mirror the existing §3.5 JIT-on-AOT trace mechanism at the *quantifier*
layer: **precompute the prelude's instantiation closure once at `--aot-bake`,
store it as a bank, and at each `(check-sat)` replay the bank + instantiate
only the GOAL delta** (the new ground terms the goal introduces, via the
frontier index). That is the O(query-delta) shape rc.34.4/34.5 already
achieved for the trace/digest; here it is the natural home for it, because
the clean engine's instances are a pure function of the ground index. The
bank is model-independent (instances are valid lemmas), so it caches and
replays with zero soundness caveat. See [[jit-aot-replay-section-3-5]].

### Open questions for the discussion

- Relevance gating needs the host to expose "is `Q` true in the current
  model?" — a one-method extension of `ModelEval` (`is_active(quant)`). Cheap
  and high-value; propose adding it in M3.5 before the port.
- The prelude bank wants a stable term identity across check-sat calls. In
  OxiZ the `TermManager` is persistent (hash-consed), so a baked instance's
  `TermId` is stable — the bank can key on it directly, same as the §3.5
  clause-fold. Confirm at port time.
- Frontier mod-time interacts with the host's backtracking: on pop, ground
  terms added under the popped scope must leave the index (or be marked
  inactive). The engine must take a `push`/`pop` from the host. Design the
  engine's incremental API to mirror the host's assertion stack.

## Port plan (M4)

Implement `TermLang` for `oxiz_core::ast::TermManager`, drop `engine` in
behind `Solver::check`'s quantifier phase, delete the four patched modules,
re-run the full OxiZ + verus-prelude regression.
