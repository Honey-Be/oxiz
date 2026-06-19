# Dense-real model construction for the clean MBQI engine

*Design note — the `[다른 SMT solver들의 구현들을 참고하여 실수 모델 설계]` frontier.*

## 0. Problem

The clean MBQI engine (`oxiz-solver/src/clean_mbqi.rs`) never concludes `Unsat`
and never fabricates a witness; it reports `Sat` only when one of its
*model-construction recognizers* in `SolverModel::eval_forall` certifies that a
universal axiom can be satisfied by a concrete (conservative) model extension.
On the `z3_parity` corpus the engine is sound everywhere (0 spurious verdicts)
but reports the sound-but-incomplete `Unknown` on a cluster of quantified
real-arithmetic (`UFLRA`) cases that z3 decides `Sat`. This note designs the
recognizers that close that gap, referencing how the mainstream solvers build
models for quantified linear real arithmetic.

The five corpus cases and the technique each needs:

| corpus case        | universal axiom (sketch)                 | technique                                  |
|--------------------|-------------------------------------------|--------------------------------------------|
| `real_bounds`      | `∀x. 0 ≤ f(x) ≤ 1`                        | **constant range completion**              |
| `real_lipschitz`   | `∀x,y∈[0,5]. \|f(x)−f(y)\| ≤ 10`          | **bounded-oscillation** (constant default) |
| `real_archimedean` | `∀r∈[0,10]. ceil(r) ≥ r`                  | **guarded, variable-relative bound**       |
| `real_interp`      | `f ≥ 0 ∧ f ≤ g ∧ g = 2x+1` (3 axioms)     | **multi-axiom** (definitional g + bounded f)|
| `real_composition` | `∀x∈[0,5]. f(g(x)) = g(f(x))`             | **`f ≡ g` identity collapse**              |

## 1. How the mainstream solvers do it

**Z3 — model-based quantifier instantiation (MBQI) over a default-extended UF
model.** Z3 maintains a candidate model in which every uninterpreted function is
a *finite graph plus an `else` (default) value* — the `as-array`/`else` model
representation. To check a universal it evaluates the body under this model; if a
counterexample instance is found it is added as a ground lemma and the model is
repaired, otherwise the model is accepted. The crucial representational idea for
us is the **`else` value**: `f` is pinned at the finitely many points the problem
mentions and takes a single default everywhere else.

**CVC5 — counterexample-guided instantiation (CEGQI) + bounded finite-model
finding.** For linear real arithmetic cvc5 instantiates the bound variable with
*model-based* terms computed by Loos–Weispfenning / virtual term substitution,
and `--fmf-bound` treats a guarded quantifier `∀x. lo ≤ x ≤ hi ⇒ φ` by reasoning
over the guard interval. The takeaway: a *guard* `lo ≤ x ≤ hi` is the lever that
makes a real-domain quantifier tractable — the body only has to hold on the
guarded region.

**The common thread** that fits the clean engine's "recognizer + verify"
discipline is the **default-value model with symbolic verification**:

> Pick a default interpretation `f := λx̄. δ(x̄)` (a constant, the identity, a
> sup-of-guard value, or another function `g`). Symbolically check that the
> universal body holds for all `x̄` in the guard region under that default, and
> that the finitely many pinned (ground) points already satisfy it. If both hold,
> the default + pinned points is a model, so the axiom is `Sat`.

Every recognizer below is a specialization of this frame with a particular `δ`
and a particular (decidable, cheap) verification.

## 2. The soundness skeleton — conservative extension + accounting

A recognizer may answer `Some(true)` for an axiom `A` only when it exhibits a
model extension that satisfies `A` **without disturbing any model of the rest of
the formula** (a *conservative extension* over the symbols `A` introduces or
completes). Two gates make this safe and are shared by every recognizer:

1. **Single-quantifier gate** — `facts.quant_count[f] == 1`. The completed
   function `f` must be constrained by no *other* quantifier; otherwise a second
   universal could forbid the default we are about to choose.
2. **Accounting gate** — every application of `f` in the whole formula must be
   accounted for, either as one of the body's `f(x̄)` occurrences (handled by the
   completion) or as a *literal* ground point we explicitly verify. The check is
   `global_occ[f] == (f-occurrences in the body) + |ground_apps[f]|`.

   The accounting gate is not optional. A function application at a **symbolic**
   argument — `f(c)` for a free constant `c`, as in `real_unsat`
   (`∀x. f(x) ≤ 1` together with `f(c) > 1`) — is *not* a literal ground point
   (its argument is a variable, so `collect_ground_apps` does not record it), so
   the per-point verify never sees the constraint it carries and a constant
   completion would silently violate it. The accounting shortfall
   (`global_occ` exceeds body + literal points) is exactly the signal that such
   an unaccounted application exists; the recognizer then declines to the sound
   `Unknown` (and the engine's ground instantiation goes on to refute the case,
   recovering z3's `Unsat`). This gate is the symbolic-point companion to the
   `#260` literal-ground verify and lives in both
   `try_function_completion` and `try_range_completion`.

## 3. Recognizer roadmap

### 3.1 Constant range completion — `real_bounds` *(implemented)*

Body `∀x̄. ⋀ᵢ cmpᵢ(f(x̄), cᵢ)`: a conjunction of comparison atoms each bounding
one uninterpreted `f` against a ground constant. The atoms intersect to an
interval `[lo, hi]`; over a **dense** order a nonempty interval always has an
interior point, so the `else` value `δ ≡ k` for any `k ∈ [lo, hi]` satisfies the
body off the pinned points. Verification: the interval is nonempty (else the
axiom is itself unsatisfiable — decline), and every literal ground `f`-point is
eq-pinned to a rational inside `[lo, hi]`. This is the dense generalization of
the single-comparison `try_function_completion` (recognizer 4) to (a) `Real`
rationals and (b) a two-sided range. Lives in `try_range_completion`
(recognizer 4b). *Status: implemented; `real_bounds` → `Sat`.*

### 3.2 Bounded oscillation — `real_lipschitz` *(implemented)*

Body `∀x,y∈G. f(x)−f(y) ≤ B ∧ f(y)−f(x) ≤ B` (`|f(x)−f(y)| ≤ B` on a guard
region `G`). The `else` value is again a constant `δ ≡ k`: between two non-pinned
points the difference is `0 ≤ B`; between a non-pinned and a pinned point it is
`|k − vᵢ|`, which must be `≤ B`; between two pinned points it is `|vᵢ − vⱼ|`.
So the axiom is `Sat` iff the pinned values within `G` lie in an interval of
width `≤ B` (`max vᵢ − min vᵢ ≤ B`) — then `k = min vᵢ` (or any pinned value)
witnesses it. Verification is a single pass over the pinned points computing
`max − min`. Same two soundness gates. *Status: designed; not yet implemented.*

### 3.3 Guarded, variable-relative bound — `real_archimedean` *(designed)*

Body `∀r. (lo ≤ r ≤ hi) ⇒ cmp(f(r), τ(r))` where the bound `τ(r)` mentions the
variable (e.g. `ceil(r) ≥ r`). A *constant* default no longer works (a constant
cannot dominate `r` for all `r`), but the **guard** bounds the region: for
`cmp = ≥` choose `δ ≡ hi` (the guard's supremum dominates every `r ≤ hi`); for
`cmp = ≤` choose `δ ≡ lo`. More generally `δ` is the extreme value of `τ` over
the guard interval, which for an affine `τ` is attained at an endpoint and is a
cheap LRA evaluation. Verification: the chosen `δ` satisfies `cmp(δ, τ(r))` for
all `r ∈ [lo, hi]` (an endpoint check for affine `τ`) and the pinned points
satisfy the body. This is where cvc5's `--fmf-bound` "reason over the guard
interval" idea enters. *Status: implemented (`try_var_relative_bound`, 4d) for
the NON-STRICT case via the reflexive identity default `f(r) := r` — guard-free
and constant-free; strict `>`/`<` (needing the guard sup/inf) deferred.*

### 3.4 `f ≡ g` identity collapse — `real_composition` *(implemented)*

Body `∀x∈G. f(g(x)) = g(f(x))`. The default is *relational*: set `f ≡ g` (the
same graph). Then `f(g(x)) = g(g(x)) = g(f(x))` holds definitionally. This is
sound when (a) `f` and `g` agree on every point where both are pinned
(`f(p) = g(p)` for all shared pinned `p`), and (b) neither is otherwise
universally constrained (the single-quantifier gate, applied to both). The model
identifies the two functions' graphs and takes a common default. Verification is
a pinned-points agreement scan. *Status: implemented (`try_commuting_functions`,
4e), with the agreement scan + the accounting gate applied to BOTH functions.*

### 3.5 Multi-axiom completion — `real_interp` *(implemented)*

Three interacting universals: a definitional `g(x) = 2x+1` on a guard, a relation
`f(x) ≤ g(x)`, and a sign bound `f(x) ≥ 0`. No single-quantifier recognizer can
fire (`f` lives in two universals), so the firewall is relaxed CAREFULLY: a
dedicated pass (`collect_layered_bounds`, Pass 7) classifies the group, verifies
the canonical model `f ≡ L` (max constant lower bound), `g ≡ affine` once, and
marks each member in `layered_ok`; `eval_forall` certifies each by membership
(2b). The verification: `g`'s affine is unique and covers the `f≤g` region;
`L ≤ min(affine)` over that region (compatible layers — a dipping affine such as
`g=2x−15` is rejected); ground `g`-points equal the affine, ground `f`-points lie
in the band and `≤ affine`; and the accounting gate confirms `f`,`g` are local to
the group. *Status: implemented — the largest piece, the only recognizer that
relaxes the single-quantifier gate, hence the most validation-heavy.*

## 4. Implementation order — DONE

All five recognizers are implemented and corpus-validated (agree 157 → 163 across
§3.2–§3.5, 0 spurious throughout):

1. **§3.1 constant range completion** — `try_range_completion` (4b); `real_bounds`.
2. **§3.2 bounded oscillation** — `try_bounded_oscillation` (4c); `real_lipschitz`.
3. **§3.3 variable-relative bound** — `try_var_relative_bound` (4d); `real_archimedean`.
4. **§3.4 identity collapse** — `try_commuting_functions` (4e); `real_composition`.
5. **§3.5 layered bounds** — `collect_layered_bounds` + `layered_ok` (2b); `real_interp`.

Each keeps the two soundness gates of §2 and ships a regression case plus a
deliberate soundness control (a near-miss that must stay `Unknown`/`Unsat`, never
`Sat`), validated by the `clean_mbqi_corpus` z3-parity gate.

## 5. Remaining real/quantifier frontier

`real_fixed_point` (§5.1) and `nested_quantifiers` (§5.2) are now handled. One
`z3=Sat` case stays the sound `Unknown`:

- **`array_sorted`** — a cross-variable triangular guard `i≤j` (not an axis-aligned
  box), beyond the current bounded-domain machinery.

### 5.1 Done — `real_fixed_point` (guard-aware range + Skolem fixed-point)

`∀x∈[0,1]. 0≤f(x)≤1` **plus** `∃x∈[0,1]. f(x)=x` plus `f(0.5)=0.5`. Two parts:
(a) the range completion (§3.1) now peels an optional `(=> guard …)`, so the
GUARDED range certifies; (b) the ∃ skolemizes to `f(sk)=sk` with `sk` bounded —
a symbolic point that is nonetheless IN-RANGE (`f(sk)=sk`, `sk` bounded). Pass 8
(`collect_skolem_fixedpoints`) records each such fresh-Skolem self-fixed-point
with `sk`'s bounds; the range completion accounts for it and folds `sk`'s bounds
into the feasible interval for the constant `k` (since `f(sk)=k` forces `sk=k`).
An out-of-range fixed-point folds to an empty interval and is declined; a
non-eq-pinned `f(c)` (real_unsat) is not a self-fixed-point and still trips the
plain accounting gate.

### 5.2 Done — `nested_quantifiers` (substitute fix + threshold guard)

Triple-nested `∀x.∃y.∀z. (z≥y ⇒ f(x,z)≥0)`. Two parts: (a) a CORE bug — the
manager's `substitute` left `Forall`/`Exists` unchanged, so skolemizing the inner
`∃y` LEAKED `y` into the nested `∀z` (and nested-quantifier instantiation kept its
bound var); fixed with capture-avoiding quantifier arms (`subst_under_binder`).
(b) With the skolemized `∀x,z. (z≥sk(x) ⇒ f(x,z)≥0)`, the FRESH threshold `sk(x)`
can be pushed above every (finitely many) ground point of `f` — so the pinned
points fall in the excluded region `z<sk(x)` (vacuous) and the constrained region
holds only fresh points where `f` is free. `try_threshold_guard` recognizes the
shape (fresh-skolem lower threshold on a bound var, feasible single-`f` range
consequent with the threshold var as an `f`-arg, `f` single-quantifier) and
certifies. An infeasible consequent makes the axiom `∀z. z<sk` — unsat — so it
declines.
