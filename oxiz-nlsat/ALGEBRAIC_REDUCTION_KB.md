# Algebraic Reduction Knowledge Base (`reduction_kb.rs`)

## Problem

`oxiz-nlsat`'s variable assignment is **rational-only**
(`assignment.rs: arith_values: Vec<Option<BigRational>>`,
`solver/decide.rs::pick_arith_value -> Option<BigRational>`). For a coupled
polynomial-equality system whose only real solution is **irrational**, the base
CDCL+CAD search picks a rational value for the first "free" variable, the second
variable's feasible region then becomes empty, and `solve()` backtracks to level 0
and returns a **spurious `Unsat`**.

Canonical repro (the previously-`#[ignore]`d test
`solver/mod.rs::test_solver_circle_and_line`):

```text
x^2 + y^2 - 25 = 0      (circle, radius 5)
y - x = 0               (line  y = x)
```

The only real solutions are `x = y = ±sqrt(12.5)`, which no `BigRational` can hold.

## Solution: a leveled reduction KB (mirrors `oxiz-solver/src/calculus.rs`)

A new self-contained module `oxiz-nlsat/src/reduction_kb.rs` implements a
*leveled* reduction knowledge base, invoked as a **SAT-only pre-pass** from
`NlsatSolver::solve()` (after initial propagation, before the main search loop)
via `NlsatSolver::try_algebraic_reduction()`.

### Level 0 — primitive reductions (linear-equality elimination)
`try_solve_equalities` gathers the asserted single-factor `Eq` atoms (`p = 0`),
then repeatedly:
1. finds an equality that is **linear in a variable `v` that also occurs in
   another active equality** (the *coupling* variable),
2. isolates `v = f(other vars)` exactly (`isolate_linear_var`, requires `v`'s
   coefficient to be a non-zero rational constant), and
3. substitutes `v := f` into every other active equality
   (`oxiz_math::polynomial::Polynomial::substitute` — exact, no approximation),
   recording the substitution in a chain `subs`.

This triangularizes toward a single **univariate** polynomial `q`. For
circle ∩ line: `y := x` substituted into the circle yields `2x^2 - 25` (univariate).

### Level 1 — derived/composite forms (resultant elimination)
If no univariate eliminant survives Level 0, `try_resultant_eliminant` eliminates
a shared variable from a 2-equation system via
`Polynomial::resultant` (conic ∩ conic). This is composed on the Level-0
primitive and re-verified by the back-substitution check below.

### Confirmation (real root) + exact algebraic model
The univariate eliminant `q(root_var)` is fed to `crate::cad::SturmSequence`;
`isolate_roots()` returns isolating rational intervals. The first interval is used
to build an exact `oxiz_math::algebraic::AlgebraicNumber` (its constructor
*re-validates* single-root isolation via its own Sturm sequence — a built-in
soundness gate). Eliminated variables are back-substituted
(`build_assignment` / `realise_in_root`): for `y = x` (the identity in
`root_var`), `y` reuses the same `AlgebraicNumber`.

### Verification (the soundness gate)
Before concluding SAT, **every** original equality `p = 0` is verified *exactly*:
`p` is reduced through the substitution chain (`apply_subs`); the residue must be
either identically zero, or univariate in `root_var` and **divisible by `q`**
(`pseudo_remainder(reduced, q, root_var).is_zero()`). Because `root_var` equals a
root of `q`, divisibility guarantees `p = 0` at the model point — a *symbolic*
check, never a numeric/interval-midpoint eval.

## Carrying the irrational value

- `Assignment` gains a **parallel** map `algebraic_values: FxHashMap<Var,
  AlgebraicNumber>` (+ `set_algebraic` / `algebraic_value`); every existing
  rational path is byte-identical (zero regression risk). `clear` / `unset_arith`
  scrub it.
- `Model` gains `algebraic_values: HashMap<Var, AlgebraicNumber>` (+
  `Model::algebraic_value`). For an algebraic variable, `arith_values` holds the
  isolating-interval **midpoint** (a rational approximation, so `is_complete`,
  `get_model`, and the rest of the machinery stay well-defined); the exact value
  lives in `algebraic_values`.

## Soundness invariants (hard constraints honored)

1. **SAT only after exact verification.** No SAT is concluded unless the
   elimination is exact, Sturm confirms a real root, the `AlgebraicNumber`
   constructor accepts the interval, and *every* original equality is verified
   by symbolic divisibility. The interval midpoint is never used as the proof.
2. **Never fabricate / never report Unsat.** The KB is a purely *additive*
   recognizer: on any uncertainty (system not all-equalities, not reducible, no
   real root, `AlgebraicNumber::new` error, verification failure) it returns
   `None`. It never returns `Unsat` (an inexact `resultant` could otherwise
   fabricate one). The approximate-resultant path is gated by the exact
   back-substitution verify, so it can only *fail to find* a model.
3. **Side-effect-free failure.** `try_algebraic_reduction` performs a
   completeness pre-check (all booleans asserted; all arithmetic variables either
   already assigned or covered by the solution) **before** writing anything. On
   the `None` path the assignment/trail/atoms are untouched, so the fallback
   CDCL+CAD search runs verbatim and the KB can never change a verdict the
   existing path already gets right.
4. **Strictly additive gating.** The KB fires only when (a) at least one variable
   was actually eliminated (`subs` non-empty — a genuinely *coupled* multivariate
   system), and (b) the isolated root is **irrational** (`!root.is_rational()`).
   Single-equation problems (`x^3 - x = 0`, `x - 1 = 0`) and rational-root systems
   are left to the unchanged base path — which both represents them exactly and,
   for NIA, applies the integer-domain constraint the KB is unaware of.

## Files changed

- `oxiz-nlsat/src/reduction_kb.rs` (new): the KB. Key functions:
  `try_solve_equalities`, `isolate_linear_var`, `find_univariate_eliminant`,
  `try_resultant_eliminant`, `build_assignment` / `realise_in_root`,
  `apply_subs`, `to_univariate`, `collect_asserted_equalities`.
- `oxiz-nlsat/src/solver/mod.rs`: `NlsatSolver::try_algebraic_reduction()`
  pre-pass + call site in `solve()`; `Model.algebraic_values` field +
  `Model::algebraic_value`; `get_model` copies algebraic values.
- `oxiz-nlsat/src/assignment.rs`: `Assignment.algebraic_values` parallel map +
  `set_algebraic` / `algebraic_value`; `clear` / `unset_arith` updated.
- `oxiz-nlsat/src/lib.rs`: `pub mod reduction_kb;`.
- `oxiz-nlsat/src/solver/mod.rs` test: `test_solver_circle_and_line` un-ignored
  and adapted to verify the **algebraic** model exactly (x satisfies `2x^2-25=0`
  via sign-straddle of its isolating interval, is irrational, and `y = x` shares
  representation).

## Scope / known limitations

- Back-substitution `realise_in_root` exactly realises only the identity
  (`v = root_var`) and rational-constant cases; other affine/nonlinear
  back-substitution forms fall back (conservative).
- `test_quadratic_roots` (integration_tests.rs, still `#[ignore]`d): a *single*
  univariate irrational equality `x^2 - 2 = 0`. This is a **pre-existing**
  limitation (verified identical on the pristine tree) outside the requested
  coupled-system bug; the strictly-additive `subs`-non-empty gate intentionally
  does not fire on single-equation systems (avoids the NIA integer-domain hazard).
