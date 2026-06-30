# oxiz-nl2

Clean-room **nonlinear-arithmetic solver** (QF_NRA + QF_NIA) for
[OxiZ](https://example.invalid) — a sound-first replacement for OxiZ's
`NlsatSolver` and `NiaSolver`, which a z3-differential proved broadly unsound on
nonlinear `unsat`.

**One idea:** a frozen model-constructing **MCSAT trail** + a growing
**explainer ladder**. The whole soundness obligation reduces to one contract on
one function — `explain` returns a clause valid over ℝ — and two runtime gates
(**G-SAT** exact model re-check, **G-UNSAT** covering re-verify) make
`FALSE_UNSAT = 0` / `FALSE_SAT = 0` hold *regardless of explainer correctness*.

> Priority order, non-negotiable: **soundness ≫ completeness ≫ latency**.
> `Unknown` is always acceptable; a false `Unsat` never is.

See [`DESIGN.md`](DESIGN.md) for the full architecture, the M0–M7 roadmap, and
the reuse-vs-build plan.

## Status — M1 (sound spine + interval/§G explainer)

The MCSAT-style model-construction spine + Layer-0 §G/§G-SOS pre-deciders are
live behind `oxiz_nl2::check`. It decides every documented single-atom
false-unsat shape correctly; harder problems return `Unknown`.

* `Sat` — only via a full assignment that passes G-SAT exactly (integer vars get
  integer values).
* `Unsat` — only from a sound source: §G/§G-SOS definite-sign, or a
  single-variable problem proved unsatisfiable by representative-point
  evaluation. **Never** trusts the substrate's `IntervalSet::intersect` or
  `SturmSequence::count_roots` for a verdict (both were found unsound during M1 —
  see the regression tests in `src/spine.rs`).
* `Unknown` — everything else.

An **in-house univariate real-root engine** (`src/univariate.rs`, exact Sturm —
built because every substrate root tool is unreliable) gives a *complete* exact
decision for single-variable problems: `Unsat`, `Sat` with a rational witness,
or `SatIrrational` (real-sat with only irrational witnesses → integer-unsat, or
`Unknown` over ℝ until the M3 algebraic models).

Multivariate unsat is closed by cheap sound pre-deciders: constant-false atoms,
**even-monomial definite sign** (generalises §G past quadratics — `3x⁴<0`,
`x²+y²+1=0`), and **univariate sub-cores** (the single-variable atoms decided by
the Sturm engine — `-5x⁴≥0 ∧ 2x⁴≠0` is unsat in `x` alone).

Single-variable irrational-only sats are now decided with **exact algebraic
models**: an in-house `AlgebraicReal` (defining polynomial + isolating interval)
and an exact `sign_at_algebraic` built on the same Sturm machinery (no substrate
`AlgebraicNumber`). `x² = 3` over ℝ → `Sat` with the witness `√3`; over ℤ →
`Unsat`. The G-SAT gate verifies algebraic-coordinate models exactly.

The MCSAT search decides the **last variable exactly**: with all earlier vars
fixed to rationals, the remaining problem is univariate, so the Sturm engine
finds a rational/algebraic value (or proves the prefix dead) — a true MCSAT leaf
rather than sampling.

Latest full z3-differential (1007 random + seeded problems): **FALSE_UNSAT = 0,
FALSE_SAT = 0**, 948 agree with z3, 59 sound `Unknown`. The remaining frontier
is the *large* milestones: ~47 genuinely-multivariate unsat (need projection /
CDCAC, M4) + 8 single-variable-integer (real-sat but no integer ⇒ NIA, M5) + a
few multivariate sat needing an irrational prefix (local search).

```sh
cargo test                      # unit tests + scoped differential (fast)
cargo test -- --ignored         # full z3 differential sweep (the ! gate)
```

The differential gate (`tests/differential.rs`) cross-checks every verdict
against `z3` and asserts `FALSE_UNSAT = 0 && FALSE_SAT = 0`. It skips gracefully
if no `z3` binary is reachable.

## Layout

| path | role |
|---|---|
| `src/atom.rs` | normalised polynomial atoms `p ⋈ 0` |
| `src/value.rs` | exact `Value`/`Model` + **G-SAT** `Model::checks` |
| `src/verdict.rs` | `Verdict` + the `UnsatReason` covering certificate |
| `src/explain.rs` | the `Explainer` soundness seam |
| `src/corpus.rs` | seeded failing shapes + deterministic random generator |
| `src/differential.rs` | SMT-LIB serialiser + z3 oracle + classifier |

Dev-wired against the vendored `oxiz-math` via a path dependency (reused
substrate: `AlgebraicNumber`, `Polynomial`, root isolation, resultants). The
M4-port converts this to an in-workspace dependency.

## License

Apache-2.0.
