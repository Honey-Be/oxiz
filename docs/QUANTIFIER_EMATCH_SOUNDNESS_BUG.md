<!-- SPDX-License-Identifier: Apache-2.0 -->

# Quantifier e-matching soundness bug (forall + ground term)

**Status:** found 2026-06-12 · branch `0.2.4-feat/streaming-stdin` @ `26b8454`
**Severity:** soundness (wrong verdict in **both** directions) on quantified
formulas that need a single e-matching / MBQI instantiation
**Scope:** `oxiz-solver` solve loop (`solver/mod.rs` MBQI + e-matching
phase). Reproduces identically via the `oxiz` CLI **and** in-process
`Context::execute_script`, in **debug and release**, with and without
`set-logic`. Independent of the OxiZ↔adsmt delegation wiring.

## How it surfaced

adsmt routes its `:abduct-theory` per-subset `check-sat` through OxiZ
delegation (adsmt rc.36) so that abduction works on Verus's axiomatized
encoding (`(> (Add x y) 0)` with `Add` defined by a `:pattern` axiom).
The abducts came back wrong; isolating the per-subset `check-sat` showed
OxiZ — not the adsmt wiring — returns the wrong verdict on the underlying
quantified query. z3 on the *same* files returns the correct verdict.

## Minimal reproductions (z3 is the oracle)

### R1 — unary, conflict via instantiation → should be **UNSAT**, OxiZ says `sat`

```smt2
(declare-fun f (Int) Int)
(assert (forall ((a Int)) (! (= (f a) a) :pattern ((f a)))))
(assert (= (f 3) 4))      ; with f(a)=a this forces f(3)=3, contradicting 4
(check-sat)
```

- **z3:** `unsat` ✓
- **OxiZ:** `sat` ✗ — the `:pattern ((f a))` trigger never instantiates at
  the ground term `(f 3)`, so the universal is ignored and a quantifier-
  free model (`f(3)=4`) is reported as `sat`. (No-pattern `forall` is the
  same.) This is the **incompleteness-reported-as-`sat`** direction:
  unsound, because a `sat` claims a model that violates the axiom.

### R2 — binary + arithmetic body, *consistent* ground fact → should be **SAT**, OxiZ says `unsat`

```smt2
(declare-fun Add (Int Int) Int)
(assert (forall ((a Int) (b Int)) (! (= (Add a b) (+ a b)) :pattern ((Add a b)))))
(assert (= (Add 2 3) 5))  ; consistent: the axiom forces Add(2,3)=2+3=5
(check-sat)
```

- **z3:** `sat` ✓
- **OxiZ:** `unsat` ✗ — here the instantiation *does* fire (the `(+ a b)`
  body), but the quantifier-instantiation × LIA interaction derives a
  **spurious conflict** from a satisfiable set. This is the opposite
  (`unsat`-for-`sat`) unsoundness.

### Bracketing observations

| # | formula | expect | OxiZ |
|---|---|---|---|
| a | `forall a b. g(a,b)=a` ; `g(7,3)=7` (no arith) | sat | `sat` ✓ |
| b | `forall a b. g(a,b)=a` ; `g(7,3)=9` (no arith) | unsat | `sat` ✗ (R1-class) |
| c | bare `Add` axiom alone | sat | `sat` ✓ |
| d | `z = (Add 2 3)`, no value constraint | sat | `sat` ✓ |
| e | `Add(2,3)=5` (R2) | sat | `unsat` ✗ |
| f | `Add(2,3)=6` (genuine contradiction) | unsat | `unsat` ✓ (right, maybe by luck) |

So: e-matching does not produce the conflict clause for the simple
ground-instantiation case (b/R1), and the arithmetic-body instantiation
path produces a spurious conflict on a consistent ground equation (e/R2).

## Why it was never caught

The "100% Z3 parity" suite (`TODO.md`) is **all `QF_*`** (quantifier-free)
logics. There is **no end-to-end integration test that asserts `unsat` in
the presence of a `forall`** (grep `oxiz-solver/tests` for `forall` +
`unsat` → none). The MBQI unit tests cover heuristics/scoring internals,
not the parse→solve→verdict path on a quantified conflict.

## What a fix must restore

1. R1 → `unsat`: the active ground term `(f 3)` must trigger the
   `:pattern ((f a))` instantiation `f(3)=3`, yielding the conflict with
   `f(3)=4`. Equivalently, when a universal cannot be instantiated and a
   ground model is found that does not verify it, the verdict must be
   `unknown`, **never `sat`** (no spurious model).
2. R2 → `sat`: the instantiation `Add(2,3)=2+3` must be reconciled with the
   ground `Add(2,3)=5` as `5=5` (consistent), **not** a conflict.
3. Add regression tests that assert the correct verdict for R1 and R2 (and
   the bracketing rows) through the real solve path — the gap that let this
   ship.

## Cross-check harness

`z3 file.smt2` (or `z3 -in < file.smt2`) is the reference for every case
above. adsmt also pins this with
`adsmt-cli/tests/theory_abduction_delegation.rs`, which drives the
delegation against a complete oracle (z3) and would go green against a
fixed OxiZ used as the oracle.

---

# Root cause and fix (2026-06-12)

Three independent defects compounded; all are fixed. Regression coverage:
`oxiz-solver/tests/uf_sort_and_quant_soundness.rs`.

## 1. Function-application sort lost across `execute_script` calls

The decisive defect. `Context::execute_script` parsed each call with a
**fresh** `Parser` (`parse_script`), and the parser's declared-function /
constant / sort tables live on the parser, not on the persistent
`TermManager`. So when a front-end feeds commands ONE at a time (the
streaming `oxiz` CLI, and adsmt's in-process delegation, which replays the
buffer command-by-command because batch `parse_script` mis-parses large
multi-command inputs), `(declare-fun f (Int) Int)` and a later
`(assert (… (f 3) …))` landed in *different* parser instances. The second
parser's `functions` table was empty, so `parse_application` (terms.rs)
defaulted `(f 3)` to **`Bool`** sort — and a Bool-sorted `f(3)` is invisible
to EUF/LIA reasoning. `mk_eq`'s canonical reorder then made the symptom
asymmetric (`f(3)=3` vs `f(3)=4` classified differently), which is why the
verdicts looked *inverted* rather than merely wrong.

**Fix:** persist the parser symbol tables in the `Context` across calls.
New `oxiz_core::smtlib::ParserEnv` + `parse_script_with_env`; `Context`
holds a `parser_env` and threads it through every `execute_script`. (This
is a State-monad threading of the parser environment — `&mut ParserEnv` as
the carried state.)

## 2. Integer constants not pinned apart on the EUF equality path

`intern_term_for_congruence` (used for `(= a b)` merges) handled
`BitVecConst` with pairwise disequalities but **omitted `IntConst`**, so
`f(3)=3 ∧ f(3)=4` merged `{f(3),3,4}` into one class with no `3≠4` edge and
no conflict — even once `f(3)` was correctly Int-sorted. **Fix:** mirror the
BV arm for `IntConst` (canonical node per value + pairwise diseqs); a diseq
between distinct constant *values* is a tautology, so it can only fire on a
genuine `3=4` contradiction — never a spurious UNSAT.

## 3. Model-based MBQI enumeration blew up on `:pattern` axioms

With `Add` correctly Int-sorted, the model-based counterexample generator
enumerated `Add(v,w)` over candidate integers; each is a fresh trigger term
that re-fires e-matching, and over an infinite domain it never converged —
turning a SAT formula (`Add(2,3)=5`, or `y>0 ∧ ¬(Add(x,y)>0)`) into a hang.

**Fix (completeness):** make pattern-guided e-matching the primary discipline.
- The parser now threads `:pattern` triggers into `TermKind::Forall`
  (`parse_forall` → `collect_trigger_patterns` → `mk_forall_with_patterns`);
  previously they were dropped, so the MBQI engine could not tell a
  trigger-guided axiom from a trigger-free one.
- The solve loop runs **e-matching to a fixpoint first**
  (`Solver::ematch_fixpoint_step`): instantiate at trigger matches, dedup via
  the match cache, re-solve. This catches pattern conflicts (`Add(2,3)=2+3`
  vs an asserted `Add(2,3)=6`).
- The model-based pass (`MBQIIntegration::run`) then **skips quantifiers that
  carry explicit patterns** — they are handled by e-matching — and enumerates
  only trigger-free quantifiers. Once e-matching saturates, a `:pattern`
  quantifier is satisfied at every relevant ground term (the standard z3/cvc5
  trigger semantics), so the model is reported `sat` without the blow-up.

**Fix (termination backstop):** a wall-clock guard on the MBQI loop
(`MBQI_NONTERMINATION_GUARD_MS`, or the configured `timeout_ms`) returns the
sound `Unknown` rather than hang, for genuinely-recursive triggers the
fixpoint can't bound. Quantifier-free problems never reach it.

## Result

Every case in the tables above now matches z3 (`f(3)=4`→`unsat`,
`Add(2,3)=5`→`sat`, `Add(2,3)=6`→`unsat`, the precondition entailment
→`unsat`, the empty-hypothesis countermodel →`sat`). adsmt's in-process
`:abduct-theory` delegation returns the correct `(>= x 0)` abduct on the
verus `Add` encoding in ~0.01s. No regressions across the oxiz-core /
oxiz-solver / oxiz-cli / bench-regression suites.
