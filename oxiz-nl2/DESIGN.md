# oxiz-nl2 — clean-room nonlinear-arithmetic solver for OxiZ

> Status: **DESIGN** (2026-06-23). Pre-implementation spec. Successor to OxiZ's
> `NlsatSolver` (real, `oxiz-nlsat/src/solver/`) + `NiaSolver` (integer,
> `oxiz-nlsat/src/nia.rs`), which a z3-differential proved **broadly unsound on
> nonlinear `unsat`**. Clean-room precedent: `oxiz-mbqi`, the SAT-core redesign.

---

## 0. Why this exists

A randomized z3-differential over OxiZ's nonlinear path found that **both** core
solvers decide nonlinear `unsat` incorrectly at high rates — single-atom
false-unsat NRA deg-2 13% / deg-3 32% / deg-4 16%, NIA 58/400 (`3x²<5`,
`x⁴>4`, `3x²≥25`, `x²=3`-as-integer all decided spurious `unsat`). This is not a
patchable bug; the cores *pronounce* unsat from procedures that are not sound on
that class. OxiZ is currently held sound only by **band-aid gates** in
`oxiz-theories/src/nlsat.rs` (`unsat_is_trustworthy = poly_atoms.all(total_degree
≤ 1)` — trust the core's unsat only on the linear fragment) plus §G/§G-SOS/
trichotomy as the *sound* nonlinear-unsat deciders. That restores soundness at a
**completeness cost**: the ~25% residual z3-divergences are all FALSE_SAT
(verus-safe; "a sound nlsat would decide these").

`oxiz-nl2` is the sound replacement. It is designed so that **every milestone is
sound by construction from its first verdict-producing commit**, and completeness
is added monotonically without ever rewriting the core loop.

### Non-negotiable priority order

```
soundness  ≫  completeness  ≫  latency
FALSE_UNSAT = 0   (hard, verus-DANGEROUS: a false proof)
FALSE_SAT   = 0   (hard, verus-safe but still wrong; gated)
Unknown is ALWAYS an acceptable verdict.
```

`FALSE_UNSAT` is the catastrophic direction: an OxiZ `unsat` that z3 calls `sat`
becomes, on a negated Verus goal, a **false verification**. `FALSE_SAT` cannot
produce a false proof (it surfaces as Verus *incompleteness*), but it is still a
wrong answer and is gated to 0 too. `Unknown` is the sound fallback everywhere.

---

## 1. The one idea: a frozen MCSAT loop + a growing explainer ladder

`oxiz-nl2` is a **model-constructing MCSAT trail** (Jovanović–de Moura nlsat
lineage) over OxiZ's *existing* per-variable feasible-region substrate. The loop
and its data structures are **frozen at M1 and never rewritten**. All future
completeness lands as new tiers behind a single trait:

```
                    ┌─────────────────────────────────────────┐
   asserted atoms → │  MCSAT trail loop  (FROZEN at M1)        │ → Sat(model)
                    │   • assign vars one at a time            │ → Unsat(covering)
                    │   • narrow feasible regions (IntervalSet)│ → Unknown
                    │   • on conflict: call explain(...)       │
                    └───────────────┬─────────────────────────┘
                                    │  the ONE soundness seam
                          ┌─────────▼──────────┐
                          │  Explainer ladder  │   (GROWS over M1→M7)
                          │  Layer 0  pre-deciders (§G/§G-SOS/trichotomy)
                          │  Tier 1   interval-exclusion        (M1)
                          │  Tier 2   linearization lemmas (IL) (M2, PERMANENT)
                          │  Tier 3   McCallum → CDCAC covering (M4)
                          └────────────────────┘
```

The soundness of the whole solver reduces to **one contract on one function**:

> **`explain(conflict, trail) → Clause`** must return a clause that is **valid
> over ℝ** (true in every real model) and that is **falsified by the current
> partial assignment** (so it actually prunes). Nothing else in the loop can
> produce an `unsat`.

Because `explain` is the only path to `unsat`, and because the cheapest tier
(interval-exclusion) is sound from day 1, the solver is sound at M1 and *stays*
sound as richer tiers are added — a richer tier only ever turns an `Unknown`
into a decided verdict.

### Why this design over the alternatives

The design-workflow scored three architectures (full synthesis at
`~/research-library/nonlinear-solvers/DESIGN-WORKFLOW-SYNTHESIS.md`):

| | sound-first-IL | cdcac-complete | **mcsat-hybrid (chosen)** |
|---|---|---|---|
| M1 effort | smallest | small (univariate slice) | small (wire existing substrate) |
| Completeness ceiling | **capped** — only breaks it by *becoming* CDCAC | full QF_NRA | full QF_NRA, **inside the same loop** |
| Rewrite to reach ceiling | yes (bolt on a 2nd engine) | n/a (paid up front) | **none — explainer grows, loop fixed** |
| Reuses OxiZ substrate | partial (UFLRA) | projection toolkit | **trail substrate as-is** |

mcsat-hybrid is the only one whose single fixed loop spans the entire
sound-first → conflict-driven-complete arc with **no rewrite**, because it makes
*the explainer* the growing part. IL's lemma library is not discarded — it is
**folded in as the M2 explainer tier** (cheap, rational-only, Verus-trivial).
CDCAC's covering is **realized inside `explain` at M4**.

---

## 2. The two runtime gates (soundness independent of explainer correctness)

Two re-check gates wrap every verdict. They enforce `FALSE_UNSAT=0` /
`FALSE_SAT=0` **even if the explainer or projection has a bug** — a faulty result
downgrades to `Unknown`, never to a false verdict. This is what makes each
milestone independently shippable.

- **G-SAT — exact model re-check.** Every `Sat` carries an explicit point
  `Model: Var → Value` where `Value = Rational(BigRational) | Algebraic(AlgebraicNumber)`.
  Before returning, substitute into *every* input atom and check the sign
  **exactly** (rational coords → `Polynomial::eval_at`; algebraic coords →
  `AlgebraicNumber::signum`). A failed re-check ⇒ `Unknown`. **False-Sat is
  structurally impossible.** (Promotes today's `model_satisfies_atoms` backstop,
  `oxiz-theories/src/nlsat.rs`, from band-aid to invariant; kept permanently as
  defense-in-depth.)

- **G-UNSAT — covering re-verification.** Every `Unsat` carries a covering: a
  set of cells, each tagged with the origin atom that is false on it, plus an
  infeasible subset of origin atoms. Before returning, cheaply re-verify (i) each
  cell is genuinely all-unsat for its tagged atom (sample + sign-check), and (ii)
  the cells union to the whole space at the top dimension. A failed re-check ⇒
  `Unknown`. **False-Unsat downgrades to Unknown** even with an unverified
  projection.

These gates are the *whole* soundness story for M1. Everything the explainer
ladder adds (M2→M7) only buys *completeness* (fewer Unknowns), never soundness.

---

## 3. Core data structures

Reuse OxiZ's substrate verbatim where it exists; build only the loop glue and the
two algebraic primitives (§7).

```rust
// ── Values & model (M0) ──────────────────────────────────────────────
/// A coordinate is exact: rational in the common case, algebraic only when an
/// equality forces an irrational. NEVER an f64.
enum Value { Rational(BigRational), Algebraic(AlgebraicNumber) }

struct Model { vals: IndexMap<Var, Value> }
impl Model {
    /// G-SAT: re-check every atom exactly. The mandatory final Sat gate.
    fn checks(&self, atoms: &[PolyAtom]) -> bool;
}

// ── Normalised atom (reuse the existing translator output) ───────────
struct PolyAtom { poly: Polynomial, op: AtomCmp /*Lt,Le,Gt,Ge,Eq,Ne*/, sort: VarSort, origin: OriginId }

// ── The MCSAT trail (FROZEN at M1) ───────────────────────────────────
struct Trail {
    /// var assignment order; reuse oxiz-nlsat/src/var_order.rs
    order: VarOrder,
    /// per-variable feasible region; reuse oxiz-nlsat/src/interval_set.rs
    feasible: HashMap<Var, IntervalSet>,
    /// committed point assignments so far; reuse oxiz-nlsat/src/assignment.rs
    assign: Assignment,
    /// decision/propagation stack for backjumping
    entries: Vec<TrailEntry>,
    /// learned ℝ-valid clauses from explain()
    learned: Vec<Clause>,
}

// ── The soundness seam (the ONLY interface that grows) ───────────────
trait Explainer {
    /// MUST return a clause valid over ℝ and falsified by `trail`.
    /// MAY return GiveUp(reason) → the loop treats that subproblem as Unknown.
    fn explain(&self, conflict: &Conflict, trail: &Trail) -> ExplainResult;
}
enum ExplainResult { Clause(Clause), GiveUp(GiveUpReason) }

// ── Unsat certificate (carried for G-UNSAT) ──────────────────────────
struct UnsatReason { covering: Vec<Cell>, infeasible_subset: Vec<OriginId> }
struct Cell { region: IntervalSet, falsifies: OriginId }   // sampled + sign-checked by G-UNSAT
```

`Verdict = Sat(Model) | Unsat(UnsatReason) | Unknown(Cause)`.

---

## 4. The solve loop (pseudocode — frozen at M1)

```text
fn check(atoms) -> Verdict
  # ── Layer 0: exact one-sided pre-deciders (cheap, already sound; PERMANENT) ──
  if trichotomy_infeasible(atoms):            return Unsat(bound_conflict(atoms))
  if let Some(c) = definite_sign_unsat(atoms): return Unsat(single_atom(c))   # §G/§G-SOS
  if let Some(c) = integer_infeasible(atoms):  return Unsat(c)                # x²=3, parity…

  # ── MCSAT trail loop ─────────────────────────────────────────────────────
  let mut trail = Trail::new(atoms)
  loop:
    if budget.exhausted():                    return Unknown(Budget)
    match pick_unassigned_var(&trail):
      None =>                                  # all vars assigned & feasible
        let m = trail.model()
        return if m.checks(atoms) { Sat(m) } else { Unknown(GSatFailed) }  # G-SAT
      Some(v) =>
        let region = trail.feasible[v]         # narrowed by all committed atoms
        match region.sample():                 # rational-preferred sample point
          Some(point) => trail.assign(v, point); continue
          None =>                              # region empty ⇒ conflict at v
            match explainer.explain(&conflict_at(v), &trail):
              Clause(c) =>
                trail.learn(c)
                match analyze_and_backjump(&trail, &c):
                  Backjump(level) => trail.backjump(level); continue
                  TopLevelConflict(reason) =>
                    return if g_unsat_verify(&reason) { Unsat(reason) }     # G-UNSAT
                           else { Unknown(GUnsatFailed) }
              GiveUp(_) =>                      return Unknown(NoExplanation)
```

Load-bearing properties:
- The **only** route to `Unsat` is Layer-0 (exact, sound) or a `Clause` from
  `explain` (ℝ-valid by contract, re-verified by G-UNSAT). No procedure ever
  *pronounces* unsat off an unsound search.
- `Sat` is witnessed by the trail and re-checked by G-SAT.
- Every escape hatch (`budget.exhausted`, `GiveUp`, gate failure) goes to
  `Unknown` — never to a guessed verdict.

---

## 5. The explainer ladder (what grows over M1→M7)

Each tier is a valid-clause source behind `explain`. Tiers are tried
cheapest-first; the first that returns a `Clause` wins. Adding a tier can only
*reduce* the Unknown rate.

- **Layer 0 (pre-deciders, PERMANENT).** §G univariate-quadratic definite-sign
  (discriminant), §G-SOS multivariate PSD via LDLᵀ inertia, trichotomy bound
  conflicts — kept verbatim from `oxiz-nlsat/src/discriminant.rs` +
  `check_term_bound_infeasible`. Absorbed as the fast front line; never deleted.

- **Tier 1 — interval-exclusion (M1).** `explain` returns "the sign of this poly
  is constant between its rational roots, and that sign contradicts the atom on
  this whole cell." Rational-only; when a separating bound would be algebraic →
  `GiveUp` → Unknown. **Closes every documented single-atom false-unsat.**

- **Tier 2 — linearization lemmas / IL (M2, PERMANENT).** The incremental-
  linearization lemma library folded in as a clause source: sign (`a>0∧b>0 →
  ab>0`), zero (`ab=0 ↔ a=0∨b=0`), monotonicity (`b≥0∧a₁≤a₂ → a₁b≤a₂b`),
  tangent-plane/secant (`ab − (ab₀+a₀b−a₀b₀) = (a−a₀)(b−b₀)`, **rational anchors
  only**), square (`a²≥0`). Each lemma is an ℝ-validity theorem proved once
  (Verus, M6). Closes the bulk of "needs one valid lemma" multivariate unsats
  *without any algebraic machinery*. **Kept permanently** (user call) as a fast
  pre-explainer even after M4 subsumes it on QF_NRA.

- **Tier 3 — model-based McCallum → CDCAC covering (M4).** `explain` does
  model-based projection (discriminant + required leading coeffs + relevant
  resultants, reusing `resultant`/`subresultant_prs`/`leading_coeff_wrt`) and
  returns a cylindrical-covering clause. This is where G-UNSAT's covering
  re-verification turns on. Nullification → `GiveUp` → Unknown (removed at M7 by
  Lazard). **Sound + complete QF_NRA modulo nullification.**

---

## 6. NIA — same loop, integer as a modular layer (M5)

Integer `unsat` only ever comes from a *real-unsat* or an *exact
integer-infeasibility certificate*. Four sound sources, in order:

1. **Real-relaxation** (`∀ℝ-unsat ⟹ ∀ℤ-unsat`): run the real loop over the
   relaxation; any `Unsat` is sound for the integers (covers `x²<0`, the §G
   family).
2. **Exact integer certificates:** perfect-square (`x²=3` → not a square),
   divisibility, parity. Cheap, Unknown-friendly.
3. **Conflict-directed branch-and-bound** over integer-prefer feasible-set
   sampling, with the **Borralleras Thm 3.1 artificial-bound-core gate**: a
   bounded integer search's `unsat` is sound for NIA *only if no artificial bound
   appears in the unsat core* — else widen and retry. This is the *precise*
   condition that replaces the blunt `total_degree≤1` NIA band-aid.
4. **Integer local search** (Sat-only, exact integer witness, never unsat).

Pure NIA is undecidable (Matiyasevich); when none decides → `Unknown`. **Routing
invariant preserved:** never integerize a real var — a mixed NIRA problem routes
to the real core (keep the existing `term_mentions_real_sort` /`route_real`
guards in `check_nlsat.rs`).

---

## 7. Real-algebraic reuse vs build

**Reuse as-is** (verified present in `oxiz-math` / `oxiz-nlsat`):
`AlgebraicNumber{new,signum,compare,add,mul,negate,refine}`
(`algebraic/number.rs`); `root_isolation::isolate_roots` + Sturm
`root_counting`; the projection toolkit
`resultant`/`discriminant`/`subresultant_prs`/`leading_coeff_wrt`/`eval_at`/
`square_free`/`primitive`; `IntervalSet{intersect,complement,sample,is_reals,
from_constraint}` and the whole trail substrate
`Assignment`/`feasible`/`var_order`; §G/§G-SOS `discriminant.rs`; the
`TermPolyTranslator` term→poly bridge; UFLRA+EUF (only if a tier wants a sanity
check — not load-bearing for the spine).

**Build exactly TWO primitives — both at M3, both behind the G-gates** (all three
literature studies independently name these as THE soundness-critical gaps):

1. **`sign_at_algebraic(p, partial_model) → Sign`** — exact multivariate sign at
   a possibly-algebraic point. Rational fast path via `eval_at`; algebraic coords
   via `AlgebraicNumber` arithmetic + `signum` (refine until decisive, else →
   undetermined → Unknown). **The existing `advanced_ops::sign_at` is a
   *syntactic* `Var→sign` heuristic returning `None` when undetermined — it MUST
   NOT be used for verdicts.**
2. **Real-root isolation with an algebraic sample coordinate**, via the
   **resultant-encoding** route (`res_{x_j}(p, m_j)` keeps coefficients over ℚ,
   then `isolate_roots` + disambiguate with `sign_at_algebraic`) — *avoiding* an
   extension-field arithmetic tower.

**Staging payoff:** M1 and M2 need *neither* primitive (rational-only sampling
keeps the partial model rational until the McCallum tier). The hardest,
most-spurious-prone math (sign-at-irrational) is deferred to M3/M4, fuzzed in
isolation against z3 before wiring, and shielded by the G-gates.

---

## 8. The z3-differential gate (day-1 regression spine, [후검증])

Stand up **before** the first verdict-producing commit. The harness that *found*
the bug (`$CLAUDE_JOB_DIR/tmp/diff_*.py`) becomes the `nl_differential` corpus.

- **Generator:** random conjunctions of polynomial atoms (vary degree, var count,
  op, coefficients, conjunct count) + the documented failing shapes seeded
  explicitly: `3x²<5`, `x⁴>4`, `x·y>5`, `3x²≥25`, `x²=3`, the §G perfect-square
  family, bivariate bilinear.
- **Hard invariants (panic on violation):** `FALSE_UNSAT = 0` (oxiz=Unsat ∧
  z3=Sat — the gate); `FALSE_SAT = 0` (oxiz=Sat ∧ z3=Unsat — plus every `Sat`
  must carry a model that `Model::checks`).
- **Non-gating telemetry:** Unknown-rate vs z3 per degree/arity — makes
  completeness growth measurable without ever pressuring soundness.
- Oracles: z3 4.16.0 + cvc5 1.3.0 at `/usr/bin/`. Full-corpus sweeps are the
  user's `!` gate; the harness ships scoped + a one-command full run. A green
  unit suite is necessary but **not sufficient** — see
  `feedback-z3-differential-for-unsat-trust` (the 13/13 unit battery that hid 119
  false-unsats).

---

## 9. Verus pre-verification ([선검증], M6, mirror `oxiz-sat-redesign-verification`)

Discharge in the separate `~/oxiz-nl2-verification` repo (precedent:
`oxiz-sat-redesign-verification`, 28 obligations). Targets, smallest-surface
first:
- **Tier validity (highest leverage):** each Tier-1 interval-exclusion and each
  Tier-2 lemma schema's defining inequality — small decidable algebraic facts,
  rational anchors so no irrational ever appears in a lemma.
- **Loop invariant:** the committed partial model violates no atom at any
  assigned stage.
- **Covering bookkeeping:** "certified-unsat cells covering the space ⟹ UNSAT"
  (the G-UNSAT predicate).
- **G-SAT predicate:** `Model::checks` is a faithful exact evaluator.
- **NIA bound-core gate:** Borralleras Thm 3.1 ("bounded-search unsat with no
  artificial bound in the core ⟹ NIA-unsat").

Explicitly **out of Verus scope** (and fine, because the G-gates re-check at
runtime): the reused UFLRA engine's own soundness (separately trusted), and
McCallum delineability (runtime-guarded by G-UNSAT). Runnable in parallel from M2.

---

## 10. Milestone roadmap

Each milestone ships **sound** (G-SAT + G-UNSAT green, differential
`FALSE_UNSAT=0`) and only *adds decisiveness*. The loop + data structures are
fixed at M0/M1.

| M | Deliverable | Exit criterion |
|---|---|---|
| **M0** | z3-diff gate (seeded + bounded random) + crate skeleton `~/oxiz-nl2`, `Explainer` trait, `Value`/`Model` carrying `AlgebraicNumber` losslessly. No verdicts yet. | harness runs, builds green |
| **M1** | Sound MCSAT spine + **interval explainer + §G folded in** (user call). Rational-only sampling; algebraic bound → GiveUp→Unknown; G-SAT live. | **decides every documented single-atom false-unsat correctly**; differential FALSE_UNSAT=0 |
| **M2** | Linearization explainer tier (IL lemmas, rational anchors) behind `explain`. Still rational-only, Verus-trivial. | bulk of "one valid lemma" multivariate unsats decided; differential clean |
| **M3** | Local-search SAT portfolio (never-unsat, exact witnesses) + build the two algebraic primitives, fuzzed in isolation vs z3 first. | `x·y>5` decided Sat; primitives pass isolated fuzz |
| **M4** | Model-based McCallum projection → CDCAC covering; G-UNSAT covering re-verify ON; nullification→Unknown. | **sound+complete QF_NRA modulo nullification**; delete NRA `total_degree≤1` band-aid |
| **M5** | NIA: real-relaxation + integer certs + conflict-directed B&B + Borralleras bound-core gate + integer LS. | NIA differential FALSE_UNSAT=0; delete NIA band-aid |
| **M6** | Verus pre-verification in `~/oxiz-nl2-verification` (parallel from M2). | obligations discharged |
| **M7** | **Lazard projection (COMMITTED, user call)** — kills nullification-Unknown; + projective-delineability, conflict minimization, capped cheap resultants. | nullification-Unknown removed |

### Band-aid deletion schedule (gated on the differential, NEVER a date)
- `model_satisfies_atoms` → demoted to defense-in-depth at M1 (kept, cheap).
- `unsat_is_trustworthy = total_degree≤1` → delete **NRA gate at M4**, **NIA gate
  at M5** (after the bound-core gate lands), each only once the differential is
  `FALSE_UNSAT=0` on the full nonlinear corpus.
- §G/§G-SOS/trichotomy → **kept permanently** as Layer-0 pre-deciders (absorbed).
- `NlsatSolver` + `NiaSolver` → deleted after `oxiz-nl2` passes corpus +
  differential (same as `oxiz-solver/src/mbqi/` #262).

---

## 11. M4-port seam

Develop `oxiz-nl2` standalone against `oxiz-math` (already a dependency) with its
own differential suite; then M4-port (mirrors the SAT-core / MBQI ports):

1. Add `oxiz-nl2` to the OxiZ workspace.
2. Rewrite only the *body* of `dispatch_nl_solver` (`check_nlsat.rs`) so
   `dispatch_nra_constraints` / `dispatch_nia_constraints` delegate to
   `oxiz_nl2::check`, keeping their signatures + the `NlDispatchResult` return so
   `mod.rs` dispatch order is untouched.
3. Reuse verbatim: the translator (`TermPolyTranslator`/`RealPolyTranslator`),
   the verus `Mul`/`RMul`/`Add`/`Sub` bridge-rewrite path, the NIRA real-sort
   guard. They produce `PolyAtom`s for the new core.
4. Delete the unsound cores + their now-dead band-aid gates only *after* the
   `nl_differential` corpus is green at FALSE_UNSAT=0 on the new core. **No
   "delete and hope"** — every gate removal is paired with the evidence (z3-diff
   + the relevant Verus invariant) that the verdict it guarded is now sound by
   construction.

---

## 12. Tactical defaults (overridable)

Two knobs the synthesis flagged for a call. Defaults chosen here; revisit if the
verus workload's Unknown-rate/latency says otherwise.

- **Budget topology = PER-TIER, not global.** Separate budgets: LS time-box ⟂
  projection step-cap ⟂ NIA branch-depth cap. Rationale: the tiers have wildly
  different cost profiles and a single global node-budget would let a cheap tier
  starve an expensive-but-decisive one (or vice versa). Per-tier budgets make the
  Unknown-vs-latency tradeoff tunable where it matters and keep each tier's
  termination argument local. Each budget exhaustion → `Unknown` (sound).
- **NIA artificial-bound policy = bounded-first with one widening round.** Initial
  symmetric bound `|xᵢ| ≤ 2^10` per unbounded integer var; on a bound-core
  conflict (Borralleras Thm 3.1 says the unsat is *not* yet sound), widen to
  `2^20` once, then → `Unknown`. Rationale: most verus integer obligations are
  small-coefficient; one widening round catches the rest cheaply; unbounded
  iterative widening's latency is not worth it for a first cut. "Unknown on
  genuinely-unbounded-integer" is an acceptable M5 starting point.

---

## 13. Repo topology (user call)

- **`~/oxiz-nl2`** — the solver, clean-room (this repo). M4-ported into
  `external/oxiz/oxiz-nl2/`.
- **`~/oxiz-nl2-verification`** — the Verus pre-verification project, mirroring
  `oxiz-sat-redesign-verification`.

Both standalone, like the `oxiz-mbqi` precedent.

---

## 14. Top risks (and why each is contained, not just tested)

1. **Exact sign / model-check correctness** (where the *current* nlsat went
   wrong: sign of a poly at an irrational point). *Contained:* the sound core is
   all-rational through M2 (no algebraic sign needed); the mandatory G-SAT /
   G-UNSAT gates make any error `Unknown`-not-unsound; the algebraic sign path is
   confined to M3+ behind the gates and the differential's algebraic-sign
   double-check against z3.
2. **Too many Unknowns on the verus workload** before M4 lands CDCAC. *Contained:*
   Layer 0 + Tier 1/2 cover the documented cases; the differential's
   per-degree Unknown-rate telemetry makes the gap *measurable* before it bites,
   so M3/M4 are prioritized by data, not guesswork; Unknown is the accepted sound
   fallback meanwhile.
3. **Lemma/projection non-termination or blow-up.** *Contained:* per-tier
   `Budget` → `Unknown`; rational-anchor damping; incremental re-solve.
   Termination is **not** required for soundness (only ℝ-valid-clauses-only is),
   so this is a perf/completeness risk, never a soundness one.

---

## References

- Full design-workflow synthesis (3 studies + 3 proposals + scored comparison):
  `~/research-library/nonlinear-solvers/DESIGN-WORKFLOW-SYNTHESIS.md`.
- Papers: `~/research-library/nonlinear-solvers/README.md` (CDCAC 2020/2026,
  nlsat/MCSAT 2012→2025, incremental-linearization 2018, NIA, local search, CAD
  surveys).
- Auto-memory: `oxiz-nlsat-redesign`, `nlsat-algebraic-reduction-kb`,
  `feedback-z3-differential-for-unsat-trust`, `oxiz-redesign-verification-pipeline`.
