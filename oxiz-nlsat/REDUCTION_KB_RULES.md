# Reduction-KB rule catalog (oxiz-nlsat algebraic-solution)

The reduction KB (mirroring `oxiz-solver/src/calculus.rs`'s leveled monotonicity KB)
turns a multivariate (in)equation system into a **univariate** one whose real
roots can be isolated by Sturm sequences, then builds an algebraic model. This
file is the **rule catalog** (user-provided, 2026-06-22). Each rule must be
applied SOUNDLY: it preserves the real solution set (so "reduced system has a
real root ⇒ original is SAT", verified by back-substitution against every
original atom).

Levels mirror calculus.rs: **Level 0** = primitive, directly verifiable;
**Level 1+** = derived/composite, re-verified from lower levels.

---

## A. Bivariate polynomial → univariate

### A0 (Level 0) — linear-equality elimination *(the circle-line case)*
A `(a·x + b·y + c) = 0` equality with `b ≠ 0` ⇒ `y = −(a·x + c)/b`; substitute
into every other atom → univariate in `x`. EXACT, purely algebraic, complete for
linear equalities. (For `x²+y²=25 ∧ y−x=0`: `y=x` ⇒ `2x²−25=0`, roots ±√12.5.)
This is the rule the foundation must ship — it discharges the failing test.

### A1 (Level 0) — resultant / Gröbner elimination
For two polynomial equalities `p(x,y)=0 ∧ q(x,y)=0` with no linear relation, the
**resultant** `Res_y(p,q)` is a univariate polynomial in `x` whose real roots
contain every `x`-coordinate of a common solution. Algebraic + complete for the
polynomial-equality fragment. (Reuse `grobner_preprocess.rs` / a resultant
helper — see the design survey.) Soundness: a real `x`-root must be lifted and
the lifted `(x,y)` re-checked against `p,q` (resultant roots are a superset).

### A2 (Level 1) — product-of-linear-forms collapse
`(a·x + b·y + c)·(d·x + e·y + f) = k`, `a,b,d,e ≠ 0`. If there is a UNIQUE
function `f` with `f(a·x+b·y+c) = (d·x+e·y+f)` for all admissible `(x,y)` (i.e.
the two linear forms are functionally dependent), set `t = a·x+b·y+c` and rewrite
as `t·f(t) = k` — univariate in `t`. (Only sound when that `f` exists and is
unique; otherwise the two forms are independent and this is a genuine 2-D
variety — use A1.)

### A3 (Level 1) — conic parameterisations (transcendental)
**A conic GENERALISES the circle** — circle ⊂ ellipse ⊂ conic — so do NOT keep a
separate "circle" rule. ONE recognizer classifies any degree-2 bivariate equality
`A·x² + B·xy + C·y² + D·x + E·y + F = 0` by the discriminant `B² − 4AC`
(`<0` ellipse · `=0` parabola · `>0` hyperbola), normalises it (rotate to kill
`B·xy`, translate by completing the square), and dispatches to the matching
parameterisation. The crate's `discriminant.rs` is the natural home for the
classifier. The circle `x²+y²=c²` is just the `B=D=E=0, A=C` ellipse instance
(`a=b=1`), recovered automatically — no special case.

- Ellipse `(x/a)² + (y/b)² = c²`, `c>0` ⇒ `x = a·c·cos(t), y = b·c·sin(t)`
  (or `x = a·c·sin(t), y = b·c·cos(t)`). **Circle = the `a=b` specialisation.**
- Hyperbola `(x/a)² − (y/b)² = c²`, `c>0` ⇒ `x = a·c·cosh(t), y = b·c·sinh(t)`.
- *(parabola + rotated/translated conics handled by the normalise step above.)*

These parameterise the FULL real conic, so substituting into the other atom and
finding a real `t` is sound for SAT. BUT they introduce transcendental symbols —
the reduced equation in `t` is transcendental, not polynomial, so Sturm does not
apply directly. PREFER A0/A1 (algebraic) when a linear/polynomial elimination
exists; A3 is for genuinely transcendental or conic∩conic shapes. Transcendental
symbols connect to `oxiz-solver/src/calculus.rs`'s treatment of `exp`/`ln`/`sin`/
`cos`/`tan` as KB-described uninterpreted functions.

## B. Univariate function inter-conversion (normalise the transcendental term)
- `sinh(t) = (eᵗ − e⁻ᵗ)/2`
- `cosh(t) = (eᵗ + e⁻ᵗ)/2`
- *(tanh, the inverse hyperbolics, and the circular↔exponential `e^{it}` forms —
  extend as needed; goal: reduce a mixed transcendental expression to a single
  base symbol, e.g. `u = eᵗ`, turning `t·f(t)=k`-style hyperbolic equations into
  a polynomial/Laurent equation in `u` that Sturm CAN isolate.)*

## C. Exponential / logarithm conversions (`a>0, b>0`)
- `a^(x+y) = aˣ · aʸ`
- `log_a(x·y) = log_a(x) + log_a(y)`
- `log_a(x) / log_a(y) = log_y(x)` (change of base)
- `a^(x·y) = (aˣ)^y`
- `a^(log_a(b)) = b`
- *(extend: `log_a(x/y)=log_a x − log_a y`, `a^(x−y)=aˣ/aʸ`, `log_a(xⁿ)=n·log_a x`.)*

Use C to collapse an exp/log expression to a single monomial in a base symbol
(e.g. `u = aˣ`), after which B/A reductions and Sturm can finish. Same
soundness rule: the rewrite is an identity over the admissible domain
(`a>0,b>0,x>0` for logs), so it preserves the solution set; verify the final
model against every original atom.

---

## D. `x^k = a` domain ladder (single univariate power equality)
For `x^k = a` (`k ∈ ℕ`), escalate domains *soundly* — the domain a variable
RANGES OVER decides which solution space yields a valid SMT model:
1. **Integer** (only when the var is integer-typed — `nia.rs IntegerVarType::Integer`):
   solvable iff `a` is a perfect `k`-th power (`x = ±a^{1/k} ∈ ℤ`). If not →
   that branch is **UNSAT for an integer var** (do NOT escalate to real).
2. **Real** (the var is real-typed — the pure `NlsatSolver` is all-real NRA):
   - `k` odd ⇒ exactly one real root `x = sign(a)·|a|^{1/k}` (algebraic).
   - `k` even, `a > 0` ⇒ `x = ±a^{1/k}` (algebraic); `a = 0` ⇒ `x = 0`.
   This is the sound SAT fix for `x² − 2 = 0` (`test_quadratic_roots`): no integer
   root ⇒ real root `±√2`, returned as an `AlgebraicNumber`.
   - `k` even, `a < 0` ⇒ **NO real root** ⇒ the *real* query is **UNSAT**.
3. **Complex** — NOT a valid SMT model for NRA/NIA. Reaching the
   even-`k`/`a<0` case means real-UNSAT; the complex roots are irrelevant to a
   real/integer satisfiability verdict. So the KB stays **SAT-only-additive**:
   on "no real root" it FALLS BACK to the complete CAD path (which concludes the
   sound UNSAT) rather than reporting anything from the complex domain.

Precondition: the KB must know the variable's domain. The pure `NlsatSolver` is
all-real (escalate straight to the real step); the NIA layer (`nia.rs`) carries
`is_integer_var` and must gate step 1. The current implementation conservatively
declines single-equation cases to avoid the NIA interaction; rule D is the
principled un-gate (real var ⇒ real algebraic root; integer var ⇒ perfect-power
or hand back to NIA branch-and-bound).

## Soundness invariant (applies to EVERY rule)
A reduction may only be used to conclude **SAT** when (1) it is an exact identity
on the admissible domain (no approximation), (2) the reduced univariate problem
is shown to have a real solution (Sturm for algebraic; a verified root for
transcendental), and (3) the reconstructed full assignment is checked to satisfy
**every original atom**. If a rule's preconditions are not met, FALL BACK — never
fabricate SAT. UNSAT may only be concluded by the existing complete machinery,
not by "no rule applied".

## Implementation status
- **Foundation:** A0 linear-elimination + Sturm real-root test + algebraic
  (`AlgebraicNumber`) model — discharges `test_solver_circle_and_line`.
- **Rule D — LANDED.** `reduction_kb::try_rule_d` un-gates the single-equation
  case for a univariate `p = 0`: it isolates the real root via Sturm and returns
  an exact `AlgebraicNumber`, but ONLY when the root is *irrational*. Soundness /
  NIA safety: `reduction_kb::has_rational_root` (rational-root theorem) declines
  every polynomial with a rational root — `x²-4` (±2), `x³-x` ({-1,0,1}), `x-1`,
  `x-1/2` — leaving them to the base CDCL+CAD search (which represents rationals
  exactly and, for NIA, owns the integer-domain branch-and-bound). Even-`k`/`a<0`
  (`x²+1`) has no real root ⇒ falls back (the CAD path concludes the sound
  real-UNSAT); the KB never returns Sat from a complex root and never returns
  Unsat. Discharges `test_quadratic_roots` (`x²-2 ⇒ ±√2`). Regression tests:
  `test_rule_d_*` in `reduction_kb.rs`.
- **A1 resultant / A3 conic recogniser — LANDED.**
  - `discriminant::recognize_conic` + `ConicForm`/`ConicKind` classify a degree-2
    bivariate `A x²+B xy+C y²+D x+E y+F = 0` by `B²-4AC` (`<0` ellipse, `=0`
    parabola, `>0` hyperbola). The circle is the `A=C, B=0` ellipse instance
    (`ConicForm::is_circle`), recovered automatically — no separate circle rule.
    Pure recogniser/normaliser; does NO solving. Tests:
    `discriminant::tests::test_recognize_*`.
  - The actual *solving* for pure-polynomial conic∩conic / conic∩line stays on the
    exact algebraic path. `reduction_kb::augment_with_linear_combinations` adds the
    sound radical-axis linear combination (`p − λ·r` that cancels the shared
    quadratic part) so the Level-0 linear elimination handles two-conic systems
    through the same Sturm + exact-verify machinery (a genuine conic∩conic becomes
    the already-handled conic∩line). Two intersecting circles, ellipse∩line, and
    the disjoint-circles fall-back are covered (`test_two_circles_*`,
    `test_ellipse_and_line_sat` in `reduction_kb.rs`; `test_conic_*` +
    `audit_conic_false_sat_with_inequality` end-to-end in `integration_tests.rs`).
- **Still Level-1+ frontier (NOT implemented — unsound to fake):** A2
  product-of-forms; the A3 **transcendental trig parameterisation**
  `x = a·c·cos(t), y = b·c·sin(t)` (and the hyperbolic `cosh/sinh`), which needs
  transcendental equation solving beyond Sturm; B/C transcendental normalisation.
  These tie into `oxiz-solver/src/calculus.rs`'s sin/cos/exp/ln KB. The conic
  classifier recognises these shapes but the algebraic path solves only the
  polynomial fragment; a transcendental conic with no polynomial elimination
  falls back (never a fabricated SAT).

---

## E. Range-intersection search bound (parameterized conic∩conic) — *suggestion 2*
Parameterise each side: `conic₁ = {(e(u), f(u))}`, `conic₂ = {(g(v), h(v))}`. A
common point needs `e(u)=g(v) ∧ f(u)=h(v)`, so its **x-coordinate ∈ range(e) ∩
range(g)** and its **y-coordinate ∈ range(f) ∩ range(h)** — solutions live only in
the product box `[range(e)∩range(g)] × [range(f)∩range(h)]`. Bounding the `(u,v)`
search to that box is a **necessary-condition PRUNE**: it discards no solution
(completeness-preserving) and it is a bound, not a verdict, so it is sound in both
directions. Most effective on BOUNDED conics (ellipse: range is a finite interval
`[−ac, ac]`); a hyperbola's coordinate range is all of ℝ ⇒ no pruning.

**Applicability to what we built.** The current conic∩conic SOLVE is the *algebraic*
radical-axis path (rule A1/A0 + Sturm), NOT the parameterised form rule E assumes —
Sturm already isolates finitely many real roots, so the parameterised range search
does not exist to be bounded. Rule E therefore lands in two places: (E-light, now-
applicable) restrict the resultant eliminant's **root isolation to the feasible
x-interval** `range₁(x) ∩ range₂(x)` (each conic's x-extent from its bounding box),
pruning roots outside it — a sound, modest speedup; (E-full) the genuine `(u,v)`
range-box belongs to the transcendental parameterisation frontier (A3 full + B/C),
where it is the key tractability lever.

## F. `unknown` → invertible-transformation hint engine (advisory) — *suggestion 3*
When the solver/KB cannot reduce or decide a system (verdict `unknown`), do not
just give up: GUESS **invertible space transformations** that would map it into a
KB-recognisable form, and surface them as ADVISORY hints. Candidates:
- **Rotation** `θ = ½·atan2(B, A−C)` to kill a `B·xy` cross-term ⇒ the A3 conic
  classifier recognises the result.
- **Translation** (complete the square) to centre a conic; **scaling**; **shear**;
  **variable substitution** `u = φ(x,y)` (e.g. the A2 `t = a·x+b·y+c`).
**Soundness:** hints are advisory and DO NOT change the verdict — `unknown` stays
`unknown` until a hint is actually applied and the reduced problem solved+verified.
A wrong hint is merely unhelpful, never unsound; and an invertible transform of ℝⁿ
(rotation/translation/scaling) is a bijection that PRESERVES the solution set, so a
hint that reduces to a solvable form yields a sound result when followed. This is
**"abduction for the transformation"** — the same advisory philosophy as adsmt's
`(abduce)` / `:abduct-theory` (abduct = advice; the user/downstream must justify).

---

## G. Definite sign by discriminant (univariate quadratic) — *the perfect-square completeness rule*
For a UNIVARIATE quadratic `f(x) = a·x² + b·x + c` (`a ≠ 0`, exact rationals) with
discriminant `D = b² − 4·a·c`, the sign of `f` over ALL real `x` is FIXED — it is the
standard parabola sign analysis (a THEOREM, not a heuristic). Stated as the KB facts
the user requested:

- **`x² ≥ 0` for every real `x`** — the primitive (`a=1, b=0, c=0, D=0, a>0` instance,
  exactly as "the circle is the `A=C, B=0` ellipse instance"). No grinding through
  Sturm/CAD root isolation for it: a single `b²−4ac` decides.
- `D = 0 ∧ a > 0  ⟺  f(x) ≥ 0 ∀x`   (perfect square `a·(x−r)²`)
- `D = 0 ∧ a < 0  ⟺  f(x) ≤ 0 ∀x`
- `D < 0 ∧ a > 0  ⟺  f(x) > 0 ∀x`
- `D < 0 ∧ a < 0  ⟺  f(x) < 0 ∀x`
- `D > 0`         ⟹  `f` changes sign (two real roots) — **indefinite, NOT decided here.**

**As a solver rule (one-sided UNSAT recogniser).** Deciding a NEGATED goal: an asserted
atom that claims a sign the parabola can never take is UNSATISFIABLE. From the table,
`f` is `AllPositive/AllNegative/AllNonNegative/AllNonPositive`; the impossible atoms are:

| definite sign of `f`        | atoms that are UNSAT                  |
|-----------------------------|---------------------------------------|
| `> 0 ∀x` (D<0, a>0)         | `f < 0`, `f ≤ 0`, `f = 0`             |
| `< 0 ∀x` (D<0, a<0)         | `f > 0`, `f ≥ 0`, `f = 0`             |
| `≥ 0 ∀x` (D=0, a>0)         | `f < 0` **only**                      |
| `≤ 0 ∀x` (D=0, a<0)         | `f > 0` **only**                      |

The perfect-square case is the verus completeness lead `x² − 2x + 1 ≥ 0` (= `(x−1)² ≥ 0`,
valid): its negation `(x−1)² < 0` is the `≥0 ∀x` row's `f < 0` ⇒ **UNSAT** ⇒ the
obligation is **provable**.

**Implementation — LANDED.** `discriminant::recognize_univariate_quadratic` reads exact
`a,b,c` (via `Polynomial::univ_coeff`) ONLY for a genuinely univariate degree-2 poly
(`vars().len()==1`, `total_degree()==2`, `a≠0`); `discriminant::DefiniteSign::definite_sign`
classifies by `(sign a, sign D)`; `discriminant::quadratic_atom_is_unsat(poly, AtomCmp)`
returns the one-sided UNSAT verdict per the table above. It is wired as a pre-check in
BOTH `oxiz-theories::nlsat::{dispatch_nia_constraints, dispatch_nra_constraints}` (over the
already-built entailed `PolyAtom`s) — so it serves both the explicit `QF_NIA`/`QF_NRA`
path and the term-based verus Mul/RMul path. To let MULTI-TERM verus goals reach it, the
`check_nlsat.rs` bridge-rewrite was generalised from `Mul`/`RMul` to the whole polynomial
spine `Add`/`Sub`/`Mul` + `RAdd`/`RSub`/`RMul` (each folded to native `+`/`-`/`*` ONLY when
its bridge axiom `(= (Sym x y) (op x y))` is asserted; `EucDiv`/`EucMod`/`RDiv` stay
uninterpreted). Tests: `discriminant::tests::test_quadratic_atom_*`,
`nlsat::tests::g_*` (dispatch wiring), `check_nlsat::tests::nl_perfect_square_*` (e2e).

**Soundness.** One-sided: returns ONLY UNSAT (never Sat). EXACT (rationals, no float).
Fires ONLY on a genuine univariate degree-2 poly; `D > 0` / non-quadratic / multivariate
DECLINE (fall through). Each `PolyAtom` is a top-level CONJUNCT (entailed), so a single
individually-contradictory atom makes the whole conjunction UNSAT — valid even when other
atoms were dropped (subset-UNSAT ⟹ full-UNSAT). And a real-domain UNSAT is a fortiori an
integer-domain UNSAT (`∀ real x` ⟹ `∀ int x`), so the rule is sound for BOTH NRA and NIA.
Verified by an adversarial soundness audit (2026-06-22): no false unsat / false sat.

### G-SOS — the MULTIVARIATE generalisation (PSD / sum-of-squares)
§G's univariate `(sign a, sign D)` test generalises to a multivariate quadratic FORM
`f(x) = xᵀ A x + bᵀ x + c` via the symmetric **Gram (bordered) matrix**
`M = [[A, b/2], [(b/2)ᵀ, c]]`, so that `f(x) = [x; 1]ᵀ M [x; 1]` and `[x; 1] ≠ 0`:

- `M` POSITIVE DEFINITE ⟹ `f > 0 ∀x`            (`AllPositive`);
- `M` POSITIVE SEMIDEFINITE (not PD) ⟹ `f ≥ 0 ∀x` (`AllNonNegative` — the SOS case);
- `−M` PD / PSD ⟹ `f < 0` / `f ≤ 0 ∀x`           (`AllNegative` / `AllNonPositive`);
- otherwise indefinite — NOT decided.

The verus lead `(x − y)² ≥ 0` = `x² − 2xy + y² ≥ 0` is the canonical case: its Gram matrix
`[[1, −1], [−1, 1]]` is PSD (a sum of squares), so the form is `≥ 0` everywhere and its
negation `(x − y)² < 0` is UNSAT. §G is exactly the `1×1`-variable instance of this
(`M = [[a, b/2], [b/2, c]]`, `det M = −D/4`). Implemented in `discriminant.rs`:
`recognize_quadratic_form` builds `M` (cross term `xᵢxⱼ` split symmetrically `M[i][j] =
M[j][i] = k/2`); `matrix_is_pd` (Sylvester — all LEADING principal minors `> 0`) and
`matrix_is_psd` (ALL principal minors `≥ 0` — the non-leading ones are required, e.g.
`diag(0,−1)` is not PSD); `quadratic_form_definite_sign` + `quadratic_form_is_unsat` reuse
the same `DefiniteSign` verdict table. Wired into the same `definite_sign_unsat` pre-check
(`quadratic_atom_is_unsat || quadratic_form_is_unsat`). Determinants are EXACT over
`BigRational`. The variable count is capped (`MAX_FORM_VARS = 6`) since the PSD test
enumerates `2^(n+1)` principal minors; a wider form declines (sound — incomplete). The
PD/PSD conditions are SUFFICIENT (`M` definite ⟹ `f` definite); a form non-negative only
on the affine slice while `M` is indefinite is conservatively declined (never a false
verdict). Adversarial-audited (2026-06-23): 7/7 probes PASS, the exact PSD classifier
cross-checked against eigenvalues on 60 000 matrices (0 false positives). Tests:
`discriminant::tests::test_form_*`, `nlsat::tests::g_sos_*`,
`check_nlsat::tests::nl_multivariate_sos_*`. THE BAR: `multivariate-sos.smt2` goal →
`unsat` via the OxiZ CLI.
