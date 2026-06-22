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
- **Foundation (this branch):** A0 linear-elimination + Sturm real-root test +
  algebraic (`AlgebraicNumber`) model — discharges `test_solver_circle_and_line`.
- **Follow-up Level-1+:** A1 resultant, A2 product-of-forms, A3 conic
  parameterisations, B/C transcendental normalisation (tie into calculus.rs).
