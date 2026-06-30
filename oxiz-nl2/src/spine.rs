//! The frozen MCSAT-style model-construction spine (DESIGN.md §4).
//!
//! Variables are assigned one at a time in a fixed order. For each variable the
//! solver computes a feasible region (an [`IntervalSet`]) from the atoms that
//! have become univariate under the current partial assignment, samples a
//! **rational** point, and recurses; on a dead end it backtracks. A full
//! assignment is a candidate model, gated by **G-SAT** before it is trusted.
//!
//! ## Soundness (the only thing that matters)
//!
//! * **`Sat`** is returned only for a full assignment that passes
//!   [`Model::checks`] exactly — so a `Sat` is never wrong.
//! * **`Unsat`** is returned only from two sound sources: Layer-0 §G/§G-SOS (a
//!   single atom is definitely sign-infeasible), or a genuinely
//!   **single-variable** problem whose *exactly-computed* feasible region (over
//!   atoms with rational-or-no real roots) is empty. Atoms with irrational
//!   roots are only ever *skipped* from that intersection — skipping enlarges
//!   the region, so an empty intersection is a true emptiness. The multi-
//!   variable conflict generalisation that would let the spine itself conclude
//!   `Unsat` is an M4 explainer; until then such conflicts only trigger
//!   backtracking and, if unresolved, `Unknown`.
//! * Everything else is **`Unknown`** (budget exhaustion, no model found,
//!   irrational bounds). Always sound.
//!
//! M1 is rational-only: it never constructs an algebraic coordinate. The
//! documented single-atom false-unsat shapes are all decided here (sat ones by
//! a rational sample, unsat ones by §G or single-var emptiness).

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};
use oxiz_nlsat::interval_set::{ConstraintKind, IntervalSet};
use rustc_hash::{FxHashMap, FxHashSet};

use crate::atom::{AtomCmp, PolyAtom, Polynomial, Var, VarSort};
use crate::layer0;
use crate::univariate;
use crate::value::{Model, Value};
use crate::verdict::{Cause, Cell, UnsatReason, Verdict};

/// Node budget for the backtracking search. Exhaustion → `Unknown` (sound).
const SEARCH_BUDGET: u64 = 20_000;

/// Decide a conjunction of polynomial atoms (DESIGN.md §4 top-level loop).
#[must_use]
pub fn solve(atoms: &[PolyAtom]) -> Verdict {
    // ── Layer 0: exact one-sided pre-deciders ────────────────────────────
    // A constant atom that is false, or a single atom of definite sign
    // (§G / §G-SOS / even-monomial) — either makes the conjunction unsat.
    if let Some(i) = layer0::constant_false_atom(atoms).or_else(|| layer0::definite_sign_unsat(atoms)) {
        return Verdict::Unsat(UnsatReason {
            covering: vec![Cell { falsifies: atoms[i].origin }],
            infeasible_subset: vec![atoms[i].origin],
        });
    }

    let sort = problem_sort(atoms);
    let mut vars: Vec<Var> = atoms.iter().flat_map(|a| a.poly.vars()).collect();
    vars.sort_unstable();
    vars.dedup();

    // Empty problem (no variables): all atoms are constants — evaluate them.
    if vars.is_empty() {
        return decide_constant_only(atoms);
    }

    // ── Exact single-variable decision (the own univariate Sturm engine) ──
    if vars.len() == 1 {
        let v = vars[0];
        let uni: Vec<(Vec<BigRational>, AtomCmp)> =
            atoms.iter().map(|a| (univariate_coeffs(&a.poly, v), a.op)).collect();
        let all_unsat = || {
            Verdict::Unsat(UnsatReason {
                covering: atoms.iter().map(|a| Cell { falsifies: a.origin }).collect(),
                infeasible_subset: atoms.iter().map(|a| a.origin).collect(),
            })
        };
        match univariate::decide(&uni) {
            univariate::UniResult::Unsat => return all_unsat(),
            univariate::UniResult::SatAlgebraic(alpha) => {
                // Real-satisfiable only at an irrational point ⇒ no rational
                // (hence no integer) point. For ℤ that is integer-unsat (sound).
                // For ℝ, witness it with an exact algebraic model and G-SAT it.
                if sort == VarSort::Integer {
                    return all_unsat();
                }
                let mut m = Model::new();
                m.insert(v, Value::Algebraic(alpha));
                if m.checks(atoms) {
                    return Verdict::Sat(m);
                }
                return Verdict::Unknown(Cause::AlgebraicBound);
            }
            univariate::UniResult::Sat(w) => {
                if sort == VarSort::Real || w.is_integer() {
                    let mut m = Model::new();
                    m.insert(v, Value::Rational(w));
                    if m.checks(atoms) {
                        return Verdict::Sat(m);
                    }
                } else {
                    // Integer sort, non-integer real witness (M5/NIA): the real
                    // relaxation is feasible, so decide INTEGER feasibility by an
                    // exhaustive search over the Cauchy-bounded range (complete:
                    // every integer solution lies within it). Unsat ⇒ sound
                    // integer-unsat; a too-large range ⇒ Unknown.
                    match single_var_integer_feasible(atoms, v) {
                        IntFeas::Sat(m) => return Verdict::Sat(m),
                        IntFeas::Unsat => return all_unsat(),
                        IntFeas::Unknown => {} // fall through
                    }
                }
            }
        }
    }

    // ── Univariate sub-core unsat (multivariate) ─────────────────────────
    // For each variable, the atoms that mention ONLY that variable form a
    // univariate sub-problem. If that subset is unsatisfiable, so is the whole
    // conjunction (a subset being unsat ⇒ unsat). Reuses the exact univariate
    // engine; closes e.g. `−5x⁴ ≥ 0 ∧ 2x⁴ ≠ 0` embedded in a 2-var problem.
    for &v in &vars {
        let sub: Vec<(Vec<BigRational>, AtomCmp)> = atoms
            .iter()
            .filter(|a| a.poly.vars() == [v])
            .map(|a| (univariate_coeffs(&a.poly, v), a.op))
            .collect();
        if sub.is_empty() {
            continue;
        }
        let unsat = match univariate::decide(&sub) {
            univariate::UniResult::Unsat => true,
            // No rational (hence no integer) point satisfies the v-only atoms ⇒
            // integer-unsat; over ℝ the var may still take an irrational value.
            univariate::UniResult::SatAlgebraic(_) => sort == VarSort::Integer,
            univariate::UniResult::Sat(_) => false,
        };
        if unsat {
            let subset: Vec<_> = atoms.iter().filter(|a| a.poly.vars() == [v]).map(|a| a.origin).collect();
            return Verdict::Unsat(UnsatReason {
                covering: subset.iter().map(|&o| Cell { falsifies: o }).collect(),
                infeasible_subset: subset,
            });
        }
    }

    // ── Multivariate decision tiers (CDCAC + CAC) ───────────────────────
    // Both run on the **real relaxation**.
    //
    // SOUNDNESS — confirmed vs UNconfirmed UNSAT. A multivariate CDCAC/CAC `Unsat`
    // is NOT independently re-checkable here: unlike the Layer-0 definite-sign /
    // univariate-Sturm sub-cores above (each an exact, re-derivable certificate)
    // and unlike the fdlcg path (which `g_unsat_reverify`s), the CAD covering is
    // trusted on the implementation's word — and the implementation has produced
    // false `unsat`s on multivariate, equality-bearing inputs (e.g.
    // `i=2j+4 ∧ −3i+4j > k+k²`, real-SAT at `j=−100`, that `decide_nvar`
    // mis-refuted). Per the "trust only a CONFIRMED verdict" rule, an
    // unconfirmed multivariate `Unsat` MUST NOT be emitted: we fall through to the
    // model-constructing SAT search instead, which either RECOVERS a real model
    // (the `Unsat` claim was wrong — `dfs` decides the last variable exactly via
    // the Sturm engine, so an equality-pinned witness like the one above is
    // found) or, finding none, yields the sound `Unknown`. A real `Sat` from the
    // CAD IS confirmed (G-SAT-verified `Model`) and is kept for real-sorted
    // problems; for integer problems the real witness need not be integral, so it
    // is discarded (the SAT search below looks for an integral model).
    // CDCAC: 2 variables take the tuned `decide_2var` path; 3+ take `decide_nvar`.
    let cdcac = if vars.len() == 2 {
        Some(crate::cdcac::decide_2var(atoms, vars[0], vars[1], VarSort::Real))
    } else if vars.len() >= 3 {
        Some(crate::cdcac::decide_nvar(atoms, &vars, VarSort::Real))
    } else {
        None
    };
    if let Some(d) = cdcac {
        match d {
            // Unconfirmed multivariate UNSAT — do NOT trust; fall through.
            crate::cdcac::Decision::Unsat => {}
            crate::cdcac::Decision::Sat(m) if sort == VarSort::Real => return Verdict::Sat(m),
            _ => {} // real Sat on an integer problem, or Unknown ⇒ fall through to CAC
        }
    }

    // CAC: the algebraic-breakpoint tier — irrational section points and non-strict
    // conjunctions the full-CAD CDCAC defers. Runs on what CDCAC left `Unknown`.
    if vars.len() >= 2 {
        match crate::cac::decide_cac(atoms, &vars, VarSort::Real) {
            // Unconfirmed multivariate UNSAT — do NOT trust; fall through.
            crate::cdcac::Decision::Unsat => {}
            crate::cdcac::Decision::Sat(m) if sort == VarSort::Real => return Verdict::Sat(m),
            _ => {} // real Sat on an integer problem, or Unknown ⇒ fall through
        }
    }

    // ── SAT search (model construction + backtracking) ───────────────────
    let mut st = Search { budget: SEARCH_BUDGET, budget_hit: false, sort };
    let mut assign: FxHashMap<Var, BigRational> = FxHashMap::default();
    if let Some(model) = st.dfs(0, &vars, &mut assign, atoms) {
        // model already passed G-SAT inside dfs
        return Verdict::Sat(model);
    }

    Verdict::Unknown(if st.budget_hit { Cause::Budget } else { Cause::NoExplanation })
}

/// The dominant sort of the problem. (M1 treats a problem as integer iff any
/// variable-bearing atom is integer-sorted; mixed NIRA is routed real, matching
/// OxiZ's `route_real` guard — refined at M5.)
fn problem_sort(atoms: &[PolyAtom]) -> VarSort {
    if atoms.iter().any(|a| a.sort == VarSort::Real) {
        VarSort::Real
    } else if atoms.iter().any(|a| a.sort == VarSort::Integer) {
        VarSort::Integer
    } else {
        VarSort::Real
    }
}

/// All atoms are constant (no variables): evaluate each exactly.
fn decide_constant_only(atoms: &[PolyAtom]) -> Verdict {
    let empty: FxHashMap<Var, BigRational> = FxHashMap::default();
    for a in atoms {
        if !atom_holds_at(a, &empty) {
            return Verdict::Unsat(UnsatReason {
                covering: vec![Cell { falsifies: a.origin }],
                infeasible_subset: vec![a.origin],
            });
        }
    }
    Verdict::Sat(Model::new())
}

struct Search {
    budget: u64,
    budget_hit: bool,
    sort: VarSort,
}

impl Search {
    /// Depth-first model construction with backtracking. Returns a G-SAT-verified
    /// model, or `None` (search exhausted / budget hit — caller maps to Unknown).
    fn dfs(
        &mut self,
        idx: usize,
        order: &[Var],
        assign: &mut FxHashMap<Var, BigRational>,
        atoms: &[PolyAtom],
    ) -> Option<Model> {
        if idx == order.len() {
            // full assignment → integrality guard (for NIA) + G-SAT
            if self.sort == VarSort::Integer && !assign.values().all(|r| r.is_integer()) {
                return None; // never claim an integer model with a non-integer coord
            }
            let model = model_from(assign, self.sort);
            return model.checks(atoms).then_some(model);
        }
        if self.budget == 0 {
            self.budget_hit = true;
            return None;
        }
        let v = order[idx];

        // ── Last variable: decide it EXACTLY under the rational prefix ────
        // With all earlier variables fixed to rationals, every atom is
        // univariate in `v` — so the exact engine finds a rational/algebraic
        // value or proves this prefix dead (proper MCSAT leaf, not sampling).
        if idx + 1 == order.len() {
            let uni: Vec<(Vec<BigRational>, AtomCmp)> = atoms
                .iter()
                .map(|a| (univariate_coeffs(&substitute(&a.poly, assign), v), a.op))
                .collect();
            match univariate::decide(&uni) {
                univariate::UniResult::Unsat => return None, // dead prefix ⇒ backtrack
                univariate::UniResult::Sat(w) if self.sort == VarSort::Real || w.is_integer() => {
                    let mut m = model_from(assign, self.sort);
                    m.insert(v, Value::Rational(w));
                    if m.checks(atoms) {
                        return Some(m);
                    }
                }
                univariate::UniResult::SatAlgebraic(alpha) if self.sort == VarSort::Real => {
                    let mut m = model_from(assign, self.sort);
                    m.insert(v, Value::Algebraic(alpha));
                    if m.checks(atoms) {
                        return Some(m);
                    }
                }
                // integer sort with a non-integer/algebraic witness: fall through
                // to the integer candidate search below.
                _ => {}
            }
        }

        let feas = feasible_region(v, assign, atoms, self.sort);
        for c in candidates(&feas, self.sort) {
            if self.budget == 0 {
                self.budget_hit = true;
                return None;
            }
            self.budget -= 1;
            if !accepts(v, &c, assign, atoms) {
                continue;
            }
            assign.insert(v, c);
            if let Some(m) = self.dfs(idx + 1, order, assign, atoms) {
                return Some(m);
            }
            assign.remove(&v);
        }
        None
    }
}

/// Build a [`Model`] (all rational coordinates) from a rational assignment.
fn model_from(assign: &FxHashMap<Var, BigRational>, _sort: VarSort) -> Model {
    let mut m = Model::new();
    for (&v, r) in assign {
        m.insert(v, Value::Rational(r.clone()));
    }
    m
}

/// A candidate value `c` is accepted at variable `v` iff *every* atom whose
/// variables are now all assigned (under `assign ∪ {v ↦ c}`) is satisfied
/// exactly. This catches atoms whose feasible region was *skipped* (irrational
/// roots) — they are verified by evaluation instead.
fn accepts(v: Var, c: &BigRational, assign: &FxHashMap<Var, BigRational>, atoms: &[PolyAtom]) -> bool {
    let mut ext = assign.clone();
    ext.insert(v, c.clone());
    for a in atoms {
        if a.poly.vars().iter().all(|x| ext.contains_key(x)) && !atom_holds_at(a, &ext) {
            return false;
        }
    }
    true
}

/// Evaluate a fully-assigned atom exactly and check its comparison.
fn atom_holds_at(a: &PolyAtom, assign: &FxHashMap<Var, BigRational>) -> bool {
    let value = a.poly.eval(assign);
    a.op.holds_for_sign(sign_of(&value))
}

fn sign_of(r: &BigRational) -> i32 {
    if r.is_zero() {
        0
    } else if r.is_negative() {
        -1
    } else {
        1
    }
}

/// Compute the feasible region for `v` as the intersection of the *exactly
/// computable* atom feasible sets (atoms univariate in `v` under `assign` whose
/// real roots are all rational, or which are constant/root-free). Atoms with
/// irrational roots are skipped (the result stays an over-approximation, which
/// is sound for emptiness and is tightened by `accepts` during sampling).
fn feasible_region(
    v: Var,
    assign: &FxHashMap<Var, BigRational>,
    atoms: &[PolyAtom],
    sort: VarSort,
) -> IntervalSet {
    let mut region = IntervalSet::reals();
    for a in atoms {
        // univariate in v iff v ∈ vars and every other var is assigned
        let vs = a.poly.vars();
        if !vs.contains(&v) {
            continue;
        }
        if !vs.iter().all(|x| *x == v || assign.contains_key(x)) {
            continue; // still multivariate — not yet constrained on v
        }
        let q = substitute(&a.poly, assign); // now univariate in v (or constant)
        if let Some(set) = exact_feasible_univariate(&q, v, a.op) {
            region = region.intersect(&set);
            if region.is_empty() {
                break;
            }
        }
        // else: irrational roots → skip (handled by `accepts`)
    }
    if sort == VarSort::Integer {
        region = region.restrict_to_integers();
    }
    region
}

/// Substitute all assigned variables into `poly`, yielding a polynomial in the
/// remaining variables (a constant if all are assigned).
fn substitute(poly: &Polynomial, assign: &FxHashMap<Var, BigRational>) -> Polynomial {
    let mut p = poly.clone();
    for (&var, val) in assign {
        if p.degree(var) > 0 || p.vars().contains(&var) {
            p = p.eval_at(var, val);
        }
    }
    p
}

/// Coefficient vector of a univariate-in-`v` polynomial, **low degree first**
/// (`c[k]` is the coefficient of `vᵏ`), as consumed by [`univariate::decide`].
/// `poly` must mention no variable other than `v` (the single-variable case).
fn univariate_coeffs(poly: &Polynomial, v: Var) -> Vec<BigRational> {
    let deg = poly.degree(v);
    (0..=deg).map(|k| poly.univ_coeff(v, k)).collect()
}

/// Result of the single-variable integer-feasibility search (M5/NIA).
enum IntFeas {
    Sat(Model),
    Unsat,
    Unknown,
}

/// Decide integer feasibility of a single-variable conjunction by exhaustive
/// search over the Cauchy-bounded range `[−⌈B⌉−1, ⌈B⌉+1]`. `B` bounds every real
/// root, so beyond `±B` the sign is constant and the boundary integer represents
/// each unbounded tail — hence the range contains *every* integer solution
/// (Verus: `nia::bounded_search_sound`). `Unsat` is therefore sound integer-
/// unsat; a range too large to enumerate yields `Unknown`.
fn single_var_integer_feasible(atoms: &[PolyAtom], v: Var) -> IntFeas {
    use num_traits::ToPrimitive;
    let mut bound = BigRational::one();
    for a in atoms {
        let cb = univariate::cauchy_bound(&univariate_coeffs(&a.poly, v));
        if cb > bound {
            bound = cb;
        }
    }
    let hi_big: BigInt = bound.ceil().to_integer() + BigInt::from(1);
    let Some(hi) = hi_big.to_i64() else {
        return IntFeas::Unknown;
    };
    if hi > 100_000 {
        return IntFeas::Unknown; // range too large to enumerate
    }
    for n in -hi..=hi {
        let val = BigRational::from_integer(BigInt::from(n));
        let mut point: FxHashMap<Var, BigRational> = FxHashMap::default();
        point.insert(v, val.clone());
        if atoms.iter().all(|a| a.op.holds_for_sign(sign_of(&a.poly.eval(&point)))) {
            let mut m = Model::new();
            m.insert(v, Value::Rational(val));
            return IntFeas::Sat(m);
        }
    }
    IntFeas::Unsat
}

/// The exact feasible [`IntervalSet`] for `q(v) ⋈ 0`, or `None` when an exact
/// rational interval set cannot be soundly built (an irrational real root, or a
/// non-real-rooted polynomial of degree > 2 that §G does not cover).
///
/// `q` is univariate in `v` (or constant in `v`). Returns `Some` in exactly two
/// soundly-decidable shapes:
/// * **constant in `v`**: `reals()` or `empty()` by the constant's sign;
/// * **all real roots rational**, *proved by exact deflation* (the quotient of
///   `q` by `∏(x−rᵢ)` reduces to a constant): the exact set via
///   [`IntervalSet::from_constraint`].
///
/// Crucially this does **not** rely on any library real-root *count*
/// (`SturmSequence::count_roots` is unsound on negative-leading-coeff polys,
/// e.g. it reports `-5x⁴+1` as rootless — the false-unsat the differential
/// caught). Deflation is exact polynomial division, so a `Some` result is sound
/// regardless of substrate counter bugs; everything else conservatively `None`.
fn exact_feasible_univariate(q: &Polynomial, v: Var, op: AtomCmp) -> Option<IntervalSet> {
    let deg = q.degree(v) as usize;
    if deg == 0 {
        // constant in v
        let val = q.eval(&FxHashMap::default());
        let s = sign_of(&val);
        return Some(if op.holds_for_sign(s) {
            IntervalSet::reals()
        } else {
            IntervalSet::empty()
        });
    }

    let roots = rational_roots(q, v); // distinct, sorted, verified (eval == 0)
    // Univariate rational coefficients c[0..=deg].
    let coeffs: Vec<BigRational> = (0..=deg as u32).map(|k| q.univ_coeff(v, k)).collect();
    if !fully_rational_factorable(coeffs, &roots) {
        return None; // a non-rational (irrational/complex) root remains — skip
    }
    // deg > 0 and fully factorable ⇒ roots is non-empty.
    debug_assert!(!roots.is_empty());
    let signs = signs_between(q, v, &roots);
    Some(IntervalSet::from_constraint(&roots, &signs, to_constraint_kind(op)))
}

/// Does `q` (given by its rational coefficient vector, `coeffs[k]` = coeff of
/// `xᵏ`) split completely into rational linear factors over the verified
/// rational `roots`? Proved by repeatedly deflating `q` by `(x − rᵢ)` while the
/// remainder is exactly zero; `q` is fully rational-factorable iff the quotient
/// reduces to a constant. Exact — no floating point, no root counting.
fn fully_rational_factorable(mut coeffs: Vec<BigRational>, roots: &[BigRational]) -> bool {
    for r in roots {
        while coeffs.len() > 1 {
            match deflate_by_root(&coeffs, r) {
                Some(quot) => coeffs = quot,
                None => break, // not (further) divisible by (x - r)
            }
        }
    }
    coeffs.len() == 1
}

/// Synthetic-divide a univariate polynomial (coeffs `c[k]` = coeff of `xᵏ`,
/// highest index = degree) by `(x − r)`. Returns the quotient's coefficient
/// vector if the division is exact (remainder zero), else `None`.
fn deflate_by_root(coeffs: &[BigRational], r: &BigRational) -> Option<Vec<BigRational>> {
    let d = coeffs.len() - 1;
    if d == 0 {
        return None;
    }
    // q_{d-1} = c_d ; q_{k-1} = c_k + r·q_k (k = d-1 … 1) ; R = c_0 + r·q_0
    let mut quot = vec![BigRational::zero(); d];
    quot[d - 1] = coeffs[d].clone();
    let mut k = d - 1;
    while k >= 1 {
        quot[k - 1] = coeffs[k].clone() + r * &quot[k];
        k -= 1;
    }
    let remainder = coeffs[0].clone() + r * &quot[0];
    if remainder.is_zero() { Some(quot) } else { None }
}

fn to_constraint_kind(op: AtomCmp) -> ConstraintKind {
    match op {
        AtomCmp::Lt => ConstraintKind::Lt,
        AtomCmp::Le => ConstraintKind::Le,
        AtomCmp::Gt => ConstraintKind::Gt,
        AtomCmp::Ge => ConstraintKind::Ge,
        AtomCmp::Eq => ConstraintKind::Eq,
        AtomCmp::Ne => ConstraintKind::Ne,
    }
}

/// Sign (`-1/0/1`) of univariate `q` at `v = x` (other vars must be absent).
fn eval_sign_at(q: &Polynomial, v: Var, x: &BigRational) -> i32 {
    let mut m: FxHashMap<Var, BigRational> = FxHashMap::default();
    m.insert(v, x.clone());
    sign_of(&q.eval(&m))
}

/// Signs of `q` in the open regions delimited by the sorted distinct `roots`:
/// `(-∞,r₀), (r₀,r₁), …, (r_{m-1},∞)` — `roots.len()+1` entries.
fn signs_between(q: &Polynomial, v: Var, roots: &[BigRational]) -> Vec<i8> {
    let one = BigRational::one();
    let mut signs = Vec::with_capacity(roots.len() + 1);
    // before first root
    signs.push(eval_sign_at(q, v, &(&roots[0] - &one)) as i8);
    // between consecutive roots
    for w in roots.windows(2) {
        let mid = (&w[0] + &w[1]) / BigRational::from_integer(BigInt::from(2));
        signs.push(eval_sign_at(q, v, &mid) as i8);
    }
    // after last root
    signs.push(eval_sign_at(q, v, &(&roots[roots.len() - 1] + &one)) as i8);
    signs
}

/// All distinct rational roots of univariate `q` (in `v`), sorted. Uses the
/// rational-root theorem on the denominator-cleared integer polynomial, then
/// verifies each candidate exactly. Misses irrational roots by construction —
/// the caller compares the count against Sturm to detect that case.
fn rational_roots(q: &Polynomial, v: Var) -> Vec<BigRational> {
    let deg = q.degree(v) as usize;
    if deg == 0 {
        return Vec::new();
    }
    // univariate rational coefficients c[0..=deg]
    let coeffs: Vec<BigRational> = (0..=deg as u32).map(|k| q.univ_coeff(v, k)).collect();

    // clear denominators → integer coeffs
    let mut lcm = BigInt::one();
    for c in &coeffs {
        lcm = lcm_bigint(&lcm, c.denom());
    }
    let int_coeffs: Vec<BigInt> = coeffs.iter().map(|c| (c.numer() * &lcm) / c.denom()).collect();

    let a0 = &int_coeffs[0]; // constant term
    let an = &int_coeffs[deg]; // leading
    if an.is_zero() {
        return Vec::new();
    }

    // candidates ± p/q with p | a0, q | an. If a0 == 0, x = 0 is a root.
    let mut roots: FxHashSet<BigRational> = FxHashSet::default();
    let mut found_sorted: Vec<BigRational> = Vec::new();
    let p_divs = divisors(a0);
    let q_divs = divisors(an);
    let zero = BigRational::zero();
    if a0.is_zero() {
        roots.insert(zero.clone());
    }
    for p in &p_divs {
        for qd in &q_divs {
            if qd.is_zero() {
                continue;
            }
            for sgn in [BigInt::one(), -BigInt::one()] {
                let cand = BigRational::new(&sgn * p, qd.clone());
                if roots.contains(&cand) {
                    continue;
                }
                if eval_sign_at(q, v, &cand) == 0 {
                    roots.insert(cand);
                }
            }
        }
    }
    found_sorted.extend(roots);
    found_sorted.sort();
    found_sorted.dedup();
    found_sorted
}

/// Positive divisors of `|n|` (and the empty set semantics: if `n == 0`, returns
/// `[1]` so the root-theorem loop still probes `±1/q`).
fn divisors(n: &BigInt) -> Vec<BigInt> {
    let m = n.magnitude();
    if m.bits() == 0 {
        // n == 0
        return vec![BigInt::one()];
    }
    let n_abs = BigInt::from(m.clone());
    let mut out = Vec::new();
    let mut d = BigInt::one();
    // bound the search: only small coefficients arise in M1's corpus; cap at a
    // few thousand to keep it cheap (a missed large divisor only costs
    // completeness, never soundness — Sturm still flags irrationals).
    let cap = BigInt::from(4096);
    while d <= n_abs && d <= cap {
        if (&n_abs % &d).is_zero() {
            out.push(d.clone());
        }
        d += BigInt::one();
    }
    out
}

fn lcm_bigint(a: &BigInt, b: &BigInt) -> BigInt {
    if a.is_zero() || b.is_zero() {
        return BigInt::one();
    }
    let g = gcd_bigint(a, b);
    (a / &g * b).magnitude().clone().into()
}

fn gcd_bigint(a: &BigInt, b: &BigInt) -> BigInt {
    let mut a = BigInt::from(a.magnitude().clone());
    let mut b = BigInt::from(b.magnitude().clone());
    while !b.is_zero() {
        let t = b.clone();
        b = &a % &b;
        a = t;
    }
    a
}

/// A bounded spread of candidate sample points for variable assignment. For an
/// **integer**-sorted variable this returns ONLY integer values (a non-integer
/// that satisfies the atoms over ℝ would be a false integer model — the
/// false-sats the differential caught). Candidates are *hints*: every one is
/// re-verified by [`accepts`] and the final model by G-SAT, so this never has to
/// be exact (and stays robust to the substrate's buggy `IntervalSet::intersect`
/// — `feas` is a preference, not a hard filter).
fn candidates(feas: &IntervalSet, sort: VarSort) -> Vec<BigRational> {
    const CAP: usize = 32;
    let is_int = sort == VarSort::Integer;
    let ok = |r: &BigRational| !is_int || r.is_integer();
    let mut out: Vec<BigRational> = Vec::new();
    let push = |r: BigRational, out: &mut Vec<BigRational>| {
        if ok(&r) && !out.contains(&r) {
            out.push(r);
        }
    };

    // feasible-set hints first (help tight bounded real cells like (1,2) → 3/2).
    if let Some(s) = feas.sample() {
        push(s, &mut out);
    }
    for e in feas.endpoints() {
        // nudge inward by ¼ for reals; ±1 lands on the integer neighbours of a bound.
        let deltas: &[BigRational] = if is_int {
            &[]
        } else {
            &[
                BigRational::new(BigInt::one(), BigInt::from(4)),
                BigRational::new(-BigInt::one(), BigInt::from(4)),
            ]
        };
        for d in deltas {
            push(&e + d, &mut out);
        }
        if is_int {
            push(e.clone(), &mut out);
        }
    }
    // fixed integer spread (covers the documented sat shapes: x=2 for x⁴>4,
    // x=3 for 3x²≥25, x=±1 bilinear pivots, …).
    for k in [0i64, 1, -1, 2, -2, 3, -3, 4, -4, 5, -5, 8, -8, 16, -16, 32, -32] {
        push(BigRational::from_integer(BigInt::from(k)), &mut out);
    }
    if !is_int {
        for (n, d) in [(1i64, 2i64), (-1, 2), (3, 2), (-3, 2)] {
            push(BigRational::new(BigInt::from(n), BigInt::from(d)), &mut out);
        }
    }
    out.truncate(CAP);
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::atom::OriginId;

    fn at(coeffs: &[(i64, &[(u32, u32)])], op: AtomCmp, sort: VarSort) -> PolyAtom {
        PolyAtom::new(Polynomial::from_coeffs_int(coeffs), op, sort, OriginId(0))
    }
    fn re(coeffs: &[(i64, &[(u32, u32)])], op: AtomCmp) -> PolyAtom {
        at(coeffs, op, VarSort::Real)
    }

    // ── documented single-atom SAT shapes (were spurious unsat) ──────────
    #[test]
    fn sat_3x2_lt_5() {
        // 3x² < 5  (x = 0 works; roots irrational)
        assert!(solve(&[re(&[(3, &[(0, 2)]), (-5, &[])], AtomCmp::Lt)]).is_sat());
    }
    #[test]
    fn sat_x4_gt_4() {
        // x⁴ > 4  (x = 2 works; roots ±√2)
        assert!(solve(&[re(&[(1, &[(0, 4)]), (-4, &[])], AtomCmp::Gt)]).is_sat());
    }
    #[test]
    fn sat_3x2_ge_25() {
        // 3x² ≥ 25  (x = 3 works; roots ±√(25/3))
        assert!(solve(&[re(&[(3, &[(0, 2)]), (-25, &[])], AtomCmp::Ge)]).is_sat());
    }
    #[test]
    fn sat_xy_gt_5() {
        // x·y > 5  (x = 3, y = 2)
        assert!(solve(&[re(&[(1, &[(0, 1), (1, 1)]), (-5, &[])], AtomCmp::Gt)]).is_sat());
    }
    #[test]
    fn sat_x2_eq_4_and_y_in_1_2() {
        // x² = 4 ∧ 1 < y < 2  — the over-eager-downgrade regression
        let v = solve(&[
            re(&[(1, &[(0, 2)]), (-4, &[])], AtomCmp::Eq),
            re(&[(1, &[(1, 1)]), (-1, &[])], AtomCmp::Gt),
            re(&[(1, &[(1, 1)]), (-2, &[])], AtomCmp::Lt),
        ]);
        assert!(v.is_sat(), "got {v:?}");
    }

    // ── documented UNSAT shapes ──────────────────────────────────────────
    #[test]
    fn unsat_x2_lt_0() {
        assert!(solve(&[re(&[(1, &[(0, 2)])], AtomCmp::Lt)]).is_unsat());
    }
    #[test]
    fn unsat_perfect_square() {
        // (x-1)² < 0
        assert!(solve(&[re(&[(1, &[(0, 2)]), (-2, &[(0, 1)]), (1, &[])], AtomCmp::Lt)]).is_unsat());
    }
    #[test]
    fn unsat_sos_multivariate() {
        // (x-y)² < 0  — decided by §G-SOS
        assert!(
            solve(&[re(
                &[(1, &[(0, 2)]), (-2, &[(0, 1), (1, 1)]), (1, &[(1, 2)])],
                AtomCmp::Lt
            )])
            .is_unsat()
        );
    }
    #[test]
    fn unsat_single_var_no_real_root() {
        // x² + 1 < 0  (no real roots, always positive)
        assert!(solve(&[re(&[(1, &[(0, 2)]), (1, &[])], AtomCmp::Lt)]).is_unsat());
    }
    #[test]
    fn unsat_single_var_conjunction() {
        // x ≥ 2  ∧  x ≤ 1   (rational bounds, empty)
        let v = solve(&[
            re(&[(1, &[(0, 1)]), (-2, &[])], AtomCmp::Ge),
            re(&[(1, &[(0, 1)]), (-1, &[])], AtomCmp::Le),
        ]);
        assert!(v.is_unsat(), "got {v:?}");
    }

    // ── integer-sort soundness: must not invent a non-integer model ──────
    #[test]
    fn int_x2_eq_3_is_not_sat() {
        // x² = 3 over ℤ: real-sat (±√3) but NO integer model — must be Unknown
        // (sound; the integer perfect-square cert that would say unsat is M5).
        let v = solve(&[at(&[(1, &[(0, 2)]), (-3, &[])], AtomCmp::Eq, VarSort::Integer)]);
        assert!(!v.is_sat(), "must not claim a non-integer model: {v:?}");
    }
    #[test]
    fn int_sat_finds_integer_model() {
        // x² = 4 over ℤ  (x = 2)
        let v = solve(&[at(&[(1, &[(0, 2)]), (-4, &[])], AtomCmp::Eq, VarSort::Integer)]);
        assert!(v.is_sat(), "got {v:?}");
    }

    // ── differential regressions (exact shapes the z3-diff caught) ───────
    #[test]
    fn reg_deflation_quartic_not_false_unsat() {
        // -5x⁴ + 1 = 0 is SAT over ℝ (x = ±(1/5)^¼); the buggy substrate Sturm
        // count reported it rootless → was a false unsat. Must NOT be unsat.
        let v = solve(&[re(&[(-5, &[(0, 4)]), (1, &[])], AtomCmp::Eq)]);
        assert!(!v.is_unsat(), "deflation regression: got {v:?}");
    }
    #[test]
    fn reg_intersect_boundary_not_false_unsat() {
        // 5x² = 0 ∧ 2x² ≥ 0 is SAT (x = 0); IntervalSet::intersect dropped {0}
        // against (-∞,0)∪[0,∞) → was a false unsat. Must be sat (x = 0).
        let v = solve(&[
            re(&[(5, &[(0, 2)])], AtomCmp::Eq),
            re(&[(2, &[(0, 2)])], AtomCmp::Ge),
        ]);
        assert!(v.is_sat(), "intersect-boundary regression: got {v:?}");
    }
    #[test]
    fn reg_neg_quartic_ge_and_sq_ge_is_sat() {
        // -x⁴ ≥ 0 ∧ 2x² ≥ 0  is SAT (x = 0). (false-unsat regression)
        let v = solve(&[
            re(&[(-1, &[(0, 4)])], AtomCmp::Ge),
            re(&[(2, &[(0, 2)])], AtomCmp::Ge),
        ]);
        assert!(v.is_sat(), "got {v:?}");
    }
    #[test]
    fn x2_eq_3_real_sat_via_algebraic_model() {
        // x² = 3 over ℝ: sat at ±√3 (irrational) — now decided Sat with an exact
        // algebraic model (G-SAT verified), not Unknown.
        let v = solve(&[re(&[(1, &[(0, 2)]), (-3, &[])], AtomCmp::Eq)]);
        assert!(v.is_sat(), "got {v:?}");
    }
    #[test]
    fn m5_linear_no_integer_unsat() {
        // 2x = 1 over ℤ: real-sat (x=1/2) but no integer ⇒ integer-unsat (M5).
        let v = solve(&[at(&[(2, &[(0, 1)]), (-1, &[])], AtomCmp::Eq, VarSort::Integer)]);
        assert!(v.is_unsat(), "got {v:?}");
    }
    #[test]
    fn m5_nonlinear_integer_sat() {
        // x² ≥ 5 ∧ x ≤ 3 ∧ x ≥ 0 over ℤ: real witness may be non-integer, but
        // x=3 is an integer model — the bounded search finds it (M5).
        let v = solve(&[
            at(&[(1, &[(0, 2)]), (-5, &[])], AtomCmp::Ge, VarSort::Integer),
            at(&[(1, &[(0, 1)]), (-3, &[])], AtomCmp::Le, VarSort::Integer),
            at(&[(1, &[(0, 1)])], AtomCmp::Ge, VarSort::Integer),
        ]);
        assert!(v.is_sat(), "got {v:?}");
    }

    #[test]
    fn x2_eq_3_int_unsat() {
        // x² = 3 over ℤ: no integer square root ⇒ unsat (algebraic ⇒ no integer).
        let v = solve(&[at(&[(1, &[(0, 2)]), (-3, &[])], AtomCmp::Eq, VarSort::Integer)]);
        assert!(v.is_unsat(), "got {v:?}");
    }
    #[test]
    fn irrational_inequality_real_sat() {
        // x² < 2 ∧ x > 1 : sat on (1, √2) — interior has rationals, so this is a
        // rational Sat; but x² = 2 ∧ x > 0 forces x = √2 (algebraic).
        let v = solve(&[
            re(&[(1, &[(0, 2)]), (-2, &[])], AtomCmp::Eq),
            re(&[(1, &[(0, 1)])], AtomCmp::Gt),
        ]);
        assert!(v.is_sat(), "got {v:?}");
    }

    #[test]
    fn multivar_last_var_algebraic_sat() {
        // x - 2 = 0 ∧ y² - x - 1 = 0  → x=2 (rational, found by sampling),
        // then y² = 3 ⇒ y = √3 decided exactly as the last variable (algebraic).
        let v = solve(&[
            re(&[(1, &[(0, 1)]), (-2, &[])], AtomCmp::Eq),
            re(&[(1, &[(1, 2)]), (-1, &[(0, 1)]), (-1, &[])], AtomCmp::Eq),
        ]);
        assert!(v.is_sat(), "got {v:?}");
    }

    #[test]
    fn multivar_constant_false_atom_unsat() {
        // (5 = 0) ∧ (x·y > 0)  → unsat via the constant-false atom
        let v = solve(&[
            re(&[(5, &[])], AtomCmp::Eq),
            re(&[(1, &[(0, 1), (1, 1)])], AtomCmp::Gt),
        ]);
        assert!(v.is_unsat(), "got {v:?}");
    }

    #[test]
    fn multivar_even_monomial_definite_unsat() {
        // (3x⁴ < 0) ∧ (x·y = 1)  → unsat: 3x⁴<0 is definite-unsat (degree 4)
        let v = solve(&[
            re(&[(3, &[(0, 4)])], AtomCmp::Lt),
            re(&[(1, &[(0, 1), (1, 1)]), (-1, &[])], AtomCmp::Eq),
        ]);
        assert!(v.is_unsat(), "got {v:?}");
    }

    #[test]
    fn multivar_univariate_subcore_unsat() {
        // (-5x⁴ ≥ 0) ∧ (2x⁴ ≠ 0) ∧ (8x⁴ - x²y < 0)  over ℤ.
        // The x-only sub-core {-5x⁴≥0, 2x⁴≠0} is unsat (≥0 forces x=0, ≠0 forbids it).
        let v = solve(&[
            at(&[(-5, &[(0, 4)])], AtomCmp::Ge, VarSort::Integer),
            at(&[(2, &[(0, 4)])], AtomCmp::Ne, VarSort::Integer),
            at(&[(8, &[(0, 4)]), (-1, &[(0, 2), (1, 1)])], AtomCmp::Lt, VarSort::Integer),
        ]);
        assert!(v.is_unsat(), "got {v:?}");
    }

    #[test]
    fn reg_integer_no_nonint_model_strict() {
        // 5x³+5x < 0 ∧ 2x⁴-2x² < 0 ∧ -5x ≠ 0 over ℤ: real-sat (x∈(-1,0)) but
        // NO integer model → must NOT be claimed sat (was a false integer sat).
        let v = solve(&[
            at(&[(5, &[(0, 3)]), (5, &[(0, 1)])], AtomCmp::Lt, VarSort::Integer),
            at(&[(2, &[(0, 4)]), (-2, &[(0, 2)])], AtomCmp::Lt, VarSort::Integer),
            at(&[(-5, &[(0, 1)])], AtomCmp::Ne, VarSort::Integer),
        ]);
        assert!(!v.is_sat(), "integer non-integer-model regression: got {v:?}");
    }
}
