//! Algebraic reduction knowledge base (KB).
//!
//! This module implements a *leveled* "reduction knowledge base" that recognizes
//! polynomial-equality systems whose only satisfying assignment is **irrational**
//! (and therefore cannot be represented by the solver's rational-only
//! `arith_values`). The canonical example is the circle/line system
//!
//! ```text
//!   x^2 + y^2 - 25 = 0      (circle of radius 5)
//!   y - x = 0               (line y = x)
//! ```
//!
//! whose real solutions are `x = y = ±sqrt(12.5)`, irrational. The base NLSAT
//! search picks a rational value for the first "free" variable, after which the
//! second variable's feasible region becomes empty, and the solver spuriously
//! reports `Unsat`.
//!
//! ## Strategy (mirrors the leveled-KB pattern in `oxiz-solver/src/calculus.rs`)
//!
//! - **Level 0 (primitive reductions).** Use asserted equality atoms (`p = 0`)
//!   to eliminate variables. A linear-in-some-variable equality (e.g. `y - x = 0
//!   ⇒ y = x`) is *exactly* substituted into the other equalities, repeating to
//!   triangularize the system toward a single **univariate** polynomial `q(x)`.
//!   When no equality is linear in a shared variable, fall to a resultant-based
//!   elimination (Level 1).
//! - **Level 1+ (derived/composite forms).** Recognized conic ∩ line / conic ∩
//!   conic patterns built *on top of* the Level-0 primitives (the linear
//!   substitution above, or `Polynomial::resultant` for two genuine conics).
//!   Every derived rule is re-verified from the level below by the final
//!   back-substitution check.
//! - **Confirmation.** Once reduced to a univariate `q(x)`, the crate's Sturm
//!   machinery (`crate::cad::SturmSequence`) isolates a real root; if one exists,
//!   we build an exact [`AlgebraicNumber`] for it (its constructor re-validates
//!   single-root isolation via Sturm — a built-in soundness gate).
//! - **Verification.** Before concluding SAT, the candidate algebraic assignment
//!   is verified to satisfy **every** original equality atom *exactly* (symbolic
//!   divisibility `q | p_reduced`, never a numeric midpoint eval).
//!
//! ## Soundness
//!
//! This KB is a purely **additive recognizer**: it can only turn a spurious
//! `Unsat` into a *verified* `Sat`. Its failure path is side-effect-free — when
//! anything is uncertain (system not all-equalities, not reducible by exact
//! substitution, no real root, or the verification fails), it returns `None` and
//! the existing CDCL+CAD search runs verbatim, unchanged. It NEVER concludes
//! `Unsat` (an inexact resultant could otherwise fabricate one) and NEVER writes
//! to the assignment unless the exact verification has passed.

use crate::assignment::Assignment;
use crate::cad::SturmSequence;
use crate::types::{Atom, AtomKind};
use num_rational::BigRational;
use num_traits::Zero;
use oxiz_math::algebraic::AlgebraicNumber;
use oxiz_math::polynomial::root_counting::Polynomial as UniPolynomial;
use oxiz_math::polynomial::{Polynomial, Var};

/// A solved algebraic system, ready to be written into the assignment.
///
/// Holds the exact algebraic value for every arithmetic variable that appears
/// in the recognized equality system. Construction of this struct already
/// implies the full back-substitution verification succeeded.
#[derive(Debug, Clone)]
pub struct AlgebraicSolution {
    /// Exact algebraic value for each solved variable.
    pub values: Vec<(Var, AlgebraicNumber)>,
}

/// An asserted equality `p = 0`, the Level-0 KB input.
#[derive(Debug, Clone)]
struct EqConstraint {
    poly: Polynomial,
}

/// Try to recognize and solve an all-equality polynomial system algebraically.
///
/// `equalities` are the polynomials `p` of asserted (`bool_value == true`),
/// single-factor equality atoms, with the semantics `p = 0`.
///
/// Returns `Some(solution)` only when:
///   1. the system reduces (by exact substitution and/or resultant elimination)
///      to a single univariate polynomial `q` of degree ≥ 1,
///   2. `q` has a real root (confirmed by Sturm), an exact [`AlgebraicNumber`] is
///      built for it, and
///   3. the resulting assignment satisfies **every** original equality exactly.
///
/// Otherwise returns `None` (fall back to the existing solver). This function is
/// pure: it has no observable side effects.
pub fn try_solve_equalities(equalities: &[Polynomial]) -> Option<AlgebraicSolution> {
    if equalities.is_empty() {
        return None;
    }

    // Collect the active constraints, dropping trivial (constant) ones. A
    // non-zero constant equality means the system is inconsistent — but we do
    // NOT conclude Unsat from the KB (soundness asymmetry), we just fall back.
    let mut constraints: Vec<EqConstraint> = Vec::new();
    for p in equalities {
        if p.is_constant() {
            if !p.constant_value().is_zero() {
                // 0 = c with c != 0 — genuinely unsat, but leave the verdict to
                // the existing path. The KB never reports Unsat.
                return None;
            }
            // 0 = 0 is trivially true; ignore it.
            continue;
        }
        constraints.push(EqConstraint { poly: p.clone() });
    }

    if constraints.is_empty() {
        return None;
    }

    // The set of variables that the system constrains.
    let mut all_vars: Vec<Var> = Vec::new();
    for c in &constraints {
        for v in c.poly.vars() {
            if !all_vars.contains(&v) {
                all_vars.push(v);
            }
        }
    }
    all_vars.sort_unstable();

    // ---- Level 0: linear-equality elimination + triangularization. ----
    //
    // `subs` records the elimination chain `var := replacement(remaining vars)`,
    // in the order performed. `active` holds the equalities not yet consumed as
    // an elimination pivot (with prior substitutions already applied).
    let mut active: Vec<Polynomial> = constraints.iter().map(|c| c.poly.clone()).collect();
    let mut subs: Vec<(Var, Polynomial)> = Vec::new();

    // ---- Radical-axis augmentation (conic ∩ conic, catalog §A1/§A3). ----
    //
    // Two conics that share their quadratic part (e.g. two circles/ellipses
    // `x²+y²=25` and `x²+(y-1)²=25`) have a *linear* difference — the radical axis
    // `2y - 1 = 0`. A linear combination of equalities is itself an equality that
    // holds on the common solution set, so adding it is sound and exact. We add any
    // pairwise scalar-balanced difference that is strictly lower total degree than
    // both parents; the Level-0 loop below can then pivot on the new linear
    // equation, turning a genuine conic∩conic into the already-handled conic∩line
    // shape. The final verification still checks every ORIGINAL equality exactly,
    // so an augmented equation can never fabricate a model. (This makes the §A1
    // resultant path's common case reachable through the exact Level-0 machinery.)
    augment_with_linear_combinations(&mut active);

    // Repeatedly find an equality that is linear in some variable still present
    // in other equalities, isolate that variable, and substitute it away.
    loop {
        let mut progressed = false;

        'find_pivot: for i in 0..active.len() {
            // Skip equalities that have collapsed to constants.
            if active[i].is_constant() {
                continue;
            }
            let vars_i = active[i].vars();
            for &v in &vars_i {
                if active[i].degree(v) != 1 {
                    continue;
                }
                // Only eliminate a variable that *couples* this equation to at
                // least one OTHER active equation. Eliminating a variable that
                // appears nowhere else would simply consume the equation without
                // reducing coupling, and could leave the system with no
                // univariate eliminant to confirm (e.g. a pure `2x - 6 = 0`).
                let appears_elsewhere = active
                    .iter()
                    .enumerate()
                    .any(|(j, eq)| j != i && eq.vars().contains(&v));
                if !appears_elsewhere {
                    continue;
                }
                // Isolate `v = f(other vars)` from this (degree-1-in-v) equality.
                let Some(replacement) = isolate_linear_var(&active[i], v) else {
                    continue;
                };
                // The replacement must not itself depend on `v` (it can't, since
                // we removed the v-term) — guaranteed by `isolate_linear_var`.

                // Substitute `v := replacement` into all OTHER active equalities.
                for (j, eq) in active.iter_mut().enumerate() {
                    if j == i {
                        continue;
                    }
                    if eq.vars().contains(&v) {
                        *eq = eq.substitute(v, &replacement);
                    }
                }
                // Record the elimination and drop the pivot equation.
                subs.push((v, replacement));
                active.remove(i);
                progressed = true;
                break 'find_pivot;
            }
        }

        if !progressed {
            break;
        }
    }

    // Gate: when no variable was eliminated by substitution, the system did not
    // couple two equations — it is a *single-equation* problem (e.g. `x^2 - 2 = 0`,
    // `x^3 - x = 0`, `x - 1 = 0`). Most such cases the base CDCL+CAD search already
    // solves (and, for NIA, applies the integer-domain constraint the KB is unaware
    // of), so we fall back. The ONE exception is **Rule D**: a single univariate
    // power equality `x^k = a` whose unique satisfying value is *irrational* — the
    // base rational search picks rationals and spuriously reports Unsat. Rule D
    // recognizes exactly that shape and returns the exact algebraic root, reusing
    // the same Sturm + AlgebraicNumber + exact-verify machinery as the coupled
    // path. It DECLINES rational-root and even-`k`/`a<0` (no real root) cases,
    // keeping the KB SAT-only-additive and NIA-typing-safe (see `try_rule_d`).
    if subs.is_empty() {
        return try_rule_d(&constraints);
    }

    // Drop any equalities that became `0 = 0`. A non-zero constant means unsat —
    // again, fall back rather than report Unsat.
    let mut remaining: Vec<Polynomial> = Vec::new();
    for eq in active {
        if eq.is_constant() {
            if !eq.constant_value().is_zero() {
                return None;
            }
            continue;
        }
        remaining.push(eq);
    }

    // Find the eliminant: a single univariate polynomial of degree ≥ 1. If
    // Level-0 substitution did not already leave one, fall to the Level-1
    // resultant elimination for a 2-equation conic system.
    let (q, root_var) = match find_univariate_eliminant(&remaining) {
        Some(qr) => qr,
        None => try_resultant_eliminant(&remaining)?,
    };

    // ---- Confirmation: isolate a real root of q via Sturm. ----
    let sturm = SturmSequence::new(&q, root_var);
    let roots = sturm.isolate_roots();
    let (lower, upper) = roots.into_iter().next()?; // no real root ⇒ fall back

    // Build the exact algebraic number for the root variable. Its constructor
    // re-validates (via its own Sturm sequence on the univariate type) that the
    // interval isolates exactly one root — a built-in soundness gate. Any error
    // means we cannot certify ⇒ fall back.
    let uni_q = to_univariate(&q, root_var)?;
    let root = AlgebraicNumber::new(uni_q, lower, upper).ok()?;

    // Gate: the KB is the *irrational-solution* recognizer. If the isolated root
    // is rational, the base CDCL+CAD search already represents and finds it
    // exactly (and a rational `arith_value` would otherwise need to be written,
    // duplicating that path). Fall back so the KB only ever supplies the value
    // type the base path *cannot* (an irrational algebraic number). This keeps
    // the change strictly additive and avoids the midpoint-vs-exact mismatch a
    // rational root would introduce in the rational `arith_values` map.
    if root.is_rational() {
        return None;
    }

    // ---- Back-substitution: assign every system variable. ----
    //
    // The root variable takes `root`. Each eliminated `v := f` must reduce, under
    // the full substitution chain, to an expression in `root_var` only; we only
    // support the case where that reduced expression is itself univariate in
    // `root_var` so the value is exactly representable. For the canonical
    // circle/line system this is `y = x` (the identity in `root_var`).
    let assignment = build_assignment(&q, root_var, &root, &subs, &all_vars)?;

    // ---- Verification: every original equality must hold exactly. ----
    //
    // For an equality `p = 0`, we reduce `p` through the recorded substitution
    // chain to a polynomial `p_reduced` in `root_var` only, then confirm
    // `q | p_reduced` (pseudo-remainder is zero). Because `root_var = root` is a
    // root of `q`, divisibility guarantees `p_reduced(root) = 0` exactly. This is
    // a symbolic check — never a numeric/interval approximation.
    for c in &constraints {
        let reduced = apply_subs(&c.poly, &subs);

        // The substituted polynomial reduced to identically zero ⇒ this equality
        // holds for *every* value of the root variable (e.g. the eliminated
        // `y - x = 0` becomes `0` after `y := x`). Trivially satisfied.
        if reduced.is_zero() {
            continue;
        }
        // A non-zero *constant* residue means `c = 0` for some non-zero `c` ⇒ the
        // equality is unsatisfiable under the substitution ⇒ fall back (the KB
        // never reports Unsat).
        if reduced.is_constant() {
            return None;
        }
        // Otherwise the residue must be univariate in the root variable; any
        // other variable means the elimination was incomplete ⇒ fall back.
        let rvars = reduced.vars();
        if rvars.len() != 1 || rvars[0] != root_var {
            return None;
        }
        // q | reduced ?  (exact, via pseudo-remainder over Q). Because the root
        // variable equals a root of `q`, divisibility guarantees `reduced` is
        // exactly zero at the model point.
        let rem = reduced.pseudo_remainder(&q, root_var);
        if !rem.is_zero() {
            return None;
        }
    }

    Some(AlgebraicSolution {
        values: assignment,
    })
}

/// Augment the active equality set with sound linear combinations (catalog §A1/§A3).
///
/// For each pair of multivariate active equalities `p = 0`, `r = 0` that share an
/// identical degree-2 part, the difference `p − r` cancels that quadratic part and
/// is therefore strictly lower total degree (the *radical axis* of two conics).
/// More generally we look for a rational scalar `λ` with `deg(p − λ·r) < deg(p)`
/// by matching the (lexicographically) highest-degree term, which kills the
/// leading monomial; for two conics sharing the full quadratic part this collapses
/// `p − r` to a line. A linear combination of equalities holds on the common
/// solution set, so adding it is SOUND and EXACT — and because the final per-atom
/// verification re-checks every ORIGINAL equality, an augmented equation can never
/// fabricate a model. We only ADD strictly-lower-degree, not-already-present
/// combinations (so the routine is a single bounded pass and cannot loop).
fn augment_with_linear_combinations(active: &mut Vec<Polynomial>) {
    let n = active.len();
    let mut additions: Vec<Polynomial> = Vec::new();

    for i in 0..n {
        if active[i].is_constant() {
            continue;
        }
        let deg_i = active[i].total_degree();
        if deg_i < 2 {
            continue; // already linear/constant — nothing to reduce
        }
        for j in (i + 1)..n {
            if active[j].is_constant() {
                continue;
            }
            if let Some(combo) = degree_reducing_combination(&active[i], &active[j]) {
                // Only keep a strictly-lower-degree, non-trivial, novel equation.
                if combo.is_constant() {
                    continue;
                }
                let cd = combo.total_degree();
                if cd >= deg_i && cd >= active[j].total_degree() {
                    continue;
                }
                if active.iter().chain(additions.iter()).any(|e| *e == combo) {
                    continue;
                }
                additions.push(combo);
            }
        }
    }

    active.extend(additions);
}

/// Find a rational `λ` so that `p − λ·r` drops the highest-degree monomial of `p`,
/// returning the reduced combination. Returns `None` if no single scalar cancels
/// the leading term (the two conics' quadratic parts are not proportional, so the
/// difference stays degree 2 — handled by the resultant path instead).
fn degree_reducing_combination(p: &Polynomial, r: &Polynomial) -> Option<Polynomial> {
    use num_traits::Zero;

    // Highest total-degree monomial of p (any one of them); cancel it with r.
    let lead = p
        .terms()
        .iter()
        .filter(|t| !t.coeff.is_zero())
        .max_by_key(|t| t.monomial.total_degree())?;
    let lead_deg = lead.monomial.total_degree();
    if lead_deg < 2 {
        return None;
    }
    // Coefficient of the SAME monomial in r.
    let r_coeff = r
        .terms()
        .iter()
        .find(|t| t.monomial == lead.monomial)
        .map(|t| t.coeff.clone())
        .unwrap_or_else(BigRational::zero);
    if r_coeff.is_zero() {
        return None; // r has no matching leading monomial ⇒ no single-λ cancel
    }
    let lambda = &lead.coeff / &r_coeff;
    // combo = p − λ·r
    let scaled_r = r.scale(&lambda);
    Some(Polynomial::sub(p, &scaled_r))
}

/// Rule D — single univariate power equality `x^k = a` (catalog §D).
///
/// Fires only on a *single* asserted equality `p = 0` that is univariate in one
/// variable `x` of degree `k ≥ 1`. The pure `NlsatSolver` is all-real NRA, so we
/// escalate straight to the **real** domain step of the rule's domain ladder:
///
///   * `k` odd ⇒ one real root `sign(a)·|a|^{1/k}` (always exists);
///   * `k` even & `a > 0` ⇒ `±a^{1/k}` (two real roots);
///   * `a = 0` ⇒ root `0`;
///   * `k` even & `a < 0` ⇒ **no real root** ⇒ return `None` (fall back so the
///     complete CAD path concludes the sound real-UNSAT). The KB NEVER reports a
///     complex root and NEVER reports Unsat.
///
/// SOUNDNESS / NIA SAFETY: like the coupled path, Rule D is SAT-only-additive. It
/// returns a value only after Sturm confirms a real root and the exact
/// [`AlgebraicNumber`] is verified (via `pseudo_remainder`) against the original
/// equality. Crucially it **declines a rational root** (e.g. `x^2 - 4 = 0`,
/// `x - 1 = 0`, `x^3 - x = 0`): the base CDCL+CAD search already finds those
/// exactly, and — for the NIA layer — must remain in charge of the integer-domain
/// constraint (`is_integer_var` branch-and-bound runs on top of the real
/// relaxation). By only ever supplying the *irrational* value the base path
/// cannot represent, Rule D cannot perturb any NIA verdict.
///
/// The recognizer accepts any univariate polynomial (not only the bare `x^k - a`
/// monomial-minus-constant shape): the irrational-root + exact-verify gates make
/// it sound for every univariate `p = 0`, and restricting the *form* would only
/// reduce completeness. The catalog frames it as `x^k = a` because that is the
/// motivating family (`x^2 - 2`).
fn try_rule_d(constraints: &[EqConstraint]) -> Option<AlgebraicSolution> {
    // Exactly one asserted equality.
    if constraints.len() != 1 {
        return None;
    }
    let q = &constraints[0].poly;

    // Must be univariate of degree ≥ 1 (a single power equality in one variable).
    let vars = q.vars();
    if vars.len() != 1 {
        return None;
    }
    let root_var = vars[0];
    if q.degree(root_var) < 1 {
        return None;
    }

    // NIA-safety / additivity gate (PRIMARY): decline the equation if `q` has ANY
    // rational root. The rational-root theorem decides this exactly. When `q` has
    // a rational root the base CDCL+CAD search already finds a rational model (and,
    // for NIA, owns the integer-domain decision), so Rule D must defer entirely —
    // e.g. `x^2 - 4 = 0` (±2), `x - 1 = 0` (1), `x^3 - x = 0` ({-1,0,1}). When `q`
    // has NO rational root but a real root (next), that real root is *provably
    // irrational*, which is exactly the value the base rational search cannot
    // reach. This gate is stronger than `AlgebraicNumber::is_rational()`, which is
    // a structural check that misses rational roots of a *reducible* polynomial
    // (the isolated interval of, say, root -1 of x^3-x does not collapse and the
    // reducible degree-3 minimal_poly is not degree 1).
    if has_rational_root(q, root_var) {
        return None;
    }

    // ---- Confirmation: isolate a real root via Sturm. ----
    // k even & a<0 (no real root) yields an empty isolation ⇒ `?` falls back, and
    // the complete CAD path then concludes the sound real-UNSAT. Never Unsat here.
    let sturm = SturmSequence::new(q, root_var);
    let roots = sturm.isolate_roots();
    let (lower, upper) = roots.into_iter().next()?;

    // Build the exact algebraic number for the root. Its constructor re-validates
    // single-root isolation via its own Sturm sequence (a built-in soundness gate).
    let uni_q = to_univariate(q, root_var)?;
    let root = AlgebraicNumber::new(uni_q, lower, upper).ok()?;

    // Defensive secondary gate: even after the rational-root rejection above, never
    // emit a value the AlgebraicNumber type itself reports as rational.
    if root.is_rational() {
        return None;
    }

    // ---- Verification: the original equality must hold exactly at the root. ----
    // `q(root) = 0` because `root` is a root of `q` (which IS `q` here); the
    // pseudo-remainder check is `q | q`, trivially zero. We still run it through
    // the same exact gate for uniformity and as a defensive re-check.
    let rem = q.pseudo_remainder(q, root_var);
    if !rem.is_zero() {
        return None;
    }

    Some(AlgebraicSolution {
        values: vec![(root_var, root)],
    })
}

/// Does the univariate polynomial `q` (in `var`) have any rational root?
///
/// Decides it exactly via the rational-root theorem: clear denominators to integer
/// coefficients `a_n x^n + … + a_0`, then every rational root `p/s` (lowest terms)
/// has `p | a_0` and `s | a_n`. We enumerate `±(divisor of a0)/(divisor of an)` and
/// test each by exact evaluation. Used by Rule D to keep the KB SAT-only-additive
/// and NIA-typing-safe: a polynomial *with* a rational root is left to the base
/// path (which finds rationals exactly); only a polynomial with NO rational root
/// but a real root yields the irrational value Rule D supplies.
fn has_rational_root(q: &Polynomial, var: Var) -> bool {
    use num_bigint::BigInt;
    use num_traits::{One, Signed};

    let deg = q.degree(var) as usize;
    if deg == 0 {
        return false;
    }

    // Rational coefficients coeff[k] = coeff of var^k.
    let rat_coeffs: Vec<BigRational> = (0..=deg).map(|k| q.univ_coeff(var, k as u32)).collect();

    // Scale by LCM of denominators → integer coefficients.
    let lcm_denom: BigInt = rat_coeffs.iter().fold(BigInt::one(), |acc, r| {
        let d = r.denom().abs();
        let g = gcd_bigint(acc.clone(), d.clone());
        if g.is_zero() { acc } else { acc / g * d }
    });
    let int_coeffs: Vec<BigInt> = rat_coeffs
        .iter()
        .map(|r| r.numer() * (&lcm_denom / r.denom()))
        .collect();

    rational_root_exists(&int_coeffs)
}

/// Recursive rational-root-theorem test over integer coefficients (low→high).
fn rational_root_exists(int_coeffs: &[num_bigint::BigInt]) -> bool {
    use num_bigint::BigInt;
    use num_traits::{Signed, Zero};

    let n = int_coeffs.len();
    if n < 2 {
        return false;
    }
    let a0 = &int_coeffs[0];
    // x = 0 is a root iff the constant term is zero.
    if a0.is_zero() {
        return true;
    }
    let an = &int_coeffs[n - 1];
    if an.is_zero() {
        // Leading coefficient vanished (shouldn't happen for a normalized poly);
        // retry on the lower-degree slice to stay sound.
        return rational_root_exists(&int_coeffs[..n - 1]);
    }

    let divisors_a0 = pos_divisors(a0.abs());
    let divisors_an = pos_divisors(an.abs());

    let eval = |cand: &BigRational| -> bool {
        // Horner over the rational candidate.
        let mut acc = BigRational::from_integer(BigInt::zero());
        for c in int_coeffs.iter().rev() {
            acc = acc * cand + BigRational::from_integer(c.clone());
        }
        acc.is_zero()
    };

    for p in &divisors_a0 {
        for s in &divisors_an {
            if s.is_zero() {
                continue;
            }
            for &sign in &[1i64, -1i64] {
                let cand = BigRational::new(p * BigInt::from(sign), s.clone());
                if eval(&cand) {
                    return true;
                }
            }
        }
    }
    false
}

/// Euclidean GCD for BigInts (non-negative result).
fn gcd_bigint(mut a: num_bigint::BigInt, mut b: num_bigint::BigInt) -> num_bigint::BigInt {
    use num_traits::Signed;
    a = a.abs();
    b = b.abs();
    while !b.is_zero() {
        let t = &a % &b;
        a = b;
        b = t;
    }
    a
}

/// All positive divisors of a positive BigInt (1 for zero, by convention).
fn pos_divisors(n: num_bigint::BigInt) -> Vec<num_bigint::BigInt> {
    use num_bigint::BigInt;
    use num_traits::{One, Zero};

    if n.is_zero() {
        return vec![BigInt::one()];
    }
    let mut divs = Vec::new();
    let mut i = BigInt::one();
    loop {
        if &i * &i > n {
            break;
        }
        if (&n % &i).is_zero() {
            divs.push(i.clone());
            let q = &n / &i;
            if q != i {
                divs.push(q);
            }
        }
        i += BigInt::one();
    }
    divs
}

/// Isolate a degree-1 variable `v` from `p = 0`, returning `f` with `v = f`.
///
/// `p` must be exactly degree 1 in `v`. Returns `None` if `v`'s coefficient is
/// not a non-zero constant (e.g. `x*y` makes `v=x`'s coefficient `y`, which is
/// not a constant — substituting then would not be an equivalence we can later
/// represent), keeping the substitution exact and one variable lighter.
fn isolate_linear_var(p: &Polynomial, v: Var) -> Option<Polynomial> {
    // Coefficient of v^1 must be a non-zero rational constant.
    let lead = p.coeff(v, 1);
    if !lead.is_constant() {
        return None;
    }
    let a = lead.constant_value();
    if a.is_zero() {
        return None;
    }
    // p must have no higher powers of v.
    if p.degree(v) != 1 {
        return None;
    }
    // rest = p - a*v  (the v^0 coefficient polynomial in the other variables).
    let rest = p.coeff(v, 0);
    // v = -rest / a
    let inv_neg = -BigRational::from_integer(num_bigint::BigInt::from(1)) / a;
    Some(rest.scale(&inv_neg))
}

/// Among the remaining equalities, find one that is univariate of degree ≥ 1.
fn find_univariate_eliminant(remaining: &[Polynomial]) -> Option<(Polynomial, Var)> {
    for eq in remaining {
        if eq.is_constant() {
            continue;
        }
        let vars = eq.vars();
        if vars.len() == 1 {
            let v = vars[0];
            if eq.degree(v) >= 1 {
                return Some((eq.clone(), v));
            }
        }
    }
    None
}

/// Level-1 resultant elimination for a (conic ∩ conic) two-equation system.
///
/// Picks a shared variable, eliminates it via `Polynomial::resultant`, and
/// returns the eliminant if it is univariate of degree ≥ 1. The eliminant from
/// the in-crate resultant is documented as approximate; soundness is preserved
/// because the final per-atom back-substitution verification gates every SAT —
/// an inexact resultant can only fail to find a model, never fabricate one.
fn try_resultant_eliminant(remaining: &[Polynomial]) -> Option<(Polynomial, Var)> {
    if remaining.len() != 2 {
        return None;
    }
    let p = &remaining[0];
    let r = &remaining[1];

    // Find a variable shared by both, to eliminate.
    let pv = p.vars();
    let rv = r.vars();
    let shared: Vec<Var> = pv.iter().copied().filter(|v| rv.contains(v)).collect();
    if shared.is_empty() {
        return None;
    }

    // Eliminate one shared var; the eliminant should be univariate in the other.
    for &elim in &shared {
        let res = p.resultant(r, elim);
        if res.is_zero() || res.is_constant() {
            continue;
        }
        let vars = res.vars();
        if vars.len() == 1 && res.degree(vars[0]) >= 1 {
            return Some((res, vars[0]));
        }
    }
    None
}

/// Build the exact assignment for every system variable.
///
/// `root_var` takes `root`. Each elimination `v := f` (newest last) is resolved
/// back to a value in `root_var` only. We only accept the case where the chained
/// substitution leaves a polynomial univariate in `root_var` whose value we can
/// realise exactly:
///   - a rational constant (representable as a rational AlgebraicNumber), or
///   - exactly `root_var` itself (reuse `root`).
///
/// Anything more complex (a non-trivial polynomial of `root_var`) is conservative
/// territory we do not yet model exactly ⇒ return `None` (fall back).
fn build_assignment(
    _q: &Polynomial,
    root_var: Var,
    root: &AlgebraicNumber,
    subs: &[(Var, Polynomial)],
    all_vars: &[Var],
) -> Option<Vec<(Var, AlgebraicNumber)>> {
    let mut out: Vec<(Var, AlgebraicNumber)> = Vec::new();
    out.push((root_var, root.clone()));

    // Resolve each eliminated variable. Apply the *later* substitutions to each
    // `f` so it is expressed purely in terms of variables that are themselves
    // resolved (ultimately root_var).
    for idx in 0..subs.len() {
        let (v, f) = &subs[idx];
        // Apply all substitutions recorded AFTER this one (which eliminate the
        // vars that `f` may still mention).
        let mut resolved = f.clone();
        for (lv, lf) in subs.iter().skip(idx + 1) {
            if resolved.vars().contains(lv) {
                resolved = resolved.substitute(*lv, lf);
            }
        }

        let value = realise_in_root(&resolved, root_var, root)?;
        out.push((*v, value));
    }

    // Sanity: every variable of the system must now have a value.
    for &v in all_vars {
        if !out.iter().any(|(w, _)| *w == v) {
            return None;
        }
    }

    Some(out)
}

/// Realise a polynomial `expr` (in `root_var` only, or constant) as an exact
/// algebraic value, given `root_var = root`.
fn realise_in_root(
    expr: &Polynomial,
    root_var: Var,
    root: &AlgebraicNumber,
) -> Option<AlgebraicNumber> {
    if expr.is_constant() {
        return Some(AlgebraicNumber::from_rational(expr.constant_value()));
    }
    let vars = expr.vars();
    if vars.len() != 1 || vars[0] != root_var {
        return None;
    }
    // expr == c1 * root_var + c0 ?  (affine in root_var) — the c1*x + c0 case.
    if expr.degree(root_var) == 1 {
        let c1 = expr.univ_coeff(root_var, 1);
        let c0 = expr.univ_coeff(root_var, 0);
        // Pure identity `root_var` (c1 == 1, c0 == 0): reuse the root exactly.
        if c1 == BigRational::from_integer(num_bigint::BigInt::from(1)) && c0.is_zero() {
            return Some(root.clone());
        }
        // Other affine forms are not realised exactly here (would need algebraic
        // arithmetic); be conservative and fall back.
        return None;
    }
    None
}

/// Apply the full substitution chain to a polynomial.
fn apply_subs(p: &Polynomial, subs: &[(Var, Polynomial)]) -> Polynomial {
    let mut out = p.clone();
    for (v, f) in subs {
        if out.vars().contains(v) {
            out = out.substitute(*v, f);
        }
    }
    out
}

/// Convert a multivariate polynomial that is univariate in `var` into the
/// dense `root_counting::Polynomial` (low-to-high coefficients) required by
/// [`AlgebraicNumber::new`]. Returns `None` if `p` mentions any other variable.
fn to_univariate(p: &Polynomial, var: Var) -> Option<UniPolynomial> {
    let vars = p.vars();
    if vars.len() > 1 {
        return None;
    }
    if vars.len() == 1 && vars[0] != var {
        return None;
    }
    let deg = p.degree(var) as usize;
    let mut coeffs = Vec::with_capacity(deg + 1);
    for k in 0..=deg {
        coeffs.push(p.univ_coeff(var, k as u32));
    }
    Some(UniPolynomial::new(coeffs))
}

/// Gather the asserted single-factor equality polynomials from a solver's atoms.
///
/// An atom contributes iff it is an `Atom::Ineq` with `kind == Eq`, exactly one
/// factor, and its boolean variable is currently assigned **true** (asserted at
/// the top level). This respects the boolean structure: a negated equality is
/// not eligible for elimination.
pub(crate) fn collect_asserted_equalities(
    atoms: &[Atom],
    assignment: &Assignment,
) -> Vec<Polynomial> {
    let mut out = Vec::new();
    for atom in atoms {
        if let Atom::Ineq(ineq) = atom {
            if ineq.kind != AtomKind::Eq {
                continue;
            }
            if ineq.factors.len() != 1 {
                continue;
            }
            if !assignment.bool_value(ineq.bool_var).is_true() {
                continue;
            }
            out.push(ineq.factors[0].poly.clone());
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_traits::Signed;

    fn rat(n: i64) -> BigRational {
        BigRational::from_integer(num_bigint::BigInt::from(n))
    }

    #[test]
    fn test_circle_and_line_algebraic() {
        // x^2 + y^2 - 25 = 0  and  y - x = 0
        let x = Polynomial::from_var(0);
        let y = Polynomial::from_var(1);
        let x2 = Polynomial::mul(&x, &x);
        let y2 = Polynomial::mul(&y, &y);
        let circle = Polynomial::sub(&Polynomial::add(&x2, &y2), &Polynomial::constant(rat(25)));
        let line = Polynomial::sub(&y, &x);

        let sol = try_solve_equalities(&[circle, line]).expect("should solve circle/line");
        assert_eq!(sol.values.len(), 2);

        // x must satisfy 2x^2 - 25 = 0 (i.e. its minimal polynomial divides it).
        let xnum = &sol
            .values
            .iter()
            .find(|(v, _)| *v == 0)
            .expect("x present")
            .1;
        // The defining polynomial should have a real root in the isolating interval,
        // and 2x^2 - 25 should be a multiple of the minimal polynomial.
        let lo = xnum.lower.clone();
        let hi = xnum.upper.clone();
        // 2x^2 - 25 changes sign across the isolating interval.
        let f = |t: &BigRational| rat(2) * t * t - rat(25);
        assert!(
            f(&lo).signum() != f(&hi).signum() || f(&lo).is_zero() || f(&hi).is_zero(),
            "2x^2-25 must straddle a root in the isolating interval"
        );

        // y must equal x (same algebraic number representation).
        let ynum = &sol
            .values
            .iter()
            .find(|(v, _)| *v == 1)
            .expect("y present")
            .1;
        assert_eq!(xnum.lower, ynum.lower);
        assert_eq!(xnum.upper, ynum.upper);
        assert_eq!(xnum.minimal_poly, ynum.minimal_poly);
    }

    #[test]
    fn test_falls_back_on_non_reducible() {
        // A single bivariate equality with no linear variable: x^2 + y^2 - 1 = 0.
        // Not reducible to univariate by linear substitution and only one eq, so
        // resultant elimination (needs 2 eqs) does not apply ⇒ None (fall back).
        let x = Polynomial::from_var(0);
        let y = Polynomial::from_var(1);
        let x2 = Polynomial::mul(&x, &x);
        let y2 = Polynomial::mul(&y, &y);
        let circle = Polynomial::sub(&Polynomial::add(&x2, &y2), &Polynomial::constant(rat(1)));
        assert!(try_solve_equalities(&[circle]).is_none());
    }

    #[test]
    fn test_no_real_root_falls_back() {
        // x^2 + 1 = 0 (no real root) AND y - x = 0 — eliminant x^2+1 has no real
        // root, so the KB returns None (never reports Unsat).
        let x = Polynomial::from_var(0);
        let y = Polynomial::from_var(1);
        let x2 = Polynomial::mul(&x, &x);
        let eq = Polynomial::add(&x2, &Polynomial::constant(rat(1)));
        let line = Polynomial::sub(&y, &x);
        assert!(try_solve_equalities(&[eq, line]).is_none());
    }

    #[test]
    fn test_rational_solution_falls_back() {
        // 2x - 6 = 0 (x = 3) AND y - x = 0 (y = 3). Linear, RATIONAL solution.
        // The system is reducible (y:=x, then 2x-6=0), but the root is rational
        // and therefore representable by the base CDCL+CAD search. The KB is the
        // irrational-solution recognizer, so it falls back here (returns None) to
        // stay strictly additive.
        let x = Polynomial::from_var(0);
        let y = Polynomial::from_var(1);
        let eq = Polynomial::sub(&Polynomial::scale(&x, &rat(2)), &Polynomial::constant(rat(6)));
        let line = Polynomial::sub(&y, &x);
        assert!(try_solve_equalities(&[eq, line]).is_none());
    }

    // ---- Rule D — single univariate power equality `x^k = a` (catalog §D). ----

    #[test]
    fn test_rule_d_x2_minus_2_irrational_sat() {
        // x^2 - 2 = 0  ⇒  x = ±√2 (irrational). Rule D returns the exact
        // algebraic root. This is the `test_quadratic_roots` SAT fix.
        let x = Polynomial::from_var(0);
        let x2 = Polynomial::mul(&x, &x);
        let eq = Polynomial::sub(&x2, &Polynomial::constant(rat(2)));

        let sol = try_solve_equalities(&[eq]).expect("Rule D should solve x^2 - 2 = 0");
        assert_eq!(sol.values.len(), 1);
        let (v, root) = &sol.values[0];
        assert_eq!(*v, 0);
        // √2 is irrational.
        assert!(!root.is_rational(), "sqrt(2) must be irrational");
        // 2t^2 - ... actually t^2 - 2 must straddle a sign change over [lo, hi].
        let f = |t: &BigRational| t * t - rat(2);
        let lo = f(&root.lower);
        let hi = f(&root.upper);
        assert!(
            lo.is_zero() || hi.is_zero() || lo.signum() != hi.signum(),
            "x^2 - 2 must have a root inside the isolating interval [{}, {}]",
            root.lower,
            root.upper
        );
    }

    #[test]
    fn test_rule_d_cube_root_2_irrational_sat() {
        // x^3 - 2 = 0  ⇒  one real root x = 2^(1/3) (irrational, k odd). Rule D
        // must return it.
        let x = Polynomial::from_var(0);
        let x2 = Polynomial::mul(&x, &x);
        let x3 = Polynomial::mul(&x2, &x);
        let eq = Polynomial::sub(&x3, &Polynomial::constant(rat(2)));

        let sol = try_solve_equalities(&[eq]).expect("Rule D should solve x^3 - 2 = 0");
        assert_eq!(sol.values.len(), 1);
        assert!(!sol.values[0].1.is_rational(), "cbrt(2) must be irrational");
    }

    #[test]
    fn test_rule_d_x2_plus_1_no_real_root_falls_back() {
        // x^2 + 1 = 0 (k even, a < 0 after moving: x^2 = -1) has NO real root.
        // Rule D must FALL BACK (None) — never report Sat (complex root) and never
        // report Unsat; the complete CAD path concludes the sound real-UNSAT.
        let x = Polynomial::from_var(0);
        let x2 = Polynomial::mul(&x, &x);
        let eq = Polynomial::add(&x2, &Polynomial::constant(rat(1)));
        assert!(try_solve_equalities(&[eq]).is_none());
    }

    #[test]
    fn test_rule_d_x2_minus_4_rational_falls_back() {
        // x^2 - 4 = 0  ⇒  x = ±2 (RATIONAL). Rule D declines so the base CDCL+CAD
        // path (which represents rationals exactly, and owns the NIA integer
        // decision) handles it. Stays SAT-only-additive.
        let x = Polynomial::from_var(0);
        let x2 = Polynomial::mul(&x, &x);
        let eq = Polynomial::sub(&x2, &Polynomial::constant(rat(4)));
        assert!(try_solve_equalities(&[eq]).is_none());
    }

    #[test]
    fn test_rule_d_cubic_rational_roots_falls_back() {
        // x^3 - x = 0  ⇒  roots {-1, 0, 1}, all RATIONAL. Rule D declines (the
        // rational-root gate fires) — this protects `test_solver_cubic_polynomial`.
        let x = Polynomial::from_var(0);
        let x2 = Polynomial::mul(&x, &x);
        let x3 = Polynomial::mul(&x2, &x);
        let eq = Polynomial::sub(&x3, &x);
        assert!(try_solve_equalities(&[eq]).is_none());
    }

    #[test]
    fn test_rule_d_linear_rational_falls_back() {
        // x - 1 = 0 (x = 1, rational). Rule D declines so NIA's branch-and-bound
        // sees the rational relaxation (protects `test_nia_simple_integer` and
        // `test_nia_fractional_infeasible`).
        let x = Polynomial::from_var(0);
        let eq = Polynomial::sub(&x, &Polynomial::constant(rat(1)));
        assert!(try_solve_equalities(&[eq]).is_none());

        // x - 1/2 = 0 (rational 0.5): also declines.
        let half = Polynomial::constant(BigRational::new(1.into(), 2.into()));
        let eq2 = Polynomial::sub(&x, &half);
        assert!(try_solve_equalities(&[eq2]).is_none());
    }

    // ---- Conic ∩ conic / conic ∩ line via the exact algebraic path (§A1/§A3). ----

    #[test]
    fn test_two_circles_radical_axis_sat() {
        // x²+y²-25 = 0  AND  x²+(y-1)²-25 = 0  (two circles).
        // Their difference (radical axis) is the LINE 2y - 1 = 0 ⇒ y = 1/2.
        // Then x² = 25 - 1/4 = 99/4 ⇒ x = ±√99/2 (IRRATIONAL). The augmentation
        // exposes the line, Level-0 pivots on it, and the eliminant 4x² - 99 = 0
        // has an irrational root ⇒ solved exactly via the existing machinery.
        let x = Polynomial::from_var(0);
        let y = Polynomial::from_var(1);
        let x2 = Polynomial::mul(&x, &x);
        let y2 = Polynomial::mul(&y, &y);
        let circle1 =
            Polynomial::sub(&Polynomial::add(&x2, &y2), &Polynomial::constant(rat(25)));
        // x² + (y-1)² - 25 = x² + y² - 2y + 1 - 25
        let ym1 = Polynomial::sub(&y, &Polynomial::constant(rat(1)));
        let ym1sq = Polynomial::mul(&ym1, &ym1);
        let circle2 =
            Polynomial::sub(&Polynomial::add(&x2, &ym1sq), &Polynomial::constant(rat(25)));

        let sol = try_solve_equalities(&[circle1, circle2])
            .expect("two circles should be solved via radical-axis + Level-0");
        // x must be irrational (√99 / 2); y is determined as 1/2.
        let xnum = &sol.values.iter().find(|(v, _)| *v == 0).expect("x present").1;
        assert!(!xnum.is_rational(), "x = sqrt(99)/2 must be irrational");
        // 4x² - 99 straddles a sign change across the isolating interval.
        let f = |t: &BigRational| rat(4) * t * t - rat(99);
        let lo = f(&xnum.lower);
        let hi = f(&xnum.upper);
        assert!(lo.is_zero() || hi.is_zero() || lo.signum() != hi.signum());
    }

    #[test]
    fn test_ellipse_and_line_sat() {
        // Ellipse x² + 4y² - 100 = 0  AND  line y - x = 0.
        // y := x ⇒ 5x² - 100 = 0 ⇒ x² = 20 ⇒ x = ±√20 (IRRATIONAL).
        let x = Polynomial::from_var(0);
        let y = Polynomial::from_var(1);
        let x2 = Polynomial::mul(&x, &x);
        let y2 = Polynomial::mul(&y, &y);
        let ellipse = Polynomial::sub(
            &Polynomial::add(&x2, &y2.scale(&rat(4))),
            &Polynomial::constant(rat(100)),
        );
        let line = Polynomial::sub(&y, &x);

        let sol = try_solve_equalities(&[ellipse, line])
            .expect("ellipse ∩ line should be solved via Level-0 elimination");
        assert_eq!(sol.values.len(), 2);
        let xnum = &sol.values.iter().find(|(v, _)| *v == 0).expect("x present").1;
        let ynum = &sol.values.iter().find(|(v, _)| *v == 1).expect("y present").1;
        assert!(!xnum.is_rational(), "x = sqrt(20) must be irrational");
        // y = x exactly.
        assert_eq!(xnum.minimal_poly, ynum.minimal_poly);
        assert_eq!(xnum.lower, ynum.lower);
        // 5x² - 100 straddles a sign change.
        let f = |t: &BigRational| rat(5) * t * t - rat(100);
        let lo = f(&xnum.lower);
        let hi = f(&xnum.upper);
        assert!(lo.is_zero() || hi.is_zero() || lo.signum() != hi.signum());
    }

    #[test]
    fn test_two_circles_no_intersection_falls_back() {
        // x²+y²-1 = 0 AND x²+(y-10)²-1 = 0 : two unit circles 10 apart — NO real
        // intersection. Radical axis 20y - 100 = 0 ⇒ y = 5; then x² = 1 - 25 = -24
        // ⇒ no real x ⇒ the eliminant has no real root ⇒ KB falls back (None),
        // never reporting Sat (and never Unsat). The CAD path concludes the sound
        // real-UNSAT.
        let x = Polynomial::from_var(0);
        let y = Polynomial::from_var(1);
        let x2 = Polynomial::mul(&x, &x);
        let y2 = Polynomial::mul(&y, &y);
        let circle1 = Polynomial::sub(&Polynomial::add(&x2, &y2), &Polynomial::constant(rat(1)));
        let ym10 = Polynomial::sub(&y, &Polynomial::constant(rat(10)));
        let ym10sq = Polynomial::mul(&ym10, &ym10);
        let circle2 =
            Polynomial::sub(&Polynomial::add(&x2, &ym10sq), &Polynomial::constant(rat(1)));
        assert!(try_solve_equalities(&[circle1, circle2]).is_none());
    }

    #[test]
    fn test_has_rational_root() {
        // x^2 - 4: rational roots ±2.
        let x = Polynomial::from_var(0);
        let x2 = Polynomial::mul(&x, &x);
        let q1 = Polynomial::sub(&x2, &Polynomial::constant(rat(4)));
        assert!(has_rational_root(&q1, 0));
        // x^2 - 2: no rational root.
        let q2 = Polynomial::sub(&x2, &Polynomial::constant(rat(2)));
        assert!(!has_rational_root(&q2, 0));
        // 2x^2 - 25: no rational root (the circle/line eliminant).
        let q3 = Polynomial::sub(&x2.scale(&rat(2)), &Polynomial::constant(rat(25)));
        assert!(!has_rational_root(&q3, 0));
        // x^3 - x: rational roots {-1,0,1}.
        let x3 = Polynomial::mul(&x2, &x);
        let q4 = Polynomial::sub(&x3, &x);
        assert!(has_rational_root(&q4, 0));
        // x^2 + 1: no rational (no real) root.
        let q5 = Polynomial::add(&x2, &Polynomial::constant(rat(1)));
        assert!(!has_rational_root(&q5, 0));
    }
}
