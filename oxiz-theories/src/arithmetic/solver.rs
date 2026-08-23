//! Arithmetic Theory Solver

use super::simplex::{LinExpr, Simplex, VarId};
use core::fmt;
#[allow(unused_imports)]
use crate::prelude::*;
use crate::theory::{EqualityNotification, Theory, TheoryCombination, TheoryId, TheoryResult};
use crate::ArithRat;
use num_traits::{One, Signed, Zero};
use oxiz_core::ast::TermId;
use oxiz_core::error::Result;
use portable_bijectives::FlatRadixBimap;

/// Compute GCD of two `i128` values.
///
/// `i128` because all coefficients/constants flowing through here are now
/// `ArithRat` (= `Ratio<i128>`) numerators ([`crate::ArithRat`]); the GCD-based
/// integer-infeasibility check and the coefficient-reduction normalisation must
/// run over the full `i128` value — truncating to `i64` could compute a wrong
/// GCD and either miss a genuine LIA infeasibility or fabricate a spurious one.
fn gcd_i128(mut a: i128, mut b: i128) -> i128 {
    a = a.abs();
    b = b.abs();
    while b != 0 {
        let temp = b;
        b = a % b;
        a = temp;
    }
    a
}

/// Arithmetic Theory Solver (LRA/LIA)
pub struct ArithSolver {
    /// Simplex instance
    simplex: Simplex,
    /// Term ↔ simplex-variable interner. ONE bijection replaces the old
    /// `term_to_var` (forward) + `var_to_term` (reverse / intern-order) pair:
    /// a scope `pop` now rolls BOTH directions back in a single `truncate`, so
    /// the desync that pair once allowed — the forward map left un-rolled-back,
    /// handing a later `intern()` a stale `VarId` the popped simplex no longer
    /// had → a pivot index-out-of-bounds panic — is structurally
    /// unrepresentable. `FlatRadixBimap` (the dense-id radix backend) is the
    /// benchmarked winner for these dense, (near-)monotonic `TermId`/`VarId`s
    /// (id-as-index lookup: O(1), zero compares, one cache miss).
    interner: FlatRadixBimap<TermId, VarId>,
    /// Reason counter
    reason_counter: u32,
    /// Reason to term mapping
    reasons: Vec<TermId>,
    /// #433: unit-atom bounds recorded at ASSERT time, append-only and
    /// truncate-rolled on `pop` (a `ContextState` field carries the length —
    /// the pop-scrub rule for assert-time-populated state). One entry per
    /// single-term, unit-coefficient `assert_le`/`assert_ge`/`assert_eq`:
    /// `(term, is_lower, integer bound value, asserting atom)`. This exists
    /// because the simplex holds every constraint through a SLACK variable —
    /// `1 <= x` bounds the slack, not `x` — so "the asserted bounds of x" is
    /// not a question its bound store can answer.
    unit_bounds: Vec<(TermId, bool, i128, TermId)>,
    /// Is this LIA (integers) or LRA (reals)?
    ///
    /// #427 — this is now only the FALLBACK for a term whose sort was never
    /// declared (see `declared_sorts`). It is set from the `(set-logic …)`
    /// name, which is not a reliable source of integrality: `ALL`, a missing
    /// `(set-logic)`, and mixed names like `AUFLIRA`/`QF_LIRA` all match none of
    /// the `LIA`/`IDL`/`NIA`/`BV` substrings `Solver::set_logic` tests, so they
    /// fell through to the default LRA and every Int-sorted constraint was
    /// solved over the RATIONALS.
    is_integer: bool,
    /// #427 — per-TERM integrality, keyed by the term's SMT SORT rather than by
    /// the logic name. `Some(true)` = Int-sorted (or a bitvector, whose values
    /// are integers), `Some(false)` = Real-sorted, absent = never declared (the
    /// `is_integer` fallback applies).
    ///
    /// Sort is a permanent property of a term, so this map is deliberately NOT
    /// rolled back by `pop`: re-interning the same `TermId` after a backtrack
    /// must recover the same integrality. Only `reset` clears it (the term
    /// arena itself is being discarded there).
    declared_sorts: FxHashMap<TermId, bool>,
    /// Whether any term has been declared Int-sorted. Cheap gate for the
    /// integrality check in `check()` — see `needs_integrality_check`.
    any_int_declared: bool,
    /// Context stack
    context_stack: Vec<ContextState>,
    /// Accumulated shared equalities (from notify_equality calls)
    shared_equalities: Vec<EqualityNotification>,
    /// Diagnostics for the most recent `check()` conflict, used by the theory
    /// manager to detect a *stale-bound* pseudo-conflict (see `check`):
    /// `(number of distinct reason-ids, number of distinct reason atom terms)`.
    /// A real conflict over a single self-infeasible atom (e.g. `(< x x)` or the
    /// LIA GCD branch) reports its contradictory bounds under ONE reason-id, so
    /// `distinct_ids == 1`.  TWO OR MORE distinct ids that collapse onto a
    /// single atom term mean the same atom was asserted under BOTH polarities
    /// into the live simplex — a transient stale bound from a SAT backtrack +
    /// re-decision the theory frame stack did not retract.
    last_conflict_distinct_ids: usize,
    last_conflict_distinct_terms: usize,
    /// #289 — the VALID integer assignment recovered by branch-and-bound on the
    /// most recent `Sat` integer `check()`. `value()`/`rounded_int_value()` read
    /// it so the reported model satisfies coupled integer equalities, instead of
    /// independently rounding the rational LP vertex (which produces models that
    /// violate the constraints). `None` outside integer mode or when B&B did not
    /// run / did not find one.
    integer_model: Option<FxHashMap<VarId, ArithRat>>,
}

/// Node budget for the #289 integer branch-and-bound. Hit only by a genuinely
/// hard integer search (most LP vertices are already integer or decide in a few
/// branches); exhausting it yields the sound `Unknown`, never a fabricated sat.
const INT_BNB_NODE_BUDGET: u32 = 4000;

/// Outcome of [`ArithSolver::integer_branch_and_bound`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum IntFeasibility {
    /// An all-integer assignment exists; `integer_model` is populated.
    Sat,
    /// Every branch is LP-infeasible — no integer solution.
    Infeasible,
    /// The node budget was exhausted before deciding (sound: not a fabricated sat).
    Unknown,
}

/// State for push/pop
#[derive(Debug, Clone)]
struct ContextState {
    num_vars: usize,
    num_reasons: usize,
    /// #433: `unit_bounds` length at push time.
    num_unit_bounds: usize,
    num_shared_equalities: usize,
}

impl Default for ArithSolver {
    fn default() -> Self {
        Self::new(false)
    }
}

// `FlatRadixBimap` is not `Debug`, so derive cannot apply; summarise the
// interner by its size rather than dumping its index vectors.
impl fmt::Debug for ArithSolver {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("ArithSolver")
            .field("simplex", &self.simplex)
            .field("interned_terms", &self.interner.len())
            .field("is_integer", &self.is_integer)
            .field("context_depth", &self.context_stack.len())
            .field("reasons", &self.reasons.len())
            .field("shared_equalities", &self.shared_equalities.len())
            .finish_non_exhaustive()
    }
}

impl ArithSolver {
    /// Create a new arithmetic solver
    #[must_use]
    pub fn new(is_integer: bool) -> Self {
        Self {
            simplex: Simplex::new(),
            interner: FlatRadixBimap::new(),
            reason_counter: 0,
            unit_bounds: Vec::new(),
            reasons: Vec::new(),
            is_integer,
            declared_sorts: FxHashMap::default(),
            any_int_declared: false,
            context_stack: Vec::new(),
            shared_equalities: Vec::new(),
            last_conflict_distinct_ids: 0,
            last_conflict_distinct_terms: 0,
            integer_model: None,
        }
    }

    /// Distinct (reason-id count, atom-term count) of the most recent `check()`
    /// conflict.  See the field docs and `is_stale_bound_conflict`.
    #[must_use]
    pub fn last_conflict_shape(&self) -> (usize, usize) {
        (
            self.last_conflict_distinct_ids,
            self.last_conflict_distinct_terms,
        )
    }

    /// Whether the most recent `check()` conflict is a stale-bound artifact:
    /// two or more distinct assertions (reason-ids) collapsing onto fewer than
    /// two distinct atom terms.  Such a "conflict" is unsound to report — the
    /// currently-assigned constraints are jointly satisfiable; the contradiction
    /// only exists because an atom's previous-polarity bound was never retracted.
    #[must_use]
    pub fn last_conflict_is_stale_bound(&self) -> bool {
        self.last_conflict_distinct_ids >= 2 && self.last_conflict_distinct_terms < 2
    }

    /// Create a new LRA solver
    #[must_use]
    pub fn lra() -> Self {
        Self::new(false)
    }

    /// Create a new LIA solver
    #[must_use]
    pub fn lia() -> Self {
        Self::new(true)
    }

    /// Whether this solver operates in integer (LIA) mode
    #[must_use]
    pub fn is_integer(&self) -> bool {
        self.is_integer
    }

    /// #427 — declare a term's integrality from its SMT SORT.
    ///
    /// The caller (which holds the `TermManager`) is the only party that can see
    /// a term's sort; the arithmetic solver only ever sees `TermId`s. Every path
    /// that puts a term into this solver — `Solver::track_theory_vars` /
    /// `Solver::encode` on the registration side, `TheoryManager` on the
    /// assertion side — declares it here first, so the integrality of an
    /// Int-sorted term no longer depends on the `(set-logic …)` name matching a
    /// hardcoded substring.
    ///
    /// Idempotent, and monotone in the `true` direction only in the sense that
    /// `any_int_declared` never un-sets: a term's sort cannot change.
    pub fn declare_sort(&mut self, term: TermId, is_int: bool) {
        self.declared_sorts.insert(term, is_int);
        if is_int {
            self.any_int_declared = true;
        }
    }

    /// #427 — is `term` integer-valued? Declared sort wins; an undeclared term
    /// falls back to the global LIA/LRA mode (so every logic-named path that was
    /// already correct is bit-identical).
    #[must_use]
    fn term_is_integer(&self, term: TermId) -> bool {
        match self.declared_sorts.get(&term) {
            Some(&is_int) => is_int,
            None => self.is_integer,
        }
    }

    /// #427 — is the linear form `Σ cᵢ·tᵢ` guaranteed to take INTEGER values?
    ///
    /// Both conditions are load-bearing for the integer strengthenings below
    /// (`t < k ⇒ t ≤ ⌈k⌉−1`, the `assert_eq` GCD-infeasibility test):
    /// - every variable is integer-valued, and
    /// - every coefficient is an integer.
    ///
    /// The coefficient half was NOT checked by the old global-mode gate, which
    /// is unsound in its own right: under LIA `(1/2)·x = 3/2` took the
    /// "non-integer constant ⇒ infeasible" branch even though `x = 3` satisfies
    /// it. Requiring integral coefficients closes that too.
    #[must_use]
    fn expr_is_integral(&self, lhs: &[(TermId, ArithRat)]) -> bool {
        lhs.iter()
            .all(|(t, c)| c.denom() == &1 && self.term_is_integer(*t))
    }

    /// #427 — whether `check()` must confirm INTEGER feasibility, not just LP
    /// feasibility: either the global mode is LIA, or at least one term has been
    /// declared Int-sorted (the `ALL` / no-`set-logic` / mixed-logic case).
    #[must_use]
    fn needs_integrality_check(&self) -> bool {
        self.is_integer || self.any_int_declared
    }

    /// Intern a term as a variable
    pub fn intern(&mut self, term: TermId) -> VarId {
        if let Some(&var) = self.interner.get(&term) {
            return var;
        }

        let var = self.simplex.new_var();
        // Bijectivity holds by construction: `term` just missed the `get` above,
        // and `var` is a freshly minted simplex id whose reverse bimap slot was
        // cleared on the last `pop` — so neither side is already mapped and the
        // insert cannot fail. Run the insert unconditionally (NOT inside the
        // assert, which is compiled out in release) and only check the verdict.
        let inserted = self.interner.insert(term, var).is_ok();
        debug_assert!(
            inserted,
            "arith interner bijectivity violated: fresh term/var pair must insert"
        );
        var
    }

    /// Add a reason and return its ID
    fn add_reason(&mut self, term: TermId) -> u32 {
        let id = self.reason_counter;
        self.reason_counter += 1;
        self.reasons.push(term);
        id
    }

    /// Normalize a linear expression
    ///
    /// Normalization performs:
    /// 1. Coefficient reduction: divide by GCD of all coefficients
    /// 2. Sorting: order terms by variable ID for canonical form
    /// 3. Sign normalization: ensure first coefficient (after sorting) is positive
    ///
    /// IMPORTANT: Step 3 is only safe for symmetric constraints (equalities).
    /// For inequalities (Le/Ge), sign normalization flips the direction and must
    /// NOT be applied.  Call `normalize_expr_no_sign` for those cases instead.
    fn normalize_expr(&self, expr: &mut LinExpr) {
        if expr.terms.is_empty() {
            return;
        }

        // For integer arithmetic, reduce by GCD
        if self.is_integer {
            // Find GCD of all coefficients (i128 — see `gcd_i128`).
            let gcd = expr
                .terms
                .iter()
                .map(|(_, c)| c.numer().abs())
                .fold(0i128, |acc, n| if acc == 0 { n } else { gcd_i128(acc, n) });

            if gcd > 1 {
                let divisor = ArithRat::from_integer(gcd);
                expr.scale(ArithRat::one() / divisor);
            }
        }

        // Ensure first coefficient is positive
        if let Some((_, c)) = expr.terms.first()
            && c.is_negative()
        {
            expr.negate();
        }

        // Sort terms by variable ID for canonical form
        expr.terms.sort_by_key(|(v, _)| *v);
    }

    /// Normalize for inequalities: GCD reduction and sorting only.
    ///
    /// Sign normalization is deliberately omitted because negating an inequality
    /// expression reverses its direction (e.g., fa - fb <= 0 becomes fb - fa <= 0,
    /// which represents the opposite constraint fa >= fb).
    fn normalize_ineq_expr(&self, expr: &mut LinExpr) {
        if expr.terms.is_empty() {
            return;
        }

        // For integer arithmetic, reduce by GCD only (preserves sign)
        if self.is_integer {
            let gcd = expr
                .terms
                .iter()
                .map(|(_, c)| c.numer().abs())
                .fold(0i128, |acc, n| if acc == 0 { n } else { gcd_i128(acc, n) });

            if gcd > 1 {
                let divisor = ArithRat::from_integer(gcd);
                expr.scale(ArithRat::one() / divisor);
            }
        }

        // Sort terms by variable ID — safe because sorting doesn't change the sign
        // of the overall expression for inequalities (we don't negate afterwards).
        // NOTE: Sorting alone is also problematic because it reorders terms but the
        // sign is determined by all terms together.  We keep the sort for consistent
        // canonical form but do NOT apply the sign-flip step.
        expr.terms.sort_by_key(|(v, _)| *v);
    }

    /// Assert: lhs <= rhs
    /// #433: record a single-term atom bound (`c*t <= rhs` / `c*t >= rhs`,
    /// any nonzero rational `c`) for an INTEGER-sorted term, normalised to a
    /// bound on `t` itself and tightened to its integer endpoint
    /// (`2t <= 25` records `t <= 12`; `2t >= 5` records `t >= 3`). Sound for
    /// integer terms only, which is why the sort gate is here — a negative
    /// coefficient flips the direction (`-t <= r` is `t >= -r`). The first
    /// differential ran with a `|c| = 1` gate and found 32 of its 120 seeds
    /// still open purely on `(* 2 x)`-style atoms; general division closed
    /// every one. Multi-term atoms stay out of scope by design (see
    /// `unit_bounds`).
    fn record_unit_bound(
        &mut self,
        lhs: &[(TermId, ArithRat)],
        rhs: ArithRat,
        reason: TermId,
        is_le: bool,
        strict: bool,
    ) {
        let [(term, coef)] = lhs else { return };
        if coef.is_zero() {
            return;
        }
        if !self.term_is_integer(*term) {
            return;
        }
        let bound = rhs / *coef;
        // A negative coefficient flips the direction; `is_le` below is the
        // post-normalisation side, so the strict adjustment lands on the
        // correct side automatically.
        let is_le = is_le == (*coef > ArithRat::from_integer(0));
        let val = if is_le {
            if strict && bound.is_integer() {
                bound.to_integer() - 1 // t < 5  ⇒  t <= 4
            } else {
                bound.floor().to_integer() // t <= 25/2, t < 5/2  ⇒  t <= 12, t <= 2
            }
        } else if strict && bound.is_integer() {
            bound.to_integer() + 1 // t > 5  ⇒  t >= 6
        } else {
            bound.ceil().to_integer() // t >= 5/2, t > 5/2  ⇒  t >= 3
        };
        self.unit_bounds.push((*term, !is_le, val, reason));
    }

    pub fn assert_le(&mut self, lhs: &[(TermId, ArithRat)], rhs: ArithRat, reason: TermId) {
        self.record_unit_bound(lhs, rhs, reason, true, false);
        let mut expr = LinExpr::new();

        for (term, coef) in lhs {
            let var = self.intern(*term);
            expr.add_term(var, *coef);
        }
        expr.add_constant(-rhs);

        // Use inequality-safe normalization: GCD reduction + sort, but NO sign flip.
        // sign normalization (negation) would reverse the inequality direction.
        self.normalize_ineq_expr(&mut expr);

        let reason_id = self.add_reason(reason);
        self.simplex.add_le(expr, reason_id);
    }

    /// Assert: lhs >= rhs
    pub fn assert_ge(&mut self, lhs: &[(TermId, ArithRat)], rhs: ArithRat, reason: TermId) {
        self.record_unit_bound(lhs, rhs, reason, false, false);
        let mut expr = LinExpr::new();

        for (term, coef) in lhs {
            let var = self.intern(*term);
            expr.add_term(var, *coef);
        }
        expr.add_constant(-rhs);

        // Use inequality-safe normalization: GCD reduction + sort, but NO sign flip.
        self.normalize_ineq_expr(&mut expr);

        let reason_id = self.add_reason(reason);
        self.simplex.add_ge(expr, reason_id);
    }

    /// Assert: lhs = rhs
    ///
    /// For integer arithmetic (LIA), checks GCD-based infeasibility:
    /// If all coefficients share a common GCD that doesn't divide the RHS,
    /// the constraint is infeasible over integers.
    ///
    /// Example: 2x + 2y = 7 is infeasible because gcd(2,2) = 2 doesn't divide 7.
    pub fn assert_eq(&mut self, lhs: &[(TermId, ArithRat)], rhs: ArithRat, reason: TermId) {
        self.record_unit_bound(lhs, rhs, reason, true, false);
        self.record_unit_bound(lhs, rhs, reason, false, false);
        let mut expr = LinExpr::new();

        for (term, coef) in lhs {
            let var = self.intern(*term);
            expr.add_term(var, *coef);
        }
        expr.add_constant(-rhs);

        // For LIA, check GCD-based infeasibility BEFORE normalization
        // (normalization divides by GCD, which would lose the infeasibility signal)
        //
        // #427 — gated on the INTEGRALITY OF THIS EXPRESSION (all variables
        // Int-sorted, all coefficients integral), not on the global logic-derived
        // mode. That both (a) extends the test to `ALL`/no-logic/mixed-logic
        // problems, where it was silently skipped, and (b) stops it firing on a
        // fractional-coefficient form, where it was unsound.
        if self.expr_is_integral(lhs) {
            // Extract integer coefficients. `c.numer()` is `i128` (the `ArithRat`
            // numerator); kept i128 so a coefficient outside `i64` is never
            // silently truncated before the GCD-infeasibility test (truncation
            // could miss or fabricate an integer infeasibility → unsound).
            let coeffs: Vec<i128> = expr
                .terms
                .iter()
                .filter_map(|(_, c)| {
                    if c.denom() == &1 {
                        Some(*c.numer())
                    } else {
                        None
                    }
                })
                .collect();

            // Extract the constant (which is -rhs in expr = 0 form). i128 — the
            // whole point of the widening: with `rhs: ArithRat` the earlier
            // `expr.add_constant(-rhs)` can no longer overflow on `i64::MIN`.
            let const_term: i128 = if expr.constant.denom() == &1 {
                -*expr.constant.numer()
            } else {
                // Non-integer constant in equality - infeasible for integers.
                // Record THIS assertion's reason so the resulting simplex
                // conflict explains itself (a hardcoded reason 0 would resolve to
                // an unrelated term, producing a conflict clause that omits this
                // equality's literal → the SAT solver cannot flip an OR to its
                // satisfiable disjunct → spurious UNSAT).
                if let Some(&(var, _)) = expr.terms.first() {
                    let reason_id = self.add_reason(reason);
                    self.simplex.set_lower(var, ArithRat::from_integer(1), reason_id);
                    self.simplex.set_upper(var, ArithRat::from_integer(0), reason_id);
                }
                return;
            };

            // Check GCD infeasibility if all coefficients are integers
            if !coeffs.is_empty() && coeffs.len() == expr.terms.len() {
                // Compute GCD of all coefficients (i128 — see `gcd_i128`).
                let g = coeffs.iter().fold(0i128, |acc, &c| gcd_i128(acc, c.abs()));

                if g > 0 && const_term % g != 0 {
                    // GCD infeasibility detected (e.g. 2c = 3)!
                    // Add contradictory constraints: x >= 1 and x <= 0, BOTH
                    // tagged with this assertion's reason (see the note above) so
                    // the simplex conflict resolves back to this equality's atom
                    // and the learned clause soundly blocks only this disjunct.
                    if let Some(&(var, _)) = expr.terms.first() {
                        let reason_id = self.add_reason(reason);
                        self.simplex.set_lower(var, ArithRat::from_integer(1), reason_id);
                        self.simplex.set_upper(var, ArithRat::from_integer(0), reason_id);
                    }
                    return;
                }
            }
        }

        // Normalize the expression
        self.normalize_expr(&mut expr);

        let reason_id = self.add_reason(reason);
        self.simplex.add_eq(expr, reason_id);
    }

    /// Assert: lhs < rhs (strict inequality)
    /// For LRA, uses infinitesimals: lhs <= rhs - δ
    /// For LIA, transforms to: lhs <= rhs - 1 (since no integer exists between k and k+1)
    pub fn assert_lt(&mut self, lhs: &[(TermId, ArithRat)], rhs: ArithRat, reason: TermId) {
        self.record_unit_bound(lhs, rhs, reason, true, true);
        // For integer arithmetic, x < k is equivalent to x <= ceil(k) - 1
        // because there's no integer strictly between ceil(k)-1 and ceil(k).
        //
        // #427 — keyed on `expr_is_integral` (this expression's variables and
        // coefficients), NOT on the global logic-derived mode. Without this the
        // `ALL` / no-`set-logic` / mixed-logic path leaves `x > 0 ∧ x < 1` as the
        // δ-rational relaxation `x ≥ 0+δ ∧ x ≤ 1−δ`, which is LP-feasible; the
        // integrality gate in `check()` would then have to recover the
        // contradiction by branch-and-bound (a sound `Unknown` at best), instead
        // of the simplex deriving the real conflict `x ≥ 1 ∧ x ≤ 0` directly.
        //
        // `ceil(rhs) - 1` rather than `rhs - 1`: for an INTEGRAL `rhs` the two
        // agree (so every existing LIA path is bit-identical), but for a
        // fractional `rhs` the old form was too STRONG — `2x < 1/2` became
        // `2x ≤ -1/2` (i.e. `x ≤ -1`), wrongly excluding the solution `x = 0`.
        if self.expr_is_integral(lhs) {
            // Transform: lhs < rhs becomes lhs <= ceil(rhs) - 1
            let bound = ArithRat::from_integer(rhs.ceil().to_integer() - 1);
            self.assert_le(lhs, bound, reason);
            return;
        }

        // For reals, use delta-rationals
        // lhs < rhs is equivalent to lhs - rhs < 0
        let mut expr = LinExpr::new();

        for (term, coef) in lhs {
            let var = self.intern(*term);
            expr.add_term(var, *coef);
        }
        expr.add_constant(-rhs);

        // Note: We do NOT normalize here because normalize_expr may negate
        // the expression to make the first coefficient positive, which would
        // flip the inequality direction for strict inequalities.

        let reason_id = self.add_reason(reason);
        self.simplex.add_strict_lt(expr, reason_id);
    }

    /// Assert: lhs > rhs (strict inequality)
    /// For LRA, uses infinitesimals: lhs >= rhs + δ
    /// For LIA, transforms to: lhs >= rhs + 1 (since no integer exists between k and k+1)
    pub fn assert_gt(&mut self, lhs: &[(TermId, ArithRat)], rhs: ArithRat, reason: TermId) {
        self.record_unit_bound(lhs, rhs, reason, false, true);
        // For integer arithmetic, x > k is equivalent to x >= floor(k) + 1
        // because there's no integer strictly between floor(k) and floor(k)+1.
        // #427 — see `assert_lt` for why this is gated on `expr_is_integral` and
        // why the bound is `floor(rhs) + 1` (identical to `rhs + 1` whenever
        // `rhs` is integral, correct instead of too-strong when it is not).
        if self.expr_is_integral(lhs) {
            // Transform: lhs > rhs becomes lhs >= floor(rhs) + 1
            let bound = ArithRat::from_integer(rhs.floor().to_integer() + 1);
            self.assert_ge(lhs, bound, reason);
            return;
        }

        // For reals, use delta-rationals
        // lhs > rhs is equivalent to rhs - lhs < 0
        // We build rhs - lhs directly instead of negating lhs - rhs
        // This avoids issues with normalize_expr which ensures positive first coefficient
        let mut expr = LinExpr::new();

        for (term, coef) in lhs {
            let var = self.intern(*term);
            // Add negative coefficient since we want rhs - lhs
            expr.add_term(var, -(*coef));
        }
        // Add +rhs (since we want rhs - lhs, not lhs - rhs)
        expr.add_constant(rhs);

        // Note: We do NOT normalize here because:
        // 1. normalize_expr may negate to make first coefficient positive
        // 2. This would flip the inequality direction
        // 3. For strict inequalities, the sign matters

        let reason_id = self.add_reason(reason);
        self.simplex.add_strict_lt(expr, reason_id);
    }

    /// Get the current value of a variable
    ///
    /// For integer arithmetic (LIA), this properly rounds values that have
    /// infinitesimal components from strict inequalities:
    /// - If value is `r + δ` (positive delta), return `ceil(r)` for integers
    /// - If value is `r - δ` (negative delta), return `floor(r)` for integers
    #[must_use]
    pub fn value(&self, term: TermId) -> Option<ArithRat> {
        self.interner.get(&term).map(|&var| {
            // #427 — the TERM's sort decides the rounding, not the global mode.
            if self.term_is_integer(term) {
                // Get the full delta-rational value
                let dval = self.simplex.delta_value(var);

                // For integer arithmetic, round based on delta:
                // - Positive delta means we have a strict lower bound (x > r)
                //   so round up to the next integer
                // - Negative delta means we have a strict upper bound (x < r)
                //   so round down to the previous integer
                // - Zero delta means exact value, round to nearest integer
                if dval.delta.is_positive() {
                    // x > r implies x >= ceil(r) for integers
                    // If r is already an integer, we need r + 1
                    let real_val = dval.real;
                    if real_val.is_integer() {
                        ArithRat::from_integer(real_val.to_integer() + 1)
                    } else {
                        ArithRat::from_integer(real_val.ceil().to_integer())
                    }
                } else if dval.delta.is_negative() {
                    // x < r implies x <= floor(r) for integers
                    // If r is already an integer, we need r - 1
                    let real_val = dval.real;
                    if real_val.is_integer() {
                        ArithRat::from_integer(real_val.to_integer() - 1)
                    } else {
                        ArithRat::from_integer(real_val.floor().to_integer())
                    }
                } else {
                    // No strict bound, just return the value
                    // Round to nearest integer for consistency
                    dval.real
                }
            } else {
                // For reals, just return the real part
                self.simplex.value(var)
            }
        })
    }

    /// #353 — δ-materialized CONCRETE value of every variable, indexed by `VarId`.
    /// Delegates to [`Simplex::materialize`]; the model builder calls it ONCE per
    /// `check_sat` and indexes it with [`Self::var_index`] so a strict inequality
    /// `x > y` ships a model where `x` is concretely above `y` instead of the
    /// real-part-only `x = y` that [`Self::value`] would return for a Real-sorted
    /// term.
    #[must_use]
    pub fn materialize(&self) -> Vec<ArithRat> {
        self.simplex.materialize()
    }

    /// The simplex `VarId` (as a `usize` index) a term is interned to, if any —
    /// used to look a term up in the [`Self::materialize`] vector.
    #[must_use]
    pub fn var_index(&self, term: TermId) -> Option<usize> {
        self.interner.get(&term).map(|&v| v as usize)
    }

    /// #353 — the delta-aware INTEGER value of an Int-sorted term, applied
    /// regardless of the solver's `is_integer` mode. A term solved in real mode
    /// (the mixed/`ALL` logic that falls to LRA) still has a δ-rational
    /// assignment, and the SORT — not the solver mode — decides that its model
    /// value must be an integer: round toward the side the δ part came from
    /// (a strict lower `x > r` ⇒ `delta > 0` ⇒ round up, a strict upper ⇒ round
    /// down, otherwise to nearest). For a genuinely integer-feasible problem this
    /// reproduces the valid model the pure-LIA path already builds; for an
    /// integer-INFEASIBLE one (`2x = 1`) the rounded value won't satisfy the
    /// assertion — that residual is the #289 integrality gate's job, not this one.
    #[must_use]
    pub fn rounded_int_value(&self, term: TermId) -> Option<i128> {
        let &var = self.interner.get(&term)?;
        // #289 — prefer the branch-and-bound integer model when present: it is a
        // GENUINE integer assignment (satisfies coupled equalities), unlike the
        // per-variable rounding of the rational vertex below, which can violate
        // them (`j+2k=4 ∧ j≤-5` rounds to `{j=-5,k=5}`, j+2k=5≠4).
        if let Some(model) = &self.integer_model
            && let Some(v) = model.get(&var)
        {
            return Some(v.to_integer());
        }
        let dval = self.simplex.delta_value(var);
        let v = if dval.delta.is_positive() {
            if dval.real.is_integer() {
                dval.real.to_integer() + 1
            } else {
                dval.real.ceil().to_integer()
            }
        } else if dval.delta.is_negative() {
            if dval.real.is_integer() {
                dval.real.to_integer() - 1
            } else {
                dval.real.floor().to_integer()
            }
        } else {
            dval.real.round().to_integer()
        };
        Some(v)
    }

    /// #289 branch-and-bound — confirm integer feasibility of the (already
    /// LP-feasible) constraints and record a VALID integer model. See
    /// [`IntFeasibility`]. Resets `integer_model`, then explores from the current
    /// LP vertex under a node budget.
    fn integer_branch_and_bound(&mut self) -> IntFeasibility {
        self.integer_model = None;
        let mut budget: u32 = INT_BNB_NODE_BUDGET;
        self.bnb_node(&mut budget)
    }

    /// One branch-and-bound node: the simplex is LP-feasible on entry. If every
    /// INTEGER-SORTED interned variable already has an integer LP value, snapshot
    /// those and return `Sat`. Otherwise branch on the first such variable `x`
    /// whose value `v` is not integral: with `lo` the largest integer `≤ v`, the
    /// `x ≤ lo` and `x ≥ lo+1` half-spaces partition the search, and a leaf is
    /// integer-feasible iff one of them is.
    ///
    /// #427 — two changes from the LIA-mode-only version:
    /// - only Int-SORTED variables are required to take integer values. A Real
    ///   variable sharing the simplex (the mixed `ALL` problem, and any Real
    ///   declared under an `…LIA…`-named logic) must NOT be branched on: doing so
    ///   rejects the perfectly good model `0 < r < 1` as integer-infeasible.
    /// - integrality is judged δ-AWARE. `Simplex::value` returns only the REAL
    ///   part, so a variable sitting at `0 + δ` (from a strict bound the
    ///   `expr_is_integral` strengthening did not reach — e.g. a mixed
    ///   `x + r < 5`) reads as the integer `0` and would be accepted as an
    ///   integer witness even though its true value is strictly above `0`.
    ///   `DeltaRational::floor` already implements "largest integer ≤ value"
    ///   correctly across the δ sign, and using `lo`/`lo+1` (rather than
    ///   `⌊v⌋`/`⌈v⌉`) also guarantees BOTH branches exclude the current point, so
    ///   a `real`-integral-but-δ-offset value cannot loop.
    fn bnb_node(&mut self, budget: &mut u32) -> IntFeasibility {
        if *budget == 0 {
            return IntFeasibility::Unknown;
        }
        *budget -= 1;

        let mut fractional: Option<(TermId, i128)> = None;
        for (&term, &var) in self.interner.iter() {
            if !self.term_is_integer(term) {
                continue;
            }
            let dval = self.simplex.delta_value(var);
            if !dval.delta.is_zero() || !dval.real.is_integer() {
                fractional = Some((term, dval.floor()));
                break;
            }
        }
        let Some((term, lo)) = fractional else {
            // Every integer-sorted interned variable is integer-valued. The
            // constraints are integer linear combinations of them, so this LP
            // vertex restricted to those variables IS a valid integer assignment.
            // Snapshot exactly those for the model builder (`rounded_int_value`
            // is only consulted for Int-sorted terms; a Real variable's fractional
            // LP value has no business in the integer model).
            let mut model: FxHashMap<VarId, ArithRat> = FxHashMap::default();
            for (&t, &var) in self.interner.iter() {
                if self.term_is_integer(t) {
                    model.insert(var, self.simplex.value(var));
                }
            }
            self.integer_model = Some(model);
            return IntFeasibility::Sat;
        };

        let lo_v = ArithRat::from_integer(lo);
        let hi_v = ArithRat::from_integer(lo + 1);

        // Branch down (`x ≤ lo`) then up (`x ≥ lo+1`); `Sat`/`Unknown` short-circuit.
        match self.bnb_branch(term, false, lo_v, budget) {
            IntFeasibility::Infeasible => {}
            decided => return decided,
        }
        self.bnb_branch(term, true, hi_v, budget)
    }

    /// Explore one B&B branch under a fresh context frame: tighten `term` by a
    /// lower (`up = true` ⇒ `term ≥ bound`) or upper (`term ≤ bound`) bound,
    /// re-solve, and recurse while LP-feasible. The frame is ALWAYS popped before
    /// returning, so the caller's incremental state is left intact.
    ///
    /// The branch bound is asserted through the SAME fresh-slack path the SMT
    /// `(assert (<= t k))` interface uses (`assert_le`/`assert_ge` → `add_le`/
    /// `add_ge`), NOT a direct `simplex.set_lower/set_upper`. A direct bound on a
    /// STRUCTURAL variable is not reliably repaired by the incremental `check()`:
    /// `crash_basis` re-pins only NON-basic variables to their bounds, so a
    /// structural variable pinned to a bound that contradicts a basic equality row
    /// (e.g. `i ≤ -2` while `3j+4i = 0 ∧ j = 2` forces `i = -1.5`) was silently
    /// accepted as feasible at the crash-basis point — a spurious integer model
    /// (`{i = -2, j = 2}`, which violates the equality). Routing through a slack
    /// constraint turns the new bound into a basic-row violation that
    /// `find_violating` always detects, so an infeasible branch returns `Err`.
    ///
    /// `term` is interned, and `add_le`/`add_ge` only add a fresh simplex slack
    /// (never a new interner entry), so the snapshot of interned variables in
    /// `bnb_node` is unaffected. The reason is `term` itself; a B&B branch never
    /// surfaces a conflict (`Err` → `Infeasible` → `Unknown`, never `Unsat`), so
    /// the reason is never cited in a learned clause.
    fn bnb_branch(
        &mut self,
        term: TermId,
        up: bool,
        bound: ArithRat,
        budget: &mut u32,
    ) -> IntFeasibility {
        self.push();
        let one = ArithRat::from_integer(1);
        if up {
            self.assert_ge(&[(term, one)], bound, term); // term >= ceil(v)
        } else {
            self.assert_le(&[(term, one)], bound, term); // term <= floor(v)
        }
        let result = match self.simplex.check() {
            Ok(()) if self.simplex.last_check_incomplete() => IntFeasibility::Unknown,
            Ok(()) => self.bnb_node(budget),
            Err(_) => IntFeasibility::Infeasible,
        };
        self.pop();
        result
    }

    /// If `term` is FIXED to a single value by the current arithmetic bounds,
    /// return `(value, reason_atoms)` — `reason_atoms` being the currently
    /// asserted constraint atoms (TermIds) that pin the value. Returns `None`
    /// when `term` is not arith-known or is not pinned to a single value.
    ///
    /// This is the arith→EUF interface query for theory combination: a fixed
    /// term `t = v` is an ENTAILED equality, so it is sound to merge `t` with the
    /// constant node for `v` in EUF (firing congruence), and the returned reason
    /// atoms are exactly the literals that must appear (negated) in any conflict
    /// the resulting congruence produces.
    ///
    /// Implementation: a scratch probe. `t` is fixed to `v` iff BOTH half-spaces
    /// `t > v` and `t < v` (or, for integers, `t >= v+1` and `t <= v-1`) are
    /// infeasible; each infeasibility's reason set (minus the scratch sentinel
    /// `term` itself, which is the placeholder reason of the probe assertion —
    /// never a real Bool atom) is one side's pinning bound. The scratch frame is
    /// pushed and popped, so `reasons`/`reason_counter`/simplex are fully
    /// restored (the probe leaves NO residue — verified against `push`/`pop`).
    /// #433: one pass over the unit-bound journal, folded to the STRONGEST
    /// asserted integer bounds per term: `term -> ((lo, lo_atom), (hi,
    /// hi_atom))`, keeping the maximal lower and minimal upper (ties keep the
    /// first, i.e. the earliest-asserted atom). Entries are on the current
    /// trail by construction (`unit_bounds` is truncate-rolled on `pop`).
    /// A term with only one side bounded appears with the other side `None`.
    #[must_use]
    pub fn asserted_unit_int_bounds(
        &self,
    ) -> FxHashMap<TermId, (Option<(i128, TermId)>, Option<(i128, TermId)>)> {
        let mut out: FxHashMap<TermId, (Option<(i128, TermId)>, Option<(i128, TermId)>)> =
            FxHashMap::default();
        for &(term, is_lower, val, atom) in &self.unit_bounds {
            let entry = out.entry(term).or_default();
            let side = if is_lower { &mut entry.0 } else { &mut entry.1 };
            let stronger = match side {
                None => true,
                Some((cur, _)) => {
                    if is_lower {
                        val > *cur
                    } else {
                        val < *cur
                    }
                }
            };
            if stronger {
                *side = Some((val, atom));
            }
        }
        out
    }

    #[must_use]
    pub fn fixed_value_with_reasons(&mut self, term: TermId) -> Option<(ArithRat, Vec<TermId>)> {
        let v = self.value(term)?;
        let one = ArithRat::from_integer(1);
        let mut reasons: Vec<TermId> = Vec::new();

        // HIGH side: prove `term` cannot exceed `v`.
        // #427 — the `v±1` (integer) vs strict (real) probe is chosen by the
        // TERM's sort, not by the global mode.
        let term_is_int = self.term_is_integer(term);
        self.push();
        if term_is_int {
            self.assert_ge(&[(term, one)], v + one, term); // term >= v+1
        } else {
            self.assert_gt(&[(term, one)], v, term); // term > v
        }
        let high_infeasible = match self.check() {
            Ok(TheoryResult::Unsat(rs)) => {
                for r in rs {
                    if r != term && !reasons.contains(&r) {
                        reasons.push(r);
                    }
                }
                true
            }
            _ => false,
        };
        self.pop();
        if !high_infeasible {
            return None;
        }

        // LOW side: prove `term` cannot fall below `v`.
        self.push();
        if term_is_int {
            self.assert_le(&[(term, one)], v - one, term); // term <= v-1
        } else {
            self.assert_lt(&[(term, one)], v, term); // term < v
        }
        let low_infeasible = match self.check() {
            Ok(TheoryResult::Unsat(rs)) => {
                for r in rs {
                    if r != term && !reasons.contains(&r) {
                        reasons.push(r);
                    }
                }
                true
            }
            _ => false,
        };
        self.pop();
        if !low_infeasible {
            return None;
        }

        Some((v, reasons))
    }

    /// Tighten a rational bound for integer variables
    ///
    /// For integer variables:
    /// - x <= 5.7 becomes x <= 5
    /// - x >= 2.3 becomes x >= 3
    /// - x < 5.0 becomes x <= 4
    /// - x > 2.0 becomes x >= 3
    #[allow(dead_code)]
    fn tighten_bound(&self, bound: ArithRat, is_upper: bool) -> ArithRat {
        if !self.is_integer {
            return bound;
        }

        // For upper bounds (<=), floor the value
        // For lower bounds (>=), ceiling the value
        if bound.is_integer() {
            bound
        } else if is_upper {
            // x <= 5.7 becomes x <= 5
            ArithRat::from_integer(bound.floor().to_integer())
        } else {
            // x >= 2.3 becomes x >= 3
            ArithRat::from_integer(bound.ceil().to_integer())
        }
    }

    /// Tighten constraints for integer arithmetic
    ///
    /// Returns true if any tightening was performed
    pub fn tighten_constraints(&mut self) -> bool {
        if !self.is_integer {
            return false;
        }

        // In a full implementation, we would:
        // 1. Iterate through all bounds
        // 2. Apply tightening rules
        // 3. Propagate tightened bounds
        //
        // For now, tightening is applied during assertion
        false
    }
}

impl Theory for ArithSolver {
    fn id(&self) -> TheoryId {
        if self.is_integer {
            TheoryId::LIA
        } else {
            TheoryId::LRA
        }
    }

    fn name(&self) -> &str {
        if self.is_integer { "LIA" } else { "LRA" }
    }

    fn can_handle(&self, _term: TermId) -> bool {
        // In a full implementation, check if term is arithmetic
        true
    }

    fn assert_true(&mut self, term: TermId) -> Result<TheoryResult> {
        // In a full implementation, parse the term and add constraints
        let _ = self.intern(term);
        Ok(TheoryResult::Sat)
    }

    fn assert_false(&mut self, term: TermId) -> Result<TheoryResult> {
        let _ = self.intern(term);
        Ok(TheoryResult::Sat)
    }

    fn check(&mut self) -> Result<TheoryResult> {
        match self.simplex.check() {
            // `Ok(())` = no conflict. But if the simplex gave up at the pivot cap,
            // feasibility is UNPROVEN — report the sound `Unknown`, never a
            // spurious `Sat` (a cycling/large LP would otherwise be certified
            // satisfiable without proof).
            Ok(()) if self.simplex.last_check_incomplete() => Ok(TheoryResult::Unknown),
            Ok(()) => {
                // #289 — the simplex only proved the LP RELAXATION feasible. In
                // integer mode a fractional LP vertex (e.g. `j+2k=4 ∧ j≤-5` →
                // `k=4.5`) has NO integer point without branching, so report `Sat`
                // ONLY when branch-and-bound recovers a genuine integer assignment
                // (recorded in `integer_model` for the model builder). A branch-
                // exhausted infeasibility or the node budget yields the sound
                // `Unknown` — never a fabricated integer `Sat`.
                //
                // #427 — the gate is `needs_integrality_check()`, not the global
                // `is_integer`: under `ALL` / no `(set-logic)` / a mixed logic
                // name the mode stays LRA, and this arm used to certify the LP
                // RELAXATION as `Sat` for a problem whose variables are all
                // Int-sorted (bounded pigeonhole: three holes in `{1,2}` pairwise
                // distinct is rationally feasible at `1, 3/2, 2` and was reported
                // `sat`).
                if self.needs_integrality_check() {
                    match self.integer_branch_and_bound() {
                        IntFeasibility::Sat => Ok(TheoryResult::Sat),
                        IntFeasibility::Infeasible | IntFeasibility::Unknown => {
                            Ok(TheoryResult::Unknown)
                        }
                    }
                } else {
                    Ok(TheoryResult::Sat)
                }
            }
            Err(reasons) => {
                // Record the conflict shape so the theory manager can recognise
                // a stale-bound pseudo-conflict (see `last_conflict_is_stale_bound`).
                let mut distinct_ids: Vec<u32> = Vec::new();
                for &r in &reasons {
                    if !distinct_ids.contains(&r) {
                        distinct_ids.push(r);
                    }
                }
                let mut distinct_terms: Vec<TermId> = Vec::new();
                for &r in &distinct_ids {
                    if let Some(&t) = self.reasons.get(r as usize)
                        && !distinct_terms.contains(&t)
                    {
                        distinct_terms.push(t);
                    }
                }
                self.last_conflict_distinct_ids = distinct_ids.len();
                self.last_conflict_distinct_terms = distinct_terms.len();

                let terms: Vec<_> = reasons
                    .iter()
                    .filter_map(|&r| self.reasons.get(r as usize).copied())
                    .collect();
                Ok(TheoryResult::Unsat(terms))
            }
        }
    }

    fn push(&mut self) {
        self.context_stack.push(ContextState {
            num_vars: self.interner.len(),
            num_reasons: self.reasons.len(),
            num_unit_bounds: self.unit_bounds.len(),
            num_shared_equalities: self.shared_equalities.len(),
        });
        self.simplex.push();
    }

    fn pop(&mut self) {
        if let Some(state) = self.context_stack.pop() {
            // Roll the interner back to its push-time size. Because it is now a
            // single bijection, this `truncate` discards BOTH directions in one
            // step — there is no forward map that can be left holding a stale
            // `VarId` for a term whose simplex variable `simplex.pop()` below
            // discards. (The old two-map form could roll back the reverse log
            // and forget the forward map, so a later `intern()` of the same term
            // returned a VarId the popped simplex no longer had → a pivot index-
            // out-of-bounds panic on otherwise-valid push/pop input, surfaced by
            // the persistent OxiZ delegation replaying a prelude-scale multi-
            // `(push)` session. That desync is now structurally unrepresentable.)
            self.interner.truncate(state.num_vars);
            self.reasons.truncate(state.num_reasons);
            self.reason_counter = state.num_reasons as u32;
            self.unit_bounds.truncate(state.num_unit_bounds);
            self.shared_equalities.truncate(state.num_shared_equalities);
            self.simplex.pop();
        }
    }

    fn reset(&mut self) {
        self.simplex.reset();
        self.interner.clear();
        self.reason_counter = 0;
        self.reasons.clear();
        self.unit_bounds.clear();
        self.context_stack.clear();
        self.shared_equalities.clear();
        // #427 — the declared sorts are keyed by `TermId`; a reset discards the
        // whole term association, so drop them too (unlike `pop`, which must keep
        // them: sort is a permanent property of a still-live term).
        self.declared_sorts.clear();
        self.any_int_declared = false;
        self.integer_model = None;
    }

    fn get_model(&self) -> Vec<(TermId, TermId)> {
        // Return variable -> value pairs
        // In a full implementation, we'd create value terms
        Vec::new()
    }
}

impl TheoryCombination for ArithSolver {
    fn notify_equality(&mut self, eq: EqualityNotification) -> bool {
        // Check if both terms are relevant to arithmetic
        let lhs_var = self.interner.get(&eq.lhs).copied();
        let rhs_var = self.interner.get(&eq.rhs).copied();

        if let (Some(lhs), Some(rhs)) = (lhs_var, rhs_var) {
            // Enforce lhs = rhs in the simplex by asserting lhs - rhs <= 0 and rhs - lhs <= 0.
            // This is equivalent to lhs - rhs = 0, i.e., add_eq(lhs - rhs, 0).
            let reason_id = if let Some(r) = eq.reason {
                self.add_reason(r)
            } else {
                self.add_reason(eq.lhs)
            };

            // Build expression: lhs - rhs
            let mut expr_le = LinExpr::new();
            expr_le.add_term(lhs, ArithRat::one());
            expr_le.add_term(rhs, -ArithRat::one());
            // lhs - rhs <= 0
            self.simplex.add_le(expr_le, reason_id);

            // Build expression: rhs - lhs
            let mut expr_ge = LinExpr::new();
            expr_ge.add_term(rhs, ArithRat::one());
            expr_ge.add_term(lhs, -ArithRat::one());
            // rhs - lhs <= 0  (i.e., lhs - rhs >= 0)
            self.simplex.add_le(expr_ge, reason_id);

            // Record so that get_shared_equalities can return it
            self.shared_equalities.push(eq);

            true
        } else {
            // Terms not relevant to this arithmetic solver
            false
        }
    }

    fn get_shared_equalities(&self) -> Vec<EqualityNotification> {
        // Sound Nelson-Oppen propagation (model-based + entailment verification).
        //
        // Algorithm:
        // a) Collect interface variables (those mapped from interned terms).
        // b) Group by current delta_value in the simplex model — same-valued vars
        //    are candidates for equality.
        // c) For each adjacent same-bucket pair (x, y):
        //    i)  Probe: push, add x - y < 0 (strict), check → if UNSAT then
        //        "x < y" is infeasible → entailed_ge holds.
        //    ii) Probe: push, add y - x < 0 (strict), check → if UNSAT then
        //        "x > y" is infeasible → entailed_le holds.
        //    iii) Emit equality only if BOTH probes are UNSAT.
        // d) Also include equalities accumulated via notify_equality.

        // We need a mutable borrow on the simplex for probing, so we collect
        // results in a separate step.  Use an immutable reference for reading
        // variable assignments first, then do mutable probing.

        // Need &mut self for probing; but the trait signature is &self.
        // We work around this by cloning the accumulated `shared_equalities` and
        // returning them — the model-based probing path requires &mut self, so we
        // use an internal helper that takes &mut ArithSolver.
        self.shared_equalities.clone()
    }

    fn is_relevant(&self, term: TermId) -> bool {
        // Check if this term has been interned in the arithmetic solver
        self.interner.contains_key(&term)
    }
}

impl ArithSolver {
    /// Sound Nelson-Oppen equality propagation.
    ///
    /// Returns entailed equalities between interface terms that are shared between
    /// this arithmetic theory and other theories in the Nelson-Oppen combination.
    ///
    /// Only emits `x = y` if BOTH `x < y` and `x > y` are infeasible in the
    /// current simplex state — this guarantees soundness: no false equality is
    /// ever propagated.
    ///
    /// Uses probe-and-pop to avoid permanently modifying the simplex state.
    pub fn derive_shared_equalities(&mut self) -> Vec<EqualityNotification> {
        let num_interface_terms = self.interner.len();
        if num_interface_terms < 2 {
            return self.shared_equalities.clone();
        }

        // Collect (delta_value, VarId, TermId) for all interned variables. The
        // bijection yields the `(TermId, VarId)` pairs directly in intern order,
        // so there is no second forward-map lookup to keep in sync.
        let mut candidates: Vec<(super::delta::DeltaRational, VarId, TermId)> = self
            .interner
            .iter()
            .map(|(&term, &var)| {
                let dval = self.simplex.delta_value(var);
                (dval, var, term)
            })
            .collect();

        if candidates.len() < 2 {
            return self.shared_equalities.clone();
        }

        // Sort by current assignment value so same-valued pairs are adjacent.
        candidates.sort_by_key(|a| a.0);

        let mut result = self.shared_equalities.clone();

        // Check adjacent same-bucket pairs.
        let mut i = 0;
        while i < candidates.len() {
            // Find end of this bucket (same delta_value)
            let bucket_start = i;
            while i < candidates.len() && candidates[i].0 == candidates[bucket_start].0 {
                i += 1;
            }
            let bucket = &candidates[bucket_start..i];

            // For each adjacent pair in the bucket, probe for entailment.
            for pair_idx in 0..bucket.len().saturating_sub(1) {
                let (_, var_x, term_x) = bucket[pair_idx];
                let (_, var_y, term_y) = bucket[pair_idx + 1];

                // Probe 1: Can x < y? (i.e., x - y < 0)
                // If UNSAT → x >= y is entailed (x cannot be strictly less than y).
                let entailed_ge = {
                    self.simplex.push();
                    // Add strict x - y < 0
                    let mut expr = LinExpr::new();
                    expr.add_term(var_x, ArithRat::one());
                    expr.add_term(var_y, -ArithRat::one());
                    self.simplex.add_strict_lt(expr, 0);
                    let infeasible = self.simplex.check().is_err();
                    self.simplex.pop();
                    infeasible
                };

                // Probe 2: Can x > y? (i.e., y - x < 0)
                // If UNSAT → x <= y is entailed (x cannot be strictly greater than y).
                let entailed_le = {
                    self.simplex.push();
                    // Add strict y - x < 0
                    let mut expr = LinExpr::new();
                    expr.add_term(var_y, ArithRat::one());
                    expr.add_term(var_x, -ArithRat::one());
                    self.simplex.add_strict_lt(expr, 0);
                    let infeasible = self.simplex.check().is_err();
                    self.simplex.pop();
                    infeasible
                };

                // Both strict directions infeasible → x = y is entailed.
                if entailed_ge && entailed_le {
                    // Avoid duplicates from shared_equalities.
                    let already_known = result.iter().any(|eq| {
                        (eq.lhs == term_x && eq.rhs == term_y)
                            || (eq.lhs == term_y && eq.rhs == term_x)
                    });
                    if !already_known {
                        result.push(EqualityNotification {
                            lhs: term_x,
                            rhs: term_y,
                            reason: None,
                        });
                    }
                }
            }
        }

        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_traits::{One, Zero};

    #[test]
    fn test_arith_basic() {
        let mut solver = ArithSolver::lra();

        let x = TermId::new(1);
        let y = TermId::new(2);
        let reason = TermId::new(100);

        // x >= 0
        solver.assert_ge(
            &[(x, ArithRat::one())],
            ArithRat::from_integer(0),
            reason,
        );

        // y >= 0
        solver.assert_ge(
            &[(y, ArithRat::one())],
            ArithRat::from_integer(0),
            reason,
        );

        // x + y <= 10
        solver.assert_le(
            &[(x, ArithRat::one()), (y, ArithRat::one())],
            ArithRat::from_integer(10),
            reason,
        );

        let result = solver.check().expect("test operation should succeed");
        assert!(matches!(result, TheoryResult::Sat));
    }

    #[test]
    fn test_fixed_value_with_reasons() {
        let mut solver = ArithSolver::lia();
        let x = TermId::new(1);
        let ge = TermId::new(50); // reason atom for x >= 5
        let le = TermId::new(51); // reason atom for x <= 5
        solver.assert_ge(&[(x, ArithRat::one())], ArithRat::from_integer(5), ge);
        solver.assert_le(&[(x, ArithRat::one())], ArithRat::from_integer(5), le);
        assert!(matches!(solver.check().unwrap(), TheoryResult::Sat));

        // No-leak baseline.
        let reasons_before = solver.reasons.len();

        let fixed = solver.fixed_value_with_reasons(x);
        assert!(fixed.is_some(), "x is pinned to 5 by its two bounds");
        let (v, rs) = fixed.unwrap();
        assert_eq!(v, ArithRat::from_integer(5));
        assert!(
            rs.contains(&ge) && rs.contains(&le),
            "both pinning bounds are reasons: {rs:?}"
        );
        assert!(!rs.contains(&x), "scratch sentinel (the term) is filtered out");

        // The probe must leave NO residue (this is the #1 spurious-UNSAT risk).
        assert_eq!(
            solver.reasons.len(),
            reasons_before,
            "probe left reason residue"
        );
        assert!(
            matches!(solver.check().unwrap(), TheoryResult::Sat),
            "solver state intact after probe"
        );

        // A non-pinned term returns None.
        let y = TermId::new(2);
        let gy = TermId::new(60);
        solver.assert_ge(&[(y, ArithRat::one())], ArithRat::from_integer(0), gy);
        assert!(
            solver.fixed_value_with_reasons(y).is_none(),
            "y has only a lower bound, not pinned"
        );
    }

    #[test]
    fn test_arith_unsat() {
        let mut solver = ArithSolver::lra();

        let x = TermId::new(1);
        let reason = TermId::new(100);

        // x >= 10
        solver.assert_ge(
            &[(x, ArithRat::one())],
            ArithRat::from_integer(10),
            reason,
        );

        // x <= 5
        solver.assert_le(
            &[(x, ArithRat::one())],
            ArithRat::from_integer(5),
            reason,
        );

        let result = solver.check().expect("test operation should succeed");
        assert!(matches!(result, TheoryResult::Unsat(_)));
    }

    #[test]
    fn test_arith_strict_inequality() {
        let mut solver = ArithSolver::lra();

        let x = TermId::new(1);
        let reason = TermId::new(100);

        // x > 0 (strict)
        solver.assert_gt(
            &[(x, ArithRat::one())],
            ArithRat::from_integer(0),
            reason,
        );

        // x < 10 (strict)
        solver.assert_lt(
            &[(x, ArithRat::one())],
            ArithRat::from_integer(10),
            reason,
        );

        let result = solver.check().expect("test operation should succeed");
        assert!(matches!(result, TheoryResult::Sat));
    }

    #[test]
    fn test_arith_strict_unsat() {
        let mut solver = ArithSolver::lra();

        let x = TermId::new(1);
        let reason = TermId::new(100);

        // x >= 5
        solver.assert_ge(
            &[(x, ArithRat::one())],
            ArithRat::from_integer(5),
            reason,
        );

        // x < 5 (strict) - should be unsatisfiable with x >= 5
        solver.assert_lt(
            &[(x, ArithRat::one())],
            ArithRat::from_integer(5),
            reason,
        );

        let result = solver.check().expect("test operation should succeed");
        assert!(matches!(result, TheoryResult::Unsat(_)));
    }

    #[test]
    fn test_coefficient_normalization_lia() {
        let mut solver = ArithSolver::lia();

        let x = TermId::new(1);
        let y = TermId::new(2);
        let reason = TermId::new(100);

        // 2x + 4y <= 10 should be normalized to x + 2y <= 5 (GCD = 2)
        solver.assert_le(
            &[
                (x, ArithRat::from_integer(2)),
                (y, ArithRat::from_integer(4)),
            ],
            ArithRat::from_integer(10),
            reason,
        );

        // The solver should handle this correctly
        let result = solver.check().expect("test operation should succeed");
        assert!(matches!(result, TheoryResult::Sat));
    }

    #[test]
    fn test_coefficient_normalization_sign() {
        let solver = ArithSolver::lra();

        let _x = TermId::new(1);
        let _y = TermId::new(2);

        // Test normalization ensures first coefficient is positive
        let mut expr = LinExpr::new();
        expr.add_term(0, ArithRat::from_integer(-3));
        expr.add_term(1, ArithRat::from_integer(2));

        solver.normalize_expr(&mut expr);

        // After normalization, first coefficient should be positive
        if let Some((_, c)) = expr.terms.first() {
            assert!(c > &ArithRat::zero());
        }
    }

    #[test]
    fn test_gcd_computation() {
        assert_eq!(gcd_i128(12, 8), 4);
        assert_eq!(gcd_i128(15, 25), 5);
        assert_eq!(gcd_i128(7, 13), 1);
        assert_eq!(gcd_i128(0, 5), 5);
        assert_eq!(gcd_i128(5, 0), 5);
        assert_eq!(gcd_i128(-12, 8), 4);
        assert_eq!(gcd_i128(12, -8), 4);
    }

    /// Regression for the `i128` widening (2026-06-21): asserting `x = i64::MIN`
    /// must NOT overflow. The old `Rational64` core computed
    /// `expr.add_constant(-rhs)` in `assert_eq` with `rhs = i64::MIN`, whose
    /// negation overflows `i64` (debug panic / release wrap → spurious arith
    /// verdict). With the LRA/LIA core on `Ratio<i128>` the value is exact and
    /// `-rhs` is representable, so `x = i64::MIN ∧ x = i64::MIN` is plain `Sat`.
    /// The verus prelude legitimately contains `i64::MIN` as an integer bound.
    #[test]
    fn test_i64_min_rhs_no_overflow() {
        let i64_min = i128::from(i64::MIN); // -9223372036854775808
        let one = ArithRat::from_integer(1);
        let rhs = ArithRat::from_integer(i64_min);

        // LRA: x = i64::MIN (the `-rhs` inside assert_eq used to overflow).
        let mut lra = ArithSolver::lra();
        let x = TermId::new(1);
        lra.assert_eq(&[(x, one)], rhs, TermId::new(100));
        assert!(
            matches!(lra.check().unwrap(), TheoryResult::Sat),
            "x = i64::MIN must be SAT in LRA (no overflow)"
        );
        assert_eq!(lra.value(x), Some(rhs), "x must read back as i64::MIN");

        // LIA: same equality, exercising the GCD-infeasibility branch's i128
        // `const_term = -*expr.constant.numer()` (which is `i64::MIN`).
        let mut lia = ArithSolver::lia();
        let y = TermId::new(2);
        lia.assert_eq(&[(y, one)], rhs, TermId::new(101));
        assert!(
            matches!(lia.check().unwrap(), TheoryResult::Sat),
            "y = i64::MIN must be SAT in LIA (no overflow)"
        );

        // A genuine contradiction over i64::MIN bounds is still UNSAT (the
        // widening must not weaken any comparison): x = i64::MIN ∧ x = i64::MIN+1.
        let mut lia2 = ArithSolver::lia();
        let z = TermId::new(3);
        lia2.assert_eq(&[(z, one)], rhs, TermId::new(102));
        lia2.assert_eq(
            &[(z, one)],
            ArithRat::from_integer(i64_min + 1),
            TermId::new(103),
        );
        assert!(
            matches!(lia2.check().unwrap(), TheoryResult::Unsat(_)),
            "z = i64::MIN ∧ z = i64::MIN+1 must be UNSAT"
        );
    }

    #[test]
    fn test_bound_tightening_lia() {
        let solver = ArithSolver::lia();

        // Upper bound tightening: x <= 5.7 -> x <= 5
        let tightened = solver.tighten_bound(ArithRat::new(57, 10), true);
        assert_eq!(tightened, ArithRat::from_integer(5));

        // Lower bound tightening: x >= 2.3 -> x >= 3
        let tightened = solver.tighten_bound(ArithRat::new(23, 10), false);
        assert_eq!(tightened, ArithRat::from_integer(3));

        // Integer bounds don't change
        let tightened = solver.tighten_bound(ArithRat::from_integer(5), true);
        assert_eq!(tightened, ArithRat::from_integer(5));
    }

    #[test]
    fn test_bound_tightening_lra() {
        let solver = ArithSolver::lra();

        // No tightening for real arithmetic
        let bound = ArithRat::new(57, 10);
        let tightened = solver.tighten_bound(bound, true);
        assert_eq!(tightened, bound);
    }

    #[test]
    fn test_tighten_constraints() {
        let mut solver_lia = ArithSolver::lia();
        let mut solver_lra = ArithSolver::lra();

        // For now, this always returns false (tightening happens during assertion)
        assert!(!solver_lia.tighten_constraints());
        assert!(!solver_lra.tighten_constraints());
    }

    /// Test that x > 5 AND x < 6 is UNSAT for integers (no integer in open interval (5,6))
    /// This is the bug report test case: strict inequalities must be transformed for LIA
    #[test]
    fn test_lia_strict_inequality_empty_interval() {
        let mut solver = ArithSolver::lia();

        let x = TermId::new(1);
        let reason = TermId::new(100);

        // x > 5 (for integers, this becomes x >= 6)
        solver.assert_gt(
            &[(x, ArithRat::one())],
            ArithRat::from_integer(5),
            reason,
        );

        // x < 6 (for integers, this becomes x <= 5)
        solver.assert_lt(
            &[(x, ArithRat::one())],
            ArithRat::from_integer(6),
            reason,
        );

        // Should be UNSAT: x >= 6 AND x <= 5 is impossible
        let result = solver.check().expect("test operation should succeed");
        assert!(
            matches!(result, TheoryResult::Unsat(_)),
            "Expected UNSAT for x > 5 AND x < 6 in LIA, got {:?}",
            result
        );
    }

    /// Test that x > 5 AND x < 6 is SAT for reals (5.5 is a valid solution)
    #[test]
    fn test_lra_strict_inequality_has_solution() {
        let mut solver = ArithSolver::lra();

        let x = TermId::new(1);
        let reason = TermId::new(100);

        // x > 5
        solver.assert_gt(
            &[(x, ArithRat::one())],
            ArithRat::from_integer(5),
            reason,
        );

        // x < 6
        solver.assert_lt(
            &[(x, ArithRat::one())],
            ArithRat::from_integer(6),
            reason,
        );

        // Should be SAT for reals: x = 5.5 is a valid solution
        let result = solver.check().expect("test operation should succeed");
        assert!(
            matches!(result, TheoryResult::Sat),
            "Expected SAT for x > 5 AND x < 6 in LRA, got {:?}",
            result
        );
    }

    /// Test x >= 5 AND x <= 5 with strict bounds in LIA
    #[test]
    fn test_lia_strict_at_boundary() {
        let mut solver = ArithSolver::lia();

        let x = TermId::new(1);
        let reason = TermId::new(100);

        // x >= 5
        solver.assert_ge(
            &[(x, ArithRat::one())],
            ArithRat::from_integer(5),
            reason,
        );

        // x < 6 (becomes x <= 5)
        solver.assert_lt(
            &[(x, ArithRat::one())],
            ArithRat::from_integer(6),
            reason,
        );

        // Should be SAT: x = 5 is the only solution
        let result = solver.check().expect("test operation should succeed");
        assert!(
            matches!(result, TheoryResult::Sat),
            "Expected SAT for x >= 5 AND x < 6 in LIA, got {:?}",
            result
        );
    }

    // ---- Nelson-Oppen tests ----

    /// x <= y AND y <= x should yield an entailed equality.
    #[test]
    fn test_no_entailed_equality_bidirectional() {
        let mut solver = ArithSolver::lra();

        let x = TermId::new(1);
        let y = TermId::new(2);
        let reason = TermId::new(100);

        // Intern both so they appear in the interner.
        solver.intern(x);
        solver.intern(y);

        // x <= y
        solver.assert_le(
            &[(x, ArithRat::one()), (y, -ArithRat::one())],
            ArithRat::from_integer(0),
            reason,
        );
        // y <= x
        solver.assert_le(
            &[(y, ArithRat::one()), (x, -ArithRat::one())],
            ArithRat::from_integer(0),
            reason,
        );

        let sat = solver.check().expect("check should succeed");
        assert!(matches!(sat, TheoryResult::Sat), "Expected SAT");

        // Both x < y and x > y should be infeasible — equality is entailed.
        let eqs = solver.derive_shared_equalities();
        let has_xy = eqs
            .iter()
            .any(|e| (e.lhs == x && e.rhs == y) || (e.lhs == y && e.rhs == x));
        assert!(
            has_xy,
            "Expected entailed equality between x and y, got: {:?}",
            eqs
        );
    }

    /// x <= y alone should NOT yield an entailed equality (y could be > x).
    #[test]
    fn test_no_entailed_equality_one_direction_only() {
        let mut solver = ArithSolver::lra();

        let x = TermId::new(1);
        let y = TermId::new(2);
        let reason = TermId::new(100);

        solver.intern(x);
        solver.intern(y);

        // x <= y only (one direction)
        solver.assert_le(
            &[(x, ArithRat::one()), (y, -ArithRat::one())],
            ArithRat::from_integer(0),
            reason,
        );

        solver.check().expect("check should succeed");

        let eqs = solver.derive_shared_equalities();
        let has_xy = eqs
            .iter()
            .any(|e| (e.lhs == x && e.rhs == y) || (e.lhs == y && e.rhs == x));
        assert!(
            !has_xy,
            "Should NOT derive x=y from x<=y alone; got: {:?}",
            eqs
        );
    }

    /// notify_equality(x, y) followed by check should enforce x = y:
    /// asserting x < y should then be UNSAT.
    #[test]
    fn test_notify_equality_enforces_equality() {
        use crate::theory::{EqualityNotification, TheoryCombination};

        let mut solver = ArithSolver::lra();

        let x = TermId::new(1);
        let y = TermId::new(2);
        let reason = TermId::new(100);

        solver.intern(x);
        solver.intern(y);

        // Notify x = y
        let eq = EqualityNotification {
            lhs: x,
            rhs: y,
            reason: Some(reason),
        };
        let accepted = solver.notify_equality(eq);
        assert!(accepted, "notify_equality should accept x=y");

        // After asserting x=y, adding x < y should yield UNSAT.
        solver.push();
        solver.assert_lt(
            &[(x, ArithRat::one()), (y, -ArithRat::one())],
            ArithRat::from_integer(0),
            reason,
        );
        let result = solver.check().expect("check should not error");
        assert!(
            matches!(result, TheoryResult::Unsat(_)),
            "Expected UNSAT when x=y is enforced and x<y is added; got {:?}",
            result
        );
        solver.pop();
    }

    /// Regression: re-interning a term after the scope it was first interned in
    /// is popped must hand out a FRESH simplex variable, never the stale id the
    /// popped simplex no longer has. With the old two-map interner a `pop` that
    /// rolled back only the reverse log left the forward map holding the stale
    /// `VarId`, so this re-`intern()` returned it and the next constraint pivot
    /// indexed the simplex arrays out of bounds (a hard panic on otherwise-valid
    /// push/pop input). The single `FlatRadixBimap` rolls both directions back in
    /// one `truncate`, so the desync — and this panic — is unrepresentable.
    #[test]
    fn test_reintern_after_pop_gets_fresh_var_no_oob_panic() {
        let mut solver = ArithSolver::lra();

        let a = TermId::new(1);
        let reason = TermId::new(100);

        // Scope 1: intern `a` and constrain it, so it acquires a live simplex var.
        solver.push();
        let v1 = solver.intern(a);
        solver.assert_ge(
            &[(a, ArithRat::one())],
            ArithRat::from_integer(0),
            reason,
        );
        assert!(matches!(
            solver.check().expect("scope-1 check should not error"),
            TheoryResult::Sat
        ));
        // Pop scope 1: `simplex.pop()` discards `v1`; the interner truncates so
        // `a` is no longer mapped to it.
        solver.pop();
        assert!(
            !solver.is_relevant(a),
            "after pop, `a` must no longer be interned"
        );

        // Re-intern `a`. It must get a fresh simplex var (the popped one is gone),
        // and using it in a fresh constraint must NOT panic (the old OOB pivot).
        solver.push();
        let v2 = solver.intern(a);
        solver.assert_le(
            &[(a, ArithRat::one())],
            ArithRat::from_integer(5),
            reason,
        );
        let result = solver.check().expect("scope-2 check should not error");
        assert!(
            matches!(result, TheoryResult::Sat),
            "re-interned `a` (var {v2:?}, was {v1:?}) under a satisfiable bound \
             should be SAT; got {result:?}"
        );
        solver.pop();
    }
}
