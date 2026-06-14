//! Arithmetic Theory Solver

use super::simplex::{LinExpr, Simplex, VarId};
#[allow(unused_imports)]
use crate::prelude::*;
use crate::theory::{EqualityNotification, Theory, TheoryCombination, TheoryId, TheoryResult};
use num_rational::Rational64;
use num_traits::{One, Signed};
use oxiz_core::ast::TermId;
use oxiz_core::error::Result;

/// Compute GCD of two i64 values
fn gcd_i64(mut a: i64, mut b: i64) -> i64 {
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
#[derive(Debug)]
pub struct ArithSolver {
    /// Simplex instance
    simplex: Simplex,
    /// Term to variable mapping
    term_to_var: FxHashMap<TermId, VarId>,
    /// Variable to term mapping
    var_to_term: Vec<TermId>,
    /// Reason counter
    reason_counter: u32,
    /// Reason to term mapping
    reasons: Vec<TermId>,
    /// Is this LIA (integers) or LRA (reals)?
    is_integer: bool,
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
}

/// State for push/pop
#[derive(Debug, Clone)]
struct ContextState {
    num_vars: usize,
    num_reasons: usize,
    num_shared_equalities: usize,
}

impl Default for ArithSolver {
    fn default() -> Self {
        Self::new(false)
    }
}

impl ArithSolver {
    /// Create a new arithmetic solver
    #[must_use]
    pub fn new(is_integer: bool) -> Self {
        Self {
            simplex: Simplex::new(),
            term_to_var: FxHashMap::default(),
            var_to_term: Vec::new(),
            reason_counter: 0,
            reasons: Vec::new(),
            is_integer,
            context_stack: Vec::new(),
            shared_equalities: Vec::new(),
            last_conflict_distinct_ids: 0,
            last_conflict_distinct_terms: 0,
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

    /// Intern a term as a variable
    pub fn intern(&mut self, term: TermId) -> VarId {
        if let Some(&var) = self.term_to_var.get(&term) {
            return var;
        }

        let var = self.simplex.new_var();
        self.term_to_var.insert(term, var);
        self.var_to_term.push(term);
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
            // Find GCD of all coefficients
            let gcd = expr
                .terms
                .iter()
                .map(|(_, c)| c.numer().abs())
                .fold(0i64, |acc, n| if acc == 0 { n } else { gcd_i64(acc, n) });

            if gcd > 1 {
                let divisor = Rational64::from_integer(gcd);
                expr.scale(Rational64::one() / divisor);
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
                .fold(0i64, |acc, n| if acc == 0 { n } else { gcd_i64(acc, n) });

            if gcd > 1 {
                let divisor = Rational64::from_integer(gcd);
                expr.scale(Rational64::one() / divisor);
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
    pub fn assert_le(&mut self, lhs: &[(TermId, Rational64)], rhs: Rational64, reason: TermId) {
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
    pub fn assert_ge(&mut self, lhs: &[(TermId, Rational64)], rhs: Rational64, reason: TermId) {
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
    pub fn assert_eq(&mut self, lhs: &[(TermId, Rational64)], rhs: Rational64, reason: TermId) {
        let mut expr = LinExpr::new();

        for (term, coef) in lhs {
            let var = self.intern(*term);
            expr.add_term(var, *coef);
        }
        expr.add_constant(-rhs);

        // For LIA, check GCD-based infeasibility BEFORE normalization
        // (normalization divides by GCD, which would lose the infeasibility signal)
        if self.is_integer {
            // Extract integer coefficients
            let coeffs: Vec<i64> = expr
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

            // Extract the constant (which is -rhs in expr = 0 form)
            let const_term = if expr.constant.denom() == &1 {
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
                    self.simplex.set_lower(var, Rational64::from_integer(1), reason_id);
                    self.simplex.set_upper(var, Rational64::from_integer(0), reason_id);
                }
                return;
            };

            // Check GCD infeasibility if all coefficients are integers
            if !coeffs.is_empty() && coeffs.len() == expr.terms.len() {
                // Compute GCD of all coefficients
                let g = coeffs.iter().fold(0i64, |acc, &c| gcd_i64(acc, c.abs()));

                if g > 0 && const_term % g != 0 {
                    // GCD infeasibility detected (e.g. 2c = 3)!
                    // Add contradictory constraints: x >= 1 and x <= 0, BOTH
                    // tagged with this assertion's reason (see the note above) so
                    // the simplex conflict resolves back to this equality's atom
                    // and the learned clause soundly blocks only this disjunct.
                    if let Some(&(var, _)) = expr.terms.first() {
                        let reason_id = self.add_reason(reason);
                        self.simplex.set_lower(var, Rational64::from_integer(1), reason_id);
                        self.simplex.set_upper(var, Rational64::from_integer(0), reason_id);
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
    pub fn assert_lt(&mut self, lhs: &[(TermId, Rational64)], rhs: Rational64, reason: TermId) {
        // For integer arithmetic, x < k is equivalent to x <= k - 1
        // because there's no integer strictly between k-1 and k
        if self.is_integer {
            // Transform: lhs < rhs becomes lhs <= rhs - 1
            self.assert_le(lhs, rhs - Rational64::one(), reason);
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
    pub fn assert_gt(&mut self, lhs: &[(TermId, Rational64)], rhs: Rational64, reason: TermId) {
        // For integer arithmetic, x > k is equivalent to x >= k + 1
        // because there's no integer strictly between k and k+1
        if self.is_integer {
            // Transform: lhs > rhs becomes lhs >= rhs + 1
            self.assert_ge(lhs, rhs + Rational64::one(), reason);
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
    pub fn value(&self, term: TermId) -> Option<Rational64> {
        self.term_to_var.get(&term).map(|&var| {
            if self.is_integer {
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
                        Rational64::from_integer(real_val.to_integer() + 1)
                    } else {
                        Rational64::from_integer(real_val.ceil().to_integer())
                    }
                } else if dval.delta.is_negative() {
                    // x < r implies x <= floor(r) for integers
                    // If r is already an integer, we need r - 1
                    let real_val = dval.real;
                    if real_val.is_integer() {
                        Rational64::from_integer(real_val.to_integer() - 1)
                    } else {
                        Rational64::from_integer(real_val.floor().to_integer())
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
    #[must_use]
    pub fn fixed_value_with_reasons(&mut self, term: TermId) -> Option<(Rational64, Vec<TermId>)> {
        let v = self.value(term)?;
        let one = Rational64::from_integer(1);
        let mut reasons: Vec<TermId> = Vec::new();

        // HIGH side: prove `term` cannot exceed `v`.
        self.push();
        if self.is_integer {
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
        if self.is_integer {
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
    fn tighten_bound(&self, bound: Rational64, is_upper: bool) -> Rational64 {
        if !self.is_integer {
            return bound;
        }

        // For upper bounds (<=), floor the value
        // For lower bounds (>=), ceiling the value
        if bound.is_integer() {
            bound
        } else if is_upper {
            // x <= 5.7 becomes x <= 5
            Rational64::from_integer(bound.floor().to_integer())
        } else {
            // x >= 2.3 becomes x >= 3
            Rational64::from_integer(bound.ceil().to_integer())
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
            Ok(()) => Ok(TheoryResult::Sat),
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
            num_vars: self.var_to_term.len(),
            num_reasons: self.reasons.len(),
            num_shared_equalities: self.shared_equalities.len(),
        });
        self.simplex.push();
    }

    fn pop(&mut self) {
        if let Some(state) = self.context_stack.pop() {
            // Roll back the FORWARD map `term_to_var` too, not just the reverse
            // `var_to_term`. Every term interned in this scope holds a simplex
            // `VarId >= state.num_vars`; `simplex.pop()` below discards those
            // variables, so a stale `term_to_var` entry would make a later
            // `intern()` of the same term return a VarId the simplex no longer
            // has — and the next constraint/pivot on it indexes the simplex
            // arrays out of bounds (a hard panic on otherwise-valid push/pop
            // input, surfaced by the persistent OxiZ delegation replaying a
            // prelude-scale multi-`(push)` session). The popped scope's terms
            // are exactly `var_to_term[state.num_vars..]`.
            for &term in &self.var_to_term[state.num_vars..] {
                self.term_to_var.remove(&term);
            }
            self.var_to_term.truncate(state.num_vars);
            self.reasons.truncate(state.num_reasons);
            self.reason_counter = state.num_reasons as u32;
            self.shared_equalities.truncate(state.num_shared_equalities);
            self.simplex.pop();
        }
    }

    fn reset(&mut self) {
        self.simplex.reset();
        self.term_to_var.clear();
        self.var_to_term.clear();
        self.reason_counter = 0;
        self.reasons.clear();
        self.context_stack.clear();
        self.shared_equalities.clear();
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
        let lhs_var = self.term_to_var.get(&eq.lhs).copied();
        let rhs_var = self.term_to_var.get(&eq.rhs).copied();

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
            expr_le.add_term(lhs, Rational64::one());
            expr_le.add_term(rhs, -Rational64::one());
            // lhs - rhs <= 0
            self.simplex.add_le(expr_le, reason_id);

            // Build expression: rhs - lhs
            let mut expr_ge = LinExpr::new();
            expr_ge.add_term(rhs, Rational64::one());
            expr_ge.add_term(lhs, -Rational64::one());
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
        self.term_to_var.contains_key(&term)
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
        let num_interface_terms = self.var_to_term.len();
        if num_interface_terms < 2 {
            return self.shared_equalities.clone();
        }

        // Collect (delta_value, VarId, TermId) for all interned variables.
        let mut candidates: Vec<(super::delta::DeltaRational, VarId, TermId)> = self
            .var_to_term
            .iter()
            .enumerate()
            .filter_map(|(idx, &term)| {
                // term_to_var maps TermId → VarId; we stored in var_to_term in order
                let var = self.term_to_var.get(&term).copied()?;
                let _ = idx; // suppress warning
                let dval = self.simplex.delta_value(var);
                Some((dval, var, term))
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
                    expr.add_term(var_x, Rational64::one());
                    expr.add_term(var_y, -Rational64::one());
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
                    expr.add_term(var_y, Rational64::one());
                    expr.add_term(var_x, -Rational64::one());
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
            &[(x, Rational64::one())],
            Rational64::from_integer(0),
            reason,
        );

        // y >= 0
        solver.assert_ge(
            &[(y, Rational64::one())],
            Rational64::from_integer(0),
            reason,
        );

        // x + y <= 10
        solver.assert_le(
            &[(x, Rational64::one()), (y, Rational64::one())],
            Rational64::from_integer(10),
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
        solver.assert_ge(&[(x, Rational64::one())], Rational64::from_integer(5), ge);
        solver.assert_le(&[(x, Rational64::one())], Rational64::from_integer(5), le);
        assert!(matches!(solver.check().unwrap(), TheoryResult::Sat));

        // No-leak baseline.
        let reasons_before = solver.reasons.len();

        let fixed = solver.fixed_value_with_reasons(x);
        assert!(fixed.is_some(), "x is pinned to 5 by its two bounds");
        let (v, rs) = fixed.unwrap();
        assert_eq!(v, Rational64::from_integer(5));
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
        solver.assert_ge(&[(y, Rational64::one())], Rational64::from_integer(0), gy);
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
            &[(x, Rational64::one())],
            Rational64::from_integer(10),
            reason,
        );

        // x <= 5
        solver.assert_le(
            &[(x, Rational64::one())],
            Rational64::from_integer(5),
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
            &[(x, Rational64::one())],
            Rational64::from_integer(0),
            reason,
        );

        // x < 10 (strict)
        solver.assert_lt(
            &[(x, Rational64::one())],
            Rational64::from_integer(10),
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
            &[(x, Rational64::one())],
            Rational64::from_integer(5),
            reason,
        );

        // x < 5 (strict) - should be unsatisfiable with x >= 5
        solver.assert_lt(
            &[(x, Rational64::one())],
            Rational64::from_integer(5),
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
                (x, Rational64::from_integer(2)),
                (y, Rational64::from_integer(4)),
            ],
            Rational64::from_integer(10),
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
        expr.add_term(0, Rational64::from_integer(-3));
        expr.add_term(1, Rational64::from_integer(2));

        solver.normalize_expr(&mut expr);

        // After normalization, first coefficient should be positive
        if let Some((_, c)) = expr.terms.first() {
            assert!(c > &Rational64::zero());
        }
    }

    #[test]
    fn test_gcd_computation() {
        assert_eq!(gcd_i64(12, 8), 4);
        assert_eq!(gcd_i64(15, 25), 5);
        assert_eq!(gcd_i64(7, 13), 1);
        assert_eq!(gcd_i64(0, 5), 5);
        assert_eq!(gcd_i64(5, 0), 5);
        assert_eq!(gcd_i64(-12, 8), 4);
        assert_eq!(gcd_i64(12, -8), 4);
    }

    #[test]
    fn test_bound_tightening_lia() {
        let solver = ArithSolver::lia();

        // Upper bound tightening: x <= 5.7 -> x <= 5
        let tightened = solver.tighten_bound(Rational64::new(57, 10), true);
        assert_eq!(tightened, Rational64::from_integer(5));

        // Lower bound tightening: x >= 2.3 -> x >= 3
        let tightened = solver.tighten_bound(Rational64::new(23, 10), false);
        assert_eq!(tightened, Rational64::from_integer(3));

        // Integer bounds don't change
        let tightened = solver.tighten_bound(Rational64::from_integer(5), true);
        assert_eq!(tightened, Rational64::from_integer(5));
    }

    #[test]
    fn test_bound_tightening_lra() {
        let solver = ArithSolver::lra();

        // No tightening for real arithmetic
        let bound = Rational64::new(57, 10);
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
            &[(x, Rational64::one())],
            Rational64::from_integer(5),
            reason,
        );

        // x < 6 (for integers, this becomes x <= 5)
        solver.assert_lt(
            &[(x, Rational64::one())],
            Rational64::from_integer(6),
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
            &[(x, Rational64::one())],
            Rational64::from_integer(5),
            reason,
        );

        // x < 6
        solver.assert_lt(
            &[(x, Rational64::one())],
            Rational64::from_integer(6),
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
            &[(x, Rational64::one())],
            Rational64::from_integer(5),
            reason,
        );

        // x < 6 (becomes x <= 5)
        solver.assert_lt(
            &[(x, Rational64::one())],
            Rational64::from_integer(6),
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

        // Intern both so they appear in var_to_term.
        solver.intern(x);
        solver.intern(y);

        // x <= y
        solver.assert_le(
            &[(x, Rational64::one()), (y, -Rational64::one())],
            Rational64::from_integer(0),
            reason,
        );
        // y <= x
        solver.assert_le(
            &[(y, Rational64::one()), (x, -Rational64::one())],
            Rational64::from_integer(0),
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
            &[(x, Rational64::one()), (y, -Rational64::one())],
            Rational64::from_integer(0),
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
            &[(x, Rational64::one()), (y, -Rational64::one())],
            Rational64::from_integer(0),
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
}
