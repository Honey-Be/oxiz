//! Model and unsat core building

#[allow(unused_imports)]
use crate::prelude::*;
use num_traits::ToPrimitive;
use oxiz_core::ast::{TermId, TermKind, TermManager};
use oxiz_theories::ArithRat;

use super::Solver;
use super::types::Constraint;
use super::types::{Model, UnsatCore};

/// Narrow an `ArithRat` (= `Ratio<i128>`, the LRA/LIA core's rational) model
/// value back to oxiz-core's `RealConst` rational (`Rational64`) so it can be
/// stored as a `RealConst` term.
///
/// This is a MODEL-OUTPUT boundary only — it runs after the verdict is decided,
/// on a satisfying assignment, so it can never change a sat/unsat result. It
/// narrows EXACTLY when both numerator and denominator fit `i64` (the universal
/// case for any model derived from 64-bit SMT-LIB literals). For the
/// astronomically rare value whose reduced numer/denom exceeds `i64`, it falls
/// back to the (necessarily approximate) integer part — never a silent wrap.
fn narrow_arith_to_real64(r: ArithRat) -> num_rational::Rational64 {
    match (i64::try_from(*r.numer()), i64::try_from(*r.denom())) {
        (Ok(n), Ok(d)) => num_rational::Rational64::new(n, d),
        // Out of `i64` range (model value beyond what `RealConst` can hold):
        // approximate by the integer part. `to_integer()` truncates toward zero;
        // clamp to `i64` so the display value is well-defined. This is reachable
        // only on adversarial, i64-overflowing bounds and only affects the
        // printed model, not the (already sound) verdict.
        _ => num_rational::Rational64::from_integer(
            r.to_integer().clamp(i128::from(i64::MIN), i128::from(i64::MAX)) as i64,
        ),
    }
}

impl Solver {
    pub(super) fn build_model(&mut self, manager: &mut TermManager) {
        let mut model = Model::new();
        let sat_model = self.sat.model();

        // Get boolean values from SAT model
        for (&term, &var) in &self.term_to_var {
            let val = sat_model.get(var.index()).copied();
            if let Some(v) = val {
                let bool_val = if v.is_true() {
                    manager.mk_true()
                } else if v.is_false() {
                    manager.mk_false()
                } else {
                    continue;
                };
                model.set(term, bool_val);
            }
        }

        // Extract values from equality constraints (e.g., x = 5)
        // This handles cases where a variable is equated to a constant
        for (&var, constraint) in &self.var_to_constraint {
            // Check if the equality is assigned true in the SAT model
            let is_true = sat_model
                .get(var.index())
                .copied()
                .is_some_and(|v| v.is_true());

            if !is_true {
                continue;
            }

            if let Constraint::Eq(lhs, rhs) = constraint {
                // Check if one side is a tracked variable and the other is a constant.
                // Also handle Apply terms (uninterpreted function applications) that are
                // not in arith_terms due to the restriction on Apply terms with arith args.
                let lhs_is_apply = manager
                    .get(*lhs)
                    .is_some_and(|t| matches!(t.kind, TermKind::Apply { .. }));
                let rhs_is_apply = manager
                    .get(*rhs)
                    .is_some_and(|t| matches!(t.kind, TermKind::Apply { .. }));
                let (var_term, const_term) = if self.arith_terms.contains(lhs)
                    || self.bv_terms.contains(lhs)
                    || lhs_is_apply
                {
                    (*lhs, *rhs)
                } else if self.arith_terms.contains(rhs)
                    || self.bv_terms.contains(rhs)
                    || rhs_is_apply
                {
                    (*rhs, *lhs)
                } else {
                    continue;
                };

                // Check if const_term is actually a constant
                let Some(const_term_data) = manager.get(const_term) else {
                    continue;
                };

                match &const_term_data.kind {
                    TermKind::IntConst(n) => {
                        if let Some(val) = n.to_i64() {
                            let value_term = manager.mk_int(val);
                            model.set(var_term, value_term);
                        }
                    }
                    TermKind::RealConst(r) => {
                        let value_term = manager.mk_real(*r);
                        model.set(var_term, value_term);
                    }
                    TermKind::BitVecConst { value, width } => {
                        if let Some(val) = value.to_u64() {
                            let value_term = manager.mk_bitvec(val, *width);
                            model.set(var_term, value_term);
                        }
                    }
                    _ => {}
                }
            }
        }

        // Get arithmetic values from theory solver.
        // #353 — materialize the δ-rational model ONCE. The raw `value()` returns
        // only the REAL part, which collapses a strict inequality `x > y` (encoded
        // `x − y ≥ δ`, with the assignment sitting at `x − y = δ`) to `x = y`, so
        // the extracted model VIOLATES a constraint the solver proved satisfiable.
        // `materialize()` picks a single δ₀ > 0 keeping every bound satisfied and
        // returns a concrete real value per simplex variable. An Int-sorted term
        // instead takes the δ-aware integer rounding (its SORT — not the solver's
        // LIA/LRA mode — decides its value must be integral); the
        // sort-vs-denominator distinction below still holds: a Real-sorted term is
        // always a RealConst even when its value is an integer ratio (e.g. 2/1),
        // else mixed comparisons like `(f(c) <= 1.0)` go symbolic.
        let materialized = self.arith.materialize();
        for &term in &self.arith_terms {
            // Don't overwrite if already set (e.g., from equality extraction above)
            if model.get(term).is_some() {
                continue;
            }

            let is_int_sort = manager
                .get(term)
                .map(|t| t.sort == manager.sorts.int_sort)
                .unwrap_or(true);

            let value_term = if is_int_sort {
                match self.arith.rounded_int_value(term) {
                    Some(n) => manager.mk_int(n),
                    None => manager.mk_int(0i64),
                }
            } else {
                match self
                    .arith
                    .var_index(term)
                    .and_then(|i| materialized.get(i).copied())
                {
                    Some(r) => manager.mk_real(narrow_arith_to_real64(r)),
                    None => manager.mk_real(num_rational::Rational64::from_integer(0)),
                }
            };
            model.set(term, value_term);
        }

        // Get bitvector values - check ArithSolver first (for BV comparisons),
        // then BvSolver (for BV arithmetic/bit operations)
        for &term in &self.bv_terms {
            // Don't overwrite if already set (shouldn't happen, but be safe)
            if model.get(term).is_some() {
                continue;
            }

            // Get the bitvector width from the term's sort
            let width = manager
                .get(term)
                .and_then(|t| manager.sorts.get(t.sort))
                .and_then(|s| s.bitvec_width())
                .unwrap_or(64);

            // Prefer the BvSolver's bit-blasted value when the term was actually
            // bit-blasted (`get_value` returns `Some` only for terms with bit
            // variables). The bit-level model is authoritative for BV arithmetic
            // and bit operations, and — crucially — it carries genuine
            // counterexample witnesses (e.g. `a != b` in `not(bvadd a b = bvsub
            // a b)`). Falling back to ArithSolver covers BV terms that were
            // tracked only as bounded integers (pure comparison constraints).
            if let Some(bv_value) = self.bv.get_value(term) {
                let value_term = manager.mk_bitvec(bv_value, width);
                model.set(term, value_term);
            } else if let Some(arith_value) = self.arith.value(term) {
                let int_value = arith_value.to_integer();
                let value_term = manager.mk_bitvec(int_value, width);
                model.set(term, value_term);
            } else {
                // If no value from either solver, use default value (0)
                // This handles unconstrained BV variables
                let value_term = manager.mk_bitvec(0i64, width);
                model.set(term, value_term);
            }
        }

        self.model = Some(model);
    }

    /// Build unsat core for trivial conflicts (assertion of false)
    pub(super) fn build_unsat_core_trivial_false(&mut self) {
        if !self.produce_unsat_cores {
            self.unsat_core = None;
            return;
        }

        // Find all assertions that are trivially false
        let mut core = UnsatCore::new();

        for (i, &term) in self.assertions.iter().enumerate() {
            if term == TermId::new(1) {
                // This is a false assertion
                core.indices.push(i as u32);

                // Find the name if there is one
                if let Some(named) = self.named_assertions.iter().find(|na| na.index == i as u32)
                    && let Some(ref name) = named.name
                {
                    core.names.push(name.clone());
                }
            }
        }

        self.unsat_core = Some(core);
    }

    /// Build unsat core from SAT solver conflict analysis
    pub(super) fn build_unsat_core(&mut self) {
        if !self.produce_unsat_cores {
            self.unsat_core = None;
            return;
        }

        // Build unsat core from the named assertions
        // In assumption-based mode, we would use the failed assumptions from the SAT solver
        // For now, we use a heuristic approach based on the conflict analysis

        let mut core = UnsatCore::new();

        // If assumption_vars is populated, we can use assumption-based extraction
        if !self.assumption_vars.is_empty() {
            // Assumption-based core extraction
            // Get the failed assumptions from the SAT solver
            // Note: This requires SAT solver support for assumption tracking
            // For now, include all named assertions as a conservative approach
            for na in &self.named_assertions {
                core.indices.push(na.index);
                if let Some(ref name) = na.name {
                    core.names.push(name.clone());
                }
            }
        } else {
            // Fallback: include all named assertions
            // This provides a valid unsat core, though not necessarily minimal
            for na in &self.named_assertions {
                core.indices.push(na.index);
                if let Some(ref name) = na.name {
                    core.names.push(name.clone());
                }
            }
        }

        self.unsat_core = Some(core);
    }
}
