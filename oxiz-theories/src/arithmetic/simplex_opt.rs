//! Optimization extension for the Simplex solver.
//!
//! Provides `optimize_linexpr` for minimizing a linear expression over the
//! current feasible region using the primal simplex method with Bland's rule.

use super::delta::DeltaRational;
use super::simplex::{LinExpr, Simplex, VarId};
use crate::ArithRat;
use num_traits::Zero;

/// Status of a simplex optimization call.
#[derive(Debug, Clone, PartialEq)]
pub enum SimplexOptStatus {
    /// Optimal value found.
    Optimal(ArithRat),
    /// Objective is unbounded (can be improved without limit).
    Unbounded,
    /// The constraint set is infeasible.
    Infeasible,
    /// Could not determine (e.g., pivot limit hit).
    Unknown,
}

impl Simplex {
    /// Evaluate a linear expression at the current assignment.
    pub(super) fn eval_linexpr(&self, obj: &LinExpr) -> ArithRat {
        let mut val = obj.constant;
        for (var, coef) in &obj.terms {
            let idx = *var as usize;
            if idx < self.assignment_len() {
                val += self.assignment_at(idx) * *coef;
            }
        }
        val
    }

    /// Compute the reduced objective coefficient for a non-basic variable.
    ///
    /// After substituting all basic variables, the objective becomes:
    ///
    ///   obj_val = constant + Σ over non-basic v of (reduced_coef(v) · v)
    ///
    /// where:
    ///
    ///   reduced_coef(v) = obj_coef(v)
    ///                   + Σ over basic b of (obj_coef(b) · tableau_coef(b, v))
    pub(super) fn reduced_obj_coef(&self, obj: &LinExpr, nonbasic_var: VarId) -> ArithRat {
        // Direct coefficient of this variable in obj.
        let direct = obj
            .terms
            .iter()
            .find(|(v, _)| *v == nonbasic_var)
            .map(|(_, c)| *c)
            .unwrap_or_else(ArithRat::zero);

        // Indirect contribution via basic variables.
        let mut indirect = ArithRat::zero();
        for (basic_var, row) in self.tableau_iter() {
            let obj_coef = obj
                .terms
                .iter()
                .find(|(v, _)| v == basic_var)
                .map(|(_, c)| *c)
                .unwrap_or_else(ArithRat::zero);
            if obj_coef.is_zero() {
                continue;
            }
            let row_coef = row
                .terms
                .iter()
                .find(|(v, _)| *v == nonbasic_var)
                .map(|(_, c)| *c)
                .unwrap_or_else(ArithRat::zero);
            indirect += obj_coef * row_coef;
        }

        direct + indirect
    }

    /// Minimize a linear expression over the current feasible region.
    ///
    /// The solver must already be in a feasible state (after `check()`) before
    /// calling this method.
    ///
    /// Returns:
    /// - [`SimplexOptStatus::Optimal`]`(v)` — minimum value `v` was found.
    /// - [`SimplexOptStatus::Unbounded`] — objective can decrease without bound.
    /// - [`SimplexOptStatus::Infeasible`] — the constraint set is infeasible.
    /// - [`SimplexOptStatus::Unknown`] — pivot limit hit; result undetermined.
    ///
    /// Uses Bland's rule throughout to prevent cycling.
    pub fn optimize_linexpr(&mut self, obj: &LinExpr) -> SimplexOptStatus {
        // Phase 0: verify feasibility and find a primal feasible point.
        if self.check().is_err() {
            return SimplexOptStatus::Infeasible;
        }

        // Phase 1: primal simplex to minimise obj over the feasible region.
        //
        // Reduced cost of non-basic x_j:
        //   c̄_j = c_j + Σ_{b ∈ basic} c_b · a_{b,j}
        // where a_{b,j} is the coefficient of x_j in row b.
        //
        // If c̄_j < 0 and x_j can increase → entering (increasing reduces obj).
        // If c̄_j > 0 and x_j can decrease → entering (decreasing reduces obj).
        //
        // Bland's rule: among all improving variables, choose the one with the
        // smallest VarId index (prevents cycling).

        let mut result = SimplexOptStatus::Unknown;

        'outer: for _ in 0..self.max_pivots() {
            self.update_assignment();

            let num_vars = self.assignment_len();

            // Find entering variable (Bland's rule: ascending VarId scan).
            let mut enter_var: Option<VarId> = None;
            let mut enter_decrease: bool = false;

            for v_id in 0..num_vars as VarId {
                let v_idx = v_id as usize;
                if self.is_basic(v_idx) {
                    continue;
                }

                let rc = self.reduced_obj_coef(obj, v_id);
                let can_inc = self.can_increase(v_id);
                let can_dec = self.can_decrease(v_id);

                let is_entering =
                    (rc < ArithRat::zero() && can_inc) || (rc > ArithRat::zero() && can_dec);

                if is_entering {
                    enter_var = Some(v_id);
                    enter_decrease = rc > ArithRat::zero();
                    break;
                }
            }

            let (enter, decrease_it) = match enter_var {
                None => {
                    result = SimplexOptStatus::Optimal(self.eval_linexpr(obj));
                    break 'outer;
                }
                Some(v) => (v, enter_decrease),
            };

            // Ratio test: find the leaving variable.
            let mut leaving: Option<VarId> = None;
            let mut best_ratio: Option<ArithRat> = None;

            let basic_vars: Vec<VarId> = self.tableau_keys().collect();

            for basic_var in &basic_vars {
                let a = match self.tableau_coef_of(*basic_var, enter) {
                    Some(c) => c,
                    None => continue,
                };

                let bv_idx = *basic_var as usize;
                let bv_val = self.assignment_real_at(bv_idx);
                let eff = if decrease_it { -a } else { a };

                let ratio = if eff > ArithRat::zero() {
                    self.upper_real_at(bv_idx).map(|hi| {
                        let gap = hi - bv_val;
                        if gap >= ArithRat::zero() {
                            gap / eff
                        } else {
                            ArithRat::zero()
                        }
                    })
                } else if eff < ArithRat::zero() {
                    self.lower_real_at(bv_idx).map(|lo| {
                        let gap = bv_val - lo;
                        if gap >= ArithRat::zero() {
                            gap / (-eff)
                        } else {
                            ArithRat::zero()
                        }
                    })
                } else {
                    continue;
                };

                if let Some(r) = ratio {
                    let is_better = match best_ratio {
                        None => true,
                        Some(best) => {
                            r < best || (r == best && *basic_var < leaving.unwrap_or(VarId::MAX))
                        }
                    };
                    if is_better {
                        best_ratio = Some(r);
                        leaving = Some(*basic_var);
                    }
                }
            }

            // Check enter's own bound.
            let enter_idx = enter as usize;
            let enter_val = self.assignment_real_at(enter_idx);
            let enter_own_limit = if decrease_it {
                self.lower_real_at(enter_idx).map(|lo| {
                    let gap = enter_val - lo;
                    if gap >= ArithRat::zero() {
                        gap
                    } else {
                        ArithRat::zero()
                    }
                })
            } else {
                self.upper_real_at(enter_idx).map(|hi| {
                    let gap = hi - enter_val;
                    if gap >= ArithRat::zero() {
                        gap
                    } else {
                        ArithRat::zero()
                    }
                })
            };

            if let Some(limit) = enter_own_limit {
                let is_better = match best_ratio {
                    None => true,
                    Some(best) => limit < best,
                };
                if is_better {
                    best_ratio = Some(limit);
                    leaving = None;
                }
            }

            match leaving {
                None if best_ratio.is_some() => {
                    // Enter variable hits its own bound; no pivot needed.
                    let new_val = if decrease_it {
                        self.lower_delta_at(enter_idx)
                            .unwrap_or_else(DeltaRational::zero)
                    } else {
                        self.upper_delta_at(enter_idx)
                            .unwrap_or_else(DeltaRational::zero)
                    };
                    self.set_assignment_at(enter_idx, new_val);
                    self.update_assignment();
                }
                None => {
                    result = SimplexOptStatus::Unbounded;
                    break 'outer;
                }
                Some(lv) => {
                    self.pivot(lv, enter);
                }
            }
        }

        if matches!(result, SimplexOptStatus::Unknown) {
            self.update_assignment();
            result = SimplexOptStatus::Optimal(self.eval_linexpr(obj));
        }

        result
    }
}
