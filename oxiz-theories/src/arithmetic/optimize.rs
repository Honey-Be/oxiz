//! Optimization Support for Linear Real Arithmetic (LRA)
//!
//! Implements maximize and minimize operations for LRA using the Simplex tableau.

use super::simplex::{LinExpr, Simplex, SimplexOptStatus, VarId};
#[allow(unused_imports)]
use crate::prelude::*;
use crate::ArithRat;
use num_traits::{One, Zero};
use oxiz_core::error::Result;

/// Optimization objective
#[derive(Debug, Clone)]
pub enum Objective {
    /// Maximize the objective function
    Maximize(LinExpr),
    /// Minimize the objective function
    Minimize(LinExpr),
}

/// Optimization result
#[derive(Debug, Clone, PartialEq)]
pub enum OptResult {
    /// Optimal solution found with the optimal value
    Optimal(ArithRat),
    /// Problem is unbounded
    Unbounded,
    /// Problem is infeasible
    Infeasible,
    /// Unknown (timeout or other)
    Unknown,
}

/// LRA Optimizer using Simplex
#[derive(Debug)]
pub struct LraOptimizer {
    /// Underlying Simplex solver
    simplex: Simplex,
    /// Objective function
    objective: Option<Objective>,
    /// Optimal value (if found)
    optimal_value: Option<ArithRat>,
}

impl Default for LraOptimizer {
    fn default() -> Self {
        Self::new()
    }
}

impl LraOptimizer {
    /// Create a new LRA optimizer
    #[must_use]
    pub fn new() -> Self {
        Self {
            simplex: Simplex::new(),
            objective: None,
            optimal_value: None,
        }
    }

    /// Create a new variable
    pub fn new_var(&mut self) -> VarId {
        self.simplex.new_var()
    }

    /// Add a constraint: expr <= 0
    pub fn add_le(&mut self, expr: LinExpr, reason: u32) {
        self.simplex.add_le(expr, reason);
    }

    /// Add a constraint: expr >= 0
    pub fn add_ge(&mut self, expr: LinExpr, reason: u32) {
        self.simplex.add_ge(expr, reason);
    }

    /// Add an equality constraint: expr = 0
    pub fn add_eq(&mut self, expr: LinExpr, reason: u32) {
        self.simplex.add_eq(expr, reason);
    }

    /// Set the optimization objective
    pub fn set_objective(&mut self, objective: Objective) {
        self.objective = Some(objective);
    }

    /// Optimize the objective function
    pub fn optimize(&mut self) -> Result<OptResult> {
        // First check if the constraints are feasible
        match self.simplex.check() {
            Ok(()) => {
                // Feasible, proceed with optimization
                if let Some(obj) = self.objective.clone() {
                    self.optimize_objective(&obj)
                } else {
                    // No objective, just report feasible
                    Ok(OptResult::Optimal(ArithRat::zero()))
                }
            }
            Err(_) => {
                // Infeasible
                Ok(OptResult::Infeasible)
            }
        }
    }

    fn optimize_objective(&mut self, objective: &Objective) -> Result<OptResult> {
        match objective {
            Objective::Maximize(expr) => {
                // To maximize f, we minimize -f
                let mut neg_expr = expr.clone();
                neg_expr.negate();
                self.optimize_min(&neg_expr).map(|result| match result {
                    OptResult::Optimal(v) => OptResult::Optimal(-v),
                    other => other,
                })
            }
            Objective::Minimize(expr) => self.optimize_min(expr),
        }
    }

    fn optimize_min(&mut self, expr: &LinExpr) -> Result<OptResult> {
        match self.simplex.optimize_linexpr(expr) {
            SimplexOptStatus::Optimal(v) => {
                self.optimal_value = Some(v);
                Ok(OptResult::Optimal(v))
            }
            SimplexOptStatus::Unbounded => Ok(OptResult::Unbounded),
            SimplexOptStatus::Infeasible => Ok(OptResult::Infeasible),
            SimplexOptStatus::Unknown => Ok(OptResult::Unknown),
        }
    }

    /// Get the optimal value (if optimization succeeded)
    #[must_use]
    pub fn optimal_value(&self) -> Option<ArithRat> {
        self.optimal_value
    }

    /// Get the value of a variable in the optimal solution
    #[must_use]
    pub fn value(&self, var: VarId) -> ArithRat {
        self.simplex.value(var)
    }

    /// Reset the optimizer
    pub fn reset(&mut self) {
        self.simplex.reset();
        self.objective = None;
        self.optimal_value = None;
    }
}

/// Objective function builder
#[derive(Debug, Default)]
pub struct ObjectiveBuilder {
    /// Linear expression being built
    expr: LinExpr,
}

impl ObjectiveBuilder {
    /// Create a new objective builder
    #[must_use]
    pub fn new() -> Self {
        Self {
            expr: LinExpr::new(),
        }
    }

    /// Add a term to the objective
    pub fn add_term(&mut self, var: VarId, coef: ArithRat) -> &mut Self {
        self.expr.add_term(var, coef);
        self
    }

    /// Add a constant to the objective
    pub fn add_constant(&mut self, c: ArithRat) -> &mut Self {
        self.expr.add_constant(c);
        self
    }

    /// Build a maximize objective
    #[must_use]
    pub fn maximize(self) -> Objective {
        Objective::Maximize(self.expr)
    }

    /// Build a minimize objective
    #[must_use]
    pub fn minimize(self) -> Objective {
        Objective::Minimize(self.expr)
    }
}

/// Optimization Model for easier API
#[derive(Debug)]
pub struct OptModel {
    /// The optimizer
    optimizer: LraOptimizer,
    /// Variables created
    vars: Vec<VarId>,
}

impl Default for OptModel {
    fn default() -> Self {
        Self::new()
    }
}

impl OptModel {
    /// Create a new optimization model
    #[must_use]
    pub fn new() -> Self {
        Self {
            optimizer: LraOptimizer::new(),
            vars: Vec::new(),
        }
    }

    /// Add a new variable
    pub fn new_var(&mut self) -> VarId {
        let var = self.optimizer.new_var();
        self.vars.push(var);
        var
    }

    /// Add multiple variables
    pub fn new_vars(&mut self, count: usize) -> Vec<VarId> {
        (0..count).map(|_| self.new_var()).collect()
    }

    /// Set variable bounds: lower <= var <= upper
    pub fn set_bounds(&mut self, var: VarId, lower: Option<ArithRat>, upper: Option<ArithRat>) {
        if let Some(lb) = lower {
            let mut expr = LinExpr::new();
            expr.add_term(var, ArithRat::one());
            expr.add_constant(-lb);
            self.optimizer.add_ge(expr, 0);
        }

        if let Some(ub) = upper {
            let mut expr = LinExpr::new();
            expr.add_term(var, ArithRat::one());
            expr.add_constant(-ub);
            self.optimizer.add_le(expr, 0);
        }
    }

    /// Add a linear constraint
    pub fn add_constraint(&mut self, expr: LinExpr, sense: ConstraintSense) {
        match sense {
            ConstraintSense::Le => self.optimizer.add_le(expr, 0),
            ConstraintSense::Ge => self.optimizer.add_ge(expr, 0),
            ConstraintSense::Eq => self.optimizer.add_eq(expr, 0),
        }
    }

    /// Set the objective function
    pub fn set_objective(&mut self, objective: Objective) {
        self.optimizer.set_objective(objective);
    }

    /// Optimize the model
    pub fn optimize(&mut self) -> Result<OptResult> {
        self.optimizer.optimize()
    }

    /// Get the value of a variable
    #[must_use]
    pub fn value(&self, var: VarId) -> ArithRat {
        self.optimizer.value(var)
    }

    /// Get the optimal objective value
    #[must_use]
    pub fn optimal_value(&self) -> Option<ArithRat> {
        self.optimizer.optimal_value()
    }
}

/// Constraint sense (direction)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ConstraintSense {
    /// Less than or equal (<=)
    Le,
    /// Greater than or equal (>=)
    Ge,
    /// Equal (=)
    Eq,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_objective_builder() {
        let mut builder = ObjectiveBuilder::new();
        let x: VarId = 0;
        let y: VarId = 1;

        builder.add_term(x, ArithRat::from_integer(2));
        builder.add_term(y, ArithRat::from_integer(3));
        builder.add_constant(ArithRat::from_integer(-5));

        let obj = builder.maximize();

        assert!(matches!(obj, Objective::Maximize(_)));
    }

    #[test]
    fn test_optimizer_basic() {
        let mut opt = LraOptimizer::new();

        let x = opt.new_var();
        let y = opt.new_var();

        // x >= 0
        let mut expr1 = LinExpr::new();
        expr1.add_term(x, ArithRat::one());
        opt.add_ge(expr1, 0);

        // y >= 0
        let mut expr2 = LinExpr::new();
        expr2.add_term(y, ArithRat::one());
        opt.add_ge(expr2, 0);

        // x + y <= 10
        let mut expr3 = LinExpr::new();
        expr3.add_term(x, ArithRat::one());
        expr3.add_term(y, ArithRat::one());
        expr3.add_constant(-ArithRat::from_integer(10));
        opt.add_le(expr3, 0);

        // Maximize x + 2y
        let mut obj_expr = LinExpr::new();
        obj_expr.add_term(x, ArithRat::one());
        obj_expr.add_term(y, ArithRat::from_integer(2));

        opt.set_objective(Objective::Maximize(obj_expr));

        let result = opt.optimize().expect("optimization should succeed");

        assert!(matches!(result, OptResult::Optimal(_) | OptResult::Unknown));
    }

    #[test]
    fn test_opt_model() {
        let mut model = OptModel::new();

        let x = model.new_var();
        let y = model.new_var();

        // Set bounds: 0 <= x, y <= 10
        model.set_bounds(
            x,
            Some(ArithRat::zero()),
            Some(ArithRat::from_integer(10)),
        );
        model.set_bounds(
            y,
            Some(ArithRat::zero()),
            Some(ArithRat::from_integer(10)),
        );

        // x + y <= 8
        let mut constraint = LinExpr::new();
        constraint.add_term(x, ArithRat::one());
        constraint.add_term(y, ArithRat::one());
        constraint.add_constant(-ArithRat::from_integer(8));
        model.add_constraint(constraint, ConstraintSense::Le);

        // Maximize 3x + 4y
        let mut obj = ObjectiveBuilder::new();
        obj.add_term(x, ArithRat::from_integer(3));
        obj.add_term(y, ArithRat::from_integer(4));
        model.set_objective(obj.maximize());

        let result = model.optimize().expect("should optimize");

        assert!(matches!(result, OptResult::Optimal(_) | OptResult::Unknown));
    }

    #[test]
    fn test_infeasible_model() {
        let mut model = OptModel::new();

        let x = model.new_var();

        // x >= 10
        let mut expr1 = LinExpr::new();
        expr1.add_term(x, ArithRat::one());
        expr1.add_constant(-ArithRat::from_integer(10));
        model.add_constraint(expr1, ConstraintSense::Ge);

        // x <= 5 (contradicts x >= 10)
        let mut expr2 = LinExpr::new();
        expr2.add_term(x, ArithRat::one());
        expr2.add_constant(-ArithRat::from_integer(5));
        model.add_constraint(expr2, ConstraintSense::Le);

        let result = model.optimize().expect("should return infeasible");

        assert!(matches!(result, OptResult::Infeasible));
    }

    // ---- Optimization correctness tests ----

    /// Maximize 3x + 4y subject to: x + y <= 8, x >= 0, y >= 0.
    /// Optimal: y = 8, x = 0 → value = 32.
    #[test]
    fn test_maximize_correct_value() {
        let mut model = OptModel::new();
        let x = model.new_var();
        let y = model.new_var();

        // x >= 0
        model.set_bounds(x, Some(ArithRat::zero()), None);
        // y >= 0
        model.set_bounds(y, Some(ArithRat::zero()), None);
        // x + y <= 8
        let mut c = LinExpr::new();
        c.add_term(x, ArithRat::one());
        c.add_term(y, ArithRat::one());
        c.add_constant(-ArithRat::from_integer(8));
        model.add_constraint(c, ConstraintSense::Le);

        // Maximize 3x + 4y
        let mut obj = ObjectiveBuilder::new();
        obj.add_term(x, ArithRat::from_integer(3));
        obj.add_term(y, ArithRat::from_integer(4));
        model.set_objective(obj.maximize());

        let result = model.optimize().expect("should optimize");
        match result {
            OptResult::Optimal(v) => {
                assert_eq!(
                    v,
                    ArithRat::from_integer(32),
                    "Expected optimal 32, got {}",
                    v
                );
            }
            other => panic!("Expected Optimal(32), got {:?}", other),
        }
    }

    /// Minimize 2x + 3y subject to: x + y >= 5, x >= 0, y >= 0.
    /// Optimal: x = 5, y = 0 → value = 10.
    #[test]
    fn test_minimize_correct_value() {
        let mut model = OptModel::new();
        let x = model.new_var();
        let y = model.new_var();

        // x >= 0
        model.set_bounds(x, Some(ArithRat::zero()), None);
        // y >= 0
        model.set_bounds(y, Some(ArithRat::zero()), None);
        // x + y >= 5
        let mut c = LinExpr::new();
        c.add_term(x, ArithRat::one());
        c.add_term(y, ArithRat::one());
        c.add_constant(-ArithRat::from_integer(5));
        model.add_constraint(c, ConstraintSense::Ge);

        // Minimize 2x + 3y
        let mut obj = ObjectiveBuilder::new();
        obj.add_term(x, ArithRat::from_integer(2));
        obj.add_term(y, ArithRat::from_integer(3));
        model.set_objective(obj.minimize());

        let result = model.optimize().expect("should optimize");
        match result {
            OptResult::Optimal(v) => {
                assert_eq!(
                    v,
                    ArithRat::from_integer(10),
                    "Expected optimal 10, got {}",
                    v
                );
            }
            other => panic!("Expected Optimal(10), got {:?}", other),
        }
    }

    /// Maximize x with no upper bound on x → unbounded.
    #[test]
    fn test_maximize_unbounded() {
        let mut model = OptModel::new();
        let x = model.new_var();

        // x >= 0 only, no upper bound
        model.set_bounds(x, Some(ArithRat::zero()), None);

        // Maximize x
        let mut obj = ObjectiveBuilder::new();
        obj.add_term(x, ArithRat::one());
        model.set_objective(obj.maximize());

        let result = model.optimize().expect("should run");
        assert!(
            matches!(result, OptResult::Unbounded),
            "Expected Unbounded, got {:?}",
            result
        );
    }

    /// Infeasible system → OptResult::Infeasible.
    #[test]
    fn test_optimize_infeasible_explicit() {
        let mut model = OptModel::new();
        let x = model.new_var();

        // x >= 10 AND x <= 5 — contradictory
        model.set_bounds(
            x,
            Some(ArithRat::from_integer(10)),
            Some(ArithRat::from_integer(5)),
        );

        let mut obj = ObjectiveBuilder::new();
        obj.add_term(x, ArithRat::one());
        model.set_objective(obj.maximize());

        let result = model.optimize().expect("should detect infeasibility");
        assert!(
            matches!(result, OptResult::Infeasible),
            "Expected Infeasible, got {:?}",
            result
        );
    }
}
