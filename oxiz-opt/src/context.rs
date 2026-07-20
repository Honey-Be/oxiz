//! Optimization context.
//!
//! This module provides the main interface for optimization modulo theories.
//! It integrates MaxSAT solving with SMT solving to support:
//! - Soft constraints with weights
//! - Objective function optimization (minimize/maximize)
//! - Multi-objective (Pareto) optimization
//!
//! Reference: Z3's `opt/opt_context.cpp`

use crate::maxsat::{MaxSatConfig, MaxSatError, MaxSatResult, Weight};
use crate::objective::{Objective, ObjectiveId, ObjectiveKind};
use crate::pareto::ParetoConfig;
use num_bigint::BigInt;
use num_integer::Integer as _;
use num_rational::BigRational;
use num_traits::Zero as _;
use oxiz_core::ast::{TermId, TermKind, TermManager};
use oxiz_solver::{OptimizationResult, Optimizer, Solver, SolverResult};
use rustc_hash::FxHashMap;
use thiserror::Error;

/// Errors that can occur during optimization
#[derive(Error, Debug)]
pub enum OptError {
    /// Hard constraints are unsatisfiable
    #[error("hard constraints unsatisfiable")]
    Unsatisfiable,
    /// No solution found within limits
    #[error("unknown (resource limit)")]
    Unknown,
    /// MaxSAT error
    #[error("maxsat error: {0}")]
    MaxSat(#[from] MaxSatError),
    /// Internal error
    #[error("internal error: {0}")]
    Internal(String),
}

/// Result of optimization
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum OptResult {
    /// Optimal solution found
    Optimal,
    /// Solution found but optimality not proven
    Satisfiable,
    /// No solution exists
    Unsatisfiable,
    /// Could not determine
    Unknown,
    /// Objective is unbounded (no finite optimum)
    Unbounded,
}

impl From<MaxSatResult> for OptResult {
    fn from(r: MaxSatResult) -> Self {
        match r {
            MaxSatResult::Optimal => OptResult::Optimal,
            MaxSatResult::Satisfiable => OptResult::Satisfiable,
            MaxSatResult::Unsatisfiable => OptResult::Unsatisfiable,
            MaxSatResult::Unknown => OptResult::Unknown,
        }
    }
}

impl std::fmt::Display for OptResult {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            OptResult::Optimal => write!(f, "optimal"),
            OptResult::Satisfiable => write!(f, "satisfiable"),
            OptResult::Unsatisfiable => write!(f, "unsatisfiable"),
            OptResult::Unknown => write!(f, "unknown"),
            OptResult::Unbounded => write!(f, "unbounded"),
        }
    }
}

/// Unique identifier for a soft constraint at the SMT level
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct SoftConstraintId(pub u32);

impl SoftConstraintId {
    /// Create a new soft constraint ID
    #[must_use]
    pub const fn new(id: u32) -> Self {
        Self(id)
    }

    /// Get the raw ID value
    #[must_use]
    pub const fn raw(self) -> u32 {
        self.0
    }
}

impl From<u32> for SoftConstraintId {
    fn from(id: u32) -> Self {
        Self(id)
    }
}

impl From<usize> for SoftConstraintId {
    fn from(id: usize) -> Self {
        Self(id as u32)
    }
}

impl From<SoftConstraintId> for u32 {
    fn from(id: SoftConstraintId) -> Self {
        id.0
    }
}

impl From<SoftConstraintId> for usize {
    fn from(id: SoftConstraintId) -> Self {
        id.0 as usize
    }
}

/// A soft constraint at the SMT level
#[derive(Debug, Clone)]
pub struct SoftConstraint {
    /// Unique identifier
    pub id: SoftConstraintId,
    /// The term representing the constraint
    pub term: TermId,
    /// Weight of this soft constraint
    pub weight: Weight,
    /// Group this constraint belongs to (for grouped optimization)
    pub group: Option<String>,
}

/// Configuration for optimization context
#[derive(Debug, Clone)]
pub struct OptConfig {
    /// MaxSAT configuration
    pub maxsat: MaxSatConfig,
    /// Pareto configuration
    pub pareto: ParetoConfig,
    /// Enable incremental optimization
    pub incremental: bool,
    /// Timeout in milliseconds (0 = no timeout)
    pub timeout_ms: u64,
    /// Verbose output
    pub verbose: bool,
}

impl Default for OptConfig {
    fn default() -> Self {
        Self {
            maxsat: MaxSatConfig::default(),
            pareto: ParetoConfig::default(),
            incremental: true,
            timeout_ms: 0,
            verbose: false,
        }
    }
}

/// Statistics from optimization
#[derive(Debug, Clone, Default)]
pub struct OptStats {
    /// Number of SAT/SMT calls
    pub solver_calls: u32,
    /// Number of cores extracted
    pub cores_extracted: u32,
    /// Number of objective bounds updated
    pub bound_updates: u32,
    /// Time spent in solving (ms)
    pub solve_time_ms: u64,
}

/// Model value types
#[derive(Debug, Clone, PartialEq)]
pub enum ModelValue {
    /// Boolean value
    Bool(bool),
    /// Integer value
    Int(BigInt),
    /// Rational value
    Rational(BigRational),
    /// Bitvector value (width, value)
    BitVec(u32, BigInt),
}

impl std::fmt::Display for ModelValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ModelValue::Bool(b) => write!(f, "{}", b),
            ModelValue::Int(n) => write!(f, "{}", n),
            ModelValue::Rational(r) => write!(f, "{}", r),
            ModelValue::BitVec(width, val) => {
                write!(f, "#b{:0width$b}", val, width = *width as usize)
            }
        }
    }
}

/// Convert a `TermId` value term (returned by `Model::eval`) into a `ModelValue`.
///
/// Returns `None` when the term is a non-constant (variable or compound expression
/// that could not be fully evaluated in the model).
fn term_id_to_model_value(val: TermId, tm: &TermManager) -> Option<ModelValue> {
    let t = tm.get(val)?;
    match &t.kind {
        TermKind::True => Some(ModelValue::Bool(true)),
        TermKind::False => Some(ModelValue::Bool(false)),
        TermKind::IntConst(n) => Some(ModelValue::Int(n.clone())),
        TermKind::RealConst(r) => {
            // Rational64 → BigRational
            let big_r = BigRational::new(BigInt::from(*r.numer()), BigInt::from(*r.denom()));
            Some(ModelValue::Rational(big_r))
        }
        TermKind::BitVecConst { value, width } => Some(ModelValue::BitVec(*width, value.clone())),
        _ => None,
    }
}

/// Least common multiple of two positive `BigInt`s (via `gcd`). Used to
/// find a common integer scale factor across every rational soft-
/// constraint weight's denominator — see `optimize_maxsmt`'s doc.
pub(crate) fn lcm_bigint(a: &BigInt, b: &BigInt) -> BigInt {
    if a.is_zero() || b.is_zero() {
        return BigInt::from(0);
    }
    (a / a.gcd(b)) * b
}

/// `weight`, scaled by `scale` and truncated to an exact integer —
/// EXACT (not lossy) for `Weight::Int` and for any `Weight::Rational`
/// whose denominator divides `scale` (guaranteed when `scale` was built
/// via `lcm_bigint` over every rational weight actually present, as
/// `optimize_maxsmt` does).
pub(crate) fn scaled_weight(weight: &Weight, scale: &BigInt) -> BigInt {
    match weight {
        Weight::Int(n) => n * scale,
        Weight::Rational(r) => {
            let scaled = r * BigRational::from(scale.clone());
            debug_assert!(scaled.is_integer(), "scale must be a multiple of every weight's denominator");
            scaled.to_integer()
        }
        Weight::Infinite => BigInt::from(i64::MAX / 2),
    }
}

/// Convert a `TermId` value term into a `Weight` (for storing objective bounds).
fn term_id_to_weight(val: TermId, tm: &TermManager) -> Weight {
    let Some(t) = tm.get(val) else {
        return Weight::Infinite;
    };
    match &t.kind {
        TermKind::IntConst(n) => Weight::Int(n.clone()),
        TermKind::RealConst(r) => {
            let big_r = BigRational::new(BigInt::from(*r.numer()), BigInt::from(*r.denom()));
            Weight::Rational(big_r)
        }
        _ => Weight::Infinite,
    }
}

/// Evaluate `term` (from `tm`) to an EXACT rational value using `model` for
/// atom lookups.
///
/// Used by `optimize_pareto` to recover each objective's real numeric value
/// from the chosen Pareto point's model: unlike `optimize_single_objective`
/// (which gets an exact `Weight` straight back from
/// `oxiz_solver::Optimizer::optimize`), `optimize_pareto` only gets a
/// variable-assignment model from `Optimizer::pareto_optimize` — nothing
/// evaluates a (possibly compound) objective TERM against it. A prior
/// version left `lower_bounds`/`upper_bounds` at their `Weight::Infinite`
/// `add_objective`-time placeholder for every multi-objective run, so
/// `get-objectives` always printed "∞" even for trivially bounded
/// objectives (see the fill-the-gap/maxsat fixup pass's P0 finding).
///
/// Deliberately narrow, matching `transplant_term`'s own scope philosophy:
/// supports constants, model-resolved atoms (`Var`/`Apply`), and
/// `Neg`/`Add`/`Sub`/`Mul`/`Div` over those — the arithmetic fragment an
/// objective term actually needs. Returns `None` (never a wrong number) for
/// anything else, e.g. `Ite`, so the caller leaves the existing `Infinite`/
/// `unknown` fallback in place rather than reporting a value that might be
/// incorrect.
pub(crate) fn evaluate_term_to_rational(
    term: TermId,
    tm: &TermManager,
    model: &FxHashMap<TermId, ModelValue>,
) -> Option<BigRational> {
    if let Some(mv) = model.get(&term) {
        return model_value_to_rational(mv);
    }
    let t = tm.get(term)?;
    match &t.kind {
        TermKind::IntConst(n) => Some(BigRational::from(n.clone())),
        TermKind::RealConst(r) => {
            Some(BigRational::new(BigInt::from(*r.numer()), BigInt::from(*r.denom())))
        }
        TermKind::Neg(a) => Some(-evaluate_term_to_rational(*a, tm, model)?),
        TermKind::Add(args) => {
            let mut sum = BigRational::from(BigInt::from(0));
            for &a in args {
                sum += evaluate_term_to_rational(a, tm, model)?;
            }
            Some(sum)
        }
        TermKind::Sub(l, r) => {
            let lv = evaluate_term_to_rational(*l, tm, model)?;
            let rv = evaluate_term_to_rational(*r, tm, model)?;
            Some(lv - rv)
        }
        TermKind::Mul(args) => {
            let mut prod = BigRational::from(BigInt::from(1));
            for &a in args {
                prod *= evaluate_term_to_rational(a, tm, model)?;
            }
            Some(prod)
        }
        TermKind::Div(l, r) => {
            let rv = evaluate_term_to_rational(*r, tm, model)?;
            if rv == BigRational::from(BigInt::from(0)) {
                return None;
            }
            let lv = evaluate_term_to_rational(*l, tm, model)?;
            Some(lv / rv)
        }
        _ => None,
    }
}

fn model_value_to_rational(mv: &ModelValue) -> Option<BigRational> {
    match mv {
        ModelValue::Int(n) => Some(BigRational::from(n.clone())),
        ModelValue::Rational(r) => Some(r.clone()),
        ModelValue::Bool(_) | ModelValue::BitVec(_, _) => None,
    }
}

/// Convert an exact rational result into the narrowest `Weight` that
/// represents it exactly (an integer value becomes `Weight::Int`, matching
/// how `term_id_to_weight`/`optimize_single_objective` already report exact
/// integer objectives, rather than always widening to `Weight::Rational`).
fn weight_from_rational(r: BigRational) -> Weight {
    if r.is_integer() {
        Weight::Int(r.to_integer())
    } else {
        Weight::Rational(r)
    }
}

/// Optimization context wrapping the SMT solver.
///
/// This is the main interface for optimization problems. It supports:
/// - Hard constraints (must be satisfied)
/// - Soft constraints with weights (maximize satisfaction)
/// - Objective functions (minimize/maximize expressions)
/// - Multi-objective optimization
#[derive(Debug)]
pub struct OptContext {
    /// Hard constraints (terms that must be true)
    hard_constraints: Vec<TermId>,
    /// Soft constraints
    soft_constraints: Vec<SoftConstraint>,
    /// Next soft constraint ID
    next_soft_id: u32,
    /// Objectives to optimize
    objectives: Vec<Objective>,
    /// Next objective ID
    next_obj_id: u32,
    /// Configuration
    config: OptConfig,
    /// Statistics
    stats: OptStats,
    /// Best model found
    best_model: Option<FxHashMap<TermId, ModelValue>>,
    /// Current lower bounds for objectives
    lower_bounds: FxHashMap<ObjectiveId, Weight>,
    /// Current upper bounds for objectives
    upper_bounds: FxHashMap<ObjectiveId, Weight>,
    /// Soft constraint groups
    groups: FxHashMap<String, Vec<SoftConstraintId>>,
    /// Context stack for push/pop
    context_stack: Vec<ContextSnapshot>,
    /// Term manager for building auxiliary terms during solving
    pub terms: TermManager,
    /// Counter for generating fresh selector variable names
    next_sel_id: u32,
    /// Cached Pareto front from last `optimize_pareto` call
    pareto_front: Vec<FxHashMap<TermId, ModelValue>>,
}

/// Snapshot for push/pop
#[derive(Debug, Clone)]
struct ContextSnapshot {
    num_hard: usize,
    num_soft: usize,
    num_objectives: usize,
}

impl Default for OptContext {
    fn default() -> Self {
        Self::new()
    }
}

impl OptContext {
    /// Create a new optimization context.
    pub fn new() -> Self {
        Self::with_config(OptConfig::default())
    }

    /// Create a new optimization context with configuration.
    pub fn with_config(config: OptConfig) -> Self {
        Self {
            hard_constraints: Vec::new(),
            soft_constraints: Vec::new(),
            next_soft_id: 0,
            objectives: Vec::new(),
            next_obj_id: 0,
            config,
            stats: OptStats::default(),
            best_model: None,
            lower_bounds: FxHashMap::default(),
            upper_bounds: FxHashMap::default(),
            groups: FxHashMap::default(),
            context_stack: Vec::new(),
            terms: TermManager::new(),
            next_sel_id: 0,
            pareto_front: Vec::new(),
        }
    }

    /// Add a hard constraint
    pub fn add_hard(&mut self, term: TermId) {
        self.hard_constraints.push(term);
    }

    /// Add a soft constraint with unit weight
    pub fn add_soft(&mut self, term: TermId) -> SoftConstraintId {
        self.add_soft_weighted(term, Weight::one())
    }

    /// Add a soft constraint with weight
    pub fn add_soft_weighted(&mut self, term: TermId, weight: Weight) -> SoftConstraintId {
        self.add_soft_grouped(term, weight, None)
    }

    /// Add a soft constraint with weight and group
    pub fn add_soft_grouped(
        &mut self,
        term: TermId,
        weight: Weight,
        group: Option<String>,
    ) -> SoftConstraintId {
        let id = SoftConstraintId(self.next_soft_id);
        self.next_soft_id += 1;

        let constraint = SoftConstraint {
            id,
            term,
            weight,
            group: group.clone(),
        };
        self.soft_constraints.push(constraint);

        // Add to group if specified
        if let Some(g) = group {
            self.groups.entry(g).or_default().push(id);
        }

        id
    }

    /// Add a minimization objective
    pub fn minimize(&mut self, term: TermId) -> ObjectiveId {
        self.add_objective(term, ObjectiveKind::Minimize)
    }

    /// Add a maximization objective
    pub fn maximize(&mut self, term: TermId) -> ObjectiveId {
        self.add_objective(term, ObjectiveKind::Maximize)
    }

    /// Add an objective with specified kind
    fn add_objective(&mut self, term: TermId, kind: ObjectiveKind) -> ObjectiveId {
        let id = ObjectiveId(self.next_obj_id);
        self.next_obj_id += 1;

        let objective = Objective {
            id,
            term,
            kind,
            priority: 0,
        };
        self.objectives.push(objective);

        // Initialize bounds
        self.lower_bounds.insert(id, Weight::Infinite);
        self.upper_bounds.insert(id, Weight::Infinite);

        id
    }

    /// Set the priority of an objective (lower = higher priority)
    pub fn set_priority(&mut self, id: ObjectiveId, priority: u32) {
        if let Some(obj) = self.objectives.iter_mut().find(|o| o.id == id) {
            obj.priority = priority;
        }
    }

    /// Get the number of hard constraints
    pub fn num_hard(&self) -> usize {
        self.hard_constraints.len()
    }

    /// Get the number of soft constraints
    pub fn num_soft(&self) -> usize {
        self.soft_constraints.len()
    }

    /// Get the number of objectives
    pub fn num_objectives(&self) -> usize {
        self.objectives.len()
    }

    /// Get statistics
    pub fn stats(&self) -> &OptStats {
        &self.stats
    }

    /// Get the configuration
    pub fn config(&self) -> &OptConfig {
        &self.config
    }

    /// Get the best model
    pub fn best_model(&self) -> Option<&FxHashMap<TermId, ModelValue>> {
        self.best_model.as_ref()
    }

    /// Get the Pareto front from the last `optimize()` call (multi-objective case).
    ///
    /// Each element is a model (variable → value map) corresponding to one
    /// Pareto-optimal solution. Empty unless `optimize()` was called with
    /// multiple objectives.
    pub fn pareto_front(&self) -> &[FxHashMap<TermId, ModelValue>] {
        &self.pareto_front
    }

    /// Get the value of an objective in the best model
    pub fn objective_value(&self, id: ObjectiveId) -> Option<&Weight> {
        self.lower_bounds.get(&id)
    }

    /// Get the lower bound for an objective
    pub fn objective_lower_bound(&self, id: ObjectiveId) -> Option<&Weight> {
        self.lower_bounds.get(&id)
    }

    /// Get the upper bound for an objective
    pub fn objective_upper_bound(&self, id: ObjectiveId) -> Option<&Weight> {
        self.upper_bounds.get(&id)
    }

    /// Get all objectives
    pub fn objectives(&self) -> &[Objective] {
        &self.objectives
    }

    /// Get all soft constraints
    pub fn soft_constraints(&self) -> &[SoftConstraint] {
        &self.soft_constraints
    }

    /// Get a model value for a term
    pub fn get_model_value(&self, term: TermId) -> Option<&ModelValue> {
        self.best_model.as_ref().and_then(|m| m.get(&term))
    }

    /// Extract model as a map
    pub fn extract_model(&self) -> Option<FxHashMap<TermId, ModelValue>> {
        self.best_model.clone()
    }

    /// Push a new context level
    pub fn push(&mut self) {
        self.context_stack.push(ContextSnapshot {
            num_hard: self.hard_constraints.len(),
            num_soft: self.soft_constraints.len(),
            num_objectives: self.objectives.len(),
        });
    }

    /// Pop to previous context level
    pub fn pop(&mut self) {
        if let Some(snapshot) = self.context_stack.pop() {
            self.hard_constraints.truncate(snapshot.num_hard);
            self.soft_constraints.truncate(snapshot.num_soft);
            self.objectives.truncate(snapshot.num_objectives);
        }
    }

    /// Check satisfiability (ignoring soft constraints and objectives)
    pub fn check_sat(&mut self) -> OptResult {
        let mut solver = Solver::new();
        for &term in &self.hard_constraints {
            solver.assert(term, &mut self.terms);
        }
        self.stats.solver_calls += 1;
        match solver.check(&mut self.terms) {
            SolverResult::Sat => {
                if let Some(model) = solver.model() {
                    let snapshot = model
                        .assignments()
                        .iter()
                        .filter_map(|(&var_term, &val_term)| {
                            let mv = term_id_to_model_value(val_term, &self.terms)?;
                            Some((var_term, mv))
                        })
                        .collect();
                    self.best_model = Some(snapshot);
                }
                OptResult::Satisfiable
            }
            SolverResult::Unsat => OptResult::Unsatisfiable,
            SolverResult::Unknown => OptResult::Unknown,
        }
    }

    /// Optimize the problem
    ///
    /// This is the main optimization entry point. It will:
    /// 1. Check hard constraint satisfiability
    /// 2. Optimize soft constraints (MaxSMT)
    /// 3. Optimize objectives
    pub fn optimize(&mut self) -> Result<OptResult, OptError> {
        // If no soft constraints or objectives, just check satisfiability
        if self.soft_constraints.is_empty() && self.objectives.is_empty() {
            return Ok(self.check_sat());
        }

        // Use Pareto optimization for multiple objectives
        if self.objectives.len() > 1 {
            return self.optimize_pareto();
        }

        // For single objective or pure MaxSMT, use appropriate solver
        if !self.soft_constraints.is_empty() && self.objectives.is_empty() {
            return self.optimize_maxsmt();
        }

        // Single objective optimization
        if !self.objectives.is_empty() {
            return self.optimize_single_objective();
        }

        Ok(OptResult::Unknown)
    }

    /// Optimize using MaxSMT (soft constraints only).
    ///
    /// Uses selector-variable encoding:
    ///   For each soft constraint `t_i` with weight `w_i`:
    ///   1. Introduce fresh boolean selector `b_i`
    ///   2. Assert `b_i → t_i` (hard)
    ///   3. Model cost as integer: if `b_i` is false, pay weight `w_i`
    ///
    /// Then binary-search over the total cost budget to find the minimum
    /// cost (= maximum satisfaction) feasible assignment.
    fn optimize_maxsmt(&mut self) -> Result<OptResult, OptError> {
        if self.soft_constraints.is_empty() {
            return Ok(self.check_sat());
        }

        // Fast, TRUSTED path: if the WHOLE problem (every hard constraint
        // and every soft constraint's term) is expressible as pure
        // propositional Boolean structure, solve it via a Tseitin-CNF +
        // `PmresSolver` encoding instead of the general LIA-capable binary
        // search below. See `bool_cnf_maxsat`'s module doc: the binary
        // search below was found (z3/cvc5 differential, fill-the-gap/
        // maxsat fixup pass) to trigger a false-UNSAT bug in
        // `oxiz_solver`'s Bool/LIA integration on exactly the encoding it
        // builds, and separately to silently truncate non-integer
        // weights — this fast path is immune to both for the (extremely
        // common) fragment it covers. Falls through unchanged to the
        // existing encoding for anything outside that fragment (e.g. a
        // hard constraint or soft term that touches Int/Real).
        if let Some(outcome) = crate::bool_cnf_maxsat::try_optimize_maxsmt_boolean(
            &self.hard_constraints,
            &self.soft_constraints,
            &self.terms,
        ) {
            self.stats.solver_calls += 1;
            if let Some(model) = outcome.model {
                self.best_model = Some(model);
            }
            return Ok(outcome.result.into());
        }

        let int_sort = self.terms.sorts.int_sort;
        let bool_sort = self.terms.sorts.bool_sort;

        // Build selector variables and implication hard constraints.
        // Also build individual cost variables and their definitional constraints.
        let num_soft = self.soft_constraints.len();
        let mut sel_vars: Vec<TermId> = Vec::with_capacity(num_soft);
        let mut cost_vars: Vec<TermId> = Vec::with_capacity(num_soft);
        let mut selector_implications: Vec<TermId> = Vec::with_capacity(num_soft);
        let mut cost_defs: Vec<TermId> = Vec::with_capacity(num_soft * 2);

        // A common integer SCALE factor so every soft-constraint weight —
        // including rational/decimal ones — is representable EXACTLY as
        // an integer in the binary-search cost encoding below (which only
        // ever works over `Int`). A prior version silently collapsed any
        // non-integer weight to `1`, which could make the search pick a
        // provably non-optimal set of violated soft constraints while
        // still reporting the (real, untruncated) weight's sum as if it
        // were the true optimum — see the fill-the-gap/maxsat fixup
        // pass's weight-truncation finding. `Weight::Infinite` never
        // contributes a denominator (it's handled specially below, same
        // as before).
        let scale: BigInt = self
            .soft_constraints
            .iter()
            .filter_map(|sc| match &sc.weight {
                Weight::Rational(r) => Some(r.denom().clone()),
                Weight::Int(_) | Weight::Infinite => None,
            })
            .fold(BigInt::from(1), |acc, d| lcm_bigint(&acc, &d));

        // Pre-compute total weight for upper bound of binary search (in
        // SCALED units, so it stays an upper bound on the scaled cost sum
        // built below).
        let total_weight: BigInt = self
            .soft_constraints
            .iter()
            .map(|sc| scaled_weight(&sc.weight, &scale))
            .fold(BigInt::from(0), |acc, w| acc + w);

        for sc in &self.soft_constraints {
            let sel_name = format!("__opt_sel_{}", self.next_sel_id);
            self.next_sel_id += 1;
            let cost_name = format!("__opt_cost_{}", self.next_sel_id);
            self.next_sel_id += 1;

            let sel = self.terms.mk_var(&sel_name, bool_sort);
            let cost_var = self.terms.mk_var(&cost_name, int_sort);
            sel_vars.push(sel);
            cost_vars.push(cost_var);

            // b_i → t_i
            let implication = self.terms.mk_implies(sel, sc.term);
            selector_implications.push(implication);

            // cost_i = ite(b_i, 0, w_i) in SCALED units.
            // Encoded as two implications: b_i → cost_i = 0; ¬b_i → cost_i = w_i
            let weight_int = scaled_weight(&sc.weight, &scale);
            let w_term = self.terms.mk_int(weight_int);
            let zero = self.terms.mk_int(0i64);
            let not_sel = self.terms.mk_not(sel);
            let cost_eq_zero = self.terms.mk_eq(cost_var, zero);
            let cost_eq_w = self.terms.mk_eq(cost_var, w_term);
            let def_true = self.terms.mk_implies(sel, cost_eq_zero);
            let def_false = self.terms.mk_implies(not_sel, cost_eq_w);
            cost_defs.push(def_true);
            cost_defs.push(def_false);
        }

        // Build sum-of-costs expression: cost_0 + cost_1 + ... + cost_{n-1}
        let cost_sum = self.terms.mk_add(cost_vars.iter().copied());

        // Binary search: find minimum cost budget K such that the problem is SAT.
        let mut lo = BigInt::from(0i64);
        let mut hi = total_weight.clone();

        // First check feasibility with no soft constraints (hi = total cost).
        // We need to know if hard constraints are satisfiable at all.
        let feasible = {
            let mut solver = Solver::new();
            for &h in &self.hard_constraints {
                solver.assert(h, &mut self.terms);
            }
            for &imp in &selector_implications {
                solver.assert(imp, &mut self.terms);
            }
            for &cd in &cost_defs {
                solver.assert(cd, &mut self.terms);
            }
            self.stats.solver_calls += 1;
            solver.check(&mut self.terms) == SolverResult::Sat
        };

        if !feasible {
            return Ok(OptResult::Unsatisfiable);
        }

        // Binary search for minimum cost.
        let mut best_model_snapshot: Option<FxHashMap<TermId, ModelValue>> = None;
        // Set if the underlying solver returns `Unknown` during the search:
        // the binary search aborts at a non-tight `[lo, hi]` bound, so the
        // optimum was NOT proven and we must not report `Optimal`.
        let mut inconclusive = false;

        while lo < hi {
            let mid: BigInt = (lo.clone() + hi.clone()) / 2i32;
            let bound_term = self.terms.mk_int(mid.clone());
            let cost_le_mid = self.terms.mk_le(cost_sum, bound_term);

            let mut solver = Solver::new();
            for &h in &self.hard_constraints {
                solver.assert(h, &mut self.terms);
            }
            for &imp in &selector_implications {
                solver.assert(imp, &mut self.terms);
            }
            for &cd in &cost_defs {
                solver.assert(cd, &mut self.terms);
            }
            solver.assert(cost_le_mid, &mut self.terms);

            self.stats.solver_calls += 1;
            match solver.check(&mut self.terms) {
                SolverResult::Sat => {
                    hi = mid;
                    if let Some(model) = solver.model() {
                        best_model_snapshot = Some(
                            model
                                .assignments()
                                .iter()
                                .filter_map(|(&k, &v)| {
                                    let mv = term_id_to_model_value(v, &self.terms)?;
                                    Some((k, mv))
                                })
                                .collect(),
                        );
                    }
                }
                SolverResult::Unsat => {
                    lo = mid + BigInt::from(1i32);
                }
                SolverResult::Unknown => {
                    inconclusive = true;
                    break;
                }
            }
        }

        // Solve once more at lo to get the actual optimal model.
        {
            let bound_term = self.terms.mk_int(lo.clone());
            let cost_le_lo = self.terms.mk_le(cost_sum, bound_term);
            let mut solver = Solver::new();
            for &h in &self.hard_constraints {
                solver.assert(h, &mut self.terms);
            }
            for &imp in &selector_implications {
                solver.assert(imp, &mut self.terms);
            }
            for &cd in &cost_defs {
                solver.assert(cd, &mut self.terms);
            }
            solver.assert(cost_le_lo, &mut self.terms);
            self.stats.solver_calls += 1;
            if solver.check(&mut self.terms) == SolverResult::Sat
                && let Some(model) = solver.model()
            {
                best_model_snapshot = Some(
                    model
                        .assignments()
                        .iter()
                        .filter_map(|(&k, &v)| {
                            let mv = term_id_to_model_value(v, &self.terms)?;
                            Some((k, mv))
                        })
                        .collect(),
                );
            }
        }

        self.best_model = best_model_snapshot;
        if inconclusive {
            // The search aborted on an inconclusive (`Unknown`) solver result,
            // so the bound is not provably tight. The problem is known to be
            // feasible (the feasibility check above passed), but optimality was
            // not proven — report a solution without claiming optimality.
            Ok(OptResult::Satisfiable)
        } else {
            Ok(OptResult::Optimal)
        }
    }

    /// Optimize a single objective using `oxiz_solver::Optimizer`.
    fn optimize_single_objective(&mut self) -> Result<OptResult, OptError> {
        let obj = match self.objectives.first().cloned() {
            Some(obj) => obj,
            None => return Ok(OptResult::Unknown),
        };

        let mut opt = Optimizer::new();

        // Assert all hard constraints.
        for &h in &self.hard_constraints {
            opt.assert(h);
        }

        // Register the objective.
        match obj.kind {
            ObjectiveKind::Minimize => opt.minimize(obj.term),
            ObjectiveKind::Maximize => opt.maximize(obj.term),
        }

        self.stats.solver_calls += 1;
        match opt.optimize(&mut self.terms) {
            OptimizationResult::Optimal { value, model } => {
                // Store objective bound.
                let bound = term_id_to_weight(value, &self.terms);
                self.lower_bounds.insert(obj.id, bound.clone());
                self.upper_bounds.insert(obj.id, bound);

                // Snapshot the model.
                let snapshot = model
                    .assignments()
                    .iter()
                    .filter_map(|(&k, &v)| {
                        let mv = term_id_to_model_value(v, &self.terms)?;
                        Some((k, mv))
                    })
                    .collect();
                self.best_model = Some(snapshot);
                Ok(OptResult::Optimal)
            }
            OptimizationResult::Unbounded => Ok(OptResult::Unbounded),
            OptimizationResult::Unsat => Ok(OptResult::Unsatisfiable),
            OptimizationResult::Unknown => Ok(OptResult::Unknown),
        }
    }

    /// Optimize using Pareto (multiple objectives) via `oxiz_solver::Optimizer`.
    fn optimize_pareto(&mut self) -> Result<OptResult, OptError> {
        if self.objectives.is_empty() {
            return Ok(self.check_sat());
        }

        let mut opt = Optimizer::new();

        for &h in &self.hard_constraints {
            opt.assert(h);
        }

        for obj in &self.objectives {
            match obj.kind {
                ObjectiveKind::Minimize => opt.minimize(obj.term),
                ObjectiveKind::Maximize => opt.maximize(obj.term),
            }
        }

        self.stats.solver_calls += 1;
        let pareto_points = opt.pareto_optimize(&mut self.terms);

        if pareto_points.is_empty() {
            return Ok(OptResult::Unsatisfiable);
        }

        self.pareto_front.clear();
        for point in &pareto_points {
            let snapshot: FxHashMap<TermId, ModelValue> = point
                .model
                .assignments()
                .iter()
                .filter_map(|(&k, &v)| {
                    let mv = term_id_to_model_value(v, &self.terms)?;
                    Some((k, mv))
                })
                .collect();
            self.pareto_front.push(snapshot);
        }

        // Use the last Pareto point as the best model.
        if let Some(last) = self.pareto_front.last() {
            self.best_model = Some(last.clone());
        }

        // Populate lower/upper bounds for each objective from the SELECTED
        // point's model — see `evaluate_term_to_rational`'s doc for why
        // this is needed (a prior version left every multi-objective
        // `get-objectives` reporting `Weight::Infinite` unconditionally).
        // Cloned once up front rather than borrowed, to sidestep multi-
        // field-borrow gymnastics in a rarely-hot path.
        if let Some(model) = self.best_model.clone() {
            let obj_terms: Vec<(ObjectiveId, TermId)> =
                self.objectives.iter().map(|o| (o.id, o.term)).collect();
            for (id, term) in obj_terms {
                if let Some(r) = evaluate_term_to_rational(term, &self.terms, &model) {
                    let w = weight_from_rational(r);
                    self.lower_bounds.insert(id, w.clone());
                    self.upper_bounds.insert(id, w);
                }
            }
        }

        Ok(OptResult::Optimal)
    }

    /// Reset the context
    pub fn reset(&mut self) {
        self.hard_constraints.clear();
        self.soft_constraints.clear();
        self.next_soft_id = 0;
        self.objectives.clear();
        self.next_obj_id = 0;
        self.stats = OptStats::default();
        self.best_model = None;
        self.lower_bounds.clear();
        self.upper_bounds.clear();
        self.groups.clear();
        self.context_stack.clear();
        self.terms = TermManager::new();
        self.next_sel_id = 0;
        self.pareto_front.clear();
    }

    /// Get all soft constraints in a group
    pub fn get_group(&self, group: &str) -> Option<&[SoftConstraintId]> {
        self.groups.get(group).map(|v| v.as_slice())
    }

    /// Get the weight of a soft constraint
    pub fn soft_weight(&self, id: SoftConstraintId) -> Option<&Weight> {
        self.soft_constraints.get(id.0 as usize).map(|c| &c.weight)
    }

    /// Check if a soft constraint is satisfied in the best model
    pub fn is_soft_satisfied(&self, id: SoftConstraintId) -> bool {
        // Get the soft constraint
        let soft = match self.soft_constraints.get(id.0 as usize) {
            Some(s) => s,
            None => return false,
        };

        // Check if we have a model
        let model = match &self.best_model {
            Some(m) => m,
            None => return false, // No model, can't determine satisfaction
        };

        // Check if the constraint's term is satisfied in the model
        // For now, we check if the term has a value in the model
        // A full implementation would need to evaluate the term
        match model.get(&soft.term) {
            Some(ModelValue::Bool(true)) => true,
            Some(ModelValue::Bool(false)) => false,
            _ => false, // Non-boolean or not in model - conservatively say unsatisfied
        }
    }

    /// Get the sum of weights of unsatisfied soft constraints
    pub fn cost(&self) -> Weight {
        // If no model, all soft constraints are unsatisfied
        if self.best_model.is_none() {
            return self
                .soft_constraints
                .iter()
                .fold(Weight::zero(), |acc, c| acc.add(&c.weight));
        }

        // Sum weights of unsatisfied constraints
        self.soft_constraints
            .iter()
            .filter(|c| !self.is_soft_satisfied(c.id))
            .fold(Weight::zero(), |acc, c| acc.add(&c.weight))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_opt_context_new() {
        let ctx = OptContext::new();
        assert_eq!(ctx.num_hard(), 0);
        assert_eq!(ctx.num_soft(), 0);
        assert_eq!(ctx.num_objectives(), 0);
    }

    #[test]
    fn test_add_hard_constraint() {
        let mut ctx = OptContext::new();
        let term = TermId::from(1);
        ctx.add_hard(term);
        assert_eq!(ctx.num_hard(), 1);
    }

    #[test]
    fn test_add_soft_constraint() {
        let mut ctx = OptContext::new();
        let term = TermId::from(1);
        let id = ctx.add_soft(term);
        assert_eq!(id.0, 0);
        assert_eq!(ctx.num_soft(), 1);
    }

    #[test]
    fn test_add_weighted_soft() {
        let mut ctx = OptContext::new();
        let term = TermId::from(1);
        let id = ctx.add_soft_weighted(term, Weight::from(5));
        assert_eq!(ctx.soft_weight(id), Some(&Weight::from(5)));
    }

    #[test]
    fn test_add_grouped_soft() {
        let mut ctx = OptContext::new();
        let term1 = TermId::from(1);
        let term2 = TermId::from(2);

        let id1 = ctx.add_soft_grouped(term1, Weight::one(), Some("group1".to_string()));
        let id2 = ctx.add_soft_grouped(term2, Weight::one(), Some("group1".to_string()));

        let group = ctx.get_group("group1");
        assert!(group.is_some());
        assert_eq!(group.expect("test operation should succeed").len(), 2);
        assert!(group.expect("test operation should succeed").contains(&id1));
        assert!(group.expect("test operation should succeed").contains(&id2));
    }

    #[test]
    fn test_add_objectives() {
        let mut ctx = OptContext::new();
        let term1 = TermId::from(1);
        let term2 = TermId::from(2);

        let id1 = ctx.minimize(term1);
        let id2 = ctx.maximize(term2);

        assert_eq!(ctx.num_objectives(), 2);
        assert_eq!(id1.0, 0);
        assert_eq!(id2.0, 1);
    }

    #[test]
    fn test_push_pop() {
        let mut ctx = OptContext::new();
        let term1 = TermId::from(1);
        let term2 = TermId::from(2);

        ctx.add_hard(term1);
        assert_eq!(ctx.num_hard(), 1);

        ctx.push();
        ctx.add_hard(term2);
        assert_eq!(ctx.num_hard(), 2);

        ctx.pop();
        assert_eq!(ctx.num_hard(), 1);
    }

    #[test]
    fn pareto_multi_objective_reports_real_bounds_not_infinite() {
        // Regression test for a P0 finding (fill-the-gap/maxsat fixup
        // pass): `optimize_pareto` never populated `lower_bounds`/
        // `upper_bounds`, so `objective_value` returned the
        // `add_objective`-time `Weight::Infinite` placeholder
        // UNCONDITIONALLY for every multi-objective run, even for
        // trivially bounded objectives.
        let mut ctx = OptContext::new();
        let x = ctx.terms.mk_var("x", ctx.terms.sorts.int_sort);
        let y = ctx.terms.mk_var("y", ctx.terms.sorts.int_sort);
        let zero = ctx.terms.mk_int(0i64);
        let ten = ctx.terms.mk_int(10i64);
        let c1 = ctx.terms.mk_ge(x, zero);
        let c2 = ctx.terms.mk_le(x, ten);
        let c3 = ctx.terms.mk_ge(y, zero);
        let c4 = ctx.terms.mk_le(y, ten);
        ctx.add_hard(c1);
        ctx.add_hard(c2);
        ctx.add_hard(c3);
        ctx.add_hard(c4);

        let id_x = ctx.maximize(x);
        let id_y = ctx.maximize(y);

        let result = ctx.optimize().expect("optimize should not error");
        assert_eq!(result, OptResult::Optimal);

        let vx = ctx.objective_value(id_x).expect("x should have a bound");
        let vy = ctx.objective_value(id_y).expect("y should have a bound");
        assert!(!vx.is_infinite(), "x's objective value must not be Infinite, got {vx:?}");
        assert!(!vy.is_infinite(), "y's objective value must not be Infinite, got {vy:?}");
    }

    #[test]
    fn test_reset() {
        let mut ctx = OptContext::new();
        ctx.add_hard(TermId::from(1));
        ctx.add_soft(TermId::from(2));
        ctx.minimize(TermId::from(3));

        ctx.reset();

        assert_eq!(ctx.num_hard(), 0);
        assert_eq!(ctx.num_soft(), 0);
        assert_eq!(ctx.num_objectives(), 0);
    }

    #[test]
    fn test_config() {
        let config = OptConfig {
            incremental: false,
            timeout_ms: 5000,
            ..Default::default()
        };
        let ctx = OptContext::with_config(config);
        assert!(!ctx.config.incremental);
        assert_eq!(ctx.config.timeout_ms, 5000);
    }

    #[test]
    fn test_objective_bounds() {
        let mut ctx = OptContext::new();
        let term = TermId::from(1);
        let id = ctx.minimize(term);

        // Initially bounds are infinite
        assert!(ctx.objective_lower_bound(id).is_some());
        assert!(ctx.objective_upper_bound(id).is_some());
    }

    #[test]
    fn test_get_objectives() {
        let mut ctx = OptContext::new();
        let term1 = TermId::from(1);
        let term2 = TermId::from(2);

        ctx.minimize(term1);
        ctx.maximize(term2);

        let objs = ctx.objectives();
        assert_eq!(objs.len(), 2);
    }

    #[test]
    fn test_get_soft_constraints() {
        let mut ctx = OptContext::new();
        let term1 = TermId::from(1);
        let term2 = TermId::from(2);

        ctx.add_soft(term1);
        ctx.add_soft_weighted(term2, Weight::from(5));

        let softs = ctx.soft_constraints();
        assert_eq!(softs.len(), 2);
    }

    #[test]
    fn test_extract_model() {
        let ctx = OptContext::new();
        let model = ctx.extract_model();
        assert!(model.is_none()); // No model yet
    }

    #[test]
    fn test_get_model_value() {
        let ctx = OptContext::new();
        let term = TermId::from(1);
        let value = ctx.get_model_value(term);
        assert!(value.is_none()); // No model yet
    }

    #[test]
    fn test_opt_result_display() {
        assert_eq!(OptResult::Optimal.to_string(), "optimal");
        assert_eq!(OptResult::Satisfiable.to_string(), "satisfiable");
        assert_eq!(OptResult::Unsatisfiable.to_string(), "unsatisfiable");
        assert_eq!(OptResult::Unknown.to_string(), "unknown");
    }

    #[test]
    fn test_model_value_display() {
        assert_eq!(ModelValue::Bool(true).to_string(), "true");
        assert_eq!(ModelValue::Bool(false).to_string(), "false");
        assert_eq!(ModelValue::Int(BigInt::from(42)).to_string(), "42");
        assert_eq!(
            ModelValue::Rational(BigRational::new(BigInt::from(3), BigInt::from(2))).to_string(),
            "3/2"
        );
    }

    // Tests for From implementations

    #[test]
    fn test_soft_constraint_id_from_u32() {
        let id: SoftConstraintId = SoftConstraintId::from(5u32);
        assert_eq!(id.raw(), 5);
    }

    #[test]
    fn test_soft_constraint_id_from_usize() {
        let id: SoftConstraintId = SoftConstraintId::from(10usize);
        assert_eq!(id.raw(), 10);
    }

    #[test]
    fn test_soft_constraint_id_to_u32() {
        let id = SoftConstraintId::new(7);
        let n: u32 = id.into();
        assert_eq!(n, 7);
    }

    #[test]
    fn test_soft_constraint_id_to_usize() {
        let id = SoftConstraintId::new(9);
        let n: usize = id.into();
        assert_eq!(n, 9);
    }

    #[test]
    fn test_soft_constraint_id_roundtrip() {
        let original = 42u32;
        let id: SoftConstraintId = original.into();
        let back: u32 = id.into();
        assert_eq!(original, back);
    }
}
