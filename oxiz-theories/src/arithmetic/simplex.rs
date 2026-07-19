//! Simplex algorithm implementation

use super::delta::DeltaRational;
use crate::config::{BacktrackMode, PivotingRule, SimplexConfig};
#[allow(unused_imports)]
use crate::prelude::*;
use crate::ArithRat;
use num_traits::{One, Signed, Zero};
#[cfg(feature = "profiling")]
use oxiz_core::profiling::{ProfilingCategory, ScopedTimer};
// The scoped undo spine (single funnel for bounds, var allocs, rows, flags) —
// same pattern as the oxiz-sat clause-id ledger. Traits brought in as `_`
// (only their methods are needed); `Checkpoint` is named (it is the mark type).
use portable_collection_primitives::{
    Checkpoint, Container as _, Push as _, ScopedRollback as _, ScopedStack as _,
};
use portable_queues::VecScopedStack;
use smallvec::SmallVec;

/// Variable index
pub type VarId = u32;

/// A linear expression: sum of (coefficient, variable) pairs + constant
#[derive(Debug, Clone, Default)]
pub struct LinExpr {
    /// Terms: (variable, coefficient)
    pub terms: SmallVec<[(VarId, ArithRat); 4]>,
    /// Constant term
    pub constant: ArithRat,
}

impl LinExpr {
    /// Create a new linear expression
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Create a constant expression
    #[must_use]
    pub fn constant(c: ArithRat) -> Self {
        Self {
            terms: SmallVec::new(),
            constant: c,
        }
    }

    /// Create a variable expression
    #[must_use]
    pub fn var(v: VarId) -> Self {
        Self {
            terms: smallvec::smallvec![(v, ArithRat::one())],
            constant: ArithRat::zero(),
        }
    }

    /// Add a term
    pub fn add_term(&mut self, var: VarId, coef: ArithRat) {
        if !coef.is_zero() {
            // Check if variable already exists
            for (v, c) in &mut self.terms {
                if *v == var {
                    *c += coef;
                    if c.is_zero() {
                        self.terms.retain(|(v, _)| *v != var);
                    }
                    return;
                }
            }
            self.terms.push((var, coef));
        }
    }

    /// Add a constant
    pub fn add_constant(&mut self, c: ArithRat) {
        self.constant += c;
    }

    /// Negate the expression
    pub fn negate(&mut self) {
        for (_, c) in &mut self.terms {
            *c = -*c;
        }
        self.constant = -self.constant;
    }

    /// Multiply by a constant
    pub fn scale(&mut self, factor: ArithRat) {
        for (_, c) in &mut self.terms {
            *c *= factor;
        }
        self.constant *= factor;
    }

    /// Check if this expression subsumes another (i.e., this is weaker or equal)
    ///
    /// For example, x + y <= 10 subsumes x + y <= 5 (the latter is stronger)
    /// Returns true if adding the other constraint is redundant given this one
    #[must_use]
    pub fn subsumes(&self, other: &LinExpr, self_is_le: bool, other_is_le: bool) -> bool {
        // Check if the expressions have the same terms
        if self.terms.len() != other.terms.len() {
            return false;
        }

        // Check if all terms match (assuming sorted)
        for (i, (v1, c1)) in self.terms.iter().enumerate() {
            if let Some((v2, c2)) = other.terms.get(i) {
                if v1 != v2 || c1 != c2 {
                    return false;
                }
            } else {
                return false;
            }
        }

        // Now check if the constant makes this weaker
        // For <= constraints: larger constant is weaker
        // For >= constraints: smaller constant is weaker
        match (self_is_le, other_is_le) {
            (true, true) => {
                // Both are <=: self subsumes other if self.constant >= other.constant
                self.constant >= other.constant
            }
            (false, false) => {
                // Both are >=: self subsumes other if self.constant <= other.constant
                self.constant <= other.constant
            }
            _ => false, // Different constraint types don't subsume
        }
    }
}

// PivotingRule is now imported from crate::config

/// Bound type
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[allow(dead_code)]
pub enum BoundType {
    /// No bound
    None,
    /// Lower bound (x >= b)
    Lower,
    /// Upper bound (x <= b)
    Upper,
    /// Equality (x = b)
    Equal,
}

/// A bound on a variable
#[derive(Debug, Clone, Copy)]
pub struct Bound {
    /// Bound type
    pub kind: BoundType,
    /// Bound value (supports strict bounds via delta)
    pub value: DeltaRational,
    /// Reason (assertion that caused this bound)
    pub reason: u32,
}

/// A propagated bound derived from constraint analysis
#[derive(Debug, Clone)]
pub struct PropagatedBound {
    /// The variable that got a new bound
    pub var: VarId,
    /// Whether it's a lower bound (true) or upper bound (false)
    pub is_lower: bool,
    /// The bound value
    pub value: DeltaRational,
    /// The reasons (assertion IDs) that imply this bound
    pub reasons: SmallVec<[u32; 4]>,
}

/// An undo entry for reverting a scope's mutation — the single-funnel record
/// type of the scoped undo spine. Bound and variable-allocation arms are
/// recorded in BOTH backtrack modes; the row/flag arms are recorded only in
/// [`BacktrackMode::Trail`] (snapshot mode restores rows/flags wholesale from
/// the tableau snapshot instead).
#[derive(Debug, Clone)]
enum SimplexUndo {
    /// Lower bound was None, now has a value
    LowerWasNone(VarId),
    /// Lower bound was Some, save old value
    LowerWasSome(VarId, Bound),
    /// Upper bound was None, now has a value
    UpperWasNone(VarId),
    /// Upper bound was Some, save old value
    UpperWasSome(VarId, Bound),
    /// A new variable was added
    NewVar,
    /// A new slack variable was added
    NewSlack(VarId),
    /// (Trail mode) A tableau row keyed by this variable was inserted where
    /// none existed at the scope's first touch — undo: `tableau.remove`.
    RowInserted(VarId),
    /// (Trail mode) The pre-scope row of this variable, saved verbatim at the
    /// scope's first touch (covers both removal and in-place modification) —
    /// undo: `tableau.insert` of the saved row (exact `SmallVec` term order
    /// preserved by the clone).
    RowReplaced(VarId, LinExpr),
    /// (Trail mode) The basic flag of this variable flipped; the old value is
    /// saved — undo: `basic[v] = old`. Recorded on EVERY flip (2 per pivot),
    /// so LIFO replay restores the exact pre-push flag.
    BasicFlag(VarId, bool),
}

/// Simplex tableau state
#[derive(Debug)]
pub struct Simplex {
    /// Number of original variables
    num_vars: usize,
    /// Number of slack variables
    num_slack: usize,
    /// Current assignment (using delta-rationals for strict bounds)
    assignment: Vec<DeltaRational>,
    /// Lower bounds
    lower: Vec<Option<Bound>>,
    /// Upper bounds
    upper: Vec<Option<Bound>>,
    /// Tableau rows: basic variable -> linear combination of non-basic
    tableau: FxHashMap<VarId, LinExpr>,
    /// Basic variables
    basic: Vec<bool>,
    /// Infeasible basic variable (if any)
    infeasible: Option<VarId>,
    /// Pending propagated bounds
    propagated: Vec<PropagatedBound>,
    /// Backtracking strategy (fixed at construction; see [`BacktrackMode`])
    backtrack: BacktrackMode,
    /// Pivot-victim selection: `false` = legacy first-in-map-iteration-order
    /// (layout-dependent, byte-identical to the pre-trail trunk — the
    /// Snapshot-mode default), `true` = smallest violating `VarId` (Bland's
    /// leaving rule; layout-INdependent — required by `Trail`, whose pop
    /// keeps the grown table while a snapshot restore reinstalls the
    /// push-time clone, so map layouts legitimately diverge between modes
    /// with bit-identical contents). Derived from the mode at construction.
    deterministic_violating: bool,
    /// The scoped undo spine: ONE append-only log for every undoable mutation
    /// (bounds, var allocs, and — in trail mode — rows and basic flags).
    /// `push` records a checkpoint mark; `pop` drains the suffix LIFO.
    undo_stack: VecScopedStack<SimplexUndo>,
    /// Per-scope `(checkpoint mark, scope epoch)` pairs, innermost last.
    /// Snapshot mode carries a permanent base entry (mirroring the legacy
    /// `trail_limits = vec![0]` initialisation byte-for-byte, including the
    /// undo-everything unmatched-pop behavior); trail mode starts empty, so
    /// recording is skipped entirely at base level (nothing can pop it).
    undo_marks: Vec<(Checkpoint, u64)>,
    /// Monotone scope-epoch counter: incremented on every push, NEVER reused
    /// (so a stale `row_save_epoch` stamp can never collide with a live scope).
    push_epoch: u64,
    /// (Trail mode) Per-variable epoch of the scope that last saved this
    /// variable's row (indexed by `VarId`, grown in `new_var`/`new_slack`,
    /// kept in lock-step with `assignment`). A row's FIRST touch in a scope
    /// records exactly one undo entry and stamps the scope epoch here; later
    /// touches in the same scope compare equal and skip.
    row_save_epoch: Vec<u64>,
    /// Cached assignments for warm-starting (basis caching)
    /// Saves assignment state at each decision level for faster incremental solving
    cached_assignments: Vec<Vec<DeltaRational>>,
    /// (Snapshot mode) Saved tableau snapshots for wholesale restoration on
    /// pop. Trail mode never populates this: pivots inside the scope are
    /// undone row-by-row from the undo spine instead.
    saved_tableaux: Vec<(FxHashMap<VarId, LinExpr>, Vec<bool>)>,
    /// Pivoting rule to use
    pivoting_rule: PivotingRule,
    /// Maximum number of pivot operations before giving up
    max_pivots: usize,
    /// Set when the last `check()` exhausted `max_pivots` without reaching a
    /// feasible OR infeasible verdict. `check()` returns `Ok(())` in that case
    /// (it found no conflict), but that is NOT a proof of feasibility — the
    /// caller must treat it as **Unknown**, never `Sat` (else a cycling/large LP
    /// that hits the cap is a spurious sat).
    incomplete: bool,
}

impl Default for Simplex {
    fn default() -> Self {
        Self::new()
    }
}

impl Simplex {
    /// Create a new Simplex instance
    #[must_use]
    pub fn new() -> Self {
        Self::with_config(SimplexConfig::default())
    }

    /// Create a new Simplex instance with custom configuration
    #[must_use]
    pub fn with_config(config: SimplexConfig) -> Self {
        #[allow(unused_mut)]
        let mut backtrack = config.backtrack;
        // Env overrides (convention of `OXIZ_MBQI_GUARD_MS`; unset ⇒ config
        // wins, byte-identical at rest): `OXIZ_SIMPLEX_TRAIL=1` opts into the
        // trail scheme, `OXIZ_SIMPLEX_SNAPSHOT=1` forces the legacy snapshot
        // scheme; snapshot wins if both are set (the conservative direction).
        #[cfg(feature = "std")]
        {
            if std::env::var("OXIZ_SIMPLEX_TRAIL").is_ok_and(|v| v == "1") {
                backtrack = BacktrackMode::Trail;
            }
            if std::env::var("OXIZ_SIMPLEX_SNAPSHOT").is_ok_and(|v| v == "1") {
                backtrack = BacktrackMode::Snapshot;
            }
        }
        Self {
            num_vars: 0,
            num_slack: 0,
            assignment: Vec::new(),
            lower: Vec::new(),
            upper: Vec::new(),
            tableau: FxHashMap::default(),
            basic: Vec::new(),
            infeasible: None,
            propagated: Vec::new(),
            backtrack,
            deterministic_violating: matches!(backtrack, BacktrackMode::Trail),
            undo_stack: VecScopedStack::new(),
            undo_marks: Self::initial_marks(backtrack),
            push_epoch: 0,
            row_save_epoch: Vec::new(),
            cached_assignments: Vec::new(),
            saved_tableaux: Vec::new(),
            pivoting_rule: config.pivoting_rule,
            max_pivots: config.max_pivots,
            incomplete: false,
        }
    }

    /// Initial `undo_marks` for a mode: snapshot mode mirrors the legacy
    /// `trail_limits = vec![0]` base entry (recording active at base level, and
    /// an unmatched `pop` undoes everything, verbatim); trail mode starts with
    /// no outstanding checkpoint (base-level recording skipped entirely).
    fn initial_marks(backtrack: BacktrackMode) -> Vec<(Checkpoint, u64)> {
        match backtrack {
            BacktrackMode::Snapshot => vec![(Checkpoint::ORIGIN, 0)],
            BacktrackMode::Trail => Vec::new(),
        }
    }

    /// Record an undo entry if a scope can ever pop it. Snapshot mode always
    /// carries its base mark (legacy behavior: base-level records exist and an
    /// unmatched pop undoes them); trail mode records only inside a `push`ed
    /// scope — at base level nothing can pop, so recording is skipped.
    #[inline]
    fn record(&mut self, undo: SimplexUndo) {
        if !self.undo_marks.is_empty() {
            self.undo_stack.push(undo);
        }
    }

    /// (Trail mode) Record the FIRST in-scope touch of `var`'s tableau row —
    /// `RowReplaced(old)` if a row is present, `RowInserted` if absent — and
    /// stamp the scope epoch so later touches in the same scope skip. Must be
    /// called BEFORE the mutation. No-op in snapshot mode or at base level.
    #[inline]
    fn record_row_touch(&mut self, var: VarId) {
        if self.backtrack != BacktrackMode::Trail {
            return;
        }
        let Some(&(_, epoch)) = self.undo_marks.last() else {
            return;
        };
        let idx = var as usize;
        if self.row_save_epoch[idx] == epoch {
            return;
        }
        self.row_save_epoch[idx] = epoch;
        match self.tableau.get(&var) {
            Some(row) => self
                .undo_stack
                .push(SimplexUndo::RowReplaced(var, row.clone())),
            None => self.undo_stack.push(SimplexUndo::RowInserted(var)),
        }
    }

    /// (Trail mode) Record the current basic flag of `var` before a flip.
    /// Recorded on EVERY flip (no epoch dedup): LIFO replay walks the flips
    /// back to the exact pre-push value. No-op in snapshot mode / base level.
    #[inline]
    fn record_basic_flip(&mut self, var: VarId) {
        if self.backtrack != BacktrackMode::Trail || self.undo_marks.is_empty() {
            return;
        }
        self.undo_stack
            .push(SimplexUndo::BasicFlag(var, self.basic[var as usize]));
    }

    /// Set the pivoting rule
    pub fn set_pivoting_rule(&mut self, rule: PivotingRule) {
        self.pivoting_rule = rule;
    }

    /// Get the current pivoting rule
    #[must_use]
    pub fn pivoting_rule(&self) -> PivotingRule {
        self.pivoting_rule
    }

    /// Add a new variable
    pub fn new_var(&mut self) -> VarId {
        // Use `assignment.len()` as the ID so that regular variables and slack
        // variables never collide.  The old scheme (id = num_vars) produced IDs
        // that overlapped with previously-allocated slack IDs
        // (id_slack = num_vars + num_slack) whenever new_var() was called after
        // slacks had already been allocated.
        let id = self.assignment.len() as VarId;
        self.num_vars += 1;
        self.assignment.push(DeltaRational::zero());
        self.lower.push(None);
        self.upper.push(None);
        self.basic.push(false);
        // Lock-step with `assignment` regardless of mode/recording (the stale
        // stamp of a popped var can never equal a live scope's epoch — epochs
        // are never reused — but keeping the arrays parallel is simplest).
        self.row_save_epoch.push(0);
        self.record(SimplexUndo::NewVar);
        id
    }

    /// Add a slack variable for a constraint
    fn new_slack(&mut self) -> VarId {
        // Use `assignment.len()` as the ID for the same reason as `new_var`:
        // unified allocation prevents collisions between regular and slack IDs.
        let id = self.assignment.len() as VarId;
        self.num_slack += 1;
        self.assignment.push(DeltaRational::zero());
        self.lower.push(None);
        self.upper.push(None);
        self.basic.push(true); // Slack variables start basic
        self.row_save_epoch.push(0); // lock-step with `assignment` (see new_var)
        self.record(SimplexUndo::NewSlack(id));
        id
    }

    /// Get the current value of a variable (returns the real part)
    #[inline]
    #[must_use]
    pub fn value(&self, var: VarId) -> ArithRat {
        self.assignment
            .get(var as usize)
            .map(|d| d.real)
            .unwrap_or_default()
    }

    /// Get the current delta-rational value of a variable
    #[inline]
    #[must_use]
    pub fn delta_value(&self, var: VarId) -> DeltaRational {
        self.assignment
            .get(var as usize)
            .copied()
            .unwrap_or_default()
    }

    /// Materialize a CONCRETE rational assignment from the current delta-rational
    /// model: pick a single `δ₀ > 0` small enough that no variable bound is
    /// crossed, then return `real(v) + δ₀·delta(v)` for every variable `v`
    /// (de Moura & Bjørner, *A Fast Linear-Arithmetic Solver for DPLL(T)*, §5).
    ///
    /// The tableau rows balance in BOTH the real and the δ component (a basic
    /// variable equals its row exactly in each), so they hold for ANY `δ₀` — only
    /// the per-variable bounds constrain it. Dropping the δ part instead (as
    /// [`Self::value`] does) collapses a strict inequality `x > y` — encoded
    /// `x − y ≥ δ` with the assignment sitting at `x − y = δ` — to `x = y`, so the
    /// extracted model VIOLATES the very constraint the solver proved satisfiable.
    /// Materializing keeps it strict. The returned vector is indexed by `VarId`.
    #[must_use]
    pub fn materialize(&self) -> Vec<ArithRat> {
        // δ₀ starts at 1 and is tightened to the smallest positive ratio at which
        // the concrete value would reach a bound: for a bound `b` the assignment β
        // satisfies in δ-arithmetic, `real(β) + δ₀·delta(β)` meets `real(b) +
        // δ₀·delta(b)` exactly at δ₀ = (β.real − b.real)/(b.delta − β.delta), which
        // matters only when that quantity is positive (β is real-strictly inside
        // the bound but its δ part drifts toward it).
        let mut delta0 = ArithRat::from_integer(1);
        for i in 0..self.assignment.len() {
            let beta = self.assignment[i];
            if let Some(b) = self.lower[i]
                && beta.real > b.value.real
                && b.value.delta > beta.delta
            {
                let ratio = (beta.real - b.value.real) / (b.value.delta - beta.delta);
                if ratio < delta0 {
                    delta0 = ratio;
                }
            }
            if let Some(b) = self.upper[i]
                && b.value.real > beta.real
                && beta.delta > b.value.delta
            {
                let ratio = (b.value.real - beta.real) / (beta.delta - b.value.delta);
                if ratio < delta0 {
                    delta0 = ratio;
                }
            }
        }
        self.assignment
            .iter()
            .map(|d| d.real + d.delta * delta0)
            .collect()
    }

    /// Set a lower bound (x >= value)
    pub fn set_lower(&mut self, var: VarId, value: ArithRat, reason: u32) {
        let idx = var as usize;
        if idx < self.lower.len() {
            // Track the old value for undo
            match self.lower[idx] {
                None => self.record(SimplexUndo::LowerWasNone(var)),
                Some(old) => self.record(SimplexUndo::LowerWasSome(var, old)),
            }
            self.lower[idx] = Some(Bound {
                kind: BoundType::Lower,
                value: DeltaRational::from_rational(value),
                reason,
            });
        }
    }

    /// Set a strict lower bound (x > value), represented as x >= value + δ
    pub fn set_strict_lower(&mut self, var: VarId, value: ArithRat, reason: u32) {
        let idx = var as usize;
        if idx < self.lower.len() {
            // Track the old value for undo
            match self.lower[idx] {
                None => self.record(SimplexUndo::LowerWasNone(var)),
                Some(old) => self.record(SimplexUndo::LowerWasSome(var, old)),
            }
            self.lower[idx] = Some(Bound {
                kind: BoundType::Lower,
                value: DeltaRational::new(value, ArithRat::one()),
                reason,
            });
        }
    }

    /// Set an upper bound (x <= value)
    pub fn set_upper(&mut self, var: VarId, value: ArithRat, reason: u32) {
        let idx = var as usize;
        if idx < self.upper.len() {
            // Track the old value for undo
            match self.upper[idx] {
                None => self.record(SimplexUndo::UpperWasNone(var)),
                Some(old) => self.record(SimplexUndo::UpperWasSome(var, old)),
            }
            self.upper[idx] = Some(Bound {
                kind: BoundType::Upper,
                value: DeltaRational::from_rational(value),
                reason,
            });
        }
    }

    /// Set a strict upper bound (x < value), represented as x <= value - δ
    pub fn set_strict_upper(&mut self, var: VarId, value: ArithRat, reason: u32) {
        let idx = var as usize;
        if idx < self.upper.len() {
            // Track the old value for undo
            match self.upper[idx] {
                None => self.record(SimplexUndo::UpperWasNone(var)),
                Some(old) => self.record(SimplexUndo::UpperWasSome(var, old)),
            }
            self.upper[idx] = Some(Bound {
                kind: BoundType::Upper,
                value: DeltaRational::new(value, -ArithRat::one()),
                reason,
            });
        }
    }

    /// Add a constraint: expr <= 0
    pub fn add_le(&mut self, mut expr: LinExpr, reason: u32) {
        // First, substitute any basic variables in expr with their non-basic expressions
        // This ensures the new constraint is properly integrated into the tableau
        let mut substituted_expr = LinExpr::constant(expr.constant);
        for (var, coef) in &expr.terms {
            if let Some(basic_expr) = self.tableau.get(var).cloned() {
                // var is basic, substitute: var = basic_expr
                // Add coef * basic_expr to substituted_expr
                substituted_expr.add_constant(coef * basic_expr.constant);
                for (inner_var, inner_coef) in &basic_expr.terms {
                    substituted_expr.add_term(*inner_var, coef * inner_coef);
                }
            } else {
                // var is non-basic, add directly
                substituted_expr.add_term(*var, *coef);
            }
        }
        expr = substituted_expr;

        // Introduce slack variable: expr + s = 0, s >= 0
        let slack = self.new_slack();
        expr.add_term(slack, ArithRat::one());

        // slack is basic, express it in terms of non-basic
        let mut slack_expr = LinExpr::constant(-expr.constant);
        for (var, coef) in &expr.terms {
            if *var != slack {
                slack_expr.add_term(*var, -*coef);
            }
        }
        // Trail mode: the fresh row needs a `RowInserted` undo (the slack's
        // array entries are covered by the `NewSlack` undo popping the arrays,
        // but the tableau row itself must be removed on pop).
        self.record_row_touch(slack);
        self.tableau.insert(slack, slack_expr);

        // Mark slack as basic (it has a tableau row defining it in terms of non-basic vars)
        if slack as usize >= self.basic.len() {
            self.basic.resize(slack as usize + 1, false);
        }
        self.basic[slack as usize] = true;

        // Set slack >= 0
        self.set_lower(slack, ArithRat::zero(), reason);
    }

    /// Add a constraint: expr >= 0
    pub fn add_ge(&mut self, mut expr: LinExpr, reason: u32) {
        expr.negate();
        self.add_le(expr, reason);
    }

    /// Add a constraint: expr = 0
    pub fn add_eq(&mut self, expr: LinExpr, reason: u32) {
        // expr <= 0 and expr >= 0
        self.add_le(expr.clone(), reason);
        self.add_ge(expr, reason);
    }

    /// Add a strict constraint: expr < 0
    /// Uses infinitesimals: expr + s = 0 with s > 0
    pub fn add_strict_lt(&mut self, mut expr: LinExpr, reason: u32) {
        // First, substitute any basic variables in expr with their non-basic expressions
        // This ensures the new constraint is properly integrated into the tableau
        let mut substituted_expr = LinExpr::constant(expr.constant);
        for (var, coef) in &expr.terms {
            if let Some(basic_expr) = self.tableau.get(var).cloned() {
                // var is basic, substitute: var = basic_expr
                // Add coef * basic_expr to substituted_expr
                substituted_expr.add_constant(coef * basic_expr.constant);
                for (inner_var, inner_coef) in &basic_expr.terms {
                    substituted_expr.add_term(*inner_var, coef * inner_coef);
                }
            } else {
                // var is non-basic, add directly
                substituted_expr.add_term(*var, *coef);
            }
        }
        expr = substituted_expr;

        // Introduce slack variable: expr + s = 0, s > 0 (strict)
        let slack = self.new_slack();
        expr.add_term(slack, ArithRat::one());

        // slack is basic, express it in terms of non-basic
        let mut slack_expr = LinExpr::constant(-expr.constant);
        for (var, coef) in &expr.terms {
            if *var != slack {
                slack_expr.add_term(*var, -*coef);
            }
        }
        // Trail mode: fresh row → `RowInserted` undo (see add_le).
        self.record_row_touch(slack);
        self.tableau.insert(slack, slack_expr);

        // Set slack > 0 (strict lower bound: slack >= 0 + δ)
        self.set_strict_lower(slack, ArithRat::zero(), reason);
    }

    /// Add a strict constraint: expr > 0
    /// Uses infinitesimals: -expr < 0
    pub fn add_strict_gt(&mut self, mut expr: LinExpr, reason: u32) {
        expr.negate();
        self.add_strict_lt(expr, reason);
    }

    /// Check if bounds are consistent
    pub fn check(&mut self) -> Result<(), Vec<u32>> {
        self.incomplete = false;
        // Check for trivially infeasible bounds
        for i in 0..self.assignment.len() {
            if let (Some(lo), Some(hi)) = (&self.lower[i], &self.upper[i])
                && lo.value > hi.value
            {
                return Err(vec![lo.reason, hi.reason]);
            }
        }

        // Apply crash basis heuristic for better starting point
        self.crash_basis();

        // Pivot to find feasible solution
        self.make_feasible()
    }

    /// Crash basis initialization for faster convergence
    ///
    /// This heuristic initializes the basis to a "good" starting point instead of
    /// starting with all slack variables. It assigns variables to their bounds
    /// based on a heuristic that tries to minimize infeasibilities.
    ///
    /// Benefits:
    /// - Reduces number of pivots needed in Phase I
    /// - Speeds up incremental solving
    /// - Particularly effective when many variables have tight bounds
    ///
    /// Reference: Koberstein's crash procedure for MIP solvers
    fn crash_basis(&mut self) {
        // Simple crash heuristic: assign non-basic variables to bounds that minimize violations
        // For each non-basic variable:
        // - If it has a lower bound, assign to lower bound
        // - Else if it has an upper bound, assign to upper bound
        // - Otherwise assign to 0

        for i in 0..self.assignment.len() {
            // Skip basic variables
            if i < self.basic.len() && self.basic[i] {
                continue;
            }

            // Choose assignment based on bounds
            if let Some(lo) = &self.lower[i] {
                // Has lower bound - assign to it
                self.assignment[i] = lo.value;
            } else if let Some(hi) = &self.upper[i] {
                // Has upper bound - assign to it
                self.assignment[i] = hi.value;
            } else {
                // No bounds - assign to 0
                self.assignment[i] = DeltaRational::zero();
            }
        }

        // Update basic variables based on tableau
        self.update_assignment();
    }

    /// Pivot to make the solution feasible
    fn make_feasible(&mut self) -> Result<(), Vec<u32>> {
        // Compute initial assignment for basic variables
        self.update_assignment();

        for _ in 0..self.max_pivots {
            // Find a violating basic variable
            let violating = self.find_violating();

            if violating.is_none() {
                return Ok(());
            }

            let (basic_var, bound) =
                violating.expect("violating basic variable must exist after is_none check");

            // Find a non-basic variable to pivot with
            let pivot_col = self.find_pivot_col(basic_var, &bound);

            match pivot_col {
                Some(nonbasic_var) => {
                    self.pivot(basic_var, nonbasic_var);
                }
                None => {
                    // No pivot possible - infeasible
                    return Err(self.explain_conflict(basic_var, &bound));
                }
            }
        }

        // Too many pivots: no conflict was found, but feasibility is UNPROVEN.
        // Flag it so the caller reports Unknown rather than a spurious Sat.
        self.incomplete = true;
        Ok(())
    }

    /// Whether the last [`check`](Self::check) gave up at the pivot cap without
    /// proving feasibility OR infeasibility — its `Ok(())` must be read as
    /// `Unknown`, not `Sat`.
    pub(super) fn last_check_incomplete(&self) -> bool {
        self.incomplete
    }

    /// Dual Simplex: Restore primal feasibility while maintaining dual feasibility
    ///
    /// The dual simplex algorithm is particularly efficient when:
    /// - After adding cuts in branch-and-bound (cuts make primal infeasible but dual stays feasible)
    /// - When resolving from a previously optimal basis after bound changes
    /// - For incremental solving where the problem structure changes slightly
    ///
    /// Unlike primal simplex which maintains primal feasibility and seeks optimality,
    /// dual simplex maintains dual feasibility (optimal reduced costs) and seeks primal feasibility.
    ///
    /// This is often faster than primal simplex after adding cutting planes because:
    /// - The dual remains feasible after most cuts
    /// - Only a few pivots are needed to restore primal feasibility
    /// - Warm-starting from the previous optimal basis is very effective
    ///
    /// Reference:
    /// - Dantzig, "Linear Programming and Extensions" (1963), Chapter 7
    /// - Bixby, "Implementing the Simplex Method" (2002)
    /// - Modern MIP solvers (CPLEX, Gurobi) use dual simplex as the primary LP solver
    pub fn dual_simplex(&mut self) -> Result<(), Vec<u32>> {
        // Compute initial assignment
        self.update_assignment();

        for _ in 0..self.max_pivots {
            // Find a basic variable that violates its bounds (primal infeasible)
            let violating = self.find_violating();

            if violating.is_none() {
                return Ok(()); // Primal feasible - done!
            }

            let (leaving_var, bound) =
                violating.expect("violating basic variable must exist after is_none check");

            // Find entering variable that maintains dual feasibility
            let entering = self.find_dual_pivot_col(leaving_var, &bound);

            match entering {
                Some(entering_var) => {
                    // Pivot: leaving_var exits basis, entering_var enters basis
                    self.pivot(leaving_var, entering_var);
                }
                None => {
                    // No dual-feasible pivot exists - problem is infeasible
                    return Err(self.explain_conflict(leaving_var, &bound));
                }
            }
        }

        // Too many pivots - unknown (possibly cycling or unbounded)
        Ok(())
    }

    /// Find entering variable for dual simplex (maintains dual feasibility)
    ///
    /// Given a leaving variable (basic var violating bounds), find a non-basic variable
    /// to enter the basis such that:
    /// 1. The pivot reduces the bound violation
    /// 2. Dual feasibility is maintained (reduced costs stay optimal)
    ///
    /// For leaving variable x_i with row: x_i = c + sum(a_j * x_j)
    ///
    /// If x_i < lower_i (too small):
    /// - Need to increase x_i
    /// - Choose x_j with a_j > 0 (increases x_i) and can increase
    /// - Or x_j with a_j < 0 (decreases moves x_i up) and can decrease
    ///
    /// If x_i > upper_i (too large):
    /// - Need to decrease x_i
    /// - Choose x_j with a_j < 0 (increases x_j decreases x_i) and can increase
    /// - Or x_j with a_j > 0 (decreases x_j decreases x_i) and can decrease
    ///
    /// Among eligible variables, choose the one that maintains dual feasibility.
    /// This typically means choosing the variable with the smallest ratio of:
    /// (change in objective) / (change in constraint violation)
    ///
    /// For now, we use a simple rule: choose the first eligible variable (Bland's rule for dual)
    #[allow(dead_code)]
    fn find_dual_pivot_col(&self, leaving_var: VarId, bound: &Bound) -> Option<VarId> {
        let expr = self.tableau.get(&leaving_var)?;

        // Simple dual pivot selection: choose first eligible non-basic variable
        // A more sophisticated implementation would use ratio tests to ensure dual feasibility

        let mut best_var = None;

        for (var, coef) in &expr.terms {
            let can_increase = self.can_increase(*var);
            let can_decrease = self.can_decrease(*var);

            // Determine if this variable is eligible for dual pivot
            let is_eligible = match bound.kind {
                BoundType::Lower => {
                    // leaving_var < lower_bound, need to increase it
                    // If coef > 0: increasing var increases leaving_var ✓
                    // If coef < 0: decreasing var increases leaving_var ✓
                    (*coef > ArithRat::zero() && can_increase)
                        || (*coef < ArithRat::zero() && can_decrease)
                }
                BoundType::Upper => {
                    // leaving_var > upper_bound, need to decrease it
                    // If coef < 0: increasing var decreases leaving_var ✓
                    // If coef > 0: decreasing var decreases leaving_var ✓
                    (*coef < ArithRat::zero() && can_increase)
                        || (*coef > ArithRat::zero() && can_decrease)
                }
                _ => false,
            };

            if is_eligible {
                // Use Bland's rule for anti-cycling: choose smallest index
                best_var = match best_var {
                    None => Some(*var),
                    Some(current) if *var < current => Some(*var),
                    Some(current) => Some(current),
                };
            }
        }

        best_var
    }

    /// Find a basic variable that violates its bounds.
    ///
    /// Selection is CONTENT-deterministic (smallest violating `VarId`, i.e.
    /// Bland's leaving-variable rule), NOT first-in-map-iteration-order: the
    /// `FxHashMap` iteration order depends on the table's internal layout
    /// (capacity/tombstone history), which is not part of the logical solver
    /// state — two solvers with bit-identical contents can iterate their
    /// tableaus differently (e.g. after a pop, a trail-mode backtrack keeps
    /// the grown table while a snapshot restore returns to the push-time
    /// clone's layout). The pivot sequence — and hence which of the many valid
    /// feasible points `check()` lands on — must be a function of content
    /// alone so that the trail/snapshot randomized differential can demand
    /// bit-identical states after every operation.
    fn find_violating(&self) -> Option<(VarId, Bound)> {
        if !self.deterministic_violating {
            // Legacy trunk selection: first violating row in map-iteration
            // order. Layout-dependent but byte-identical to the pre-trail
            // engine — Snapshot mode keeps it so the default build's search
            // trajectory is exactly the trunk's.
            for var in self.tableau.keys() {
                let idx = *var as usize;
                let val = self.assignment[idx];
                if let Some(lo) = self.lower[idx]
                    && val < lo.value
                {
                    return Some((*var, lo));
                }
                if let Some(hi) = self.upper[idx]
                    && val > hi.value
                {
                    return Some((*var, hi));
                }
            }
            return None;
        }
        let mut best: Option<(VarId, Bound)> = None;
        for var in self.tableau.keys() {
            if best.is_some_and(|(b, _)| b <= *var) {
                continue;
            }
            let idx = *var as usize;
            let val = self.assignment[idx];

            if let Some(lo) = self.lower[idx]
                && val < lo.value
            {
                best = Some((*var, lo));
                continue;
            }

            if let Some(hi) = self.upper[idx]
                && val > hi.value
            {
                best = Some((*var, hi));
            }
        }
        best
    }

    /// Test-only: force the layout-independent victim selection so a
    /// Snapshot instance can be compared bit-identically against a Trail
    /// twin (the cross-mode differential's precondition).
    #[cfg(test)]
    pub(crate) fn force_deterministic_violating(&mut self) {
        self.deterministic_violating = true;
    }

    /// Find a non-basic variable to pivot with using the configured pivoting rule
    fn find_pivot_col(&self, basic_var: VarId, bound: &Bound) -> Option<VarId> {
        let expr = self.tableau.get(&basic_var)?;

        match self.pivoting_rule {
            PivotingRule::Bland => {
                // Bland's rule: choose the smallest index among eligible variables
                // This prevents cycling
                let mut best_var = None;

                for (var, coef) in &expr.terms {
                    let can_increase = self.can_increase(*var);
                    let can_decrease = self.can_decrease(*var);
                    let is_eligible = match bound.kind {
                        BoundType::Lower => {
                            (*coef > ArithRat::zero() && can_increase)
                                || (*coef < ArithRat::zero() && can_decrease)
                        }
                        BoundType::Upper => {
                            (*coef < ArithRat::zero() && can_increase)
                                || (*coef > ArithRat::zero() && can_decrease)
                        }
                        _ => false,
                    };

                    if is_eligible {
                        best_var = match best_var {
                            None => Some(*var),
                            Some(current) if *var < current => Some(*var),
                            Some(current) => Some(current),
                        };
                    }
                }
                best_var
            }
            PivotingRule::Dantzig => {
                // Dantzig's rule: choose variable with largest improvement
                let mut best_var = None;
                let mut best_improvement = ArithRat::zero();

                for (var, coef) in &expr.terms {
                    let can_increase = self.can_increase(*var);
                    let can_decrease = self.can_decrease(*var);

                    let improvement = match bound.kind {
                        BoundType::Lower if *coef > ArithRat::zero() && can_increase => {
                            coef.abs()
                        }
                        BoundType::Lower if *coef < ArithRat::zero() && can_decrease => {
                            coef.abs()
                        }
                        BoundType::Upper if *coef < ArithRat::zero() && can_increase => {
                            coef.abs()
                        }
                        BoundType::Upper if *coef > ArithRat::zero() && can_decrease => {
                            coef.abs()
                        }
                        _ => ArithRat::zero(),
                    };

                    if improvement > best_improvement {
                        best_improvement = improvement;
                        best_var = Some(*var);
                    }
                }
                best_var
            }
            PivotingRule::SteepestEdge => {
                // Steepest edge: similar to Dantzig but considers edge norms
                // For simplicity, fall back to Dantzig's rule
                // A full implementation would maintain edge weights
                let mut best_var = None;
                let mut best_score = ArithRat::zero();

                for (var, coef) in &expr.terms {
                    let can_increase = self.can_increase(*var);
                    let can_decrease = self.can_decrease(*var);

                    let score = match bound.kind {
                        BoundType::Lower if *coef > ArithRat::zero() && can_increase => {
                            coef.abs()
                        }
                        BoundType::Lower if *coef < ArithRat::zero() && can_decrease => {
                            coef.abs()
                        }
                        BoundType::Upper if *coef < ArithRat::zero() && can_increase => {
                            coef.abs()
                        }
                        BoundType::Upper if *coef > ArithRat::zero() && can_decrease => {
                            coef.abs()
                        }
                        _ => ArithRat::zero(),
                    };

                    if score > best_score {
                        best_score = score;
                        best_var = Some(*var);
                    }
                }
                best_var
            }
            PivotingRule::PartialPricing => {
                // Partial pricing: check only a subset of candidates to reduce overhead
                // Effective for large problems where full pricing is expensive
                //
                // Strategy: check every k-th variable instead of all variables
                // This reduces the complexity of pivot column selection from O(n) to O(n/k)
                const SAMPLE_RATE: usize = 4; // Check every 4th variable

                let mut best_var = None;
                let mut best_improvement = ArithRat::zero();
                let mut count = 0;

                for (var, coef) in &expr.terms {
                    // Skip most variables, only check every SAMPLE_RATE-th one
                    count += 1;
                    if count % SAMPLE_RATE != 0 {
                        continue;
                    }

                    let can_increase = self.can_increase(*var);
                    let can_decrease = self.can_decrease(*var);

                    let improvement = match bound.kind {
                        BoundType::Lower if *coef > ArithRat::zero() && can_increase => {
                            coef.abs()
                        }
                        BoundType::Lower if *coef < ArithRat::zero() && can_decrease => {
                            coef.abs()
                        }
                        BoundType::Upper if *coef < ArithRat::zero() && can_increase => {
                            coef.abs()
                        }
                        BoundType::Upper if *coef > ArithRat::zero() && can_decrease => {
                            coef.abs()
                        }
                        _ => ArithRat::zero(),
                    };

                    if improvement > best_improvement {
                        best_improvement = improvement;
                        best_var = Some(*var);
                    }
                }

                // If no candidate found in sample, fall back to first eligible
                if best_var.is_none() {
                    for (var, coef) in &expr.terms {
                        let can_increase = self.can_increase(*var);
                        let can_decrease = self.can_decrease(*var);
                        let is_eligible = match bound.kind {
                            BoundType::Lower => {
                                (*coef > ArithRat::zero() && can_increase)
                                    || (*coef < ArithRat::zero() && can_decrease)
                            }
                            BoundType::Upper => {
                                (*coef < ArithRat::zero() && can_increase)
                                    || (*coef > ArithRat::zero() && can_decrease)
                            }
                            _ => false,
                        };

                        if is_eligible {
                            return Some(*var);
                        }
                    }
                }

                best_var
            }
        }
    }

    /// Check if a variable can be increased
    #[inline]
    pub(super) fn can_increase(&self, var: VarId) -> bool {
        let idx = var as usize;
        // adsmt-patch (rc.30): a variable whose bound vectors were
        // not yet extended (idx past `upper.len()`) has no upper
        // bound — treat it as unbounded rather than panicking on
        // an out-of-range index.
        match self.upper.get(idx) {
            Some(Some(hi)) => self.assignment.get(idx).is_none_or(|a| *a < hi.value),
            _ => true,
        }
    }

    /// Check if a variable can be decreased
    #[inline]
    pub(super) fn can_decrease(&self, var: VarId) -> bool {
        let idx = var as usize;
        // adsmt-patch (rc.30): see `can_increase` — an unallocated
        // bound slot means no lower bound.
        match self.lower.get(idx) {
            Some(Some(lo)) => self.assignment.get(idx).is_none_or(|a| *a > lo.value),
            _ => true,
        }
    }

    /// Perform a pivot operation
    pub(super) fn pivot(&mut self, basic_var: VarId, nonbasic_var: VarId) {
        #[cfg(feature = "profiling")]
        let _timer = ScopedTimer::new(ProfilingCategory::SimplexPivot);
        // Trail mode: `basic_var`'s row is removed below — save it at first
        // in-scope touch.
        self.record_row_touch(basic_var);
        let expr = self
            .tableau
            .remove(&basic_var)
            .expect("basic variable must have expression in tableau");

        // Find coefficient of nonbasic in basic's row
        let coef = expr
            .terms
            .iter()
            .find(|(v, _)| *v == nonbasic_var)
            .map(|(_, c)| *c)
            .expect("nonbasic variable must appear in basic variable's expression");

        // Express nonbasic in terms of basic
        let mut new_expr = LinExpr::new();
        new_expr.add_term(basic_var, ArithRat::one() / coef);
        new_expr.add_constant(-expr.constant / coef);

        for (var, c) in &expr.terms {
            if *var != nonbasic_var {
                new_expr.add_term(*var, -*c / coef);
            }
        }

        // Trail mode: rows modified in-place below must be saved at their
        // first in-scope touch. Inlined epoch check (rather than
        // `record_row_touch`) because the loop holds `&mut self.tableau`;
        // `row_save_epoch`/`undo_stack` are disjoint fields.
        let row_epoch = if self.backtrack == BacktrackMode::Trail {
            self.undo_marks.last().map(|&(_, e)| e)
        } else {
            None
        };

        // Substitute into other rows
        for (var, row) in self.tableau.iter_mut() {
            let sub_coef = row
                .terms
                .iter()
                .find(|(v, _)| *v == nonbasic_var)
                .map(|(_, c)| *c);

            if let Some(sc) = sub_coef {
                if let Some(epoch) = row_epoch {
                    let idx = *var as usize;
                    if self.row_save_epoch[idx] != epoch {
                        self.row_save_epoch[idx] = epoch;
                        self.undo_stack
                            .push(SimplexUndo::RowReplaced(*var, row.clone()));
                    }
                }
                row.terms.retain(|(v, _)| *v != nonbasic_var);
                row.constant += sc * new_expr.constant;
                for (v, c) in &new_expr.terms {
                    row.add_term(*v, sc * *c);
                }
            }
        }

        // Trail mode: `nonbasic_var` gains a row (it was non-basic, so absent
        // → `RowInserted` at first touch; a same-scope earlier touch already
        // holds the authoritative pre-scope record and is kept by the epoch
        // skip — LIFO replay makes the EARLIEST record win).
        self.record_row_touch(nonbasic_var);
        self.tableau.insert(nonbasic_var, new_expr);
        self.record_basic_flip(basic_var);
        self.basic[basic_var as usize] = false;
        self.record_basic_flip(nonbasic_var);
        self.basic[nonbasic_var as usize] = true;

        // Update assignment
        self.update_assignment();
    }

    /// Update variable assignments after pivot
    pub(super) fn update_assignment(&mut self) {
        let num_vars = self.assignment.len();

        // Non-basic variables keep their bounds
        for i in 0..num_vars {
            if !self.basic[i] {
                if let Some(lo) = &self.lower[i] {
                    self.assignment[i] = lo.value;
                } else if let Some(hi) = &self.upper[i] {
                    self.assignment[i] = hi.value;
                }
            }
        }

        // Compute basic variables from their rows
        // Skip entries with stale variable references (can happen after pop)
        for (var, expr) in &self.tableau {
            let var_idx = *var as usize;
            if var_idx >= num_vars {
                continue; // Skip stale tableau entry
            }

            let mut val = DeltaRational::from_rational(expr.constant);
            let mut has_stale_ref = false;

            for (v, c) in &expr.terms {
                let v_idx = *v as usize;
                if v_idx >= num_vars {
                    has_stale_ref = true;
                    break;
                }
                // Fused `val += assignment[v] * c` with bit-identical zero fast
                // paths (skips the delta lane entirely for values coming from
                // non-strict bounds — the dominant case).
                val.add_mul(&self.assignment[v_idx], c);
            }

            if !has_stale_ref {
                self.assignment[var_idx] = val;
            }
        }
    }

    /// Explain why a conflict occurred using Farkas lemma
    ///
    /// When a basic variable x_i violates its bounds and no pivot is possible,
    /// we can derive a conflict clause from the bounds of all involved variables.
    ///
    /// For x_i = c + sum(a_j * x_j):
    /// - If x_i < lower(x_i), we need to explain why x_i can't reach its lower bound
    /// - If x_i > upper(x_i), we need to explain why x_i can't decrease to its upper bound
    ///
    /// The conflict clause contains the reasons for all the bounds that prevent a pivot.
    fn explain_conflict(&self, basic_var: VarId, bound: &Bound) -> Vec<u32> {
        let mut reasons = Vec::new();

        // Add the violated bound's reason
        reasons.push(bound.reason);

        // Get the row for this basic variable
        let expr = match self.tableau.get(&basic_var) {
            Some(e) => e,
            None => return reasons,
        };

        // For each non-basic variable in the row, add the reason for the bound
        // that prevents pivoting
        for (var, coef) in &expr.terms {
            let var_idx = *var as usize;

            match bound.kind {
                BoundType::Lower => {
                    // We need to increase basic_var but couldn't find a pivot
                    // For each non-basic variable:
                    // - If coef > 0, we need to increase it, so its upper bound blocks us
                    // - If coef < 0, we need to decrease it, so its lower bound blocks us
                    if *coef > ArithRat::zero()
                        && let Some(hi) = &self.upper[var_idx]
                        && !reasons.contains(&hi.reason)
                    {
                        reasons.push(hi.reason);
                    } else if *coef < ArithRat::zero()
                        && let Some(lo) = &self.lower[var_idx]
                        && !reasons.contains(&lo.reason)
                    {
                        reasons.push(lo.reason);
                    }
                }
                BoundType::Upper => {
                    // We need to decrease basic_var but couldn't find a pivot
                    // For each non-basic variable:
                    // - If coef > 0, we need to decrease it, so its lower bound blocks us
                    // - If coef < 0, we need to increase it, so its upper bound blocks us
                    if *coef > ArithRat::zero()
                        && let Some(lo) = &self.lower[var_idx]
                        && !reasons.contains(&lo.reason)
                    {
                        reasons.push(lo.reason);
                    } else if *coef < ArithRat::zero()
                        && let Some(hi) = &self.upper[var_idx]
                        && !reasons.contains(&hi.reason)
                    {
                        reasons.push(hi.reason);
                    }
                }
                _ => {}
            }
        }

        reasons
    }

    /// Perform bound propagation through the tableau
    ///
    /// For each basic variable x_i = c + sum(a_j * x_j), we can derive bounds:
    /// - If all x_j have bounds, we can compute bounds for x_i
    /// - If x_i has a bound, we may derive bounds for x_j
    pub fn propagate_bounds(&mut self) {
        self.propagated.clear();

        // Propagate forward: derive bounds for basic variables from non-basic bounds
        for (basic_var, expr) in &self.tableau {
            if let Some(bound) = self.derive_basic_bound(*basic_var, expr) {
                self.propagated.push(bound);
            }
        }

        // Apply propagated bounds
        for prop in &self.propagated {
            let idx = prop.var as usize;
            if idx >= self.lower.len() {
                continue;
            }

            if prop.is_lower {
                // Check if this tightens existing lower bound
                let should_update = match &self.lower[idx] {
                    None => true,
                    Some(existing) => prop.value > existing.value,
                };
                if should_update {
                    self.lower[idx] = Some(Bound {
                        kind: BoundType::Lower,
                        value: prop.value,
                        reason: prop.reasons.first().copied().unwrap_or(0),
                    });
                }
            } else {
                // Check if this tightens existing upper bound
                let should_update = match &self.upper[idx] {
                    None => true,
                    Some(existing) => prop.value < existing.value,
                };
                if should_update {
                    self.upper[idx] = Some(Bound {
                        kind: BoundType::Upper,
                        value: prop.value,
                        reason: prop.reasons.first().copied().unwrap_or(0),
                    });
                }
            }
        }
    }

    /// Derive bounds for a basic variable from bounds on non-basic variables
    ///
    /// For basic variable x_i = c + sum(a_j * x_j):
    /// - Lower bound: sum of (a_j * lower(x_j) if a_j > 0, a_j * upper(x_j) if a_j < 0)
    /// - Upper bound: sum of (a_j * upper(x_j) if a_j > 0, a_j * lower(x_j) if a_j < 0)
    fn derive_basic_bound(&self, basic_var: VarId, expr: &LinExpr) -> Option<PropagatedBound> {
        let idx = basic_var as usize;

        // Try to derive lower bound
        let mut lower_sum = DeltaRational::from_rational(expr.constant);
        let mut lower_reasons: SmallVec<[u32; 4]> = SmallVec::new();
        let mut can_derive_lower = true;

        for (var, coef) in &expr.terms {
            let var_idx = *var as usize;
            if *coef > ArithRat::zero() {
                // Positive coefficient: need lower bound
                if let Some(lo) = &self.lower[var_idx] {
                    lower_sum += lo.value * *coef;
                    lower_reasons.push(lo.reason);
                } else {
                    can_derive_lower = false;
                    break;
                }
            } else {
                // Negative coefficient: need upper bound
                if let Some(hi) = &self.upper[var_idx] {
                    lower_sum += hi.value * *coef;
                    lower_reasons.push(hi.reason);
                } else {
                    can_derive_lower = false;
                    break;
                }
            }
        }

        // Check if derived lower bound is tighter than existing
        if can_derive_lower {
            let is_tighter = match &self.lower[idx] {
                None => true,
                Some(existing) => lower_sum > existing.value,
            };
            if is_tighter {
                return Some(PropagatedBound {
                    var: basic_var,
                    is_lower: true,
                    value: lower_sum,
                    reasons: lower_reasons,
                });
            }
        }

        // Try to derive upper bound
        let mut upper_sum = DeltaRational::from_rational(expr.constant);
        let mut upper_reasons: SmallVec<[u32; 4]> = SmallVec::new();
        let mut can_derive_upper = true;

        for (var, coef) in &expr.terms {
            let var_idx = *var as usize;
            if *coef > ArithRat::zero() {
                // Positive coefficient: need upper bound
                if let Some(hi) = &self.upper[var_idx] {
                    upper_sum += hi.value * *coef;
                    upper_reasons.push(hi.reason);
                } else {
                    can_derive_upper = false;
                    break;
                }
            } else {
                // Negative coefficient: need lower bound
                if let Some(lo) = &self.lower[var_idx] {
                    upper_sum += lo.value * *coef;
                    upper_reasons.push(lo.reason);
                } else {
                    can_derive_upper = false;
                    break;
                }
            }
        }

        // Check if derived upper bound is tighter than existing
        if can_derive_upper {
            let is_tighter = match &self.upper[idx] {
                None => true,
                Some(existing) => upper_sum < existing.value,
            };
            if is_tighter {
                return Some(PropagatedBound {
                    var: basic_var,
                    is_lower: false,
                    value: upper_sum,
                    reasons: upper_reasons,
                });
            }
        }

        None
    }

    /// Get pending propagated bounds
    #[must_use]
    pub fn get_propagated(&self) -> &[PropagatedBound] {
        &self.propagated
    }

    /// Clear propagated bounds
    pub fn clear_propagated(&mut self) {
        self.propagated.clear();
    }

    /// Tighten bounds on a variable if possible
    /// Returns true if bounds were tightened
    pub fn tighten_bounds(&mut self, var: VarId) -> bool {
        let idx = var as usize;
        let mut changed = false;

        // If this is a basic variable, check its expression
        if let Some(expr) = self.tableau.get(&var).cloned()
            && let Some(prop) = self.derive_basic_bound(var, &expr)
        {
            if prop.is_lower {
                let should_update = match &self.lower[idx] {
                    None => true,
                    Some(existing) => prop.value > existing.value,
                };
                if should_update {
                    self.lower[idx] = Some(Bound {
                        kind: BoundType::Lower,
                        value: prop.value,
                        reason: prop.reasons.first().copied().unwrap_or(0),
                    });
                    changed = true;
                }
            } else {
                let should_update = match &self.upper[idx] {
                    None => true,
                    Some(existing) => prop.value < existing.value,
                };
                if should_update {
                    self.upper[idx] = Some(Bound {
                        kind: BoundType::Upper,
                        value: prop.value,
                        reason: prop.reasons.first().copied().unwrap_or(0),
                    });
                    changed = true;
                }
            }
        }

        changed
    }

    /// Get the number of original (non-slack) variables
    #[must_use]
    pub fn num_original_vars(&self) -> usize {
        self.num_vars
    }

    /// Get lower bound of a variable (if any)
    #[must_use]
    pub fn get_lower(&self, var: VarId) -> Option<&Bound> {
        self.lower.get(var as usize).and_then(|b| b.as_ref())
    }

    /// Get upper bound of a variable (if any)
    #[must_use]
    pub fn get_upper(&self, var: VarId) -> Option<&Bound> {
        self.upper.get(var as usize).and_then(|b| b.as_ref())
    }

    /// Reset the solver
    pub fn reset(&mut self) {
        self.num_vars = 0;
        self.num_slack = 0;
        self.assignment.clear();
        self.lower.clear();
        self.upper.clear();
        self.tableau.clear();
        self.basic.clear();
        self.infeasible = None;
        self.propagated.clear();
        self.undo_stack.clear();
        self.undo_marks = Self::initial_marks(self.backtrack);
        // `push_epoch` is deliberately NOT reset: epochs are never reused, so
        // a stale `row_save_epoch` stamp surviving a reset (there are none —
        // the vec is cleared — but belt-and-braces) can never match.
        self.row_save_epoch.clear();
        self.cached_assignments.clear();
        self.saved_tableaux.clear();
    }

    /// Push a new decision level
    pub fn push(&mut self) {
        // One checkpoint into the single undo funnel, tagged with a fresh
        // scope epoch (monotone, never reused — see `row_save_epoch`).
        self.push_epoch += 1;
        self.undo_marks
            .push((self.undo_stack.checkpoint(), self.push_epoch));
        // Cache current assignment for warm-starting on pop (basis caching).
        // This snapshot STAYS in trail mode as the documented single-funnel
        // exception: `DeltaRational` is `Copy`, so the clone is a memcpy (not
        // the profiled cost), while `update_assignment` wholesale-rewrites
        // every entry on each pivot — element-wise trailing of it would be
        // pathological (one undo record per var per pivot).
        self.cached_assignments.push(self.assignment.clone());
        // Snapshot mode only: save the full tableau snapshot so that pivots
        // during check() inside the pushed scope can be wholesale-undone on
        // pop(). Trail mode undoes them row-by-row from the undo spine and
        // skips this clone entirely (it was the dominant push cost).
        if self.backtrack == BacktrackMode::Snapshot {
            self.saved_tableaux
                .push((self.tableau.clone(), self.basic.clone()));
        }
    }

    /// Pop to previous decision level
    pub fn pop(&mut self) {
        let Some((mark, _epoch)) = self.undo_marks.pop() else {
            // Trail mode with no outstanding scope: nothing was recorded at
            // base level, so an unmatched pop is a no-op. (Snapshot mode keeps
            // its legacy base mark, so it reaches here only after ALREADY
            // consuming that mark — matching the old `trail_limits`-empty
            // no-op verbatim.)
            return;
        };

        // Undo all operations since the mark, LIFO (`drain_since` yields
        // reverse-push order — verified in the vendored VecScopedStack).
        // Direct iteration is fine: the drain borrows only `self.undo_stack`;
        // the arms touch disjoint fields.
        for undo in self.undo_stack.drain_since(mark) {
            match undo {
                SimplexUndo::LowerWasNone(var) => {
                    self.lower[var as usize] = None;
                }
                SimplexUndo::LowerWasSome(var, old) => {
                    self.lower[var as usize] = Some(old);
                }
                SimplexUndo::UpperWasNone(var) => {
                    self.upper[var as usize] = None;
                }
                SimplexUndo::UpperWasSome(var, old) => {
                    self.upper[var as usize] = Some(old);
                }
                SimplexUndo::NewVar => {
                    self.num_vars -= 1;
                    self.assignment.pop();
                    self.lower.pop();
                    self.upper.pop();
                    self.basic.pop();
                    self.row_save_epoch.pop();
                }
                SimplexUndo::NewSlack(id) => {
                    self.num_slack -= 1;
                    self.assignment.pop();
                    self.lower.pop();
                    self.upper.pop();
                    self.basic.pop();
                    self.row_save_epoch.pop();
                    // Tableau row removal: trail mode drains this scope's
                    // `RowInserted(id)` BEFORE this arm (it was recorded
                    // after `NewSlack` — LIFO); snapshot mode restores the
                    // snapshot below.
                    let _ = id;
                }
                SimplexUndo::RowInserted(var) => {
                    // Trail mode only: the scope inserted a row where none
                    // existed — remove it (the key may legitimately be absent
                    // if a later same-scope pivot already removed it; those
                    // later mutations were epoch-skipped, and this earliest
                    // record is the authority).
                    self.tableau.remove(&var);
                }
                SimplexUndo::RowReplaced(var, old_row) => {
                    // Trail mode only: restore the pre-scope row verbatim
                    // (clone preserved exact term order), overwriting any
                    // in-scope replacement or re-creating a removed row.
                    self.tableau.insert(var, old_row);
                }
                SimplexUndo::BasicFlag(var, old) => {
                    // Trail mode only: walk the flip back. Every flip is
                    // recorded, so the LIFO walk ends at the pre-push value.
                    self.basic[var as usize] = old;
                }
            }
        }

        match self.backtrack {
            BacktrackMode::Snapshot => {
                // Restore the full tableau snapshot saved at push time.
                // This correctly undoes any pivots performed during check() inside
                // the pushed scope, which is critical for sound probe-and-pop operations
                // (e.g., Nelson-Oppen equality detection).
                if let Some((saved_tableau, saved_basic)) = self.saved_tableaux.pop() {
                    self.tableau = saved_tableau;
                    // Restore basic flags up to current length.
                    let cur_len = self.basic.len();
                    let restore_len = saved_basic.len().min(cur_len);
                    self.basic[..restore_len].copy_from_slice(&saved_basic[..restore_len]);
                    // Ensure any remaining entries are set to false (shouldn't happen normally).
                    for item in self.basic.iter_mut().skip(restore_len) {
                        *item = false;
                    }
                }
                // Scrub stale-variable references from the restored tableau, for BOTH
                // the snapshot and the no-snapshot paths. The trail undo above is the
                // authority on which variables are live (it pops exactly this scope's
                // `NewVar`/`NewSlack`), so `assignment.len()` is the live count. A
                // restored tableau row keyed by — or whose expression references — a
                // variable id `>= assignment.len()` is a leftover of a popped scope
                // (the snapshot path can carry one in from a previously-dirty
                // snapshot, propagating it forward). Dropping such rows enforces the
                // invariant "the tableau only references live variables", without
                // which a later `pivot` indexes the parallel arrays out of bounds —
                // a hard panic on otherwise-valid push/pop input (surfaced by the
                // persistent OxiZ delegation feeding a prelude-scale multi-`(push)`
                // session: `simplex.rs` pivot OOB, `basic.len`=N vs a tableau var id
                // `>N`). A popped variable is not a real variable, so dropping its
                // (corrupt) row is sound.
                //
                // TRAIL MODE HAS NO FORWARD STALENESS CHANNEL and therefore no
                // scrub (see the Trail arm below): every in-scope tableau/flag
                // mutation flows through exactly one recorded funnel
                // (`add_le`/`add_strict_lt` inserts, `pivot`
                // remove/modify/insert/flips) and is exactly reverted by the
                // LIFO drain above. By induction over scopes — if the
                // invariant "tableau keys and row terms reference only live
                // variables, and `basic` mirrors row ownership" held at push
                // time, the drain restores that exact state at pop time —
                // stale rows can never be created, carried in, or propagated
                // forward. The snapshot path cannot make that argument
                // precisely because a restored snapshot may predate (or
                // outlive) trail-undone variable allocations, so it keeps the
                // scrub.
                let num_vars = self.assignment.len();
                self.tableau.retain(|&var, expr| {
                    (var as usize) < num_vars
                        && expr.terms.iter().all(|(v, _)| (*v as usize) < num_vars)
                });
                // Keep the basic-flag vector consistent with the live variable set:
                // size it to `num_vars`, and clear the flag of any variable no longer
                // carrying a tableau row (it cannot be basic without one).
                if self.basic.len() != num_vars {
                    self.basic.resize(num_vars, false);
                }
                for i in 0..num_vars {
                    if self.basic[i] && !self.tableau.contains_key(&(i as VarId)) {
                        self.basic[i] = false;
                    }
                }

                // Restore cached assignment for warm-starting.
                if let Some(cached) = self.cached_assignments.pop() {
                    let restore_len = cached.len().min(self.assignment.len());
                    self.assignment[..restore_len].copy_from_slice(&cached[..restore_len]);
                    for item in self.assignment.iter_mut().skip(restore_len) {
                        *item = DeltaRational::zero();
                    }
                } else {
                    for item in self.assignment.iter_mut() {
                        *item = DeltaRational::zero();
                    }
                }
            }
            BacktrackMode::Trail => {
                // No scrub needed (no forward staleness channel — see the
                // induction argument in the Snapshot arm above). Debug builds
                // verify the restored invariants with a full scan in the
                // scrub's place:
                #[cfg(debug_assertions)]
                {
                    let n = self.assignment.len();
                    debug_assert_eq!(
                        self.basic.len(),
                        n,
                        "trail pop: basic/assignment length desync"
                    );
                    for (var, expr) in &self.tableau {
                        debug_assert!(
                            (*var as usize) < n,
                            "trail pop: stale tableau key {var} >= {n}"
                        );
                        for (v, _) in &expr.terms {
                            debug_assert!(
                                (*v as usize) < n,
                                "trail pop: stale term var {v} in row {var} (n={n})"
                            );
                        }
                    }
                    for i in 0..n {
                        debug_assert_eq!(
                            self.basic[i],
                            self.tableau.contains_key(&(i as VarId)),
                            "trail pop: basic flag desync at var {i}"
                        );
                    }
                }

                // Restore the push-time assignment (warm-start cache). The
                // exact undo replay above already restored the allocation
                // count, so the lengths must agree; move the cached vec in
                // wholesale.
                if let Some(cached) = self.cached_assignments.pop() {
                    debug_assert_eq!(
                        cached.len(),
                        self.assignment.len(),
                        "trail pop: cached assignment length desync"
                    );
                    self.assignment = cached;
                }
            }
        }

        self.infeasible = None;
    }

    /// Get the current decision level
    #[must_use]
    pub fn decision_level(&self) -> usize {
        match self.backtrack {
            // Trail mode: one mark per outstanding push, no base entry.
            BacktrackMode::Trail => self.undo_marks.len(),
            // Snapshot mode: legacy base entry occupies one slot (and can be
            // consumed by an unmatched pop — `saturating_sub` mirrors the old
            // `trail_limits` arithmetic byte-for-byte).
            BacktrackMode::Snapshot => self.undo_marks.len().saturating_sub(1),
        }
    }

    // ── Accessor helpers for the optimization extension (simplex_opt.rs) ─────

    /// Number of allocated variable slots (original + slack).
    #[inline]
    pub(super) fn assignment_len(&self) -> usize {
        self.assignment.len()
    }

    /// Real-part of the assignment at index `idx`.
    #[inline]
    pub(super) fn assignment_real_at(&self, idx: usize) -> ArithRat {
        self.assignment[idx].real
    }

    /// Full `DeltaRational` assignment at index `idx`.
    #[inline]
    pub(super) fn assignment_at(&self, idx: usize) -> ArithRat {
        self.assignment[idx].real
    }

    /// Whether variable at `idx` is currently basic.
    #[inline]
    pub(super) fn is_basic(&self, idx: usize) -> bool {
        idx < self.basic.len() && self.basic[idx]
    }

    /// Iterate over `(basic_var, row)` pairs in the tableau.
    pub(super) fn tableau_iter(&self) -> impl Iterator<Item = (&VarId, &LinExpr)> {
        self.tableau.iter()
    }

    /// Iterate over basic variable IDs in the tableau.
    pub(super) fn tableau_keys(&self) -> impl Iterator<Item = VarId> + '_ {
        self.tableau.keys().copied()
    }

    /// Return the coefficient of `nonbasic` in the row of `basic`, or `None`.
    pub(super) fn tableau_coef_of(&self, basic: VarId, nonbasic: VarId) -> Option<ArithRat> {
        self.tableau.get(&basic).and_then(|row| {
            row.terms
                .iter()
                .find(|(v, _)| *v == nonbasic)
                .map(|(_, c)| *c)
        })
    }

    /// Real part of the upper bound for variable at `idx`, if any.
    #[inline]
    pub(super) fn upper_real_at(&self, idx: usize) -> Option<ArithRat> {
        self.upper
            .get(idx)
            .and_then(|b| b.as_ref().map(|b| b.value.real))
    }

    /// Real part of the lower bound for variable at `idx`, if any.
    #[inline]
    pub(super) fn lower_real_at(&self, idx: usize) -> Option<ArithRat> {
        self.lower
            .get(idx)
            .and_then(|b| b.as_ref().map(|b| b.value.real))
    }

    /// Full `DeltaRational` upper bound for variable at `idx`, if any.
    #[inline]
    pub(super) fn upper_delta_at(&self, idx: usize) -> Option<DeltaRational> {
        self.upper
            .get(idx)
            .and_then(|b| b.as_ref().map(|b| b.value))
    }

    /// Full `DeltaRational` lower bound for variable at `idx`, if any.
    #[inline]
    pub(super) fn lower_delta_at(&self, idx: usize) -> Option<DeltaRational> {
        self.lower
            .get(idx)
            .and_then(|b| b.as_ref().map(|b| b.value))
    }

    /// Overwrite the assignment at `idx` with `val`.
    #[inline]
    pub(super) fn set_assignment_at(&mut self, idx: usize, val: DeltaRational) {
        self.assignment[idx] = val;
    }

    /// Maximum pivot count configured for this instance.
    #[inline]
    pub(super) fn max_pivots(&self) -> usize {
        self.max_pivots
    }
}

pub use super::simplex_opt::SimplexOptStatus;

#[cfg(test)]
mod tests {
    use super::*;

    // ── Trail-vs-snapshot backtracking test rig ──────────────────────────────

    /// One canonicalized tableau row: `(key, terms-in-stored-order, constant)`.
    type CanonRow = (VarId, Vec<(VarId, ArithRat)>, ArithRat);

    /// Canonicalized full solver state for bit-identical comparisons:
    /// assignment, bounds (kind/value/reason), basic flags, tableau rows
    /// sorted by key with per-row term order PRESERVED, the incomplete flag,
    /// and the var counters.
    type CanonState = (
        Vec<DeltaRational>,
        Vec<Option<(BoundType, DeltaRational, u32)>>,
        Vec<Option<(BoundType, DeltaRational, u32)>>,
        Vec<bool>,
        Vec<CanonRow>,
        bool,
        usize,
        usize,
    );

    fn canon_state(s: &Simplex) -> CanonState {
        let canon_bounds = |v: &[Option<Bound>]| {
            v.iter()
                .map(|ob| ob.map(|b| (b.kind, b.value, b.reason)))
                .collect::<Vec<_>>()
        };
        let mut rows: Vec<CanonRow> = s
            .tableau
            .iter()
            .map(|(k, e)| (*k, e.terms.to_vec(), e.constant))
            .collect();
        rows.sort_by_key(|r| r.0);
        (
            s.assignment.clone(),
            canon_bounds(&s.lower),
            canon_bounds(&s.upper),
            s.basic.clone(),
            rows,
            s.incomplete,
            s.num_vars,
            s.num_slack,
        )
    }

    fn mode_config(backtrack: BacktrackMode) -> SimplexConfig {
        SimplexConfig {
            backtrack,
            ..SimplexConfig::default()
        }
    }

    /// xorshift64* — deterministic seeded RNG, no external dep.
    struct XorShift(u64);
    impl XorShift {
        fn next(&mut self) -> u64 {
            let mut x = self.0;
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            self.0 = x;
            x.wrapping_mul(0x2545_F491_4F6C_DD1D)
        }
        fn below(&mut self, n: u64) -> u64 {
            self.next() % n
        }
        /// Signed value in `[-r, r]`, never 0 when `nonzero`.
        fn coef(&mut self, r: i64, nonzero: bool) -> i64 {
            loop {
                let v = (self.below(2 * r as u64 + 1) as i64) - r;
                if !nonzero || v != 0 {
                    return v;
                }
            }
        }
    }

    /// Drive one differential seed (paired Trail/Snapshot instances through an
    /// identical randomized op sequence, comparing full state after every op);
    /// returns the maximum push depth reached.
    fn run_differential_seed(seed_i: u64, ops_per_seed: usize) -> usize {
        const MAX_DEPTH: usize = 4;
        const MAX_VARS: usize = 14;

        let mut global_max_depth = 0usize;

        {
            let mut rng = XorShift((seed_i + 1).wrapping_mul(0x9E37_79B9_7F4A_7C15));
            let mut trail = Simplex::with_config(mode_config(BacktrackMode::Trail));
            let mut snap = Simplex::with_config(mode_config(BacktrackMode::Snapshot));
            // Cross-mode bit-identity needs layout-independent pivot choice.
            snap.force_deterministic_violating();

            let mut vars: Vec<VarId> = Vec::new();
            for _ in 0..3 {
                let a = trail.new_var();
                let b = snap.new_var();
                assert_eq!(a, b);
                vars.push(a);
            }
            let mut depth = 0usize;
            // `vars.len()` at each push. On pop, the solver deallocates the
            // vars created inside the scope (ids get REUSED by later
            // allocations), so the driver must drop them from its universe too
            // — mirroring real callers (ArithSolver truncates its term<->var
            // interner in lock-step with pop). Feeding a constraint that
            // references a popped var violates the caller contract: snapshot
            // mode happens to silently scrub the resulting garbage row on the
            // next pop, trail mode debug-asserts it.
            let mut var_marks: Vec<usize> = Vec::new();

            for op_i in 0..ops_per_seed {
                let reason = (seed_i as u32) << 8 | op_i as u32 & 0xFF;
                match rng.below(16) {
                    0 | 1 if vars.len() < MAX_VARS => {
                        let a = trail.new_var();
                        let b = snap.new_var();
                        assert_eq!(a, b);
                        vars.push(a);
                    }
                    2..=5 => {
                        // Random constraint over 1-3 distinct declared vars.
                        let nterms = 1 + rng.below(3) as usize;
                        let mut expr = LinExpr::new();
                        let mut used: Vec<VarId> = Vec::new();
                        for _ in 0..nterms {
                            let v = vars[rng.below(vars.len() as u64) as usize];
                            if used.contains(&v) {
                                continue;
                            }
                            used.push(v);
                            expr.add_term(v, ArithRat::from_integer(rng.coef(3, true) as i128));
                        }
                        expr.add_constant(ArithRat::from_integer(rng.coef(10, false) as i128));
                        match rng.below(5) {
                            0 => {
                                trail.add_le(expr.clone(), reason);
                                snap.add_le(expr, reason);
                            }
                            1 => {
                                trail.add_ge(expr.clone(), reason);
                                snap.add_ge(expr, reason);
                            }
                            2 => {
                                trail.add_eq(expr.clone(), reason);
                                snap.add_eq(expr, reason);
                            }
                            3 => {
                                trail.add_strict_lt(expr.clone(), reason);
                                snap.add_strict_lt(expr, reason);
                            }
                            _ => {
                                trail.add_strict_gt(expr.clone(), reason);
                                snap.add_strict_gt(expr, reason);
                            }
                        }
                    }
                    6..=8 => {
                        let v = vars[rng.below(vars.len() as u64) as usize];
                        let val = ArithRat::from_integer(rng.coef(10, false) as i128);
                        match rng.below(4) {
                            0 => {
                                trail.set_lower(v, val, reason);
                                snap.set_lower(v, val, reason);
                            }
                            1 => {
                                trail.set_upper(v, val, reason);
                                snap.set_upper(v, val, reason);
                            }
                            2 => {
                                trail.set_strict_lower(v, val, reason);
                                snap.set_strict_lower(v, val, reason);
                            }
                            _ => {
                                trail.set_strict_upper(v, val, reason);
                                snap.set_strict_upper(v, val, reason);
                            }
                        }
                    }
                    9 | 10 if depth < MAX_DEPTH => {
                        trail.push();
                        snap.push();
                        var_marks.push(vars.len());
                        depth += 1;
                        global_max_depth = global_max_depth.max(depth);
                    }
                    11 if depth > 0 => {
                        trail.pop();
                        snap.pop();
                        vars.truncate(var_marks.pop().expect("var_marks in lock-step with depth"));
                        depth -= 1;
                    }
                    12 | 13 => {
                        let rt = trail.check();
                        let rs = snap.check();
                        assert_eq!(rt, rs, "seed {seed_i} op {op_i}: check() diverged");
                    }
                    14 => {
                        trail.propagate_bounds();
                        snap.propagate_bounds();
                        assert_eq!(trail.get_propagated().len(), snap.get_propagated().len());
                    }
                    _ => {
                        let v = vars[rng.below(vars.len() as u64) as usize];
                        let ct = trail.tighten_bounds(v);
                        let cs = snap.tighten_bounds(v);
                        assert_eq!(ct, cs, "seed {seed_i} op {op_i}: tighten diverged");
                    }
                }

                assert_eq!(trail.decision_level(), snap.decision_level());
                assert_eq!(
                    canon_state(&trail),
                    canon_state(&snap),
                    "seed {seed_i} op {op_i}: state diverged"
                );
            }

            // Unwind every outstanding scope, comparing after each pop.
            while depth > 0 {
                trail.pop();
                snap.pop();
                vars.truncate(var_marks.pop().expect("var_marks in lock-step with depth"));
                depth -= 1;
                assert_eq!(
                    canon_state(&trail),
                    canon_state(&snap),
                    "seed {seed_i}: state diverged on final unwind"
                );
            }
        }

        global_max_depth
    }

    /// THE gate: paired Trail/Snapshot instances driven through identical
    /// randomized op sequences; after EVERY op the complete solver state and
    /// every `check()` result (conflict vec included) must be bit-identical.
    /// 128 seeds x 100 ops = 12,800 ops, push depth reaches >= 3.
    #[test]
    fn trail_vs_snapshot_differential_randomized() {
        const SEEDS: u64 = 128;
        const OPS_PER_SEED: usize = 100;

        let mut global_max_depth = 0usize;
        for seed_i in 0..SEEDS {
            global_max_depth = global_max_depth.max(run_differential_seed(seed_i, OPS_PER_SEED));
        }

        assert!(
            global_max_depth >= 3,
            "differential never reached push depth 3 (got {global_max_depth}) — rebalance op weights"
        );
    }

    /// Nested pushes with checks forcing pivots at each level; popping back
    /// must restore the EXACT pre-push state (bit-identical canon compare) at
    /// every level. Runs under the default (Trail) mode.
    #[test]
    fn pop_restores_after_multilevel_pivots() {
        // Trail-mode pins: construct explicitly (the default is Snapshot).
        let mut s = Simplex::with_config(mode_config(BacktrackMode::Trail));
        assert_eq!(s.backtrack, BacktrackMode::Trail);

        let x = s.new_var();
        let y = s.new_var();
        s.set_lower(x, ArithRat::zero(), 0);
        s.set_lower(y, ArithRat::zero(), 1);
        assert!(s.check().is_ok());
        let s0 = canon_state(&s);

        // Level 1: x + y >= 6 forces a pivot (crash basis sits at x=y=0).
        s.push();
        let mut e1 = LinExpr::new();
        e1.add_term(x, ArithRat::one());
        e1.add_term(y, ArithRat::one());
        e1.add_constant(ArithRat::from_integer(-6));
        s.add_ge(e1, 2);
        assert!(s.check().is_ok());
        assert!(
            s.basic[x as usize] || s.basic[y as usize],
            "level-1 check should have pivoted a declared var into the basis"
        );
        let s1 = canon_state(&s);

        // Level 2: x + 2y >= 8 forces further pivoting (y enters the basis).
        s.push();
        let mut e2 = LinExpr::new();
        e2.add_term(x, ArithRat::one());
        e2.add_term(y, ArithRat::from_integer(2));
        e2.add_constant(ArithRat::from_integer(-8));
        s.add_ge(e2, 3);
        assert!(s.check().is_ok());
        assert!(
            s.basic[x as usize] && s.basic[y as usize],
            "both declared vars should be basic after the level-2 pivots"
        );
        let s2 = canon_state(&s);

        // Level 3: deterministic conflict (trivially infeasible bound pair —
        // a cap like x<=1 can drive the Bland loop to the pivot limit instead,
        // which reports Ok+incomplete, i.e. Unknown, on trunk).
        s.push();
        s.set_lower(x, ArithRat::from_integer(70), 4);
        s.set_upper(x, ArithRat::from_integer(60), 5);
        assert!(s.check().is_err());

        s.pop();
        assert_eq!(canon_state(&s), s2, "pop to level 2 must restore exactly");
        s.pop();
        assert_eq!(canon_state(&s), s1, "pop to level 1 must restore exactly");
        s.pop();
        assert_eq!(canon_state(&s), s0, "pop to level 0 must restore exactly");
        assert!(s.check().is_ok());
    }

    /// Reconstructs the pivot-OOB hazard shape (the reason the snapshot path
    /// scrubs stale rows) in Trail mode: push, add slack rows, force pivots,
    /// pop, then immediately add constraints and check at the outer level.
    /// Must not panic and must produce the correct verdicts.
    #[test]
    fn pop_then_pivot_no_oob() {
        // Trail-mode pins: construct explicitly (the default is Snapshot).
        let mut s = Simplex::with_config(mode_config(BacktrackMode::Trail));
        assert_eq!(s.backtrack, BacktrackMode::Trail);

        let x = s.new_var();
        let y = s.new_var();
        s.set_lower(x, ArithRat::zero(), 0);
        s.set_lower(y, ArithRat::zero(), 1);

        // Inner scope: slack rows + forced pivots.
        s.push();
        let mut e1 = LinExpr::new();
        e1.add_term(x, ArithRat::one());
        e1.add_term(y, ArithRat::one());
        e1.add_constant(ArithRat::from_integer(-6));
        s.add_ge(e1, 2);
        let mut e2 = LinExpr::new();
        e2.add_term(x, ArithRat::one());
        e2.add_term(y, ArithRat::from_integer(2));
        e2.add_constant(ArithRat::from_integer(-8));
        s.add_ge(e2, 3);
        assert!(s.check().is_ok());
        s.pop();

        // Immediately add fresh constraints at the outer level and pivot again:
        // any stale row/flag surviving the pop would index OOB here.
        let mut e3 = LinExpr::new();
        e3.add_term(x, ArithRat::one());
        e3.add_term(y, ArithRat::one());
        e3.add_constant(ArithRat::from_integer(-4));
        s.add_ge(e3, 4); // x + y >= 4
        assert!(s.check().is_ok(), "x+y>=4 with x,y>=0 is satisfiable");

        // Deterministic conflict to also exercise the error path post-pop
        // (trivial bound pair — Bland caps like x<=1 can end Ok+incomplete).
        s.set_lower(x, ArithRat::from_integer(70), 5);
        s.set_upper(x, ArithRat::from_integer(60), 6);
        assert!(s.check().is_err(), "x in [70, 60] must conflict");
    }

    /// A row touched twice inside one scope must be saved exactly once
    /// (save-once-per-scope epoch), and pop must restore the exact pre-push
    /// state. Two deterministic sequential pivots in ONE scope: `x`'s row is
    /// inserted by pivot 1 and removed by pivot 2 — the second touch is
    /// epoch-skipped, leaving the single authoritative `RowInserted(x)`.
    #[test]
    fn row_touched_twice_single_restore() {
        // Trail-mode pins: construct explicitly (the default is Snapshot).
        let mut s = Simplex::with_config(mode_config(BacktrackMode::Trail));
        assert_eq!(s.backtrack, BacktrackMode::Trail);

        let x = s.new_var();
        let y = s.new_var();
        s.set_lower(x, ArithRat::zero(), 0);
        s.set_lower(y, ArithRat::zero(), 1);

        // Single constraint x + y >= 6: slack u1 = x + y - 6 >= 0, the sole
        // tableau row, so every find_violating outcome is order-independent.
        let mut e1 = LinExpr::new();
        e1.add_term(x, ArithRat::one());
        e1.add_term(y, ArithRat::one());
        e1.add_constant(ArithRat::from_integer(-6));
        s.add_ge(e1, 2);
        let u1 = s.assignment.len() as VarId - 1; // slack of e1
        assert_eq!(u1, 2);

        // Base level: trail mode records nothing (nothing can pop it).
        assert_eq!(s.undo_stack.as_slice().len(), 0);

        let pre = canon_state(&s);
        s.push();

        // Pivot 1: u1 violated at the crash basis (x=y=0 -> u1=-6); Bland
        // enters x (smallest eligible id). Touches: u1's row removed
        // (RowReplaced), x's row inserted (RowInserted). x basic afterwards.
        assert!(s.check().is_ok());
        assert!(s.basic[x as usize], "pivot 1 must make x basic");

        // Pivot 2 (same scope): cap x at 4 (x sits at 6) — the only eligible
        // entering var in x's row (u1: +1 at its lower bound; y: -1, free
        // above) is y. x's row is REMOVED: second touch of a row first touched
        // by pivot 1's insert -> epoch-skipped. y's row inserted.
        s.set_upper(x, ArithRat::from_integer(4), 3);
        assert!(s.check().is_ok());
        assert!(s.basic[y as usize], "pivot 2 must make y basic");
        assert!(!s.basic[x as usize], "pivot 2 must make x non-basic");

        // Exactly one row record per touched var, despite x's row being
        // touched twice (inserted by pivot 1, removed by pivot 2).
        let mut row_records_per_var: FxHashMap<VarId, usize> = FxHashMap::default();
        let mut basic_flips = 0usize;
        for u in s.undo_stack.iter() {
            match u {
                SimplexUndo::RowReplaced(v, _) | SimplexUndo::RowInserted(v) => {
                    *row_records_per_var.entry(*v).or_insert(0) += 1;
                }
                SimplexUndo::BasicFlag(..) => basic_flips += 1,
                _ => {}
            }
        }
        for (v, n) in &row_records_per_var {
            assert_eq!(*n, 1, "row of var {v} saved more than once in one scope");
        }
        assert_eq!(
            row_records_per_var.get(&x),
            Some(&1),
            "x's row (touched twice) must have exactly one record"
        );
        assert!(
            s.undo_stack
                .iter()
                .any(|u| matches!(u, SimplexUndo::RowInserted(v) if *v == x)),
            "x's single record must be RowInserted (no row at scope entry)"
        );
        assert!(
            s.undo_stack
                .iter()
                .any(|u| matches!(u, SimplexUndo::RowReplaced(v, _) if *v == u1)),
            "u1's record must be RowReplaced (its row predates the scope)"
        );
        assert_eq!(basic_flips, 4, "two pivots record exactly 2 flips each");

        s.pop();
        assert_eq!(canon_state(&s), pre, "pop must restore the exact pre-push state");
    }

    #[test]
    fn test_simplex_basic() {
        let mut simplex = Simplex::new();

        let x = simplex.new_var();
        let y = simplex.new_var();

        // x >= 0, y >= 0
        simplex.set_lower(x, ArithRat::zero(), 0);
        simplex.set_lower(y, ArithRat::zero(), 1);

        // x <= 10
        simplex.set_upper(x, ArithRat::from_integer(10), 2);

        assert!(simplex.check().is_ok());
    }

    #[test]
    fn test_simplex_infeasible() {
        let mut simplex = Simplex::new();

        let x = simplex.new_var();

        // x >= 10 and x <= 5 is infeasible
        simplex.set_lower(x, ArithRat::from_integer(10), 0);
        simplex.set_upper(x, ArithRat::from_integer(5), 1);

        assert!(simplex.check().is_err());
    }

    #[test]
    fn test_simplex_strict_bounds() {
        let mut simplex = Simplex::new();

        let x = simplex.new_var();

        // x > 0 (strict lower bound)
        simplex.set_strict_lower(x, ArithRat::zero(), 0);

        // x < 10 (strict upper bound)
        simplex.set_strict_upper(x, ArithRat::from_integer(10), 1);

        assert!(simplex.check().is_ok());

        // Value should be between 0 and 10 (exclusive)
        let val = simplex.delta_value(x);
        assert!(val.is_positive()); // > 0
        assert!(val < DeltaRational::from(10)); // < 10
    }

    #[test]
    fn test_simplex_strict_infeasible() {
        let mut simplex = Simplex::new();

        let x = simplex.new_var();

        // x >= 5 and x < 5 is infeasible
        simplex.set_lower(x, ArithRat::from_integer(5), 0);
        simplex.set_strict_upper(x, ArithRat::from_integer(5), 1);

        assert!(simplex.check().is_err());
    }

    #[test]
    fn test_simplex_strict_feasible_boundary() {
        let mut simplex = Simplex::new();

        let x = simplex.new_var();

        // x > 5 and x <= 6 is feasible
        simplex.set_strict_lower(x, ArithRat::from_integer(5), 0);
        simplex.set_upper(x, ArithRat::from_integer(6), 1);

        assert!(simplex.check().is_ok());

        let val = simplex.delta_value(x);
        assert!(val > DeltaRational::from(5));
        assert!(val <= DeltaRational::from(6));
    }

    #[test]
    fn test_bound_propagation() {
        let mut simplex = Simplex::new();

        let x = simplex.new_var();
        let y = simplex.new_var();

        // x >= 0, x <= 10
        simplex.set_lower(x, ArithRat::zero(), 0);
        simplex.set_upper(x, ArithRat::from_integer(10), 1);

        // y >= 0, y <= 10
        simplex.set_lower(y, ArithRat::zero(), 2);
        simplex.set_upper(y, ArithRat::from_integer(10), 3);

        // Add constraint: x + y <= 15
        // This introduces slack variable s, where s = 15 - x - y, s >= 0
        let mut expr = LinExpr::new();
        expr.add_term(x, ArithRat::one());
        expr.add_term(y, ArithRat::one());
        expr.add_constant(-ArithRat::from_integer(15));
        simplex.add_le(expr, 4);

        // Propagate bounds
        simplex.propagate_bounds();

        // Check the constraint is feasible
        assert!(simplex.check().is_ok());

        // The accessor methods work
        assert!(simplex.get_lower(x).is_some());
        assert!(simplex.get_upper(x).is_some());
    }

    #[test]
    fn test_tighten_bounds() {
        let mut simplex = Simplex::new();

        let x = simplex.new_var();

        // x >= 5
        simplex.set_lower(x, ArithRat::from_integer(5), 0);

        // x <= 15
        simplex.set_upper(x, ArithRat::from_integer(15), 1);

        // The accessor methods work
        let lo = simplex.get_lower(x).expect("test operation should succeed");
        assert_eq!(lo.value.real, ArithRat::from_integer(5));

        let hi = simplex.get_upper(x).expect("test operation should succeed");
        assert_eq!(hi.value.real, ArithRat::from_integer(15));

        assert!(simplex.check().is_ok());
    }

    #[test]
    fn test_farkas_conflict_explanation() {
        let mut simplex = Simplex::new();

        let x = simplex.new_var();
        let y = simplex.new_var();

        // Constraint: x + y <= 5 (reason 0)
        // Which becomes: x + y - 5 <= 0, introduce slack s where s = 5 - x - y, s >= 0
        let mut expr1 = LinExpr::new();
        expr1.add_term(x, ArithRat::one());
        expr1.add_term(y, ArithRat::one());
        expr1.add_constant(-ArithRat::from_integer(5));
        simplex.add_le(expr1, 0);

        // x >= 3 (reason 1)
        simplex.set_lower(x, ArithRat::from_integer(3), 1);

        // y >= 3 (reason 2)
        simplex.set_lower(y, ArithRat::from_integer(3), 2);

        // This is infeasible: x >= 3, y >= 3 implies x + y >= 6, but x + y <= 5
        let result = simplex.check();
        assert!(result.is_err());

        // The conflict should include the relevant reasons
        let reasons = result.unwrap_err();
        assert!(!reasons.is_empty());
        // Should include at least the constraint reason (0) and the bound reasons
    }

    #[test]
    fn test_farkas_multiple_variables() {
        let mut simplex = Simplex::new();

        let x = simplex.new_var();
        let y = simplex.new_var();
        let z = simplex.new_var();

        // x + y + z <= 10 (reason 0)
        let mut expr = LinExpr::new();
        expr.add_term(x, ArithRat::one());
        expr.add_term(y, ArithRat::one());
        expr.add_term(z, ArithRat::one());
        expr.add_constant(-ArithRat::from_integer(10));
        simplex.add_le(expr, 0);

        // x >= 4 (reason 1)
        simplex.set_lower(x, ArithRat::from_integer(4), 1);

        // y >= 4 (reason 2)
        simplex.set_lower(y, ArithRat::from_integer(4), 2);

        // z >= 4 (reason 3)
        simplex.set_lower(z, ArithRat::from_integer(4), 3);

        // Infeasible: x + y + z >= 12 but x + y + z <= 10
        let result = simplex.check();
        assert!(result.is_err());

        let reasons = result.unwrap_err();
        // Should have multiple reasons in the conflict
        assert!(reasons.len() >= 2);
    }

    #[test]
    fn test_simplex_push_pop() {
        let mut simplex = Simplex::new();

        let x = simplex.new_var();

        // Level 0: x >= 0, x <= 100
        simplex.set_lower(x, ArithRat::zero(), 0);
        simplex.set_upper(x, ArithRat::from_integer(100), 1);

        assert!(simplex.check().is_ok());

        // Push to level 1
        simplex.push();

        // Level 1: tighten to x >= 50, x <= 60
        simplex.set_lower(x, ArithRat::from_integer(50), 2);
        simplex.set_upper(x, ArithRat::from_integer(60), 3);

        assert!(simplex.check().is_ok());
        let lo = simplex.get_lower(x).expect("test operation should succeed");
        assert_eq!(lo.value.real, ArithRat::from_integer(50));

        // Push to level 2
        simplex.push();

        // Level 2: infeasible bounds x >= 70, x <= 60
        simplex.set_lower(x, ArithRat::from_integer(70), 4);

        assert!(simplex.check().is_err());

        // Pop to level 1 - should be feasible again
        simplex.pop();

        // After pop, bounds should be back to x >= 50, x <= 60
        let lo = simplex.get_lower(x).expect("test operation should succeed");
        assert_eq!(lo.value.real, ArithRat::from_integer(50));
        let hi = simplex.get_upper(x).expect("test operation should succeed");
        assert_eq!(hi.value.real, ArithRat::from_integer(60));

        assert!(simplex.check().is_ok());

        // Pop to level 0
        simplex.pop();

        // After pop, bounds should be back to x >= 0, x <= 100
        let lo = simplex.get_lower(x).expect("test operation should succeed");
        assert_eq!(lo.value.real, ArithRat::zero());
        let hi = simplex.get_upper(x).expect("test operation should succeed");
        assert_eq!(hi.value.real, ArithRat::from_integer(100));

        assert!(simplex.check().is_ok());
    }

    #[test]
    fn test_simplex_push_pop_vars() {
        let mut simplex = Simplex::new();

        let x = simplex.new_var();
        simplex.set_lower(x, ArithRat::zero(), 0);
        simplex.set_upper(x, ArithRat::from_integer(10), 1);

        assert_eq!(simplex.num_original_vars(), 1);

        simplex.push();

        // Add a new variable at level 1
        let y = simplex.new_var();
        simplex.set_lower(y, ArithRat::zero(), 2);
        simplex.set_upper(y, ArithRat::from_integer(20), 3);

        assert_eq!(simplex.num_original_vars(), 2);
        assert!(simplex.check().is_ok());

        // Pop - the new variable should be gone
        simplex.pop();

        assert_eq!(simplex.num_original_vars(), 1);
    }

    #[test]
    fn test_dual_simplex_basic() {
        // Test dual simplex - it works best when we have a basis already
        // For a simple feasibility test, dual_simplex should find violations
        let mut simplex = Simplex::new();

        let x = simplex.new_var();
        let y = simplex.new_var();

        // x, y >= 0
        simplex.set_lower(x, ArithRat::zero(), 0);
        simplex.set_lower(y, ArithRat::zero(), 1);

        // Add a constraint: x + y = 10 (using slack variable, becomes basic)
        let mut expr = LinExpr::new();
        expr.add_term(x, ArithRat::one());
        expr.add_term(y, ArithRat::one());
        expr.add_constant(ArithRat::from_integer(-10));
        simplex.add_eq(expr, 2);

        // dual_simplex should be able to find a feasible solution
        assert!(simplex.dual_simplex().is_ok());

        // Check values
        let x_val = simplex.value(x);
        let y_val = simplex.value(y);
        assert!(x_val + y_val >= ArithRat::from_integer(9)); // Allow some slack
        assert!(x_val + y_val <= ArithRat::from_integer(11));
    }

    #[test]
    fn test_dual_simplex_feasible() {
        // Test dual simplex on a feasible problem
        let mut simplex = Simplex::new();

        let x = simplex.new_var();
        let y = simplex.new_var();

        // x >= 0, y >= 0
        simplex.set_lower(x, ArithRat::zero(), 0);
        simplex.set_lower(y, ArithRat::zero(), 1);

        // x <= 10, y <= 10
        simplex.set_upper(x, ArithRat::from_integer(10), 2);
        simplex.set_upper(y, ArithRat::from_integer(10), 3);

        // Add constraint: x + y >= 5
        let mut expr = LinExpr::new();
        expr.add_term(x, ArithRat::one());
        expr.add_term(y, ArithRat::one());
        expr.add_constant(ArithRat::from_integer(-5));
        simplex.add_ge(expr, 4);

        // Should be feasible
        assert!(simplex.dual_simplex().is_ok());

        // Check that solution satisfies bounds
        let x_val = simplex.value(x);
        let y_val = simplex.value(y);

        assert!(x_val >= ArithRat::zero());
        assert!(y_val >= ArithRat::zero());
        assert!(x_val + y_val >= ArithRat::from_integer(5));
    }

    /// Test that x<=y AND y<=x makes x<y infeasible (probe test).
    #[test]
    fn test_bidirectional_constraints_probe() {
        let mut simplex = Simplex::new();
        let x = simplex.new_var();
        let y = simplex.new_var();

        // x <= y  (x - y <= 0)
        let mut e1 = LinExpr::new();
        e1.add_term(x, ArithRat::one());
        e1.add_term(y, -ArithRat::one());
        simplex.add_le(e1, 0);

        // y <= x  (y - x <= 0)
        let mut e2 = LinExpr::new();
        e2.add_term(y, ArithRat::one());
        e2.add_term(x, -ArithRat::one());
        simplex.add_le(e2, 1);

        assert!(simplex.check().is_ok(), "x<=y AND y<=x should be SAT");

        // Probe: x < y should be UNSAT (since x=y is forced)
        {
            simplex.push();
            let mut e3 = LinExpr::new();
            e3.add_term(x, ArithRat::one());
            e3.add_term(y, -ArithRat::one());
            simplex.add_strict_lt(e3, 99);
            let probe1 = simplex.check();
            simplex.pop();
            assert!(
                probe1.is_err(),
                "x<y should be UNSAT when x=y is forced; got Ok"
            );
        }

        // Re-establish SAT state.
        assert!(simplex.check().is_ok(), "should still be SAT after probe 1");

        // Probe: y < x should also be UNSAT
        {
            simplex.push();
            let mut e4 = LinExpr::new();
            e4.add_term(y, ArithRat::one());
            e4.add_term(x, -ArithRat::one());
            simplex.add_strict_lt(e4, 99);
            let probe2 = simplex.check();
            simplex.pop();
            assert!(
                probe2.is_err(),
                "y<x should be UNSAT when x=y is forced; got Ok"
            );
        }
    }
}
