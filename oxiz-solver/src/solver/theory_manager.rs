//! Theory manager that bridges the SAT solver with theory solvers

#[allow(unused_imports)]
use crate::prelude::*;
use num_traits::ToPrimitive;
use oxiz_core::ast::{TermId, TermKind, TermManager};
use oxiz_sat::{Lit, TheoryCallback, TheoryCheckResult, TheoryHooks, TheoryReason, TheoryStep, Var};
use oxiz_theories::ArithRat;
use oxiz_theories::arithmetic::ArithSolver;
use oxiz_theories::bv::BvSolver;
use oxiz_theories::euf::EufSolver;
use oxiz_theories::{EqualityNotification, Theory, TheoryCombination};
use smallvec::SmallVec;

use super::types::{
    ArithConstraintType, Constraint, ParsedArithConstraint, Statistics, TheoryMode,
};

/// Theory decision hint
#[derive(Debug, Clone, Copy)]
#[allow(dead_code)]
pub struct TheoryDecision {
    /// The variable to branch on
    pub var: Var,
    /// Suggested value (true = positive, false = negative)
    pub value: bool,
    /// Priority (higher = more important)
    pub priority: i32,
}

/// Theory manager that bridges the SAT solver with theory solvers.
///
/// §4 redesign (Phase 2): this used to BORROW the term manager and the theory
/// solvers (`TheoryManager<'a>`); it now OWNS them. Ownership removes the
/// lifetime parameter so the same struct can satisfy the `'static` bound of the
/// lock-step `TheoryHooks` driver (`solve_with_hooks`) while still handing each
/// theory method a concrete `&TermManager` (zero generic/`&dyn` cascade into
/// oxiz-theories). The owner (`Solver::check`) MOVES its real state in for the
/// span of one solve and MOVES it back out afterward (see `take_theory_manager`
/// / `restore_theory_manager` + `into_parts`); the maps are read-only during a
/// solve so the relocation is O(1) and behaviour-identical to the old borrow.
pub(crate) struct TheoryManager {
    /// The term manager, behind an `Arc` so the per-assignment theory entry
    /// points (`on_assignment`/`final_check`) can hand `process_constraint` a
    /// `&TermManager` that is INDEPENDENT of the `&mut self` borrow it needs:
    /// `Arc::clone` (O(1) refcount bump) produces a transient handle, dropped at
    /// the end of the call, so the refcount is back to 1 by the time `check`
    /// reclaims the manager via `Arc::try_unwrap` (the old code got the same
    /// "handle not tied to self" property for free because `&'a TermManager` is
    /// `Copy` and pointed outside `self`). No `Arc` clone is ever stored, so the
    /// arena is never extended through a shared head.
    manager: Arc<TermManager>,
    /// EUF solver
    euf: EufSolver,
    /// Arithmetic solver
    arith: ArithSolver,
    /// Bitvector solver
    bv: BvSolver,
    /// Bitvector terms (for identifying BV variables)
    bv_terms: FxHashSet<TermId>,
    /// Mapping from SAT variables to constraints
    var_to_constraint: FxHashMap<Var, Constraint>,
    /// Mapping from SAT variables to parsed arithmetic constraints
    var_to_parsed_arith: FxHashMap<Var, ParsedArithConstraint>,
    /// Mapping from terms to SAT variables (for conflict clause generation)
    term_to_var: FxHashMap<TermId, Var>,
    /// Reverse mapping from SAT variables to terms (for EUF merge reasons)
    var_to_term: Vec<TermId>,
    /// Current decision level stack for backtracking
    level_stack: Vec<usize>,
    /// Number of processed assignments
    processed_count: usize,
    /// Theory checking mode
    theory_mode: TheoryMode,
    /// Whether the `arith` stale-bound suppression guards are ACTIVE.
    ///
    /// A stale-bound pseudo-conflict is an atom left in the simplex under both
    /// polarities by a SAT backtrack the theory frame did not retract; the
    /// guards suppress it (else a spurious UNSAT). The §4 lock-step hooks driver
    /// makes such a frame UNREPRESENTABLE (per-literal `unassign_hook` retracts
    /// the bound the instant its literal leaves the trail), so the guards are
    /// DEAD on the hooks path and are switched OFF there — both to realise the
    /// "make it unrepresentable, not guarded" thesis and to keep the hooks path
    /// from masking a lock-step bug. The legacy `TheoryCallback` fallback has no
    /// such guarantee, so the guards stay ON for it. (`true` = legacy.)
    suppress_stale_bounds: bool,
    /// Pending assignments for lazy theory checking
    pending_assignments: Vec<(Lit, bool)>,
    /// §4 hooks path (Phase 2b): theory propagations captured during the eager
    /// drain in `TheoryHooks::final_check`, awaiting emission one-per-poll to the
    /// `solve_with_hooks` driver as `TheoryStep::Propagate`. Each entry is the
    /// legacy `(propagated_lit, reason_clause_lits)` shape `process_constraint`
    /// returns; `reason_clause_lits` are the TRUE justifying literals that
    /// `add_theory_reason_clause` consumes directly. Empty except mid-fixpoint;
    /// cleared on backtrack (`pop_frame`) so a stale propagation never survives.
    pending_theory_propagations: Vec<(Lit, SmallVec<[Lit; 8]>)>,
    /// Arith→EUF entailed-equality propagation (Nelson-Oppen): the reason atoms
    /// (currently-asserted bound TermIds) for every arith-FIXED term that
    /// `model_based_combination` merged into its constant's EUF node THIS round.
    /// When the resulting congruence produces a conflict, these atoms MUST be
    /// added (negated) to the conflict clause — the clause `propagate_euf_…`
    /// builds otherwise OMITS the bounds that entail the equality, which is
    /// exactly the trap that flips to a spurious UNSAT. Cleared at the start of
    /// each `model_based_combination`; never crosses a check boundary.
    pending_arith_eq_reasons: Vec<TermId>,
    /// Theory decision hints for branching
    #[allow(dead_code)]
    decision_hints: Vec<TheoryDecision>,
    /// Pending equality notifications for Nelson-Oppen
    pending_equalities: Vec<EqualityNotification>,
    /// Processed equalities (to avoid duplicates)
    processed_equalities: FxHashMap<(TermId, TermId), bool>,
    /// Solver statistics (for tracking)
    statistics: Statistics,
    /// Maximum conflicts allowed (0 = unlimited)
    max_conflicts: u64,
    /// Maximum decisions allowed (0 = unlimited)
    #[allow(dead_code)]
    max_decisions: u64,
    /// Whether formula contains BV arithmetic operations (division/remainder)
    #[allow(dead_code)]
    has_bv_arith_ops: bool,
    /// Canonical EUF node for each distinct integer constant value.
    ///
    /// Maps an integer literal value (i64) to the canonical EUF node that
    /// represents it.  When a new `IntConst(v)` term is first encountered for a
    /// value `v`, we create its EUF node, assert pairwise disequalities against
    /// every canonical node of a different value, and record it here.
    ///
    /// If the same value `v` appears again (e.g., as a fresh TermId created
    /// during MBQI instantiation), we merge the new node with the existing
    /// canonical node rather than appending another entry.  This keeps the
    /// number of distinct entries — and therefore the number of pairwise
    /// disequality edges — bounded by the number of *distinct* integer literal
    /// values in the original formula, not by the total number of term IDs
    /// created across all MBQI iterations (which grows without bound).
    interned_int_constants: FxHashMap<i64, u32>,
    /// Canonical EUF nodes for distinct bit-vector constant *values*, keyed by
    /// `(value, width)`.  Mirrors `interned_int_constants` but for the BV theory:
    /// EUF has no notion that `#x00 != #x01`, so without explicit disequality
    /// edges a congruence chain merging `g(a)` (= `#x00`) with `g(b)` (= `#x01`)
    /// when `a = b` would not produce a conflict.  We track one canonical node
    /// per distinct `(value, width)` pair and assert pairwise disequalities
    /// between same-width constants, bounding the edge count by the number of
    /// distinct BV literals in the formula.
    interned_bv_constants: FxHashMap<(u64, u32), u32>,
    /// Canonical EUF nodes for Boolean true and false values.
    /// Used to track Bool-valued function applications in EUF:
    /// when `f(x)` is assigned true by the SAT solver, we merge its EUF node
    /// with `bool_true_node`; when assigned false, with `bool_false_node`.
    /// A disequality `true != false` is asserted so that congruence closure
    /// detects conflicts (e.g., f(a)=true, f(b)=false, but a=b).
    bool_true_node: Option<u32>,
    bool_false_node: Option<u32>,
    /// Current SAT phase of each theory-atom variable (`true` = assigned
    /// positively, `false` = assigned negatively).  Recorded on every
    /// assignment so that `terms_to_conflict_clause` can emit each conflict
    /// literal with the polarity that *falsifies* it under the current
    /// assignment.  Without this a diseq reason that came from a
    /// negatively-assigned equality atom (e.g. a `(= x y)` the SAT solver set
    /// false, asserted into EUF as `x != y`) would be negated the wrong way,
    /// yielding a learned clause that is satisfied rather than falsified — a
    /// malformed conflict that drives spurious UNSAT once several accumulate.
    /// Stale entries for backtracked vars are never queried: a popped EUF
    /// merge/diseq no longer contributes its reason term to any live conflict.
    assigned_phase: FxHashMap<Var, bool>,
    /// Soundness gate: did the MOST RECENT theory-consistency battery authorise
    /// its `Sat` only because an underlying theory returned `Unknown`/errored
    /// (rather than positively confirming the assignment)?  The SAT-facing
    /// `oxiz_sat::TheoryCheckResult` has no `Unknown` channel, so an incomplete
    /// theory (e.g. LIA branch-and-bound that exhausts its node budget, or proves
    /// the LP-feasible vertex has NO integer point) is reported to the SAT core as
    /// `Sat` ("no conflict, keep the assignment").  Without this flag that
    /// non-trivial / unconfirmed `Sat` is indistinguishable from a theory-CONFIRMED
    /// `Sat`, so the solver would emit a spurious `sat` verdict on an integer-
    /// infeasible problem (z3 `unsat`).  Reset to `false` at the TOP of every
    /// `theory_consistency_check` (so it reflects ONLY the last, authorising
    /// battery) and set `true` whenever that battery falls back to `Sat` from an
    /// `Unknown`/`Err` arm.  `Solver::solve` reads it after a `Sat` and DOWNGRADES
    /// the final verdict to `Unknown` — the sound report for "could not confirm".
    last_check_unconfirmed: bool,
}

/// Post-order, memoised BV term encoding.
///
/// Bit-blast every BV-sorted operand reachable through a boolean condition
/// `cond` (the kind that appears as an `ite` selector). Walks the boolean
/// connective/comparison structure and bit-blasts the BV terms underneath the
/// `Eq`/comparison leaves, so that `BvSolver::encode_bool_node` can look them
/// up. Returns `false` if any BV operand fails to encode.
fn bit_blast_cond_operands(bv: &mut BvSolver, cond: TermId, mgr: &TermManager) -> bool {
    let term = match mgr.get(cond) {
        Some(t) => t,
        None => return false,
    };
    match &term.kind {
        // Boolean structure: recurse into operands.
        TermKind::Not(inner) => bit_blast_cond_operands(bv, *inner, mgr),
        TermKind::And(args) | TermKind::Or(args) => {
            args.iter().all(|&a| bit_blast_cond_operands(bv, a, mgr))
        }
        // Comparison/equality leaves: their operands are BV terms.
        TermKind::Eq(lhs, rhs)
        | TermKind::BvUlt(lhs, rhs)
        | TermKind::BvUle(lhs, rhs)
        | TermKind::BvSlt(lhs, rhs)
        | TermKind::BvSle(lhs, rhs) => {
            let mut encoded: FxHashSet<TermId> = FxHashSet::default();
            let lhs_ok = encode_bv_term_recursive(bv, *lhs, mgr, &mut encoded) || {
                if let Some(w) = mgr
                    .get(*lhs)
                    .and_then(|t| mgr.sorts.get(t.sort))
                    .and_then(|s| s.bitvec_width())
                {
                    bv.new_bv(*lhs, w);
                    true
                } else {
                    false
                }
            };
            let rhs_ok = encode_bv_term_recursive(bv, *rhs, mgr, &mut encoded) || {
                if let Some(w) = mgr
                    .get(*rhs)
                    .and_then(|t| mgr.sorts.get(t.sort))
                    .and_then(|s| s.bitvec_width())
                {
                    bv.new_bv(*rhs, w);
                    true
                } else {
                    false
                }
            };
            lhs_ok && rhs_ok
        }
        // A bare boolean variable / constant has no BV operands to blast.
        TermKind::Var(_) | TermKind::True | TermKind::False => true,
        // Anything else is outside the supported condition fragment.
        _ => false,
    }
}

/// If `tid` is a `BitVecConst` whose value is a positive power of two, return
/// the exponent (shift amount).  Returns `None` for zero, non-powers-of-two,
/// and non-constant terms.
fn bitvec_const_pow2_shift(mgr: &TermManager, tid: TermId) -> Option<u32> {
    let term = mgr.get(tid)?;
    if let TermKind::BitVecConst { value, .. } = &term.kind {
        let digits: Vec<u64> = value.iter_u64_digits().collect();
        let set_bits: u32 = digits.iter().map(|&d| d.count_ones()).sum();
        if set_bits != 1 {
            return None;
        }
        for (chunk, &d) in digits.iter().enumerate() {
            if d != 0 {
                return Some(chunk as u32 * 64 + d.trailing_zeros());
            }
        }
    }
    None
}

/// Recursively encodes every sub-term of `root` into the BV solver using an
/// explicit work-stack so that arbitrarily deep nesting is handled without
/// overflowing the call stack.  A `FxHashSet<TermId>` memo prevents duplicate
/// encoding when the same sub-term appears in multiple branches of the DAG.
///
/// Returns `true` when `root` was fully encoded, `false` when an unrecognised
/// TermKind is encountered.
fn encode_bv_term_recursive(
    bv: &mut BvSolver,
    root: TermId,
    mgr: &TermManager,
    encoded: &mut FxHashSet<TermId>,
) -> bool {
    // Work-stack entry: (term_id, children_pushed)
    // We push a term twice: first time to push children, second time to
    // encode the term itself (post-order).
    let mut stack: Vec<(TermId, bool)> = vec![(root, false)];

    while let Some((tid, children_done)) = stack.pop() {
        if encoded.contains(&tid) {
            continue;
        }
        // If the BV solver already has a circuit for this term (encoded in a
        // previous call to encode_bv_term_recursive), skip both the child-push
        // and the encoding phases.  This makes the function globally idempotent:
        // calling it a second time for the same sub-tree is a no-op, which
        // prevents the adder/multiplier circuits from being duplicated across
        // CDCL restarts (each duplicate brings ~33 fresh carry SAT variables and
        // hundreds of new clauses, causing the embedded BV SAT to blow up).
        // Leaves (Var, BitVecConst) are already idempotent via `new_bv`'s
        // `or_insert_with`, so this guard is only strictly necessary for
        // compound operations, but checking unconditionally is correct and safe.
        if bv.get_bv(tid).is_some() {
            encoded.insert(tid);
            continue;
        }

        let term = match mgr.get(tid) {
            Some(t) => t,
            None => return false,
        };

        let width = match mgr.sorts.get(term.sort).and_then(|s| s.bitvec_width()) {
            Some(w) => w,
            None => return false,
        };

        if !children_done {
            // Re-push this node as "children done" so we encode it after children
            stack.push((tid, true));

            // Push children (they will be encoded first)
            match &term.kind {
                TermKind::BvAdd(a, b)
                | TermKind::BvMul(a, b)
                | TermKind::BvSub(a, b)
                | TermKind::BvAnd(a, b)
                | TermKind::BvOr(a, b)
                | TermKind::BvXor(a, b)
                | TermKind::BvUdiv(a, b)
                | TermKind::BvSdiv(a, b)
                | TermKind::BvUrem(a, b)
                | TermKind::BvSrem(a, b) => {
                    if !encoded.contains(a) {
                        stack.push((*a, false));
                    }
                    if !encoded.contains(b) {
                        stack.push((*b, false));
                    }
                }
                TermKind::BvNot(a) => {
                    if !encoded.contains(a) {
                        stack.push((*a, false));
                    }
                }
                // Shifts: value and shift-amount operands (same width).
                TermKind::BvShl(a, b) | TermKind::BvLshr(a, b) | TermKind::BvAshr(a, b) => {
                    if !encoded.contains(a) {
                        stack.push((*a, false));
                    }
                    if !encoded.contains(b) {
                        stack.push((*b, false));
                    }
                }
                // Concatenation: both operands (their own widths).
                TermKind::BvConcat(a, b) => {
                    if !encoded.contains(a) {
                        stack.push((*a, false));
                    }
                    if !encoded.contains(b) {
                        stack.push((*b, false));
                    }
                }
                // Extraction: single source operand (its own width).
                TermKind::BvExtract { arg, .. } => {
                    if !encoded.contains(arg) {
                        stack.push((*arg, false));
                    }
                }
                // ITE over BV: bit-blast both branches; the condition's BV
                // operands are bit-blasted separately just before encoding.
                TermKind::Ite(_cond, then_t, else_t) => {
                    if !encoded.contains(then_t) {
                        stack.push((*then_t, false));
                    }
                    if !encoded.contains(else_t) {
                        stack.push((*else_t, false));
                    }
                }
                // Leaves: Var, BitVecConst — no children to push
                TermKind::Var(_) | TermKind::BitVecConst { .. } => {}
                // Unknown term kind — cannot encode, abort
                _ => return false,
            }
        } else {
            // Encode this node (children already encoded)
            match &term.kind {
                TermKind::BvAdd(a, b) => {
                    bv.new_bv(*a, width);
                    bv.new_bv(*b, width);
                    bv.bv_add(tid, *a, *b);
                }
                TermKind::BvMul(a, b) => {
                    if let Some(shift) = bitvec_const_pow2_shift(mgr, *b) {
                        bv.new_bv(*a, width);
                        bv.bv_shl_const(tid, *a, shift, width);
                    } else if let Some(shift) = bitvec_const_pow2_shift(mgr, *a) {
                        bv.new_bv(*b, width);
                        bv.bv_shl_const(tid, *b, shift, width);
                    } else {
                        bv.new_bv(*a, width);
                        bv.new_bv(*b, width);
                        bv.bv_mul(tid, *a, *b);
                    }
                }
                TermKind::BvSub(a, b) => {
                    bv.new_bv(*a, width);
                    bv.new_bv(*b, width);
                    bv.bv_sub(tid, *a, *b);
                }
                TermKind::BvAnd(a, b) => {
                    bv.new_bv(*a, width);
                    bv.new_bv(*b, width);
                    bv.bv_and(tid, *a, *b);
                }
                TermKind::BvOr(a, b) => {
                    bv.new_bv(*a, width);
                    bv.new_bv(*b, width);
                    bv.bv_or(tid, *a, *b);
                }
                TermKind::BvXor(a, b) => {
                    bv.new_bv(*a, width);
                    bv.new_bv(*b, width);
                    bv.bv_xor(tid, *a, *b);
                }
                TermKind::BvNot(a) => {
                    bv.new_bv(*a, width);
                    bv.bv_not(tid, *a);
                }
                TermKind::BvShl(a, b) => {
                    // Operands and result share `width`.
                    bv.new_bv(*a, width);
                    bv.new_bv(*b, width);
                    bv.bv_shl(tid, *a, *b);
                }
                TermKind::BvLshr(a, b) => {
                    bv.new_bv(*a, width);
                    bv.new_bv(*b, width);
                    bv.bv_lshr(tid, *a, *b);
                }
                TermKind::BvAshr(a, b) => {
                    bv.new_bv(*a, width);
                    bv.new_bv(*b, width);
                    bv.bv_ashr(tid, *a, *b);
                }
                TermKind::BvConcat(a, b) => {
                    // Operands keep their own (possibly differing) widths; the
                    // result width is their sum (already `width` here).
                    let aw = match mgr
                        .get(*a)
                        .and_then(|t| mgr.sorts.get(t.sort))
                        .and_then(|s| s.bitvec_width())
                    {
                        Some(w) => w,
                        None => return false,
                    };
                    let bw = match mgr
                        .get(*b)
                        .and_then(|t| mgr.sorts.get(t.sort))
                        .and_then(|s| s.bitvec_width())
                    {
                        Some(w) => w,
                        None => return false,
                    };
                    bv.new_bv(*a, aw);
                    bv.new_bv(*b, bw);
                    // BvConcat(high, low) — `a` is the high (most-significant) part.
                    bv.concat(tid, *a, *b);
                }
                TermKind::BvExtract { high, low, arg } => {
                    let arg_w = match mgr
                        .get(*arg)
                        .and_then(|t| mgr.sorts.get(t.sort))
                        .and_then(|s| s.bitvec_width())
                    {
                        Some(w) => w,
                        None => return false,
                    };
                    bv.new_bv(*arg, arg_w);
                    bv.extract(tid, *arg, *high, *low);
                }
                TermKind::Ite(cond, then_t, else_t) => {
                    // Branches are already bit-blasted (pushed as children). The
                    // condition's BV operands must be bit-blasted before the
                    // condition itself is encoded inside `bv_ite`.
                    if !bit_blast_cond_operands(bv, *cond, mgr) {
                        return false;
                    }
                    bv.bv_ite(tid, *cond, *then_t, *else_t, mgr);
                }
                TermKind::BvUdiv(a, b) => {
                    bv.new_bv(*a, width);
                    bv.new_bv(*b, width);
                    bv.bv_udiv(tid, *a, *b);
                }
                TermKind::BvSdiv(a, b) => {
                    bv.new_bv(*a, width);
                    bv.new_bv(*b, width);
                    bv.bv_sdiv(tid, *a, *b);
                }
                TermKind::BvUrem(a, b) => {
                    bv.new_bv(*a, width);
                    bv.new_bv(*b, width);
                    bv.bv_urem(tid, *a, *b);
                }
                TermKind::BvSrem(a, b) => {
                    bv.new_bv(*a, width);
                    bv.new_bv(*b, width);
                    bv.bv_srem(tid, *a, *b);
                }
                TermKind::Var(_) => {
                    // Leaf variable: just ensure a BV variable exists.
                    bv.new_bv(tid, width);
                }
                TermKind::BitVecConst { value, .. } => {
                    // Leaf constant: create the BV variable AND pin its bits to
                    // the concrete value.  Without this the constant operand of a
                    // bit-blasted op (e.g. the `#x02` in `(bvmul #x02 x)`) would be
                    // an unconstrained free variable, silently weakening the
                    // encoding and causing false SAT for constant-folded identities.
                    let val_u64 = value.iter_u64_digits().next().unwrap_or(0);
                    bv.assert_const(tid, val_u64, width);
                }
                _ => return false,
            }
            encoded.insert(tid);
        }
    }

    true
}

/// The owned state that a `TheoryManager` holds for the span of one solve and
/// hands back to `Solver::check` afterward.
///
/// Bundling the moved-in/moved-out fields into one struct keeps the
/// move-in (`TheoryManager::new`) and move-out (`into_parts`) at the call site a
/// single value instead of ten loose arguments. Only the PERSISTENT theory
/// state lives here (the per-solve scratch — `level_stack`, `pending_*`,
/// `interned_*`, `assigned_phase`, … — is freshly initialised by `new` and
/// dropped by `into_parts`, exactly mirroring the old "recreate the manager each
/// MBQI iteration" semantics).
pub(crate) struct TheoryParts {
    pub manager: TermManager,
    pub euf: EufSolver,
    pub arith: ArithSolver,
    pub bv: BvSolver,
    pub bv_terms: FxHashSet<TermId>,
    pub var_to_constraint: FxHashMap<Var, Constraint>,
    pub var_to_parsed_arith: FxHashMap<Var, ParsedArithConstraint>,
    pub term_to_var: FxHashMap<TermId, Var>,
    pub var_to_term: Vec<TermId>,
    pub statistics: Statistics,
}

impl TheoryManager {
    pub(crate) fn new(
        parts: TheoryParts,
        theory_mode: TheoryMode,
        max_conflicts: u64,
        max_decisions: u64,
        has_bv_arith_ops: bool,
        suppress_stale_bounds: bool,
    ) -> Self {
        let TheoryParts {
            manager,
            euf,
            arith,
            bv,
            bv_terms,
            var_to_constraint,
            var_to_parsed_arith,
            term_to_var,
            var_to_term,
            statistics,
        } = parts;
        Self {
            manager: Arc::new(manager),
            euf,
            arith,
            bv,
            bv_terms,
            var_to_constraint,
            var_to_parsed_arith,
            term_to_var,
            var_to_term,
            level_stack: vec![0],
            processed_count: 0,
            theory_mode,
            suppress_stale_bounds,
            pending_assignments: Vec::new(),
            pending_theory_propagations: Vec::new(),
            pending_arith_eq_reasons: Vec::new(),
            decision_hints: Vec::new(),
            pending_equalities: Vec::new(),
            processed_equalities: FxHashMap::default(),
            statistics,
            max_conflicts,
            max_decisions,
            has_bv_arith_ops,
            interned_int_constants: FxHashMap::default(),
            interned_bv_constants: FxHashMap::default(),
            assigned_phase: FxHashMap::default(),
            bool_true_node: None,
            bool_false_node: None,
            last_check_unconfirmed: false,
        }
    }

    /// Move the persistent theory state back out (dropping the per-solve
    /// scratch), so the owner can reinstall it into `Solver` + the real
    /// `TermManager` after a solve.
    pub(crate) fn into_parts(self) -> TheoryParts {
        // The `Arc` must be uniquely owned here: the only clones are the
        // transient handles taken inside `on_assignment`/`final_check`, all
        // dropped before the solve returns, and none are ever stored. Reclaim
        // the real `TermManager` by value so the owner can reinstall it.
        let manager = Arc::try_unwrap(self.manager).unwrap_or_else(|_| {
            unreachable!("theory-manager Arc<TermManager> outstanding after solve")
        });
        TheoryParts {
            manager,
            euf: self.euf,
            arith: self.arith,
            bv: self.bv,
            bv_terms: self.bv_terms,
            var_to_constraint: self.var_to_constraint,
            var_to_parsed_arith: self.var_to_parsed_arith,
            term_to_var: self.term_to_var,
            var_to_term: self.var_to_term,
            statistics: self.statistics,
        }
    }

    /// Process Nelson-Oppen equality sharing
    /// Propagates equalities between theories until a fixed point is reached
    #[allow(dead_code)]
    fn propagate_equalities(&mut self) -> TheoryCheckResult {
        // Process all pending equalities
        while let Some(eq) = self.pending_equalities.pop() {
            // Avoid processing the same equality twice
            let key = if eq.lhs < eq.rhs {
                (eq.lhs, eq.rhs)
            } else {
                (eq.rhs, eq.lhs)
            };

            if self.processed_equalities.contains_key(&key) {
                continue;
            }
            self.processed_equalities.insert(key, true);

            // Notify EUF theory
            let lhs_node = self.euf.intern(eq.lhs);
            let rhs_node = self.euf.intern(eq.rhs);
            if let Err(_e) = self
                .euf
                .merge(lhs_node, rhs_node, eq.reason.unwrap_or(eq.lhs))
            {
                // Merge failed - should not happen
                continue;
            }

            // Check for conflicts after merging
            if let Some(conflict_terms) = self.euf.check_conflicts() {
                let conflict_lits = self.terms_to_conflict_clause(&conflict_terms);
                return TheoryCheckResult::Conflict(conflict_lits);
            }

            // Notify arithmetic theory
            self.arith.notify_equality(eq);
        }

        TheoryCheckResult::Sat
    }

    /// Propagate EUF-derived equalities to the arithmetic solver.
    ///
    /// When EUF fires congruence closure and derives `f(x) = f(y)` because
    /// `x = y` was asserted, the arithmetic solver is unaware of this equality.
    /// This method gathers all arithmetic terms from `var_to_parsed_arith`,
    /// looks each one up in EUF (via `term_to_node`), and for any pair whose
    /// EUF nodes are in the same equivalence class asserts `t1 - t2 = 0` into
    /// the arithmetic solver.
    ///
    /// Note: `euf.intern(t)` uses the `term_to_node` map first, so it correctly
    /// returns the shared node index even when two distinct term IDs (e.g.
    /// `f_x_term` and `f_y_term`) were mapped to the same node via congruence
    /// during `intern_app`.
    fn propagate_euf_equalities_to_arith(&mut self) -> TheoryCheckResult {
        // Collect every unique term ID that appears in any parsed arithmetic
        // constraint.  These are the terms the arithmetic solver knows about.
        let mut arith_terms: Vec<TermId> = Vec::new();
        for parsed in self.var_to_parsed_arith.values() {
            for &(term, _coef) in &parsed.terms {
                if !arith_terms.contains(&term) {
                    arith_terms.push(term);
                }
            }
        }

        // For each pair of arith terms, check if they are EUF-equal.
        // `euf.intern(t)` looks up `term_to_node` first, so two terms that
        // share the same EUF node (via congruence at intern-time) correctly
        // return the same node index.
        // App-intern every function-application / Select arith term into EUF
        // *as a congruence node* (via `intern_term_for_congruence`, which calls
        // `intern_app`), so the are_equal check below can see congruence.
        // Without this, a function app that appears only NESTED inside an arith
        // operator — e.g. `f(b)` inside `(+ (f b) 1)` — is never interned as an
        // app (the `+` is an opaque EUF leaf that is not recursed into), so the
        // congruence `a=b ⟹ f(a)=f(b)` never reaches the arith solver and a
        // genuinely-UNSAT instance like `a=b ∧ f(a)=f(b)+1` is reported `sat`
        // (verus-fork 2026-06-17 spurious-SAT survey #65). Restricted to
        // Apply/Select: interning IntConst arith terms here would add the
        // pairwise-disequality edges that `intern_term_for_congruence` warns can
        // cause spurious UNSAT when the ArithSolver is the one tracking numerics.
        // Interning an app node is sound — it registers the term and lets
        // congruence (an entailed equality) fire; it never asserts anything new.
        let mgr = Arc::clone(&self.manager);
        for &t in &arith_terms {
            let is_app_or_select = mgr.get(t).is_some_and(|td| {
                matches!(
                    td.kind,
                    TermKind::Apply { .. } | TermKind::Select(..) | TermKind::DtSelector { .. }
                )
            });
            if is_app_or_select && self.euf.term_to_node(t).is_none() {
                self.intern_term_for_congruence(t, &mgr);
            }
        }
        for i in 0..arith_terms.len() {
            for j in (i + 1)..arith_terms.len() {
                let t1 = arith_terms[i];
                let t2 = arith_terms[j];
                if t1 == t2 {
                    continue;
                }
                // Only consider terms that have been registered in EUF.
                let Some(n1) = self.euf.term_to_node(t1) else {
                    continue;
                };
                let Some(n2) = self.euf.term_to_node(t2) else {
                    continue;
                };
                if self.euf.are_equal(n1, n2) {
                    // EUF has derived t1 = t2.  Assert this equality into the
                    // arithmetic solver as `1*t1 + (-1)*t2 = 0`.
                    // Use t1 as the reason term for conflict clause generation.
                    let reason = t1;
                    let eq_terms = [
                        (t1, ArithRat::from_integer(1)),
                        (t2, ArithRat::from_integer(-1)),
                    ];
                    self.declare_arith_sorts(&eq_terms); // #427
                    self.arith
                        .assert_eq(&eq_terms, ArithRat::from_integer(0), reason);

                    // Check ArithSolver for conflicts after each new equality.
                    use oxiz_theories::Theory;
                    use oxiz_theories::TheoryCheckResult as TheoryCheckResultEnum;
                    if let Ok(TheoryCheckResultEnum::Unsat(conflict_terms)) = self.arith.check() {
                        // Suppress a stale-bound pseudo-conflict (two distinct
                        // assertions of one atom under opposite polarities left
                        // in the simplex by a SAT backtrack the theory frame did
                        // not retract); reporting it would be a spurious UNSAT.
                        if !self.suppress_stale_bounds
                            || !self.arith.last_conflict_is_stale_bound()
                        {
                            let conflict_lits = self.terms_to_conflict_clause(&conflict_terms);
                            return TheoryCheckResult::Conflict(conflict_lits);
                        }
                    }
                }
            }
        }

        TheoryCheckResult::Sat
    }

    /// Model-based theory combination
    /// Detects conflicts where EUF has derived an equality between two terms
    /// but the arithmetic solver assigns them different values.
    fn model_based_combination(&mut self) -> TheoryCheckResult {
        let shared_terms: Vec<TermId> = self.term_to_var.keys().copied().collect();

        // ── Arith→EUF entailed-equality propagation (Nelson-Oppen) ──────────
        // An arith-FIXED term `t = v` is an ENTAILED equality. Merge `t` with the
        // canonical EUF node for the integer constant `v` so congruence fires
        // (e.g. fixing `f(1)=5` lets EUF derive `f(f(1))=f(5)`). The merge's EUF
        // reason is a placeholder; the conflict clause is rebuilt from
        // `pending_arith_eq_reasons` (the real pinning bounds) so it stays sound.
        self.pending_arith_eq_reasons.clear();
        // The terms eligible for congruence are the EUF-interned SUB-terms
        // (`f(1)`, `f(5)`, the constant `5`, …) — NOT the Bool atoms in
        // `term_to_var`. Snapshot them; the merge loop mutates EUF. Negative
        // constants are reachable too: the `mk_neg` sanitizer normalises `(- 3)`
        // to `IntConst(-3)`, so `interned_int_constants` holds the canonical node
        // for negative values just like positive ones.
        let euf_terms: Vec<TermId> = self.euf.interned_term_ids();
        let mut propagated = false;
        // Bounded fixpoint: one merge can fix a deeper term — re-scan until
        // quiescent, capped by the term count.
        for _round in 0..=euf_terms.len() {
            let mut progress = false;
            for &t in &euf_terms {
                let Some(t_node) = self.euf.term_to_node(t) else {
                    continue;
                };
                // `OXIZ_MBC_DBG`: one line per EUF-interned term with its
                // arith value and whether the fixed-value probe confirmed it.
                // This is what located #434: after an int-case-split re-solve,
                // the split term probes FIXED while a variable linked to it by
                // a LEVEL-0 equality carries a value violating that equality —
                // i.e. the equality is missing from the re-solve's arith
                // state, which points at the solve-boundary theory-frame
                // accounting, not at the split.
                let dbg = std::env::var_os("OXIZ_MBC_DBG").is_some();
                let Some((v, reasons)) = self.arith.fixed_value_with_reasons(t) else {
                    if dbg {
                        eprintln!("[mbc] {t:?}: not fixed (value={:?})", self.arith.value(t));
                    }
                    continue;
                };
                if dbg {
                    eprintln!("[mbc] {t:?}: FIXED at {v:?} ({} reasons)", reasons.len());
                }
                if !v.is_integer() {
                    continue;
                }
                // `v.to_integer()` is i128 (the LRA/LIA core's `ArithRat`).
                // `interned_int_constants` is keyed by i64 (its constants come
                // from `IntConst.to_i64()`), so a fixed value outside i64 cannot
                // match any interned constant — `try_from` failure ⇒ skip the
                // merge. This is sound: no EUF congruence is fired for a value
                // the integer-constant index does not (and cannot) hold.
                let Ok(iv) = i64::try_from(v.to_integer()) else {
                    continue;
                };
                let Some(&const_node) = self.interned_int_constants.get(&iv) else {
                    continue;
                };
                if t_node == const_node || self.euf.are_equal(t_node, const_node) {
                    continue;
                }
                // Entailed merge: fires congruence; reason is a placeholder.
                let _ = self.euf.merge(t_node, const_node, t);
                self.pending_arith_eq_reasons.extend(reasons);
                progress = true;
                propagated = true;
            }
            if !progress {
                break;
            }
        }

        if propagated {
            // (A) The new congruence may expose an EUF disequality conflict.
            if let Some(conflict_terms) = self.euf.check_conflicts() {
                let mut terms = conflict_terms;
                for &r in &self.pending_arith_eq_reasons {
                    if !terms.contains(&r) {
                        terms.push(r);
                    }
                }
                return TheoryCheckResult::Conflict(self.terms_to_conflict_clause(&terms));
            }
            // (B) The new equalities may make arith infeasible. The clause
            // `propagate_euf_equalities_to_arith` builds OMITS the pinning bounds
            // (they are arith reasons, not EUF ones), so AUGMENT it with them —
            // otherwise the learned clause is not theory-valid and a spurious
            // UNSAT leaks. The augmented clause stays all-false (every pinning
            // bound is a currently-asserted atom).
            if let TheoryCheckResult::Conflict(mut lits) = self.propagate_euf_equalities_to_arith()
            {
                let fix_lits = self.terms_to_conflict_clause(&self.pending_arith_eq_reasons);
                for l in fix_lits {
                    if !lits.contains(&l) {
                        lits.push(l);
                    }
                }
                return TheoryCheckResult::Conflict(lits);
            }
        }

        // Check: EUF equality vs arith disagreement
        for i in 0..shared_terms.len() {
            for j in (i + 1)..shared_terms.len() {
                let t1 = shared_terms[i];
                let t2 = shared_terms[j];

                // Only compare terms ALREADY interned in EUF — never `intern`
                // here. `intern` is the LEAF intern, so on an application term
                // (e.g. `f(g(k))`) it would fabricate a spurious leaf node; and
                // creating ANY node DURING a theory check (after a SAT push)
                // grows the EUF node space while `pop` later truncates it,
                // leaving stale union-find roots that index past `use_list`
                // (an out-of-bounds panic / wrong `find`s).
                let (Some(t1_node), Some(t2_node)) =
                    (self.euf.term_to_node(t1), self.euf.term_to_node(t2))
                else {
                    continue;
                };

                if self.euf.are_equal(t1_node, t2_node) {
                    let t1_value = self.arith.value(t1);
                    let t2_value = self.arith.value(t2);
                    if let (Some(v1), Some(v2)) = (t1_value, t2_value)
                        && v1 != v2
                    {
                        let conflict_lits = self.terms_to_conflict_clause(&[t1, t2]);
                        return TheoryCheckResult::Conflict(conflict_lits);
                    }
                }
            }
        }

        TheoryCheckResult::Sat
    }

    /// Add an equality to be shared between theories
    #[allow(dead_code)]
    fn add_shared_equality(&mut self, lhs: TermId, rhs: TermId, reason: Option<TermId>) {
        self.pending_equalities
            .push(EqualityNotification { lhs, rhs, reason });
    }

    /// Get theory decision hints for branching
    /// Returns suggested variables to branch on, ordered by priority
    #[allow(dead_code)]
    fn get_decision_hints(&mut self) -> &[TheoryDecision] {
        // Clear old hints
        self.decision_hints.clear();

        // Collect hints from theory solvers
        // For now, we can suggest branching on variables that appear in
        // unsatisfied constraints or pending equalities

        // EUF hints: suggest branching on disequalities that might conflict
        // Arithmetic hints: suggest branching on bounds that are close to being violated

        // This is a placeholder - full implementation would query theory solvers
        // for their preferred branching decisions

        &self.decision_hints
    }

    /// Sentinel function ID used for array `select(array, index)` in EUF.
    ///
    /// `Spur::into_inner()` always returns a `NonZeroU32` (>= 1), so 0 is safe
    /// to use as a special, collision-free function ID for the built-in select
    /// operation.  By interning `select(a, i)` as `intern_app(term, SELECT_FUNC_ID,
    /// [a_node, i_node])`, the EUF congruence closure engine treats select like any
    /// other binary function application and will automatically derive
    /// `select(a, x) = select(a, y)` whenever `x = y` is merged.
    const SELECT_FUNC_ID: u32 = 0;

    /// Intern a term into EUF, using `intern_app` for Apply terms and
    /// `TermKind::Select` terms so that congruence closure works correctly.
    ///
    /// Plain `intern` creates opaque nodes with no function-symbol or argument
    /// information, which prevents the congruence closure algorithm from firing
    /// when argument classes are merged.
    ///
    /// `Select(array, index)` is treated as a binary function application with
    /// the special function ID `SELECT_FUNC_ID` (0).  This ensures that when
    /// `x = y` causes their EUF nodes to merge, congruence automatically
    /// derives `select(a, x) = select(a, y)`, which in turn allows further
    /// congruence steps (e.g., `f(select(a,x)) = f(select(a,y))`).
    #[allow(dead_code)]
    fn intern_term_deep(&mut self, term: TermId, manager: &TermManager) -> u32 {
        if let Some(idx) = self.euf.term_to_node(term) {
            return idx;
        }
        if let Some(t) = manager.get(term) {
            match &t.kind {
                TermKind::Apply { func, args, .. } => {
                    let func_id = func.into_inner().get();
                    let arg_nodes: SmallVec<[u32; 4]> = args
                        .iter()
                        .map(|&a| self.intern_term_deep(a, manager))
                        .collect();
                    return self.euf.intern_app(term, func_id, arg_nodes);
                }
                TermKind::Select(array, index) => {
                    // Intern both sub-terms first (recursively), then register
                    // `select` as a binary function application so that EUF
                    // congruence closure fires when the index (or array) args
                    // become equal.
                    let array_node = self.intern_term_deep(*array, manager);
                    let index_node = self.intern_term_deep(*index, manager);
                    return self.euf.intern_app(
                        term,
                        Self::SELECT_FUNC_ID,
                        [array_node, index_node],
                    );
                }
                TermKind::DtConstructor { constructor, args } => {
                    // #404 phase 2 — a datatype constructor application is a
                    // FUNCTION application to EUF (congruence is valid for any
                    // function; distinctness/injectivity stay elsewhere). As an
                    // opaque leaf, `x=y` never derived `C(sel(x)…)=C(sel(y)…)`,
                    // so a shape equality established at one term never reached
                    // the congruent shape atom of an equal term (the dm3
                    // decreases-check bridge init≡E).
                    let func_id = constructor.into_inner().get();
                    let arg_nodes: SmallVec<[u32; 4]> = args
                        .iter()
                        .map(|&a| self.intern_term_deep(a, manager))
                        .collect();
                    return self.euf.intern_app(term, func_id, arg_nodes);
                }
                TermKind::DtSelector { selector, arg } => {
                    // Selector application = unary function application. Keyed
                    // by the selector's name spur — identical to a same-named
                    // `Apply`'s key, so the parser's `(sel x)` (an `Apply`) and
                    // a `DtSelector` node over the same argument land in ONE
                    // congruence class automatically.
                    let arg_node = self.intern_term_deep(*arg, manager);
                    return self
                        .euf
                        .intern_app(term, selector.into_inner().get(), [arg_node]);
                }
                TermKind::IntConst(n) => {
                    // Intern the integer constant as an EUF node and maintain
                    // pairwise disequalities between *distinct* integer values.
                    //
                    // EUF has no built-in notion of numeric inequality.  Without
                    // explicit disequality edges, a congruence chain equating a
                    // node merged with `10` and one merged with `20` would not
                    // produce a conflict.  We therefore assert `10 ≠ 20` etc.
                    //
                    // Performance: we track one *canonical* EUF node per unique
                    // integer value.  When the same value appears again (e.g. as a
                    // fresh TermId created during MBQI instantiation) we merge the
                    // new node into the canonical one.  This bounds the number of
                    // entries — and therefore of pairwise disequality edges — to the
                    // number of *distinct* literal values in the formula, preventing
                    // the O(n²) blowup that arises when MBQI creates many fresh
                    // TermIds for the same integer literal across iterations.
                    if let Some(val) = n.to_i64() {
                        let new_node = self.euf.intern(term);
                        if let Some(&canonical) = self.interned_int_constants.get(&val) {
                            // This value already has a canonical node.  Merge the
                            // new term's node into it so that congruence closure
                            // treats them as equal (they represent the same number).
                            // Ignore merge errors: the nodes may already be in the
                            // same class if this term was interned before.
                            let _ = self.euf.merge(new_node, canonical, term);
                            return canonical;
                        }
                        // First time we see this value: register the canonical node
                        // and assert disequality against every other distinct value.
                        let diseq_targets: Vec<u32> =
                            self.interned_int_constants.values().copied().collect();
                        for other_node in diseq_targets {
                            self.euf.assert_diseq(new_node, other_node, term);
                        }
                        self.interned_int_constants.insert(val, new_node);
                        return new_node;
                    }
                    // BigInt too large for i64 -- fall through to plain intern.
                }
                // #433: same canonical-Bool tie as `intern_term_for_congruence`
                // — the two intern paths must agree on where `true`/`false`
                // land, and the `term_to_node` short-circuit at the top makes
                // whichever runs first authoritative for the mapping.
                TermKind::True => {
                    let node = self.euf.intern(term);
                    let (t, _) = self.ensure_bool_nodes();
                    let _ = self.euf.merge(node, t, term);
                    return node;
                }
                TermKind::False => {
                    let node = self.euf.intern(term);
                    let (_, f) = self.ensure_bool_nodes();
                    let _ = self.euf.merge(node, f, term);
                    return node;
                }
                _ => {}
            }
        }
        self.euf.intern(term)
    }

    /// Intern a term into EUF for congruence closure, using `intern_app` for
    /// Apply and Select terms so that congruence fires correctly.
    ///
    /// Unlike `intern_term_deep`, this variant does NOT add IntConst pairwise
    /// disequality edges.  Those edges are necessary for conflict detection when
    /// numeric constants are compared via the EUF layer, but they cause spurious
    /// UNSAT in SAT cases where the ArithSolver is the one tracking numeric
    /// inequalities.  This function is used exclusively inside
    /// `process_constraint` for equality/disequality assertions so that
    /// `f(a)=f(b)` congruence works while arithmetic stays in the ArithSolver.
    fn intern_term_for_congruence(&mut self, term: TermId, manager: &TermManager) -> u32 {
        if let Some(idx) = self.euf.term_to_node(term) {
            return idx;
        }
        if let Some(t) = manager.get(term) {
            match &t.kind {
                TermKind::Apply { func, args, .. } => {
                    let func_id = func.into_inner().get();
                    let arg_nodes: SmallVec<[u32; 4]> = args
                        .iter()
                        .map(|&a| self.intern_term_for_congruence(a, manager))
                        .collect();
                    return self.euf.intern_app(term, func_id, arg_nodes);
                }
                TermKind::Select(array, index) => {
                    let array_node = self.intern_term_for_congruence(*array, manager);
                    let index_node = self.intern_term_for_congruence(*index, manager);
                    return self.euf.intern_app(
                        term,
                        Self::SELECT_FUNC_ID,
                        [array_node, index_node],
                    );
                }
                TermKind::DtConstructor { constructor, args } => {
                    // #404 phase 2 — see `intern_term_deep`: ctor application
                    // is a function application to EUF (congruence only).
                    let func_id = constructor.into_inner().get();
                    let arg_nodes: SmallVec<[u32; 4]> = args
                        .iter()
                        .map(|&a| self.intern_term_for_congruence(a, manager))
                        .collect();
                    return self.euf.intern_app(term, func_id, arg_nodes);
                }
                TermKind::DtSelector { selector, arg } => {
                    // Unary app keyed by the selector's name spur (unifies with
                    // a same-named `Apply` — see `intern_term_deep`).
                    let arg_node = self.intern_term_for_congruence(*arg, manager);
                    return self
                        .euf
                        .intern_app(term, selector.into_inner().get(), [arg_node]);
                }
                TermKind::IntConst(n) => {
                    // Maintain pairwise disequalities between *distinct* integer
                    // constant VALUES, keyed by a single canonical EUF node per
                    // value (mirrors `intern_term_deep` and the `BitVecConst` arm
                    // below).  Without this, an equality chain that merges a UF
                    // term of integer sort with two distinct literals — e.g.
                    // `f(3)=3`, `f(3)=4`, or the MBQI instance `f(3)=3` against an
                    // asserted `f(3)=4` — lands `3` and `4` in one congruence class
                    // with no `3 != 4` edge, so EUF reports no conflict and the
                    // application term never reaches the ArithSolver (it is not a
                    // parsed linear constraint).  The result was an unsound `sat`
                    // (the `forall a. f(a)=a; f(3)=4` e-matching repro returned
                    // `sat`; see docs/QUANTIFIER_EMATCH_SOUNDNESS_BUG.md).
                    //
                    // A disequality between two genuinely distinct constant values
                    // is a tautology, so it can only fire a conflict when asserted
                    // equalities have *already* forced `3 = 4` — a real
                    // contradiction, never a spurious one.  Numeric *inequality*
                    // reasoning over arithmetic VARIABLES stays in the ArithSolver;
                    // this only pins distinct ground literals apart in EUF.
                    if let Some(val) = n.to_i64() {
                        let new_node = self.euf.intern(term);
                        if let Some(&canonical) = self.interned_int_constants.get(&val) {
                            let _ = self.euf.merge(new_node, canonical, term);
                            return canonical;
                        }
                        let diseq_targets: Vec<u32> =
                            self.interned_int_constants.values().copied().collect();
                        for other_node in diseq_targets {
                            self.euf.assert_diseq(new_node, other_node, term);
                        }
                        self.interned_int_constants.insert(val, new_node);
                        return new_node;
                    }
                    // BigInt too large for i64 — fall through to plain intern.
                }
                TermKind::BitVecConst { value, width } => {
                    // Register the BV constant as an EUF node and maintain pairwise
                    // disequalities between *distinct* same-width constant values.
                    //
                    // EUF has no built-in notion that two different bit-vector
                    // literals are unequal.  Without explicit disequality edges, a
                    // congruence chain that equates a node merged with `#x00` and one
                    // merged with `#x01` (e.g. `g(a)=#x00`, `g(b)=#x01`, `a=b`) would
                    // not produce a conflict.  We therefore assert `#x00 ≠ #x01` etc.
                    //
                    // As with `interned_int_constants`, we keep one canonical EUF
                    // node per distinct `(value, width)` pair: when the same value
                    // reappears (a fresh TermId) we merge it into the canonical node,
                    // bounding the number of pairwise edges by the count of distinct
                    // BV literals rather than the total number of term IDs.
                    let key = (value.iter_u64_digits().next().unwrap_or(0), *width);
                    let new_node = self.euf.intern(term);
                    if let Some(&canonical) = self.interned_bv_constants.get(&key) {
                        let _ = self.euf.merge(new_node, canonical, term);
                        return canonical;
                    }
                    // First time we see this value: assert disequality against every
                    // other distinct constant of the SAME width (different widths are
                    // different sorts and are never merged), then register it.
                    let diseq_targets: Vec<u32> = self
                        .interned_bv_constants
                        .iter()
                        .filter_map(|(&(_v, w), &node)| (w == *width).then_some(node))
                        .collect();
                    for other_node in diseq_targets {
                        self.euf.assert_diseq(new_node, other_node, term);
                    }
                    self.interned_bv_constants.insert(key, new_node);
                    return new_node;
                }
                // #433: tie the Bool literals to the CANONICAL true/false
                // nodes (the ones `Constraint::BoolApp` merges against).
                // Without this, `(= b true)` merged `b` with a private
                // per-term "true" leaf unrelated to the class a true-assigned
                // Bool application lives in, so the two "true"s never met and
                // congruence across them was silently lost.
                //
                // Intern-then-MERGE rather than returning the canonical node
                // directly: `intern` records the real `term → node` mapping,
                // so the other intern path (`intern_term_deep`, which carries
                // this same arm) and any later lookup stay consistent. The
                // merge is a tautology (`true = TRUE`), so it can never be a
                // spurious conflict source, and its reason term having no SAT
                // variable is fine — `terms_to_conflict_clause` skips var-less
                // reasons, and dropping a tautology from a conflict clause
                // keeps the clause valid.
                TermKind::True => {
                    let node = self.euf.intern(term);
                    let (t, _) = self.ensure_bool_nodes();
                    let _ = self.euf.merge(node, t, term);
                    return node;
                }
                TermKind::False => {
                    let node = self.euf.intern(term);
                    let (_, f) = self.ensure_bool_nodes();
                    let _ = self.euf.merge(node, f, term);
                    return node;
                }
                _ => {}
            }
        }
        self.euf.intern(term)
    }

    /// Ensure canonical EUF nodes for Boolean true/false exist, with a
    /// disequality between them.  Returns `(true_node, false_node)`.
    fn ensure_bool_nodes(&mut self) -> (u32, u32) {
        if let (Some(t), Some(f)) = (self.bool_true_node, self.bool_false_node) {
            return (t, f);
        }
        // Use sentinel TermIds that will never collide with real terms.
        // TermId(u32::MAX) and TermId(u32::MAX - 1) are reserved for this.
        let true_term = TermId::new(u32::MAX);
        let false_term = TermId::new(u32::MAX - 1);
        let t = self.euf.intern(true_term);
        let f = self.euf.intern(false_term);
        self.euf.assert_diseq(t, f, true_term);
        self.bool_true_node = Some(t);
        self.bool_false_node = Some(f);
        (t, f)
    }

    /// Look up the term ID for a SAT variable.
    /// Returns a sentinel zero TermId if not found.
    #[inline]
    fn term_for_var(&self, var: Var) -> TermId {
        self.var_to_term
            .get(var.index())
            .copied()
            .unwrap_or_else(|| TermId::new(0))
    }

    /// #427 — declare the SMT sort of every term about to enter the arithmetic
    /// solver as a linear-form atom.
    ///
    /// `ArithSolver` only ever sees `TermId`s, so it cannot tell an Int-sorted
    /// term from a Real-sorted one; left to guess it falls back to the LIA/LRA
    /// mode `Solver::set_logic` derived from the logic NAME, which is exactly the
    /// thing that is wrong under `ALL` / no `(set-logic)` / `AUFLIRA`.
    ///
    /// `Solver::track_theory_vars` already declares the terms it registers
    /// (variables, numeric applications, numeric selects). This covers the
    /// remainder — atoms that reach the simplex only through
    /// `parse_arith_comparison`, e.g. an opaque `(* x y)` product or a `div`/`mod`
    /// node, which `track_theory_vars` recurses THROUGH rather than registering.
    fn declare_arith_sorts(&mut self, terms: &[(TermId, ArithRat)]) {
        let int_sort = self.manager.sorts.int_sort;
        for &(t, _) in terms {
            if let Some(term) = self.manager.get(t) {
                let sort = term.sort;
                // Only Int/Real-sorted atoms carry a meaningful integrality; a
                // bitvector atom is integral too (see `track_theory_vars`).
                let is_bv = self
                    .manager
                    .sorts
                    .get(sort)
                    .is_some_and(oxiz_core::sort::Sort::is_bitvec);
                if sort == int_sort || is_bv {
                    self.arith.declare_sort(t, true);
                } else if sort == self.manager.sorts.real_sort {
                    self.arith.declare_sort(t, false);
                }
            }
        }
    }

    /// Convert a list of term IDs to a conflict clause
    /// Each term ID should correspond to a constraint that was asserted
    fn terms_to_conflict_clause(&self, terms: &[TermId]) -> SmallVec<[Lit; 8]> {
        let mut conflict = SmallVec::new();
        for &term in terms {
            if let Some(&var) = self.term_to_var.get(&term) {
                // Emit the literal in the polarity that FALSIFIES it under the
                // current assignment: a positively-assigned atom contributes its
                // negation, a negatively-assigned atom contributes itself.  A
                // reason term whose atom was asserted positively (the common
                // case: an equality the SAT solver set true, merged in EUF) maps
                // to `Lit::neg`; a reason term from a negatively-assigned atom
                // (an equality set false, asserted as a disequality) maps to
                // `Lit::pos`.  Defaulting to `neg` when the phase is unknown
                // preserves the historical behaviour for atoms we never saw
                // assigned (e.g. internally-derived reasons).
                let lit = match self.assigned_phase.get(&var) {
                    Some(false) => Lit::pos(var),
                    _ => Lit::neg(var),
                };
                conflict.push(lit);
            }
        }
        conflict
    }

    /// Look up the BV bit-width of a term from its sort, if it has a BV sort.
    fn bv_width_of(&self, term: TermId, manager: &TermManager) -> Option<u32> {
        manager
            .get(term)
            .and_then(|t| manager.sorts.get(t.sort))
            .and_then(|s| s.bitvec_width())
    }

    /// Bit-blast both operands of a BV constraint into the embedded SAT solver.
    ///
    /// Each side is encoded recursively; a bare leaf that the recursive encoder
    /// cannot handle falls back to a fresh BV variable of the operand's width.
    /// Returns `true` if both operands are BV-sorted with equal width (so that
    /// `assert_eq` / `assert_neq` may be called safely), `false` otherwise.
    fn bit_blast_bv_pair(&mut self, lhs: TermId, rhs: TermId, manager: &TermManager) -> bool {
        let (lw, rw) = match (
            self.bv_width_of(lhs, manager),
            self.bv_width_of(rhs, manager),
        ) {
            (Some(lw), Some(rw)) if lw == rw => (lw, rw),
            _ => return false,
        };
        let mut encoded: FxHashSet<TermId> = FxHashSet::default();
        if !encode_bv_term_recursive(&mut self.bv, lhs, manager, &mut encoded) {
            self.bv.new_bv(lhs, lw);
        }
        if !encode_bv_term_recursive(&mut self.bv, rhs, manager, &mut encoded) {
            self.bv.new_bv(rhs, rw);
        }
        true
    }

    /// Run the embedded BV SAT check after the caller has asserted a constraint.
    ///
    /// Records `constraint_term` so the conflict clause is non-empty, then
    /// returns `Some(Conflict(..))` if the embedded solver reports UNSAT and
    /// `None` otherwise (so the caller falls through to its conservative path).
    fn bv_run_check(&mut self, constraint_term: TermId) -> Option<TheoryCheckResult> {
        use oxiz_theories::Theory;
        use oxiz_theories::TheoryCheckResult as TheoryCheckResultEnum;
        self.bv.record_constraint_term(constraint_term);
        if let Ok(TheoryCheckResultEnum::Unsat(conflict_terms)) = self.bv.check() {
            let conflict_lits = self.terms_to_conflict_clause(&conflict_terms);
            return Some(TheoryCheckResult::Conflict(conflict_lits));
        }
        None
    }

    /// Bit-blast `lhs`/`rhs`, assert `lhs != b` at the bit level, and check.
    ///
    /// Returns `Some(Conflict(..))` on a detected BV theory conflict, `None`
    /// otherwise (including when the operands are not equal-width BV terms).
    fn bv_check_neq(
        &mut self,
        lhs: TermId,
        rhs: TermId,
        constraint_term: TermId,
        manager: &TermManager,
    ) -> Option<TheoryCheckResult> {
        if !self.bit_blast_bv_pair(lhs, rhs, manager) {
            return None;
        }
        self.bv.assert_neq(lhs, rhs);
        self.bv_run_check(constraint_term)
    }

    /// Bit-blast `lhs`/`rhs`, assert `lhs = b` at the bit level, and check.
    ///
    /// Returns `Some(Conflict(..))` on a detected BV theory conflict, `None`
    /// otherwise (including when the operands are not equal-width BV terms).
    fn bv_check_eq(
        &mut self,
        lhs: TermId,
        rhs: TermId,
        constraint_term: TermId,
        manager: &TermManager,
    ) -> Option<TheoryCheckResult> {
        if !self.bit_blast_bv_pair(lhs, rhs, manager) {
            return None;
        }
        self.bv.assert_eq(lhs, rhs);
        self.bv_run_check(constraint_term)
    }

    /// Process a theory constraint
    fn process_constraint(
        &mut self,
        var: Var,
        constraint: Constraint,
        is_positive: bool,
        manager: &TermManager,
    ) -> TheoryCheckResult {
        match constraint {
            Constraint::Eq(lhs, rhs) => {
                if is_positive {
                    // Positive assignment: a = b, tell EUF to merge.
                    // Use the constraint term (which has a SAT variable) as the
                    // merge reason so that conflict clause generation can find it
                    // in term_to_var.
                    let constraint_term = self.term_for_var(var);
                    // Use intern_term_for_congruence so that Apply/Select terms are
                    // registered with intern_app, enabling EUF congruence closure
                    // (e.g., a=b → f(a)=f(b)).  This variant does NOT add IntConst
                    // pairwise disequality edges, keeping arithmetic reasoning in the
                    // ArithSolver and avoiding spurious UNSAT in SAT cases.
                    let lhs_node = self.intern_term_for_congruence(lhs, manager);
                    let rhs_node = self.intern_term_for_congruence(rhs, manager);
                    if let Err(_e) = self.euf.merge(lhs_node, rhs_node, constraint_term) {
                        // Merge failed - should not happen in normal operation
                        return TheoryCheckResult::Sat;
                    }

                    // Check for immediate conflicts
                    if let Some(conflict_terms) = self.euf.check_conflicts() {
                        // Convert term IDs to literals for conflict clause
                        let conflict_lits = self.terms_to_conflict_clause(&conflict_terms);
                        return TheoryCheckResult::Conflict(conflict_lits);
                    }

                    // For arithmetic equalities, also send to ArithSolver
                    // Use pre-parsed constraint if available
                    if let Some(parsed) = self.var_to_parsed_arith.get(&var) {
                        let terms: Vec<(TermId, ArithRat)> =
                            parsed.terms.iter().copied().collect();
                        let constant = parsed.constant;
                        let reason = parsed.reason_term;

                        // For equality, use assert_eq which has GCD-based infeasibility detection
                        // This is critical for LIA: e.g., 2x + 2y = 7 is unsatisfiable because
                        // gcd(2,2) = 2 doesn't divide 7
                        self.declare_arith_sorts(&terms); // #427
                        self.arith.assert_eq(&terms, constant, reason);

                        // Check ArithSolver for conflicts
                        use oxiz_theories::Theory;
                        use oxiz_theories::TheoryCheckResult as TheoryCheckResultEnum;
                        if let Ok(TheoryCheckResultEnum::Unsat(conflict_terms)) = self.arith.check()
                        {
                            if !self.suppress_stale_bounds
                                || !self.arith.last_conflict_is_stale_bound()
                            {
                                let conflict_lits = self.terms_to_conflict_clause(&conflict_terms);
                                return TheoryCheckResult::Conflict(conflict_lits);
                            }
                        }
                    }

                    // For bitvector equalities, also send to BvSolver
                    // Handle variables, constants, and BV operations
                    // Check if terms have BV sort (not just if they're in bv_terms)
                    let lhs_is_bv = manager
                        .get(lhs)
                        .and_then(|t| manager.sorts.get(t.sort))
                        .is_some_and(|s| s.is_bitvec());
                    let rhs_is_bv = manager
                        .get(rhs)
                        .and_then(|t| manager.sorts.get(t.sort))
                        .is_some_and(|s| s.is_bitvec());

                    if lhs_is_bv || rhs_is_bv {
                        let mut did_assert = false;

                        // Helper to extract BV constant info
                        let get_bv_const = |term_id: TermId| -> Option<(u64, u32)> {
                            manager.get(term_id).and_then(|t| match &t.kind {
                                TermKind::BitVecConst { value, width } => {
                                    let val_u64 = value.iter_u64_digits().next().unwrap_or(0);
                                    Some((val_u64, *width))
                                }
                                _ => None,
                            })
                        };

                        // Helper to get BV width from term's sort
                        let get_bv_width = |term_id: TermId| -> Option<u32> {
                            manager.get(term_id).and_then(|t| {
                                manager.sorts.get(t.sort).and_then(|s| s.bitvec_width())
                            })
                        };

                        // Helper to check if term is a simple variable
                        let is_var = |term_id: TermId| -> bool {
                            manager
                                .get(term_id)
                                .is_some_and(|t| matches!(t.kind, TermKind::Var(_)))
                        };

                        // Memo set to track already-encoded TermIds within this
                        // constraint so that shared sub-terms are encoded exactly once.
                        let mut bv_encoded: FxHashSet<TermId> = FxHashSet::default();

                        // Check for BV operations and encode them
                        let lhs_term = manager.get(lhs);
                        let rhs_term = manager.get(rhs);

                        // Helper to check if a term is a BV operation
                        let is_bv_op = |t: &oxiz_core::ast::Term| {
                            matches!(
                                t.kind,
                                TermKind::BvAdd(_, _)
                                    | TermKind::BvMul(_, _)
                                    | TermKind::BvSub(_, _)
                                    | TermKind::BvAnd(_, _)
                                    | TermKind::BvOr(_, _)
                                    | TermKind::BvXor(_, _)
                                    | TermKind::BvNot(_)
                                    | TermKind::BvUdiv(_, _)
                                    | TermKind::BvSdiv(_, _)
                                    | TermKind::BvUrem(_, _)
                                    | TermKind::BvSrem(_, _)
                            )
                        };

                        let lhs_is_op = lhs_term.is_some_and(is_bv_op);
                        let rhs_is_op = rhs_term.is_some_and(is_bv_op);

                        let lhs_const_info = get_bv_const(lhs);
                        let rhs_const_info = get_bv_const(rhs);
                        let lhs_is_var = is_var(lhs);
                        let rhs_is_var = is_var(rhs);

                        // Case 0: BV operation = BV operation
                        // (e.g. (= (bvadd x y) (bvadd y x)), (= (bvmul #x02 x) (bvadd x x))).
                        // Both sides are fully bit-blasted and then constrained equal so
                        // that commutativity / associativity / distributivity conflicts
                        // are detected by the embedded SAT solver.
                        if lhs_is_op && rhs_is_op {
                            if let Some(_width) = get_bv_width(lhs) {
                                encode_bv_term_recursive(&mut self.bv, lhs, manager, &mut bv_encoded);
                                encode_bv_term_recursive(&mut self.bv, rhs, manager, &mut bv_encoded);
                                self.bv.assert_eq(lhs, rhs);
                                did_assert = true;
                            }
                        }
                        // Case 1: BV operation = constant (e.g., (= (bvmul x y) #x0c))
                        else if lhs_is_op {
                            if let Some(width) = get_bv_width(lhs) {
                                // Recursively encode the LHS operation and all its sub-terms
                                encode_bv_term_recursive(&mut self.bv, lhs, manager, &mut bv_encoded);

                                if let Some((val, _)) = rhs_const_info {
                                    // Assert operation result = constant
                                    self.bv.assert_const(lhs, val, width);
                                    did_assert = true;
                                } else if rhs_is_var && self.bv_terms.contains(&rhs) {
                                    // Assert operation result = variable
                                    self.bv.new_bv(rhs, width);
                                    self.bv.assert_eq(lhs, rhs);
                                    did_assert = true;
                                }
                            }
                        }
                        // Case 2: constant = BV operation
                        else if rhs_is_op {
                            if let Some(width) = get_bv_width(rhs) {
                                // Recursively encode the RHS operation and all its sub-terms
                                encode_bv_term_recursive(&mut self.bv, rhs, manager, &mut bv_encoded);

                                if let Some((val, _)) = lhs_const_info {
                                    // Assert operation result = constant
                                    self.bv.assert_const(rhs, val, width);
                                    did_assert = true;
                                } else if lhs_is_var && self.bv_terms.contains(&lhs) {
                                    // Assert variable = operation result
                                    self.bv.new_bv(lhs, width);
                                    self.bv.assert_eq(lhs, rhs);
                                    did_assert = true;
                                }
                            }
                        }
                        // Case 3: Simple variable = constant
                        else if lhs_is_var && self.bv_terms.contains(&lhs) {
                            if let Some((val, width)) = rhs_const_info {
                                self.bv.assert_const(lhs, val, width);
                                did_assert = true;
                            }
                        }
                        // Case 4: constant = simple variable
                        else if rhs_is_var && self.bv_terms.contains(&rhs) {
                            if let Some((val, width)) = lhs_const_info {
                                self.bv.assert_const(rhs, val, width);
                                did_assert = true;
                            }
                        }
                        // Case 5: Both simple variables
                        else if lhs_is_var
                            && rhs_is_var
                            && self.bv_terms.contains(&lhs)
                            && self.bv_terms.contains(&rhs)
                            && let Some(width) = get_bv_width(lhs)
                        {
                            self.bv.new_bv(lhs, width);
                            self.bv.new_bv(rhs, width);
                            self.bv.assert_eq(lhs, rhs);
                            did_assert = true;
                        }

                        // Run the BV SAT check whenever this equality was bit-blasted
                        // and asserted.  The embedded SAT solver is pushed/popped in
                        // lockstep with the outer CDCL decision levels (see
                        // `on_new_level` / `on_backtrack`), and `BvSolver::check`
                        // rolls its internal trail back to the committed (asserted)
                        // prefix after every probe, so no model-specific assignment
                        // from one `check()` survives to corrupt the next.  Any UNSAT
                        // it reports is therefore a genuine theory conflict.  The
                        // outer conflict analysis (`analyze_theory_conflict`) only
                        // forces a top-level UNSAT when ALL conflicting literals are
                        // fixed at decision level 0, so consulting `check()` here is
                        // sound in both directions: it can neither manufacture a false
                        // SAT (the previous bug was the MISSING check) nor a false
                        // UNSAT (the previous bug was the leaked-model trail).
                        if did_assert {
                            use oxiz_theories::Theory;
                            use oxiz_theories::TheoryCheckResult as TheoryCheckResultEnum;
                            // Record the constraint term so that check() can produce a
                            // non-empty conflict clause if the SAT sub-solver returns UNSAT.
                            let constraint_term = self.term_for_var(var);
                            self.bv.record_constraint_term(constraint_term);
                            let bv_check_result = self.bv.check();
                            if let Ok(TheoryCheckResultEnum::Unsat(conflict_terms)) =
                                bv_check_result
                            {
                                let conflict_lits = self.terms_to_conflict_clause(&conflict_terms);
                                return TheoryCheckResult::Conflict(conflict_lits);
                            }
                        }
                    }
                } else {
                    // Negative assignment: a != b, tell EUF about disequality.
                    // Use the constraint term as the reason (it has a SAT variable).
                    let constraint_term = self.term_for_var(var);
                    let lhs_node = self.intern_term_for_congruence(lhs, manager);
                    let rhs_node = self.intern_term_for_congruence(rhs, manager);
                    self.euf.assert_diseq(lhs_node, rhs_node, constraint_term);

                    // Check for immediate conflicts (if a = b was already derived)
                    if let Some(conflict_terms) = self.euf.check_conflicts() {
                        let conflict_lits = self.terms_to_conflict_clause(&conflict_terms);
                        return TheoryCheckResult::Conflict(conflict_lits);
                    }

                    // For bit-vector operands also send the disequality to the BV
                    // solver.  Mirrors the positive branch: fully bit-blast both
                    // operands, assert `a != b` at the bit level, then consult the
                    // embedded SAT solver.  This catches e.g. `not(= x x)` and
                    // `not(= (bvadd x y) (bvadd y x))`, which the EUF layer alone
                    // cannot refute (it has no bit-level arithmetic semantics).
                    if let Some(result) = self.bv_check_neq(lhs, rhs, constraint_term, manager) {
                        return result;
                    }
                }
            }
            Constraint::Diseq(lhs, rhs) => {
                if is_positive {
                    // Positive assignment: a != b.
                    // Use the constraint term as the reason for EUF disequality.
                    let constraint_term = self.term_for_var(var);
                    let lhs_node = self.intern_term_for_congruence(lhs, manager);
                    let rhs_node = self.intern_term_for_congruence(rhs, manager);
                    self.euf.assert_diseq(lhs_node, rhs_node, constraint_term);

                    if let Some(conflict_terms) = self.euf.check_conflicts() {
                        let conflict_lits = self.terms_to_conflict_clause(&conflict_terms);
                        return TheoryCheckResult::Conflict(conflict_lits);
                    }

                    // BV disequality (e.g. `(distinct x x)`): bit-blast and assert
                    // `a != b`, mirroring the negative-Eq branch.
                    if let Some(result) = self.bv_check_neq(lhs, rhs, constraint_term, manager) {
                        return result;
                    }
                } else {
                    // Negative assignment: ~(a != b) means a = b.
                    // Use the constraint term as the merge reason.
                    let constraint_term = self.term_for_var(var);
                    let lhs_node = self.intern_term_for_congruence(lhs, manager);
                    let rhs_node = self.intern_term_for_congruence(rhs, manager);
                    if let Err(_e) = self.euf.merge(lhs_node, rhs_node, constraint_term) {
                        return TheoryCheckResult::Sat;
                    }

                    if let Some(conflict_terms) = self.euf.check_conflicts() {
                        let conflict_lits = self.terms_to_conflict_clause(&conflict_terms);
                        return TheoryCheckResult::Conflict(conflict_lits);
                    }

                    // BV equality forced by `~(a != b)`: bit-blast and assert `a = b`.
                    if let Some(result) = self.bv_check_eq(lhs, rhs, constraint_term, manager) {
                        return result;
                    }
                }
            }
            // Arithmetic constraints - use parsed linear expressions
            Constraint::Lt(lhs, rhs)
            | Constraint::Le(lhs, rhs)
            | Constraint::Gt(lhs, rhs)
            | Constraint::Ge(lhs, rhs) => {
                // Intern both sides into EUF with congruence support so that
                // Apply/Select terms are registered for congruence closure.
                self.intern_term_for_congruence(lhs, manager);
                self.intern_term_for_congruence(rhs, manager);

                // Check if this is a BV comparison
                let lhs_is_bv = self.bv_terms.contains(&lhs);
                let rhs_is_bv = self.bv_terms.contains(&rhs);

                // Handle BV comparisons
                if lhs_is_bv || rhs_is_bv {
                    // Get BV width
                    let width = manager
                        .get(lhs)
                        .and_then(|t| manager.sorts.get(t.sort).and_then(|s| s.bitvec_width()));

                    if let Some(width) = width {
                        // Ensure both operands have BV variables in the embedded
                        // bit-blaster. A constant operand (e.g. `5` in `5 <u x`)
                        // must be pinned to its literal bit pattern via
                        // `assert_const` -- mirroring the `Constraint::Eq` BV
                        // handling above -- rather than handed FRESH,
                        // unconstrained bits by a bare `new_bv`. Without this,
                        // the bit-blasted comparison relates `x` to an
                        // independent free variable instead of the actual
                        // constant, so `BvSolver::get_value` (consulted first
                        // during model-building) can return ANY value at all
                        // for `x`, not one that actually satisfies the
                        // asserted bound (soundness of the check-sat verdict
                        // itself is unaffected, since the parallel ArithSolver
                        // bounded-integer path still decides the constraint
                        // correctly -- only the extracted model was wrong).
                        let get_bv_const = |term_id: TermId| -> Option<(u64, u32)> {
                            manager.get(term_id).and_then(|t| match &t.kind {
                                TermKind::BitVecConst { value, width } => {
                                    Some((value.iter_u64_digits().next().unwrap_or(0), *width))
                                }
                                _ => None,
                            })
                        };
                        match get_bv_const(lhs) {
                            Some((val, w)) => self.bv.assert_const(lhs, val, w),
                            None => {
                                self.bv.new_bv(lhs, width);
                            }
                        }
                        match get_bv_const(rhs) {
                            Some((val, w)) => self.bv.assert_const(rhs, val, w),
                            None => {
                                self.bv.new_bv(rhs, width);
                            }
                        }

                        // Derive signedness from the original TermKind stored for
                        // the SAT variable.  Both BvSlt and BvUlt encode to
                        // Constraint::Lt(lhs, rhs) during formula encoding (encode.rs),
                        // so the distinction is only recoverable by inspecting the term
                        // that the SAT variable was created for.
                        let constraint_term_id = self.term_for_var(var);
                        let is_signed = manager.get(constraint_term_id).is_some_and(|t| {
                            matches!(t.kind, TermKind::BvSlt(_, _) | TermKind::BvSle(_, _))
                        });

                        if is_positive {
                            // Positive assignment: constraint holds
                            match constraint {
                                Constraint::Lt(a, b) => {
                                    if is_signed {
                                        self.bv.assert_slt(a, b);
                                    } else {
                                        self.bv.assert_ult(a, b);
                                    }
                                }
                                Constraint::Le(a, b) if is_signed => {
                                    self.bv.assert_sle(a, b);
                                }
                                Constraint::Le(a, b) => {
                                    // Unsigned a <= b ≡ NOT(b <u a).
                                    self.bv.assert_ule(a, b);
                                }
                                _ => {}
                            }
                        } else {
                            // Negated assignment: the negation of the comparator
                            // holds.  By totality of BV orders the negation is the
                            // swapped non-strict / strict comparator:
                            //   ¬(a <u  b) ≡ b <=u a   ¬(a <=u b) ≡ b <u  a
                            //   ¬(a <s  b) ≡ b <=s a   ¬(a <=s b) ≡ b <s  a
                            match constraint {
                                Constraint::Lt(a, b) => {
                                    if is_signed {
                                        self.bv.assert_sle(b, a);
                                    } else {
                                        self.bv.assert_ule(b, a);
                                    }
                                }
                                Constraint::Le(a, b) => {
                                    if is_signed {
                                        self.bv.assert_slt(b, a);
                                    } else {
                                        self.bv.assert_ult(b, a);
                                    }
                                }
                                _ => {}
                            }
                        }

                        // Check BV solver for conflicts
                        use oxiz_theories::Theory;
                        use oxiz_theories::TheoryCheckResult as TheoryCheckResultEnum;
                        // Record the constraint term for non-empty conflict clause generation.
                        let constraint_term = self.term_for_var(var);
                        self.bv.record_constraint_term(constraint_term);
                        if let Ok(TheoryCheckResultEnum::Unsat(conflict_terms)) = self.bv.check() {
                            let conflict_lits = self.terms_to_conflict_clause(&conflict_terms);
                            return TheoryCheckResult::Conflict(conflict_lits);
                        }
                    }
                }

                // Look up the pre-parsed linear constraint for arithmetic
                // (fields copied out of the map entry so the immutable borrow ends
                // before `declare_arith_sorts` takes `&mut self` — #427)
                let parsed_arith = self.var_to_parsed_arith.get(&var).map(|p| {
                    (
                        p.terms.iter().copied().collect::<Vec<(TermId, ArithRat)>>(),
                        p.reason_term,
                        p.constant,
                        p.constraint_type,
                    )
                });
                if let Some((terms, reason, constant, constraint_type)) = parsed_arith {
                    // Add constraint to ArithSolver
                    self.declare_arith_sorts(&terms); // #427

                    if is_positive {
                        // Positive assignment: constraint holds
                        match constraint_type {
                            ArithConstraintType::Lt => {
                                // lhs - rhs < 0, i.e., sum of terms < constant
                                self.arith.assert_lt(&terms, constant, reason);
                            }
                            ArithConstraintType::Le => {
                                // lhs - rhs <= 0
                                self.arith.assert_le(&terms, constant, reason);
                            }
                            ArithConstraintType::Gt => {
                                // lhs - rhs > 0, i.e., sum of terms > constant
                                self.arith.assert_gt(&terms, constant, reason);
                            }
                            ArithConstraintType::Ge => {
                                // lhs - rhs >= 0
                                self.arith.assert_ge(&terms, constant, reason);
                            }
                        }
                    } else {
                        // Negative assignment: negation of constraint holds
                        // ~(a < b) => a >= b
                        // ~(a <= b) => a > b
                        // ~(a > b) => a <= b
                        // ~(a >= b) => a < b
                        match constraint_type {
                            ArithConstraintType::Lt => {
                                // ~(lhs < rhs) => lhs >= rhs
                                self.arith.assert_ge(&terms, constant, reason);
                            }
                            ArithConstraintType::Le => {
                                // ~(lhs <= rhs) => lhs > rhs
                                self.arith.assert_gt(&terms, constant, reason);
                            }
                            ArithConstraintType::Gt => {
                                // ~(lhs > rhs) => lhs <= rhs
                                self.arith.assert_le(&terms, constant, reason);
                            }
                            ArithConstraintType::Ge => {
                                // ~(lhs >= rhs) => lhs < rhs
                                self.arith.assert_lt(&terms, constant, reason);
                            }
                        }
                    }

                    // Check ArithSolver for conflicts
                    use oxiz_theories::Theory;
                    use oxiz_theories::TheoryCheckResult as TheoryCheckResultEnum;
                    let arith_result = self.arith.check();
                    match arith_result {
                        Ok(TheoryCheckResultEnum::Unsat(conflict_terms)) => {
                            // Suppress a stale-bound pseudo-conflict (an atom left
                            // in the simplex under both polarities by a SAT
                            // backtrack the theory frame did not retract) — it is
                            // satisfiable and reporting it yields spurious UNSAT.
                            if !self.suppress_stale_bounds
                                || !self.arith.last_conflict_is_stale_bound()
                            {
                                let conflict_lits =
                                    self.terms_to_conflict_clause(&conflict_terms);
                                return TheoryCheckResult::Conflict(conflict_lits);
                            }
                        }
                        Ok(TheoryCheckResultEnum::Sat) => {}
                        other => {
                            let _ = other;
                        }
                    }
                }
            }
            Constraint::BoolApp(app_term) => {
                // Bool-valued function application (e.g., `t(m)`).
                // Intern the application in EUF so that congruence closure
                // can fire.  Then merge its EUF node with the canonical
                // true or false node depending on the SAT assignment.
                let app_node = self.intern_term_for_congruence(app_term, manager);
                let (true_node, false_node) = self.ensure_bool_nodes();
                let merge_target = if is_positive { true_node } else { false_node };
                let constraint_term = self.term_for_var(var);
                if let Err(_e) = self.euf.merge(app_node, merge_target, constraint_term) {
                    // Merge error (should not happen in normal operation)
                    return TheoryCheckResult::Sat;
                }

                // Check for immediate conflicts
                if let Some(conflict_terms) = self.euf.check_conflicts() {
                    let conflict_lits = self.terms_to_conflict_clause(&conflict_terms);
                    return TheoryCheckResult::Conflict(conflict_lits);
                }
            }
            Constraint::BoolValue { term, negated } => {
                // #433: a Bool-sorted UF ARGUMENT's truth value, exactly the
                // `BoolApp` completion but with the polarity of the watched
                // literal folded in (see the variant docs).
                let node = self.intern_term_for_congruence(term, manager);
                let (true_node, false_node) = self.ensure_bool_nodes();
                let value = is_positive != negated;
                let merge_target = if value { true_node } else { false_node };
                let constraint_term = self.term_for_var(var);
                if let Err(_e) = self.euf.merge(node, merge_target, constraint_term) {
                    return TheoryCheckResult::Sat;
                }
                if let Some(conflict_terms) = self.euf.check_conflicts() {
                    let conflict_lits = self.terms_to_conflict_clause(&conflict_terms);
                    return TheoryCheckResult::Conflict(conflict_lits);
                }
            }
        }
        TheoryCheckResult::Sat
    }
}

impl TheoryCallback for TheoryManager {
    fn on_assignment(&mut self, lit: Lit) -> TheoryCheckResult {
        let var = lit.var();
        let is_positive = !lit.is_neg();

        // Remember the phase so conflict-clause generation can negate each
        // literal in the direction that falsifies it (see `assigned_phase`).
        self.assigned_phase.insert(var, is_positive);

        // Track propagation
        self.statistics.propagations += 1;

        // In lazy mode, just collect assignments for batch processing
        if self.theory_mode == TheoryMode::Lazy {
            // Check if this variable has a theory constraint
            if self.var_to_constraint.contains_key(&var) {
                self.pending_assignments.push((lit, is_positive));
            }
            return TheoryCheckResult::Sat;
        }

        // Eager mode: process immediately
        // Check if this variable has a theory constraint
        let Some(constraint) = self.var_to_constraint.get(&var).cloned() else {
            return TheoryCheckResult::Sat;
        };

        self.processed_count += 1;
        self.statistics.theory_propagations += 1;

        // Transient handle to the term manager, independent of the `&mut self`
        // borrow `process_constraint` takes (dropped at the end of this call).
        let mgr = Arc::clone(&self.manager);
        let result = self.process_constraint(var, constraint, is_positive, &mgr);

        // Track theory conflicts
        if matches!(result, TheoryCheckResult::Conflict(_)) {
            self.statistics.theory_conflicts += 1;
            self.statistics.conflicts += 1;

            // Check conflict limit
            if self.max_conflicts > 0 && self.statistics.conflicts >= self.max_conflicts {
                return TheoryCheckResult::Sat; // Return Sat to signal resource exhaustion
            }
        }

        result
    }

    fn final_check(&mut self) -> TheoryCheckResult {
        // In lazy mode, process all pending assignments now
        if self.theory_mode == TheoryMode::Lazy {
            for &(lit, is_positive) in &self.pending_assignments.clone() {
                let var = lit.var();
                let Some(constraint) = self.var_to_constraint.get(&var).cloned() else {
                    continue;
                };

                self.statistics.theory_propagations += 1;

                // Process the constraint (same logic as eager mode).
                // Transient handle, independent of the `&mut self` borrow.
                let mgr = Arc::clone(&self.manager);
                let result = self.process_constraint(var, constraint, is_positive, &mgr);
                if let TheoryCheckResult::Conflict(conflict) = result {
                    self.statistics.theory_conflicts += 1;
                    self.statistics.conflicts += 1;

                    // Check conflict limit
                    if self.max_conflicts > 0 && self.statistics.conflicts >= self.max_conflicts {
                        return TheoryCheckResult::Sat; // Signal resource exhaustion
                    }

                    return TheoryCheckResult::Conflict(conflict);
                }
            }
            // Clear pending assignments after processing
            self.pending_assignments.clear();
        }

        self.theory_consistency_check()
    }

    fn on_new_level(&mut self, level: u32) {
        // Push theory state when a new decision level is created
        // Ensure we have enough levels in the stack
        while self.level_stack.len() < (level as usize + 1) {
            self.level_stack.push(self.processed_count);
            self.euf.push();
            self.arith.push();
            self.bv.push();
        }
    }

    fn on_backtrack(&mut self, level: u32) {
        // Pop EUF, Arith, and BV states if needed
        while self.level_stack.len() > (level as usize + 1) {
            self.level_stack.pop();
            self.euf.pop();
            self.arith.pop();
            self.bv.pop();
        }
        self.processed_count = *self.level_stack.last().unwrap_or(&0);

        // Evict stale integer-constant canonicals whose EUF nodes were removed
        // by the preceding pop().  After truncation, any node index >=
        // euf.node_count() is invalid; keeping such entries would cause an
        // out-of-bounds access in `intern_term_deep` when `merge` is called
        // against the stale canonical.  Evicting them forces re-registration
        // (and fresh disequality assertions) the next time those values appear.
        let live_nodes = self.euf.node_count();
        self.interned_int_constants
            .retain(|_val, &mut canonical| (canonical as usize) < live_nodes);

        // Evict stale bit-vector-constant canonicals for the same reason.
        self.interned_bv_constants
            .retain(|_key, &mut canonical| (canonical as usize) < live_nodes);

        // Evict stale Boolean canonical nodes
        if let Some(t) = self.bool_true_node {
            if (t as usize) >= live_nodes {
                self.bool_true_node = None;
            }
        }
        if let Some(f) = self.bool_false_node {
            if (f as usize) >= live_nodes {
                self.bool_false_node = None;
            }
        }

        // Clear pending assignments on backtrack (in lazy mode)
        if self.theory_mode == TheoryMode::Lazy {
            self.pending_assignments.clear();
        }
    }
}

/// Build the driver-facing `TheoryReason` from the legacy `(propagated_lit,
/// reason_clause_lits)` shape `process_constraint` returns. `reason_clause_lits`
/// are the TRUE justifying literals that `add_theory_reason_clause` consumes
/// directly; the `solve_with_hooks` driver reconstructs them by NEGATING
/// `reason.explanation`, so store their negations (round-trips exactly).
fn theory_reason_from_clause(asserting: Lit, reason_lits: &[Lit]) -> TheoryReason {
    let explanation: SmallVec<[Lit; 8]> = reason_lits.iter().map(|l| l.negate()).collect();
    TheoryReason {
        asserting,
        explanation,
    }
}

impl TheoryManager {
    /// Pop the next theory propagation still worth emitting — one whose
    /// literal's variable is currently UNASSIGNED. Mirrors the legacy
    /// `if !self.trail.is_assigned(lit.var())` guard: an already-assigned
    /// propagation is either satisfied or a contradiction the consistency
    /// battery will catch, so it is dropped rather than emitted (emitting a
    /// satisfied literal would make the driver treat it as a fixpoint and stop
    /// draining the buffer). `assigned_phase` holds exactly the currently
    /// assigned vars (maintained by `assign_hook`/`unassign_hook`), so it is the
    /// trail's `is_assigned` shadow.
    fn next_emittable_propagation(&mut self) -> Option<(Lit, SmallVec<[Lit; 8]>)> {
        while let Some(entry) = self.pending_theory_propagations.pop() {
            if !self.assigned_phase.contains_key(&entry.0.var()) {
                return Some(entry);
            }
        }
        None
    }

    /// Drain the assignment queue through `process_constraint`: assert each
    /// newly-trail'd atom into euf/arith/bv (the cheap incremental work),
    /// return `Some(explanation)` on the FIRST direct conflict, and buffer any
    /// theory propagations for later emission. `None` ⇒ drained with no direct
    /// conflict. Shared by the hooks `final_check` / `final_check_complete`.
    fn drain_queue(&mut self) -> Option<SmallVec<[Lit; 8]>> {
        let pending = core::mem::take(&mut self.pending_assignments);
        for (lit, is_positive) in pending {
            let var = lit.var();
            let Some(constraint) = self.var_to_constraint.get(&var).cloned() else {
                continue;
            };
            self.statistics.theory_propagations += 1;
            // Transient handle, independent of the `&mut self` borrow.
            let mgr = Arc::clone(&self.manager);
            match self.process_constraint(var, constraint, is_positive, &mgr) {
                TheoryCheckResult::Sat => {}
                TheoryCheckResult::Conflict(explanation) => {
                    self.statistics.theory_conflicts += 1;
                    self.statistics.conflicts += 1;
                    // A conflict invalidates anything buffered this fixpoint.
                    self.pending_theory_propagations.clear();
                    return Some(explanation);
                }
                TheoryCheckResult::Propagated(props) => {
                    self.pending_theory_propagations.extend(props);
                }
            }
        }
        None
    }

    /// The euf → euf-to-arith → arith → model-based-combination consistency
    /// battery. Shared by the legacy `TheoryCallback::final_check` (run after its
    /// lazy queue drain) and the §4 `TheoryHooks::final_check` (run after its
    /// eager, propagation-capturing drain). Self-contained — it never touches
    /// `pending_assignments`, so either drain discipline may precede it.
    fn theory_consistency_check(&mut self) -> TheoryCheckResult {
        // Fresh battery: assume this check CONFIRMS its verdict until an
        // `Unknown`/`Err` fallback below proves otherwise. Reset-at-top means the
        // flag reflects ONLY this (the authorising) battery, never a stale
        // partial-assignment `Unknown` the search has since moved past.
        self.last_check_unconfirmed = false;

        // Check EUF for conflicts
        if let Some(conflict_terms) = self.euf.check_conflicts() {
            // Convert TermIds to Lits for the conflict clause
            let conflict_lits = self.terms_to_conflict_clause(&conflict_terms);
            self.statistics.theory_conflicts += 1;
            self.statistics.conflicts += 1;

            // Check conflict limit
            if self.max_conflicts > 0 && self.statistics.conflicts >= self.max_conflicts {
                return TheoryCheckResult::Sat; // Signal resource exhaustion
            }

            return TheoryCheckResult::Conflict(conflict_lits);
        }

        // Propagate EUF-derived equalities into the arithmetic solver.
        // When EUF fires congruence closure and derives f(x) = f(y) because
        // x = y was asserted, the arithmetic solver is unaware of this equality.
        // We must propagate it so the arithmetic solver can detect contradictions.
        let eq_result = self.propagate_euf_equalities_to_arith();
        if let TheoryCheckResult::Conflict(_) = eq_result {
            self.statistics.theory_conflicts += 1;
            self.statistics.conflicts += 1;
            return eq_result;
        }

        // Check arithmetic
        match self.arith.check() {
            Ok(result) => {
                match result {
                    oxiz_theories::TheoryCheckResult::Sat => {
                        // Arithmetic is consistent, now check model-based theory combination
                        // This ensures that different theories agree on shared terms
                        self.model_based_combination()
                    }
                    oxiz_theories::TheoryCheckResult::Unsat(conflict_terms) => {
                        // Suppress a stale-bound pseudo-conflict (an atom left in
                        // the simplex under both polarities by a SAT backtrack the
                        // theory frame did not retract) — it is satisfiable, so
                        // reporting it would be a spurious UNSAT.  Fall through to
                        // the model-based combination check instead.
                        if self.suppress_stale_bounds && self.arith.last_conflict_is_stale_bound() {
                            return self.model_based_combination();
                        }

                        // Arithmetic conflict detected - convert to SAT conflict clause
                        let conflict_lits = self.terms_to_conflict_clause(&conflict_terms);
                        self.statistics.theory_conflicts += 1;
                        self.statistics.conflicts += 1;

                        // Check conflict limit
                        if self.max_conflicts > 0 && self.statistics.conflicts >= self.max_conflicts
                        {
                            return TheoryCheckResult::Sat; // Signal resource exhaustion
                        }

                        TheoryCheckResult::Conflict(conflict_lits)
                    }
                    oxiz_theories::TheoryCheckResult::Propagate(_) => {
                        // Propagations should be handled in on_assignment
                        self.model_based_combination()
                    }
                    oxiz_theories::TheoryCheckResult::Unknown => {
                        // Theory is incomplete: it could NOT confirm this
                        // assignment is theory-consistent. The SAT-facing result
                        // has no `Unknown`, so we still return `Sat` ("no
                        // conflict, keep searching / accept"), but mark the verdict
                        // UNCONFIRMED so a final `Sat` is soundly downgraded to
                        // `Unknown` rather than emitted as a spurious model (e.g. a
                        // LIA system with no integer solution: the LP relaxation is
                        // feasible, branch-and-bound proves no integer point, arith
                        // returns `Unknown` — reporting `sat` here would contradict
                        // z3's `unsat`).
                        self.last_check_unconfirmed = true;
                        TheoryCheckResult::Sat
                    }
                }
            }
            Err(_error) => {
                // Internal error in the arithmetic solver: likewise unconfirmed —
                // do not pass it off as a theory-CONFIRMED `Sat`.
                self.last_check_unconfirmed = true;
                TheoryCheckResult::Sat
            }
        }
    }

    /// Soundness gate accessor: `true` iff the most recent
    /// [`theory_consistency_check`](Self::theory_consistency_check) authorised its
    /// `Sat` only via an `Unknown`/`Err` fallback (an incomplete theory that could
    /// not positively confirm the assignment). `Solver::solve` reads this after a
    /// `Sat` verdict and downgrades it to `Unknown`. See `last_check_unconfirmed`.
    pub(crate) fn last_check_unconfirmed(&self) -> bool {
        self.last_check_unconfirmed
    }
}

/// §4.2 redesign: drive the SAME real theory state through the lock-step
/// `TheoryHooks` contract (the new `solve_with_hooks` driver) instead of the
/// advisory `TheoryCallback`. This is opt-in behind `SolverConfig::use_hooks_driver`
/// (default OFF) until validated; the legacy `impl TheoryCallback` above is the
/// production path and stays untouched.
///
/// The mapping (4 callbacks → 6 hooks):
///   * `on_new_level`  → `push_frame`   — one euf/arith/bv frame per level (the
///     trail fires it once per single level-up, so no catch-up loop).
///   * `on_backtrack`  → `pop_frame`    — pop one frame + the stale-canonical
///     eviction; per-literal retraction is `unassign_hook` (fired by the trail).
///   * `on_assignment` → `assign_hook`  — record phase + QUEUE the atom. The driver
///     discards `assign_hook`'s return, so all checking flows through `final_check`.
///   * `final_check`   → `final_check`  — Phase 2b EAGER check: drain the queue
///     through `process_constraint`, surfacing a conflict immediately and EMITTING
///     theory propagations (one per poll) so the SAT search is pruned exactly as in
///     the legacy eager path; then the shared euf/arith/Nelson-Oppen
///     `theory_consistency_check` battery. Returns `Conflict`/`Propagate`/`Ok`.
impl TheoryHooks for TheoryManager {
    fn assign_hook(&mut self, lit: Lit, _level: u32) -> TheoryStep {
        let var = lit.var();
        let is_positive = !lit.is_neg();
        // Phase for conflict-clause polarity (see `assigned_phase`).
        self.assigned_phase.insert(var, is_positive);
        self.statistics.propagations += 1;
        // Final-check-driven: queue theory-bearing atoms; the work happens in
        // `final_check` (the driver acts on its return, not this one).
        if self.var_to_constraint.contains_key(&var) {
            self.pending_assignments.push((lit, is_positive));
        }
        TheoryStep::Ok
    }

    fn unassign_hook(&mut self, lit: Lit, _level: u32) {
        let var = lit.var();
        // Drop the literal's phase + any not-yet-drained queue entry the instant it
        // leaves the trail (its euf/arith effects are undone by the matching
        // `pop_frame`). A stale phase/queue entry for a retracted var is now
        // unrepresentable — the §4 "make the desync unrepresentable" property.
        self.assigned_phase.remove(&var);
        if let Some(pos) = self
            .pending_assignments
            .iter()
            .rposition(|&(l, _)| l == lit)
        {
            self.pending_assignments.remove(pos);
        }
    }

    fn push_frame(&mut self, _level: u32) {
        // §4.1 lock-step: exactly one theory frame per decision level, pushed
        // atomically with the level-up.
        self.euf.push();
        self.arith.push();
        self.bv.push();
    }

    fn pop_frame(&mut self, _level: u32) {
        // §4.1 lock-step: pop exactly one frame, atomically with the level-down.
        self.euf.pop();
        self.arith.pop();
        self.bv.pop();
        // Any propagation buffered for emission referred to the assignment we are
        // now unwinding — drop it so a stale theory propagation never survives a
        // backtrack (the driver re-derives fresh ones at the next fixpoint).
        self.pending_theory_propagations.clear();
        // Evict canonical EUF nodes the pop invalidated (identical to the legacy
        // `on_backtrack` eviction — keeps `intern_term_deep` from indexing a
        // truncated node vector; see the field docs on `interned_int_constants`).
        let live_nodes = self.euf.node_count();
        self.interned_int_constants
            .retain(|_val, &mut canonical| (canonical as usize) < live_nodes);
        self.interned_bv_constants
            .retain(|_key, &mut canonical| (canonical as usize) < live_nodes);
        if let Some(t) = self.bool_true_node {
            if (t as usize) >= live_nodes {
                self.bool_true_node = None;
            }
        }
        if let Some(f) = self.bool_false_node {
            if (f as usize) >= live_nodes {
                self.bool_false_node = None;
            }
        }
    }

    fn final_check(&mut self) -> TheoryStep {
        // Phase 2b — CHEAP per-fixpoint check (fired after every Boolean
        // fixpoint). Drain each newly-trail'd atom's constraint through
        // `process_constraint` — the incremental assert + direct-conflict detect
        // — and emit theory propagations one-per-poll. The EXPENSIVE global
        // consistency battery is DEFERRED to `final_check_complete` (full
        // assignment); running it here, at every fixpoint, was ~100× slower with
        // no verdict difference (the legacy eager path defers it the same way).

        // Emit a propagation buffered from an earlier poll this fixpoint.
        if let Some((lit, reason_lits)) = self.next_emittable_propagation() {
            return TheoryStep::Propagate {
                lit,
                reason: theory_reason_from_clause(lit, &reason_lits),
            };
        }
        // Drain the queue (a direct conflict returns immediately; propagations
        // are buffered for emission).
        if let Some(explanation) = self.drain_queue() {
            // `terms_to_conflict_clause` already emits the all-false set.
            return TheoryStep::Conflict { explanation };
        }
        // Emit a propagation produced by the drain just now.
        if let Some((lit, reason_lits)) = self.next_emittable_propagation() {
            return TheoryStep::Propagate {
                lit,
                reason: theory_reason_from_clause(lit, &reason_lits),
            };
        }
        TheoryStep::Ok
    }

    fn final_check_complete(&mut self) -> TheoryStep {
        // Full assignment: drain any residual queue for a direct conflict
        // (propagations are pointless — every literal is decided), then run the
        // EXPENSIVE euf → euf-to-arith → arith → model-based-combination battery
        // ONCE. Only a clean battery authorises the `Sat` verdict (this is the
        // global consistency check the legacy path also defers to here).
        if let Some(explanation) = self.drain_queue() {
            return TheoryStep::Conflict { explanation };
        }
        match self.theory_consistency_check() {
            TheoryCheckResult::Sat => TheoryStep::Ok,
            TheoryCheckResult::Conflict(explanation) => TheoryStep::Conflict { explanation },
            // The battery emits no propagations; sound to treat as a fixpoint.
            TheoryCheckResult::Propagated(_) => TheoryStep::Ok,
        }
    }

    fn eval(&mut self, _atom: Var) -> Option<bool> {
        // The SMT model is built separately (`Solver::build_model`); the hooks driver
        // needs no theory-evaluation oracle, so stay conservative.
        None
    }
}

/// Result from parallel theory checking
#[cfg(feature = "parallel-theories")]
#[allow(dead_code)]
#[derive(Debug, Clone)]
pub enum ParallelTheoryResult {
    /// All theories report SAT
    AllSat,
    /// At least one theory found a conflict
    Conflict(SmallVec<[Lit; 8]>),
}

/// Parallel theory checking support.
#[cfg(feature = "parallel-theories")]
#[allow(dead_code)]
pub struct ParallelTheoryChecker;

#[cfg(feature = "parallel-theories")]
impl ParallelTheoryChecker {
    /// Check multiple independent theory assertions in parallel.
    #[allow(dead_code)]
    pub fn check_parallel(
        assertions: &[(Var, Constraint, bool)],
        _term_to_var: &FxHashMap<TermId, Var>,
    ) -> ParallelTheoryResult {
        use rayon::prelude::*;

        let mut euf_assertions = Vec::new();
        let mut arith_assertions = Vec::new();
        let bv_assertions = Vec::new();

        for (var, constraint, is_positive) in assertions {
            match constraint {
                Constraint::Eq(_, _) | Constraint::Diseq(_, _) => {
                    euf_assertions.push((*var, constraint.clone(), *is_positive));
                }
                Constraint::Le(_, _)
                | Constraint::Lt(_, _)
                | Constraint::Ge(_, _)
                | Constraint::Gt(_, _) => {
                    arith_assertions.push((*var, constraint.clone(), *is_positive));
                }
                Constraint::BoolApp(_) | Constraint::BoolValue { .. } => {
                    euf_assertions.push((*var, constraint.clone(), *is_positive));
                }
            }
        }

        let results: Vec<Option<SmallVec<[Lit; 8]>>> =
            [&euf_assertions, &arith_assertions, &bv_assertions]
                .par_iter()
                .map(|domain| Self::check_domain_contradictions(domain))
                .collect();

        if let Some(conflict) = results.into_iter().flatten().next() {
            return ParallelTheoryResult::Conflict(conflict);
        }

        ParallelTheoryResult::AllSat
    }

    #[allow(dead_code)]
    fn check_domain_contradictions(
        assertions: &[(Var, Constraint, bool)],
    ) -> Option<SmallVec<[Lit; 8]>> {
        for i in 0..assertions.len() {
            for j in (i + 1)..assertions.len() {
                let (var_i, constraint_i, pos_i) = &assertions[i];
                let (var_j, constraint_j, pos_j) = &assertions[j];
                if Self::are_contradictory(constraint_i, *pos_i, constraint_j, *pos_j) {
                    let mut conflict = SmallVec::new();
                    conflict.push(Lit::neg(*var_i));
                    conflict.push(Lit::neg(*var_j));
                    return Some(conflict);
                }
            }
        }
        None
    }

    #[allow(dead_code)]
    fn are_contradictory(c1: &Constraint, pos1: bool, c2: &Constraint, pos2: bool) -> bool {
        match (c1, c2) {
            (Constraint::Eq(a1, b1), Constraint::Eq(a2, b2)) => {
                a1 == a2 && b1 == b2 && pos1 != pos2
            }
            (Constraint::Eq(a1, b1), Constraint::Diseq(a2, b2))
            | (Constraint::Diseq(a2, b2), Constraint::Eq(a1, b1)) => {
                a1 == a2 && b1 == b2 && pos1 && pos2
            }
            _ => false,
        }
    }
}
