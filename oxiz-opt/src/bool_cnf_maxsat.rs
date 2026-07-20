//! Pure-propositional Tseitin-CNF fast path for [`crate::context::OptContext`]'s
//! `optimize_maxsmt` (weighted partial MaxSAT over `assert-soft`).
//!
//! ## Why this exists
//!
//! `optimize_maxsmt`'s original (and still-present, see its own doc)
//! algorithm builds a selector-variable + integer-cost-sum encoding and
//! binary-searches it through `oxiz_solver::Solver` (a full DPLL(T) SMT
//! solver with Bool/LIA theory integration). A z3/cvc5 differential run
//! during the `fill-the-gap/maxsat` fixup pass found that encoding
//! triggers a **false-UNSAT** bug in `oxiz_solver`'s Bool/LIA integration
//! on exactly the shape it builds (confirmed by hand-encoding the same
//! selector-implication + cost-sum formula directly and feeding it to the
//! plain `oxiz` CLI, bypassing every line of MaxSAT-specific code) — a
//! soundness-adjacent completeness gap: the reported cost can be
//! provably too high (a strictly cheaper feasible assignment exists but
//! is missed because the solver claims a budget is infeasible when it
//! isn't).
//!
//! The overwhelmingly common `assert-soft` shape — Boolean variables,
//! clausal/Boolean-structure hard constraints, a literal or small Boolean
//! formula per soft constraint — never needs LIA at all. This module
//! Tseitin-encodes that PURELY Boolean fragment into CNF and solves it
//! with a binary search entirely over the raw `oxiz_sat` CDCL core (no
//! theory integration whatsoever), sidestepping the buggy code path
//! entirely rather than trying to fix the underlying DPLL(T) integration
//! bug (well out of this fixup pass's file scope — see the finding's own
//! `suggested_fix`, which names an alternative algorithm as the
//! explicitly sanctioned option).
//!
//! ## A first attempt that did NOT work: `PmresSolver`
//!
//! The obvious choice for "an alternative algorithm" was
//! [`crate::pmres::PmresSolver`] — flagged by the environment brief as
//! already "fixed and differential-tested". An initial version of this
//! module Tseitin-encoded into `PmresSolver` directly. **That regressed
//! the differential from ~89% to ~77% exact-match**, and a minimal
//! isolated repro (two Boolean vars, one 2-literal NAND hard clause, two
//! single-literal soft constraints with DIFFERENT weights, zero
//! transplant/Tseitin/wiring code involved) confirmed why:
//! `PmresSolver::solve_level`'s core-handling treats every member of a
//! 2+-literal unsat core as EQUALLY relaxable and lets the underlying SAT
//! solver's own (weight-oblivious) decision/propagation order pick which
//! one gets permanently relaxed — real weighted core-guided MaxSAT
//! (PMRES/OLL) needs to split a mixed-weight core by its MINIMUM member
//! weight and only relax that slice, which this implementation of
//! `PmresSolver` does not do. That is a genuine, separate, pre-existing
//! correctness bug in `PmresSolver`, reported alongside this fix rather
//! than silently routed around.
//!
//! ## What this module actually does instead
//!
//! A binary search over an integer cost budget `K`, exactly mirroring
//! `optimize_maxsmt`'s own (LIA-based) structure, but built entirely out
//! of a well-established, ALREADY-USED-ELSEWHERE-IN-THIS-CRATE cardinality
//! encoding ([`crate::totalizer::encode_at_most_k`], the same one
//! `rc2.rs`'s core-guided relaxation already trusts) instead of either
//! LIA arithmetic or a core-guided heuristic:
//!
//! 1. Tseitin-encode every hard constraint and soft-constraint term to a
//!    CNF literal.
//! 2. Build a "cost multiset": soft constraint `i`'s violated-literal
//!    (`¬l_i`), replicated `w_i` times (unary weight replication — exact,
//!    not truncated, for any non-negative integer weight; rational
//!    weights are scaled to a common integer unit first, see
//!    `scaled_weight`).
//! 3. Binary-search the minimum `K` for which "hard clauses AND at most
//!    `K` of the cost multiset are true" is SAT, using a FRESH
//!    `oxiz_sat::Solver` (the plain CDCL core) per candidate `K` — the
//!    exact same "binary search + exact SAT calls" shape the original
//!    LIA path already used, just without any arithmetic theory in the
//!    loop at all. Binary search + an exact (not heuristic) SAT oracle at
//!    each step is provably optimal, unlike core-guided relaxation's
//!    weight-blind tie-breaking.
//!
//! ## Scope
//!
//! [`try_optimize_maxsmt_boolean`] returns `None` — meaning "not
//! applicable, fall back to the general encoding" — the moment ANY hard
//! constraint or soft-constraint term (or a reachable subterm) is not
//! `Bool`-sorted, or uses a `TermKind` outside `True`/`False`/`Var`/`Not`/
//! `And`/`Or`/`Implies`/`Xor`/`Eq` (Bool operands)/`Distinct` (exactly 2
//! Bool operands)/`Ite` (Bool branches). It never guesses, never drops a
//! constraint, and never reports a wrong answer silently — a formula
//! outside this fragment (e.g. one that mixes in an LIA hard constraint)
//! simply takes the pre-existing (unchanged) fallback path.
//!
//! Also bails (returns `None`) if a single term's Tseitin encoding would
//! recurse past a conservative depth — this is a NEW recursive walk, and
//! the fill-the-gap/maxsat pass separately found that unbounded recursion
//! over a linearly-nested term can stack-overflow the process around
//! depth ~8000-9000 on the default stack (see `transplant`'s iterative
//! rewrite for the same class of bug); bailing well below that keeps this
//! module from reintroducing it, at the cost of falling back (not
//! crashing) on a pathologically deep single objective/soft term — a
//! shape `assert-soft` scripts essentially never produce in practice
//! (soft constraints are almost always shallow literals or small clauses).

use crate::context::{ModelValue, SoftConstraint, lcm_bigint, scaled_weight};
use crate::maxsat::{MaxSatResult, Weight};
use crate::totalizer::{CardinalityEncoding, encode_at_most_k};
use num_bigint::BigInt;
use num_traits::ToPrimitive;
use oxiz_core::ast::{TermId, TermKind, TermManager};
use oxiz_sat::{LBool, Lit, Solver as SatSolver, SolverResult, Var};
use rustc_hash::FxHashMap;
use smallvec::{SmallVec, smallvec};

/// Conservative recursion depth ceiling for `CnfBuilder::encode` — see the
/// module doc's "Scope" section. Comfortably below the ~8000-9000 depth
/// where a similar plain-recursive walk was found to overflow the default
/// thread stack.
const MAX_ENCODE_DEPTH: u32 = 3000;

/// Safety cap on the total (scaled) weight this fast path will encode as a
/// literal-replicated cost multiset (see `try_optimize_maxsmt_boolean`).
/// Comfortably above any realistic `assert-soft` script — weights are
/// small integers in every observed corpus/differential shape — while
/// still bailing (falling back to the general path, not exhausting memory
/// or hanging) on a pathologically large single weight.
const MAX_TOTAL_SCALED_WEIGHT: usize = 200_000;

/// Outcome of a successful (`Some`) Boolean-CNF fast-path attempt.
pub(crate) struct BoolFastPathOutcome {
    pub result: MaxSatResult,
    pub model: Option<FxHashMap<TermId, ModelValue>>,
}

/// Tseitin CNF builder over a single [`TermManager`], memoized per call so
/// DAG-shared subterms are encoded once (same rationale as
/// `oxiz_core::ast::transplant_term`'s own memoization).
struct CnfBuilder<'a> {
    tm: &'a TermManager,
    next_var: u32,
    /// `Var`-sort atoms (bare declared Bool symbols) seen so far, so the
    /// SAT model can be mapped back to the original `TermId`s afterwards.
    atom_vars: FxHashMap<TermId, Var>,
    cache: FxHashMap<TermId, Lit>,
    clauses: Vec<SmallVec<[Lit; 4]>>,
    true_lit: Option<Lit>,
}

impl<'a> CnfBuilder<'a> {
    fn new(tm: &'a TermManager) -> Self {
        Self {
            tm,
            next_var: 0,
            atom_vars: FxHashMap::default(),
            cache: FxHashMap::default(),
            clauses: Vec::new(),
            true_lit: None,
        }
    }

    fn fresh_var(&mut self) -> Var {
        let v = Var::new(self.next_var);
        self.next_var += 1;
        v
    }

    /// A literal pinned TRUE by a unit clause, minted once and cached.
    fn true_lit(&mut self) -> Lit {
        if let Some(l) = self.true_lit {
            return l;
        }
        let v = self.fresh_var();
        let l = Lit::pos(v);
        self.clauses.push(smallvec![l]);
        self.true_lit = Some(l);
        l
    }

    /// Tseitin-encode `y <-> OR(lits)`, minting a fresh auxiliary variable
    /// `y` and returning `Lit::pos(y)` — except for the trivial 0-/1-ary
    /// cases, which need no auxiliary variable at all.
    fn or_of(&mut self, lits: &[Lit]) -> Lit {
        match lits {
            [] => {
                let t = self.true_lit();
                t.negate()
            }
            [only] => *only,
            _ => {
                let y = self.fresh_var();
                let yl = Lit::pos(y);
                let mut big: SmallVec<[Lit; 4]> = SmallVec::new();
                big.push(yl.negate());
                big.extend_from_slice(lits);
                self.clauses.push(big);
                for &l in lits {
                    self.clauses.push(smallvec![l.negate(), yl]);
                }
                yl
            }
        }
    }

    /// Tseitin-encode `y <-> AND(lits)`. Mirrors `or_of`.
    fn and_of(&mut self, lits: &[Lit]) -> Lit {
        match lits {
            [] => self.true_lit(),
            [only] => *only,
            _ => {
                let y = self.fresh_var();
                let yl = Lit::pos(y);
                for &l in lits {
                    self.clauses.push(smallvec![yl.negate(), l]);
                }
                let mut big: SmallVec<[Lit; 4]> = SmallVec::new();
                big.push(yl);
                for &l in lits {
                    big.push(l.negate());
                }
                self.clauses.push(big);
                yl
            }
        }
    }

    /// Tseitin-encode `y <-> (a <-> b)`, built out of `or_of`/`and_of` (an
    /// Iff is `(a -> b) AND (b -> a)`) rather than a hand-derived 4-clause
    /// form, to keep the only real CNF-shape logic in one place.
    fn iff_of(&mut self, a: Lit, b: Lit) -> Lit {
        let fwd = self.or_of(&[a.negate(), b]);
        let bwd = self.or_of(&[a, b.negate()]);
        self.and_of(&[fwd, bwd])
    }

    fn is_bool(&self, term: TermId) -> Option<bool> {
        Some(self.tm.get(term)?.sort == self.tm.sorts.bool_sort)
    }

    /// Encode `term` (must be `Bool`-sorted) as a literal. `None` means
    /// "outside the supported fragment, or too deep" — the caller must
    /// abandon the whole fast-path attempt, not partially apply it.
    fn encode(&mut self, term: TermId, depth: u32) -> Option<Lit> {
        if let Some(&l) = self.cache.get(&term) {
            return Some(l);
        }
        if depth > MAX_ENCODE_DEPTH {
            return None;
        }
        let t = self.tm.get(term)?;
        if t.sort != self.tm.sorts.bool_sort {
            return None;
        }
        let result = match &t.kind {
            TermKind::True => self.true_lit(),
            TermKind::False => {
                let l = self.true_lit();
                l.negate()
            }
            TermKind::Var(_) => {
                if let Some(&v) = self.atom_vars.get(&term) {
                    Lit::pos(v)
                } else {
                    let v = self.fresh_var();
                    self.atom_vars.insert(term, v);
                    Lit::pos(v)
                }
            }
            TermKind::Not(a) => {
                let a = *a;
                let la = self.encode(a, depth + 1)?;
                la.negate()
            }
            TermKind::And(args) => {
                let args: SmallVec<[TermId; 4]> = args.iter().copied().collect();
                let mut lits: SmallVec<[Lit; 4]> = SmallVec::new();
                for a in args {
                    lits.push(self.encode(a, depth + 1)?);
                }
                self.and_of(&lits)
            }
            TermKind::Or(args) => {
                let args: SmallVec<[TermId; 4]> = args.iter().copied().collect();
                let mut lits: SmallVec<[Lit; 4]> = SmallVec::new();
                for a in args {
                    lits.push(self.encode(a, depth + 1)?);
                }
                self.or_of(&lits)
            }
            TermKind::Implies(l, r) => {
                let (l, r) = (*l, *r);
                let ll = self.encode(l, depth + 1)?;
                let lr = self.encode(r, depth + 1)?;
                self.or_of(&[ll.negate(), lr])
            }
            TermKind::Xor(l, r) => {
                let (l, r) = (*l, *r);
                let ll = self.encode(l, depth + 1)?;
                let lr = self.encode(r, depth + 1)?;
                let eq = self.iff_of(ll, lr);
                eq.negate()
            }
            TermKind::Eq(l, r) => {
                let (l, r) = (*l, *r);
                if !self.is_bool(l)? {
                    return None;
                }
                let ll = self.encode(l, depth + 1)?;
                let lr = self.encode(r, depth + 1)?;
                self.iff_of(ll, lr)
            }
            TermKind::Distinct(args) if args.len() == 2 => {
                let (a0, a1) = (args[0], args[1]);
                if !self.is_bool(a0)? {
                    return None;
                }
                let ll = self.encode(a0, depth + 1)?;
                let lr = self.encode(a1, depth + 1)?;
                let eq = self.iff_of(ll, lr);
                eq.negate()
            }
            TermKind::Ite(c, th, el) => {
                let (c, th, el) = (*c, *th, *el);
                if !self.is_bool(th)? {
                    return None;
                }
                let lc = self.encode(c, depth + 1)?;
                let lt = self.encode(th, depth + 1)?;
                let le = self.encode(el, depth + 1)?;
                let a = self.or_of(&[lc.negate(), lt]); // c -> t
                let b = self.or_of(&[lc, le]); // ¬c -> e
                self.and_of(&[a, b])
            }
            _ => return None,
        };
        self.cache.insert(term, result);
        Some(result)
    }
}

/// Grow `solver` (via repeated `new_var`) until it has at least `count`
/// variables.
fn ensure_vars(solver: &mut SatSolver, count: u32) {
    while (solver.num_vars() as u32) < count {
        solver.new_var();
    }
}

/// Solve `base_clauses`, plus (if `bound` is `Some(k)`) a fresh "at most
/// `k` of `cost_pool` are true" cardinality constraint, in a brand-new
/// `oxiz_sat::Solver` — one call per binary-search step, mirroring
/// `optimize_maxsmt`'s own original "fresh solver per candidate bound"
/// structure.
fn solve_bounded(
    base_clauses: &[SmallVec<[Lit; 4]>],
    cost_pool: &[Lit],
    bound: Option<usize>,
    next_var: u32,
) -> (SolverResult, Option<Vec<LBool>>) {
    let mut solver = SatSolver::new();
    let mut nv = next_var;

    let mut all: Vec<SmallVec<[Lit; 4]>> = base_clauses.to_vec();
    if let Some(k) = bound {
        let (card_clauses, assumption, new_next_var) =
            encode_at_most_k(cost_pool, k, CardinalityEncoding::Totalizer, nv);
        nv = new_next_var;
        for c in card_clauses {
            all.push(c.lits);
        }
        // `encode_at_most_k`'s returned clauses only DEFINE the totalizer's
        // internal wires (`assumption` <-> "at most k of cost_pool are
        // true") — they don't, by themselves, FORCE the bound to hold.
        // `assumption` must be asserted TRUE (or used as a solving
        // assumption) for the "at most k" constraint to actually be
        // enforced. `None` means "k already covers every input, trivially
        // true" (`Totalizer::at_most`'s doc) — no clause needed then.
        if let Some(a) = assumption {
            all.push(smallvec![a]);
        }
    }

    ensure_vars(&mut solver, nv);
    for c in &all {
        solver.add_clause(c.iter().copied());
    }
    match solver.solve() {
        SolverResult::Sat => (SolverResult::Sat, Some(solver.model().to_vec())),
        other => (other, None),
    }
}

/// Attempt the Boolean-CNF fast path for a MaxSAT problem (`hard`
/// constraints + `soft` weighted soft constraints, all terms live in
/// `tm`). Returns `None` when the problem is not fully within the
/// supported propositional fragment — the caller must fall back to the
/// general encoding in that case (see the module doc's "Scope" section).
pub(crate) fn try_optimize_maxsmt_boolean(
    hard: &[TermId],
    soft: &[SoftConstraint],
    tm: &TermManager,
) -> Option<BoolFastPathOutcome> {
    // `Weight::Infinite` soft constraints never have a sensible finite
    // replication count (and are never produced by the `assert-soft
    // :weight <numeral>` grammar in the first place) — bail rather than
    // guess.
    if soft.iter().any(|sc| matches!(sc.weight, Weight::Infinite)) {
        return None;
    }

    let mut b = CnfBuilder::new(tm);

    let mut hard_lits: Vec<Lit> = Vec::with_capacity(hard.len());
    for &h in hard {
        hard_lits.push(b.encode(h, 0)?);
    }
    let mut soft_lits: Vec<Lit> = Vec::with_capacity(soft.len());
    for sc in soft {
        soft_lits.push(b.encode(sc.term, 0)?);
    }

    // Scale every weight to a common integer unit — handles rational/
    // decimal `:weight` values EXACTLY (see `scaled_weight`'s doc),
    // unlike the general fallback path's old truncate-to-1 behavior.
    let scale: BigInt = soft
        .iter()
        .filter_map(|sc| match &sc.weight {
            Weight::Rational(r) => Some(r.denom().clone()),
            Weight::Int(_) | Weight::Infinite => None,
        })
        .fold(BigInt::from(1), |acc, d| lcm_bigint(&acc, &d));

    let mut scaled: Vec<usize> = Vec::with_capacity(soft.len());
    let mut total_cost: usize = 0;
    for sc in soft {
        let w = scaled_weight(&sc.weight, &scale).to_usize()?;
        total_cost = total_cost.checked_add(w)?;
        if total_cost > MAX_TOTAL_SCALED_WEIGHT {
            return None;
        }
        scaled.push(w);
    }

    // The cost multiset: soft constraint `i`'s violated literal
    // (`soft_lits[i].negate()`), replicated `scaled[i]` times — standard
    // unary weight replication, so "at most K true in this multiset"
    // directly encodes "sum of weights of violated soft constraints <= K".
    let mut cost_pool: Vec<Lit> = Vec::with_capacity(total_cost);
    for (&sl, &w) in soft_lits.iter().zip(scaled.iter()) {
        for _ in 0..w {
            cost_pool.push(sl.negate());
        }
    }

    // Base clauses shared by every binary-search iteration: the user's
    // hard constraints (as unit clauses) plus every Tseitin-defining
    // clause minted while encoding them.
    let mut base_clauses: Vec<SmallVec<[Lit; 4]>> =
        Vec::with_capacity(hard_lits.len() + b.clauses.len());
    for &hl in &hard_lits {
        base_clauses.push(smallvec![hl]);
    }
    base_clauses.extend(b.clauses.iter().cloned());

    // Feasibility: are the hard constraints alone satisfiable (bound =
    // "at most everything may be violated")?
    let (feas, _) = solve_bounded(&base_clauses, &cost_pool, None, b.next_var);
    match feas {
        SolverResult::Unsat => {
            return Some(BoolFastPathOutcome { result: MaxSatResult::Unsatisfiable, model: None });
        }
        SolverResult::Unknown => {
            return Some(BoolFastPathOutcome { result: MaxSatResult::Unknown, model: None });
        }
        SolverResult::Sat => {}
    }

    // Binary search for the minimum feasible cost budget K.
    let mut lo: usize = 0;
    let mut hi: usize = total_cost;
    let mut best_model: Option<Vec<LBool>> = None;
    let mut inconclusive = false;

    while lo < hi {
        let mid = lo + (hi - lo) / 2;
        let (result, model) = solve_bounded(&base_clauses, &cost_pool, Some(mid), b.next_var);
        match result {
            SolverResult::Sat => {
                hi = mid;
                best_model = model;
            }
            SolverResult::Unsat => {
                lo = mid + 1;
            }
            SolverResult::Unknown => {
                inconclusive = true;
                break;
            }
        }
    }

    if !inconclusive {
        let (result, model) = solve_bounded(&base_clauses, &cost_pool, Some(lo), b.next_var);
        if result == SolverResult::Sat {
            best_model = model;
        }
    }

    let Some(bits) = best_model else {
        return Some(BoolFastPathOutcome { result: MaxSatResult::Unknown, model: None });
    };

    let mut m: FxHashMap<TermId, ModelValue> = FxHashMap::default();
    for (&term, &var) in &b.atom_vars {
        if let Some(&bit) = bits.get(var.index()) {
            match bit {
                LBool::True => {
                    m.insert(term, ModelValue::Bool(true));
                }
                LBool::False => {
                    m.insert(term, ModelValue::Bool(false));
                }
                LBool::Undef => {}
            }
        }
    }

    Some(BoolFastPathOutcome {
        result: if inconclusive { MaxSatResult::Satisfiable } else { MaxSatResult::Optimal },
        model: Some(m),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::context::SoftConstraintId;
    use crate::maxsat::Weight;

    fn sc(id: u32, term: TermId, weight: Weight) -> SoftConstraint {
        SoftConstraint { id: SoftConstraintId::new(id), term, weight, group: None }
    }

    #[test]
    fn simple_maxsat_picks_cheaper_violation() {
        // Regression test for the `PmresSolver`-based first attempt (see
        // module doc): that version got exactly this shape WRONG (dropped
        // the expensive constraint, cost 20, instead of the cheap one,
        // cost 5) because its core-relaxation logic doesn't consult
        // weight. This asserts the actual MODEL, not just `Optimal`.
        let mut tm = TermManager::new();
        let a = tm.mk_var("a", tm.sorts.bool_sort);
        let b = tm.mk_var("b", tm.sorts.bool_sort);
        let and_ab = tm.mk_and([a, b]);
        let hard = tm.mk_not(and_ab); // not (a and b)

        let soft = vec![sc(0, a, Weight::from(2)), sc(1, b, Weight::from(3))];
        let outcome = try_optimize_maxsmt_boolean(&[hard], &soft, &tm)
            .expect("pure-boolean problem should take the fast path");
        assert_eq!(outcome.result, MaxSatResult::Optimal);
        let model = outcome.model.expect("optimal result should carry a model");
        // dropping `a` (weight 2) is cheaper than dropping `b` (weight 3):
        // the optimum is a=false, b=true, cost 2.
        assert_eq!(model.get(&a), Some(&ModelValue::Bool(false)));
        assert_eq!(model.get(&b), Some(&ModelValue::Bool(true)));
    }

    #[test]
    fn asymmetric_weight_swap_still_picks_cheaper_violation() {
        // Same shape as `simple_maxsat_picks_cheaper_violation` but with
        // the weights swapped onto the OTHER variable — catches any bug
        // that's sensitive to which soft-constraint INDEX carries the
        // smaller weight (the `PmresSolver` attempt's bug happened to be
        // masked when the smaller weight was on the later index; this
        // pins down the direction too).
        let mut tm = TermManager::new();
        let a = tm.mk_var("a", tm.sorts.bool_sort);
        let b = tm.mk_var("b", tm.sorts.bool_sort);
        let and_ab = tm.mk_and([a, b]);
        let hard = tm.mk_not(and_ab);

        let soft = vec![sc(0, a, Weight::from(20)), sc(1, b, Weight::from(5))];
        let outcome = try_optimize_maxsmt_boolean(&[hard], &soft, &tm)
            .expect("pure-boolean problem should take the fast path");
        assert_eq!(outcome.result, MaxSatResult::Optimal);
        let model = outcome.model.expect("optimal result should carry a model");
        // dropping `b` (weight 5) is cheaper than dropping `a` (weight 20).
        assert_eq!(model.get(&a), Some(&ModelValue::Bool(true)));
        assert_eq!(model.get(&b), Some(&ModelValue::Bool(false)));
    }

    #[test]
    fn unsat_hard_constraints_reported_unsatisfiable() {
        let mut tm = TermManager::new();
        let a = tm.mk_var("a", tm.sorts.bool_sort);
        let not_a = tm.mk_not(a);
        let soft = vec![sc(0, a, Weight::one())];
        let outcome = try_optimize_maxsmt_boolean(&[a, not_a], &soft, &tm)
            .expect("pure-boolean problem should take the fast path");
        assert_eq!(outcome.result, MaxSatResult::Unsatisfiable);
    }

    #[test]
    fn non_boolean_term_bails_to_none() {
        let mut tm = TermManager::new();
        let x = tm.mk_var("x", tm.sorts.int_sort);
        let zero = tm.mk_int(0i64);
        let ge = tm.mk_ge(x, zero); // Bool-sorted, but reaches Int atoms
        let soft = vec![sc(0, ge, Weight::one())];
        assert!(try_optimize_maxsmt_boolean(&[], &soft, &tm).is_none());
    }

    #[test]
    fn rational_weight_is_not_truncated() {
        let mut tm = TermManager::new();
        let a = tm.mk_var("a", tm.sorts.bool_sort);
        let b = tm.mk_var("b", tm.sorts.bool_sort);
        let and_ab = tm.mk_and([a, b]);
        let hard = tm.mk_not(and_ab);

        // Weight 20.0 for `b` is deliberately much larger than the naive
        // "rational -> 1" truncation the general path used to apply — if
        // this fast path also truncated, it would (wrongly) drop `b`
        // (cheaper post-truncation) instead of `a`.
        let big_rational =
            Weight::Rational(num_rational::BigRational::new(200.into(), 10.into()));
        let soft = vec![sc(0, a, Weight::from(5)), sc(1, b, big_rational)];
        let outcome = try_optimize_maxsmt_boolean(&[hard], &soft, &tm)
            .expect("pure-boolean problem should take the fast path");
        assert_eq!(outcome.result, MaxSatResult::Optimal);
        let model = outcome.model.expect("optimal result should carry a model");
        // `a` must be the one dropped (false), `b` kept (true) — cost 5,
        // not cost 20.
        assert_eq!(model.get(&a), Some(&ModelValue::Bool(false)));
        assert_eq!(model.get(&b), Some(&ModelValue::Bool(true)));
    }

    #[test]
    fn deep_nesting_bails_cleanly_not_overflow() {
        let mut tm = TermManager::new();
        let mut cur = tm.mk_var("v0", tm.sorts.bool_sort);
        for _ in 0..10_000 {
            cur = tm.mk_not(cur);
        }
        let soft = vec![sc(0, cur, Weight::one())];
        // Must not crash; either succeeds (well within budget for a
        // straight `Not` chain, no branching) or cleanly bails to `None`.
        let _ = try_optimize_maxsmt_boolean(&[], &soft, &tm);
    }
}
