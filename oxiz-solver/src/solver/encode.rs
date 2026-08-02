//! Term encoding (Tseitin transformation) for the SMT solver

#[allow(unused_imports)]
use crate::prelude::*;
use num_rational::Ratio;
use num_traits::{CheckedAdd, CheckedMul, One, ToPrimitive, Zero};
use oxiz_core::ast::{TermId, TermKind, TermManager};
use oxiz_sat::{Lit, Var};
use oxiz_theories::ArithRat;
use smallvec::SmallVec;

use super::Solver;
use super::trail::TrailOp;
use super::types::{
    ArithConstraintType, Constraint, NamedAssertion, ParsedArithConstraint, Polarity, UnsatCore,
};

impl Solver {
    pub(super) fn get_or_create_var(&mut self, term: TermId) -> Var {
        if let Some(&var) = self.term_to_var.get(&term) {
            return var;
        }

        let var = self.sat.new_var();
        self.term_to_var.insert(term, var);
        self.trail.push(TrailOp::VarCreated { var, term });

        while self.var_to_term.len() <= var.index() {
            self.var_to_term.push(TermId::new(0));
        }
        self.var_to_term[var.index()] = term;
        var
    }

    /// Track theory variables in a term for model extraction.
    /// Recursively scans a term to find Int/Real/BV variables and registers them.
    ///
    /// Compound terms that have already been fully traversed are recorded in
    /// `tracked_compound_terms` to avoid redundant O(depth) re-walks when the
    /// same sub-expression appears in multiple parent constraints.
    pub(super) fn track_theory_vars(&mut self, term_id: TermId, manager: &TermManager) {
        let Some(term) = manager.get(term_id) else {
            return;
        };

        match &term.kind {
            TermKind::Var(_) => {
                // Found a variable - check its sort and track appropriately
                let is_int = term.sort == manager.sorts.int_sort;
                let is_real = term.sort == manager.sorts.real_sort;

                if is_int || is_real {
                    // #427 — record the SORT with the arithmetic solver. Its
                    // LIA/LRA mode comes from the `(set-logic …)` name, which
                    // says nothing useful under `ALL` / no logic / `AUFLIRA`;
                    // the sort is what actually decides integrality.
                    self.arith.declare_sort(term_id, is_int);
                    if !self.arith_terms.contains(&term_id) {
                        self.arith_terms.insert(term_id);
                        self.trail.push(TrailOp::ArithTermAdded { term: term_id });
                        self.arith.intern(term_id);
                    }
                } else if let Some(sort) = manager.sorts.get(term.sort)
                    && sort.is_bitvec()
                    && !self.bv_terms.contains(&term_id)
                {
                    self.bv_terms.insert(term_id);
                    self.trail.push(TrailOp::BvTermAdded { term: term_id });
                    if let Some(width) = sort.bitvec_width() {
                        self.bv.new_bv(term_id, width);
                    }
                    // Also intern in ArithSolver for BV comparison constraints
                    // (BV comparisons are handled as bounded integer arithmetic)
                    // — and they ARE integral, so declare them so (#427); a
                    // `BV`-named logic already selected LIA, this just makes the
                    // `ALL`/no-logic path agree.
                    self.arith.declare_sort(term_id, true);
                    self.arith.intern(term_id);
                }
            }
            // Recursively scan compound terms.
            // Guard: if this compound node was already fully traversed, skip it.
            TermKind::Add(args)
            | TermKind::Mul(args)
            | TermKind::And(args)
            | TermKind::Or(args) => {
                if self.tracked_compound_terms.contains(&term_id) {
                    return;
                }
                self.tracked_compound_terms.insert(term_id);
                // Collect args to avoid re-borrowing `self` during iteration
                let args_vec: SmallVec<[TermId; 8]> = args.iter().copied().collect();
                for arg in args_vec {
                    self.track_theory_vars(arg, manager);
                }
            }
            TermKind::Sub(lhs, rhs)
            | TermKind::Eq(lhs, rhs)
            | TermKind::Lt(lhs, rhs)
            | TermKind::Le(lhs, rhs)
            | TermKind::Gt(lhs, rhs)
            | TermKind::Ge(lhs, rhs)
            | TermKind::BvAdd(lhs, rhs)
            | TermKind::BvSub(lhs, rhs)
            | TermKind::BvMul(lhs, rhs)
            | TermKind::BvAnd(lhs, rhs)
            | TermKind::BvOr(lhs, rhs)
            | TermKind::BvXor(lhs, rhs)
            | TermKind::BvUlt(lhs, rhs)
            | TermKind::BvUle(lhs, rhs)
            | TermKind::BvSlt(lhs, rhs)
            | TermKind::BvSle(lhs, rhs)
            // Shifts and concatenation: recurse so leaf operands are tracked
            // (and thus get model values for counterexamples).
            | TermKind::BvShl(lhs, rhs)
            | TermKind::BvLshr(lhs, rhs)
            | TermKind::BvAshr(lhs, rhs)
            | TermKind::BvConcat(lhs, rhs) => {
                if self.tracked_compound_terms.contains(&term_id) {
                    return;
                }
                self.tracked_compound_terms.insert(term_id);
                let (l, r) = (*lhs, *rhs);
                self.track_theory_vars(l, manager);
                self.track_theory_vars(r, manager);
            }
            // Bit extraction: recurse into the single source operand.
            TermKind::BvExtract { arg, .. } => {
                if self.tracked_compound_terms.contains(&term_id) {
                    return;
                }
                self.tracked_compound_terms.insert(term_id);
                let a = *arg;
                self.track_theory_vars(a, manager);
            }
            // BV arithmetic operations (division/remainder)
            // These need the has_bv_arith_ops flag for conflict detection
            TermKind::BvUdiv(lhs, rhs)
            | TermKind::BvSdiv(lhs, rhs)
            | TermKind::BvUrem(lhs, rhs)
            | TermKind::BvSrem(lhs, rhs) => {
                if self.tracked_compound_terms.contains(&term_id) {
                    return;
                }
                self.tracked_compound_terms.insert(term_id);
                self.has_bv_arith_ops = true;
                let (l, r) = (*lhs, *rhs);
                self.track_theory_vars(l, manager);
                self.track_theory_vars(r, manager);
            }
            TermKind::Neg(arg) | TermKind::Not(arg) | TermKind::BvNot(arg) => {
                if self.tracked_compound_terms.contains(&term_id) {
                    return;
                }
                self.tracked_compound_terms.insert(term_id);
                let a = *arg;
                self.track_theory_vars(a, manager);
            }
            TermKind::Ite(cond, then_br, else_br) => {
                if self.tracked_compound_terms.contains(&term_id) {
                    return;
                }
                self.tracked_compound_terms.insert(term_id);
                let (c, t, e) = (*cond, *then_br, *else_br);
                self.track_theory_vars(c, manager);
                self.track_theory_vars(t, manager);
                self.track_theory_vars(e, manager);
            }
            // Uninterpreted function application: if the sort is numeric (Int or
            // Real), treat the whole application as an opaque arithmetic variable.
            // This supports the UFLIA / UFLRA combination: `f(k)` appearing in
            // `(> (f k) 10)` must be tracked so that its model value is extracted
            // and available to the MBQI counterexample generator.
            //
            // We do NOT recurse into the arguments here -- argument terms are
            // arithmetic values passed to an opaque symbol, not arithmetic
            // variables in their own right within this constraint.  (They will be
            // tracked separately when they appear in other constraints.)
            //
            // RESTRICTION: skip Apply terms that have an argument which is itself
            // an Apply term that is already in `arith_terms` (i.e. already has a
            // numeric model value in the arithmetic solver).  When `f(g(a))` is
            // added to arith AND `g(a)` also has an arith model value `v`, the
            // arith solver treats `f(g(a))` as independent from `f(v)`, leading
            // to theory combination conflicts with EUF (which knows via congruence
            // that `f(g(a)) = f(v)`).
            //
            // In contrast, terms like `f(sk(x))` where `sk(x)` is a fresh Skolem
            // constant (NOT in arith_terms) are safe to add because there are no
            // contradictory EUF congruence facts to violate.
            TermKind::Apply { .. } => {
                let is_int = term.sort == manager.sorts.int_sort;
                let is_real = term.sort == manager.sorts.real_sort;
                if is_int || is_real {
                    // Track EVERY numeric application — including nested apps like
                    // `f(g(a))` — as an arithmetic variable so its DIRECT numeric
                    // constraints (e.g. `f(g(a)) = 20` ∧ `f(g(a)) <= 10`) reach
                    // the arithmetic solver.  Dropping a nested app here loses
                    // those constraints and is unsound (it can turn UNSAT into a
                    // spurious SAT; ground audit bug `a`).
                    //
                    // The historical reason for skipping nested apps — that arith
                    // would treat `f(g(a))` as independent from the congruent
                    // `f(v)` once `g(a) = v`, causing a spurious combination
                    // conflict — is handled the sound way instead, by
                    // `propagate_euf_equalities_to_arith` asserting the EUF
                    // congruence `f(g(a)) = f(v)` into arith.  (That propagation
                    // became reliable once the EUF proof forest was correctly
                    // backtracked; a leaked proof edge previously produced invalid
                    // conflict explanations.)
                    self.arith.declare_sort(term_id, is_int); // #427
                    if !self.arith_terms.contains(&term_id) {
                        self.arith_terms.insert(term_id);
                        self.trail.push(TrailOp::ArithTermAdded { term: term_id });
                        self.arith.intern(term_id);
                    }
                }
            }

            // Array select with numeric sort: `(select a i) : Int/Real` is an
            // opaque arithmetic variable -- the array theory handles equality
            // propagation for equal indices, while arithmetic sees the result as
            // an unconstrained integer/real.  We register it here so that
            // constraints like `(> (select a 0) 7)` are tracked by the arithmetic
            // solver and model values are extracted correctly.
            TermKind::Select(_, _) => {
                let is_int = term.sort == manager.sorts.int_sort;
                let is_real = term.sort == manager.sorts.real_sort;
                if is_int || is_real {
                    self.arith.declare_sort(term_id, is_int); // #427
                    if !self.arith_terms.contains(&term_id) {
                        self.arith_terms.insert(term_id);
                        self.trail.push(TrailOp::ArithTermAdded { term: term_id });
                        self.arith.intern(term_id);
                    }
                }
            }

            // #429 — every OTHER Int/Real-sorted term is a foreign term
            // produced by a non-arithmetic theory: a datatype selector
            // (`(fst p)`), `str.len`, `div`/`mod`, a `match`, … The arithmetic
            // linearizer now admits exactly these as Nelson-Oppen INTERFACE
            // VARIABLES (see `extract_linear_terms`'s catch-all), so register
            // them here too — same declare/intern/trail triple as the `Apply`
            // and `Select` arms above — otherwise the simplex would carry a
            // variable the encoder never declared the sort of (integrality
            // silently falling back to the logic-name default, i.e. #427
            // again) and the model builder would have no value for it.
            //
            // NUMERALS ARE EXCLUDED: `IntConst`/`RealConst`/`BitVecConst` are
            // Int/Real-sorted too, and interning one as an UNCONSTRAINED
            // variable would let the simplex pick any value for the literal
            // `5`. They are handled as constants by the linearizer and must
            // stay untracked here (this is what the old catch-all's "constants
            // and other leaf terms" comment was about).
            TermKind::IntConst(_)
            | TermKind::RealConst(_)
            | TermKind::BitVecConst { .. }
            | TermKind::True
            | TermKind::False => {}
            _ => {
                let is_int = term.sort == manager.sorts.int_sort;
                let is_real = term.sort == manager.sorts.real_sort;
                if is_int || is_real {
                    self.arith.declare_sort(term_id, is_int); // #427
                    if !self.arith_terms.contains(&term_id) {
                        self.arith_terms.insert(term_id);
                        self.trail.push(TrailOp::ArithTermAdded { term: term_id });
                        self.arith.intern(term_id);
                    }
                }
            }
        }
    }

    /// Parse an arithmetic comparison and extract linear expression.
    /// Returns: (terms with coefficients, constant, constraint_type).
    ///
    /// Results are cached by `reason` (the comparison term id).
    /// `ParsedArithConstraint` is purely structural — it depends only on the
    /// term graph — so the cache is safe to retain across CDCL backtracks.
    ///
    /// `allow_opaque_leaves` (#429) enables the Nelson-Oppen **interface
    /// variable** fallback: a sub-term whose head belongs to another theory
    /// (a datatype selector, `str.len`, `div`/`mod`, …) is represented as one
    /// opaque arithmetic variable instead of failing the WHOLE atom. Set at
    /// the genuine Int/Real comparison sites; deliberately NOT set at the
    /// `BvUlt`/`BvUle` sites, whose operands are bit-vectors the embedded
    /// bit-blaster owns (see the `BvSlt` note below for why the BV/arith
    /// bridge is kept narrow).
    pub(super) fn parse_arith_comparison(
        &mut self,
        lhs: TermId,
        rhs: TermId,
        constraint_type: ArithConstraintType,
        reason: TermId,
        manager: &TermManager,
        allow_opaque_leaves: bool,
    ) -> Option<ParsedArithConstraint> {
        // Fast path: return cached result if available.
        if let Some(cached) = self.arith_parse_cache.get(&reason) {
            return cached.clone();
        }

        // Accumulate in `Ratio<i128>` (= `oxiz_theories::ArithRat`, the LRA/LIA
        // core's rational). The accumulated value flows straight into the simplex
        // with NO narrowing: the whole arithmetic core is now `i128`, so the
        // `i64::MIN`-class literals whose negation overflowed `i64` are exact.
        //
        // #429 — two passes. The STRICT pass is exactly the historical parser
        // (every existing formula keeps its bit-identical decomposition); only
        // when it bails does the relaxed pass rerun with foreign sub-terms
        // admitted as opaque interface variables, which is strictly more
        // information than the old behaviour of dropping the atom entirely.
        let mut parsed = self.extract_comparison_sides(lhs, rhs, manager, false);
        if parsed.is_none() && allow_opaque_leaves {
            parsed = self.extract_comparison_sides(lhs, rhs, manager, true);
        }
        let Some((terms, constant)) = parsed else {
            self.arith_parse_cache.insert(reason, None);
            return None;
        };

        // Combine like terms
        let mut combined: FxHashMap<TermId, Ratio<i128>> = FxHashMap::default();
        for (term, coef) in terms {
            *combined.entry(term).or_insert_with(Ratio::zero) += coef;
        }

        // Remove zero coefficients and keep each surviving coefficient as the
        // `i128` rational it already is — no narrowing. (Zero terms are still
        // dropped: a 0·x term carries no constraint, exactly as before.)
        let mut final_terms: SmallVec<[(TermId, ArithRat); 4]> = SmallVec::new();
        for (term, coef) in combined {
            if coef.is_zero() {
                continue;
            }
            final_terms.push((term, coef));
        }

        // Move constant to RHS; pass the `i128` value straight through.
        let constant128: ArithRat = -constant;

        let result = ParsedArithConstraint {
            terms: final_terms,
            constant: constant128,
            constraint_type,
            reason_term: reason,
        };

        self.arith_parse_cache.insert(reason, Some(result.clone()));
        Some(result)
    }

    /// One pass of `lhs - rhs` linearisation, in either the strict or the
    /// opaque-leaf mode (#429). Returns the raw (uncombined) term list and the
    /// accumulated constant, or `None` if this pass bailed.
    #[allow(clippy::type_complexity)]
    fn extract_comparison_sides(
        &self,
        lhs: TermId,
        rhs: TermId,
        manager: &TermManager,
        opaque_leaves: bool,
    ) -> Option<(SmallVec<[(TermId, Ratio<i128>); 4]>, Ratio<i128>)> {
        let mut terms: SmallVec<[(TermId, Ratio<i128>); 4]> = SmallVec::new();
        let mut constant: Ratio<i128> = Ratio::zero();
        // Parse LHS (add positive coefficients)
        self.extract_linear_terms(
            lhs,
            Ratio::one(),
            &mut terms,
            &mut constant,
            manager,
            opaque_leaves,
        )?;
        // Parse RHS (subtract, so coefficients are negated).
        // For lhs OP rhs, we want lhs - rhs OP 0
        self.extract_linear_terms(
            rhs,
            -Ratio::<i128>::one(),
            &mut terms,
            &mut constant,
            manager,
            opaque_leaves,
        )?;
        Some((terms, constant))
    }

    /// Extract linear terms recursively from an arithmetic expression
    /// Returns None if the term is not linear
    ///
    /// `opaque_leaves` (#429): admit a sub-term this parser cannot decompose as
    /// a single OPAQUE arithmetic variable (a Nelson-Oppen interface variable)
    /// rather than bailing. See `parse_arith_comparison`.
    #[allow(clippy::only_used_in_recursion)]
    pub(super) fn extract_linear_terms(
        &self,
        term_id: TermId,
        scale: Ratio<i128>,
        terms: &mut SmallVec<[(TermId, Ratio<i128>); 4]>,
        constant: &mut Ratio<i128>,
        manager: &TermManager,
        opaque_leaves: bool,
    ) -> Option<()> {
        let term = manager.get(term_id)?;

        match &term.kind {
            // Integer constant
            TermKind::IntConst(n) => {
                if let Some(val) = n.to_i128() {
                    // Checked: an i128-rational overflow here must make the
                    // comparison OPAQUE (return None), never silently wrap into
                    // a wrong coefficient — wrapping fabricates a spurious arith
                    // conflict (the prelude-scale `-V adsmt` false-`unsat`). The
                    // whole LRA/LIA core is `i128` (`ArithRat`), so this value
                    // flows straight into the simplex with NO narrowing; only a
                    // genuine i128 overflow (astronomically large) bails here.
                    *constant =
                        constant.checked_add(&scale.checked_mul(&Ratio::from_integer(val))?)?;
                    Some(())
                } else {
                    // BigInt beyond i128, skip (opaque).
                    None
                }
            }

            // Rational constant
            TermKind::RealConst(r) => {
                // The term-level `RealConst` is `Rational64` (oxiz-core); widen
                // its numer/denom to the `i128` core rational (lossless) before
                // the checked product/sum.
                let r128 = Ratio::new(i128::from(*r.numer()), i128::from(*r.denom()));
                *constant = constant.checked_add(&scale.checked_mul(&r128)?)?;
                Some(())
            }

            // Bitvector constant - treat as integer
            TermKind::BitVecConst { value, .. } => {
                if let Some(val) = value.to_i128() {
                    // Checked (see the `IntConst` note): `i128` accumulation,
                    // flows straight into the `i128` LRA/LIA core, no narrowing.
                    *constant =
                        constant.checked_add(&scale.checked_mul(&Ratio::from_integer(val))?)?;
                    Some(())
                } else {
                    // BigInt beyond i128, skip (opaque).
                    None
                }
            }

            // Variable (or bitvector variable - treat as integer variable)
            TermKind::Var(_) => {
                terms.push((term_id, scale));
                Some(())
            }

            // Uninterpreted function application whose sort is numeric -- treat
            // as an opaque arithmetic variable.  This is the UFLIA / UFLRA case:
            // e.g. `f(k)` in `(> (f k) 10)` where `f : Int -> Int`.  By
            // representing `f(k)` as an arithmetic variable we ensure that
            //   (a) the arithmetic solver tracks it and assigns it a model value,
            //   (b) the constraint `f(k) > 10` is handled consistently with any
            //       later instantiation that produces `f(k) <= 10`.
            //
            // Represent EVERY numeric Apply term — flat (`f(k)`) or nested
            // (`f(g(k))`) — as an arithmetic variable so its direct linear
            // constraints are seen by the arithmetic solver.  Dropping a nested
            // app here loses its bounds and is unsound (`f(g(k)) = 20` ∧
            // `f(g(k)) <= 10` would be missed → spurious SAT; ground audit bug
            // `a`).  The EUF↔arith congruence that makes `f(g(k))` agree with the
            // congruent `f(v)` once `g(k) = v` is supplied soundly by
            // `propagate_euf_equalities_to_arith`, not by hiding the term from
            // arith.  (See the matching note in `track_theory_vars`.)
            TermKind::Apply { .. } => {
                let sort = term.sort;
                let is_numeric = sort == manager.sorts.int_sort || sort == manager.sorts.real_sort;
                if is_numeric || opaque_leaves {
                    // #429 — `opaque_leaves` also admits an application whose
                    // sort the parser could not resolve to Int/Real. That is
                    // how an SMT-LIB operator oxiz does not implement reaches
                    // this parser (`(bv2nat a)` falls through to a plain
                    // `Apply` carrying the parser's `Bool` default), and in a
                    // well-sorted input it can only be numeric.
                    terms.push((term_id, scale));
                    Some(())
                } else {
                    // Non-numeric Apply (e.g. uninterpreted predicate) -- not linear.
                    None
                }
            }

            // Array select with numeric sort: treat `(select a i) : Int/Real` as
            // an opaque arithmetic atom with the given scale coefficient.  This
            // allows expressions such as `(+ (select a 0) (select a 1))` to be
            // parsed as linear arithmetic sums.
            TermKind::Select(_, _) => {
                let sort = term.sort;
                let is_numeric = sort == manager.sorts.int_sort || sort == manager.sorts.real_sort;
                if is_numeric || opaque_leaves {
                    terms.push((term_id, scale));
                    Some(())
                } else {
                    // Select of non-numeric sort (e.g. Bool array) -- not linear.
                    None
                }
            }

            // Addition
            TermKind::Add(args) => {
                for &arg in args {
                    self.extract_linear_terms(arg, scale, terms, constant, manager, opaque_leaves)?;
                }
                Some(())
            }

            // Subtraction
            TermKind::Sub(lhs, rhs) => {
                self.extract_linear_terms(*lhs, scale, terms, constant, manager, opaque_leaves)?;
                self.extract_linear_terms(*rhs, -scale, terms, constant, manager, opaque_leaves)?;
                Some(())
            }

            // Negation
            TermKind::Neg(arg) => {
                self.extract_linear_terms(*arg, -scale, terms, constant, manager, opaque_leaves)
            }

            // Multiplication of linear terms.  A product is linear iff AT MOST ONE
            // factor is non-constant.  Every other factor must reduce to a pure
            // constant (e.g. `(- 3.0)`, `(+ 1 2)`); their product is the scalar by
            // which the single non-constant factor is multiplied.  Crucially, that
            // non-constant factor may be ANY linear expression — a bare/scaled
            // variable (`x`, `(- x)`), a multi-variable sum (`(+ x y)`), or a linear
            // expression carrying a constant offset (`(- 3 i)` = `3 - i`).  Scaling
            // a linear expression by a constant distributes exactly, so the whole
            // product stays linear.  (Previously only the single-variable, no-offset
            // case was accepted; `(* 4 (- 3 i))` and `(* -4 (- k k))` bailed to
            // `None` ⇒ the whole comparison became an OPAQUE Boolean atom ⇒ the
            // simplex never saw the constraint ⇒ spurious SAT — e.g. `0 = -6`.)
            TermKind::Mul(args) => {
                let mut const_product: Ratio<i128> = Ratio::one();
                // The single non-constant factor, if any, captured as its FULL
                // linear form: a sum of (variable, coefficient) pairs plus an
                // additive constant.  Keeping the constant offset is what makes
                // `(- 3 i)` survive instead of bailing to a nonlinear `None`.
                let mut var_factor: Option<(
                    SmallVec<[(TermId, Ratio<i128>); 4]>,
                    Ratio<i128>,
                )> = None;

                for &arg in args {
                    let mut sub_terms: SmallVec<[(TermId, Ratio<i128>); 4]> = SmallVec::new();
                    let mut sub_constant: Ratio<i128> = Ratio::zero();
                    self.extract_linear_terms(
                        arg,
                        Ratio::one(),
                        &mut sub_terms,
                        &mut sub_constant,
                        manager,
                        opaque_leaves,
                    )?;

                    if sub_terms.is_empty() {
                        // Pure constant factor — absorb into product (checked).
                        const_product = const_product.checked_mul(&sub_constant)?;
                    } else if var_factor.is_none() {
                        // The (single allowed) non-constant factor — keep its full
                        // linear form (terms + offset) so a constant offset like the
                        // `3` in `(- 3 i)` is not lost.
                        var_factor = Some((sub_terms, sub_constant));
                    } else {
                        // A SECOND non-constant factor ⇒ a genuinely nonlinear
                        // product (variable × variable); leave it opaque.
                        return None;
                    }
                }

                let new_scale = scale.checked_mul(&const_product)?;
                match var_factor {
                    Some((sub_terms, sub_constant)) => {
                        // Distribute `new_scale` over the captured linear factor.
                        for (v, coef) in sub_terms {
                            terms.push((v, new_scale.checked_mul(&coef)?));
                        }
                        *constant =
                            constant.checked_add(&new_scale.checked_mul(&sub_constant)?)?;
                        Some(())
                    }
                    None => {
                        *constant = constant.checked_add(&new_scale)?;
                        Some(())
                    }
                }
            }

            // #429 — a sub-term whose head belongs to ANOTHER theory: a
            // datatype selector (`(fst p)`), `str.len`, `div`/`mod`, a `match`,
            // an SMT-LIB operator oxiz does not implement, … Under the strict
            // pass this returns `None`, and because `None` propagates all the
            // way out of `parse_arith_comparison` the ENTIRE comparison atom is
            // dropped from the arithmetic solver and survives only as a free
            // Boolean — so `(> (fst p) 0) ∧ (< (fst p) 1)` was reported `sat`
            // (#429; z3+cvc5 `unsat`). The whole atom vanishing is the bug: the
            // Int-sorted foreign term is an INTERFACE VARIABLE between its
            // producing theory and LIA/LRA, and its bounds belong to the
            // simplex.
            //
            // SOUNDNESS. Representing `t` by one fresh, otherwise-unconstrained
            // arithmetic variable `v_t` is the standard Nelson-Oppen
            // purification: every model of the original formula induces a value
            // for `v_t` (namely `t`'s), so the abstracted constraint set is
            // IMPLIED by the original. Any conflict the simplex derives from it
            // is therefore genuine (no false UNSAT), and adding constraints can
            // never manufacture a `sat` (no false SAT). Hash-consing makes the
            // mapping `t ↦ v_t` a function, so every occurrence of the same
            // foreign term shares one variable — which is exactly what makes
            // `0 < t ∧ t < 1` contradictory. Integrality comes from the term's
            // own SMT sort via `declare_arith_sorts`/`track_theory_vars`
            // (#427), so an Int-sorted interface variable is reasoned about
            // over ℤ, not ℚ.
            _ => {
                if opaque_leaves {
                    terms.push((term_id, scale));
                    Some(())
                } else {
                    None
                }
            }
        }
    }

    /// Assert a term
    /// #397 (adsmt AIR-path residual) — ground term-ite elimination.
    ///
    /// Only the BOOL-sorted `ite` has a Tseitin arm in `encode`, and only the
    /// BV bit-blaster interprets `TermKind::Ite` on the theory side. An
    /// Int/Real/uninterpreted-sorted `ite` reaching a theory atom made the
    /// whole atom OPAQUE — EUF saw `a = <ite-term>` as an unconstrained pair,
    /// arith saw nothing — so `(= a (ite p 1 2)) ∧ a≠1 ∧ a≠2` read a
    /// confident spurious `sat` (z3+cvc5: unsat). The verus fuel-unfolding
    /// definition axioms instantiate to exactly this shape
    /// (`abs(x) = ite(x≥0, x, 0−x)`), which is how the AIR-path 1v/2e
    /// surfaced it.
    ///
    /// Every CLOSED innermost non-Bool/non-BV `ite` is replaced by a fresh
    /// constant `k` and the defining constraint `(ite c (= k t) (= k e))` — a
    /// BOOL ite, which `encode` Tseitin-encodes correctly — conjoined onto
    /// the rewritten formula, so the definition lives and dies with this
    /// assertion (push/pop-safe: no cross-assertion cache to dangle after a
    /// pop; the name counter is monotone so a popped name is never reused).
    ///
    /// Quantifier bodies keep their `ite`s: a fresh constant cannot cross a
    /// binder, a bound-var-dependent `ite` occurs only under its binder (the
    /// binder-depth-0 collector never picks it, and hash-consed sharing of a
    /// CLOSED `ite` into a body is harmless — the substitution equates it
    /// with `k` everywhere). Instance lemmas are ground by construction and
    /// run through this same pass at their own assertion sites.
    pub(super) fn eliminate_term_ites(
        &mut self,
        term: TermId,
        manager: &mut TermManager,
    ) -> TermId {
        fn find_innermost(
            id: TermId,
            manager: &TermManager,
        ) -> Option<TermId> {
            let t = manager.get(id)?;
            // Never descend into a binder: any ite in there either depends on
            // the bound vars (must stay) or is closed (its instances/shared
            // ground occurrences are handled at depth 0).
            if matches!(t.kind, TermKind::Forall { .. } | TermKind::Exists { .. }) {
                return None;
            }
            for c in oxiz_core::ast::traversal::get_children(&t.kind) {
                if let Some(found) = find_innermost(c, manager) {
                    return Some(found);
                }
            }
            if matches!(t.kind, TermKind::Ite(..))
                && t.sort != manager.sorts.bool_sort
                && manager
                    .sorts
                    .get(t.sort)
                    .and_then(|s| s.bitvec_width())
                    .is_none()
            {
                return Some(id);
            }
            None
        }

        let mut root = term;
        let mut defs: Vec<TermId> = Vec::new();
        while let Some(ite) = find_innermost(root, manager) {
            let Some(TermKind::Ite(c, t, e)) = manager.get(ite).map(|x| x.kind.clone()) else {
                break;
            };
            let sort = manager.get(ite).map(|x| x.sort);
            let Some(sort) = sort else { break };
            let name = format!("%%termite!{}", self.term_ite_counter);
            self.term_ite_counter += 1;
            let k = manager.mk_var(&name, sort);
            let eq_then = manager.mk_eq(k, t);
            let eq_else = manager.mk_eq(k, e);
            let def = manager.mk_ite(c, eq_then, eq_else);
            let mut map = FxHashMap::default();
            map.insert(ite, k);
            root = manager.substitute(root, &map);
            defs.push(def);
        }
        if defs.is_empty() {
            return term;
        }
        defs.push(root);
        manager.mk_and(defs)
    }

    pub fn assert(&mut self, term: TermId, manager: &mut TermManager) {
        let index = self.assertions.len();
        // Clean-MBQI quantifier preprocessing (equisatisfiable, polarity-safe):
        //  1. NNF — push negations to the quantifier boundaries so the engine's
        //     polarity-blind `collect_quants` sees each quantifier at its TRUE
        //     polarity. A negated `∃` becomes a positive `∀` the engine
        //     instantiates: `(not (exists y. f(y)=0))` + `f(5)=0` → unsat
        //     instead of the spurious `sat` it gave when the `∃` was collected
        //     (inactive) and never instantiated. Bodies kept opaque so the
        //     `=>`-matching recognizers survive. See `nnf_push_negations`.
        //  2. Fold any quantifier whose matrix is a recognized tautology to
        //     `true`, regardless of polarity (the now-positive valid `∀`s).
        //     See `clean_mbqi::fold_valid_quantifiers`.
        //  3. Skolemize a top-level positive *unbounded* `∃` into a fresh ground
        //     constant, so the engine (which never fabricates witnesses) can
        //     discharge surjectivity-style goals (`∃y. f(y) = 0`) it would
        //     otherwise leave `Unknown`. Bounded `∃` is left for the engine's
        //     finite disjunction (#279). See `skolemize_unbounded_existentials`.
        let term = if self.config.clean_mbqi {
            let t = crate::clean_mbqi::nnf_push_negations(manager, term);
            let t = crate::clean_mbqi::fold_valid_quantifiers(manager, t);
            crate::clean_mbqi::skolemize_unbounded_existentials(manager, t, &index.to_string())
        } else {
            term
        };
        self.assertions.push(term);
        self.trail.push(TrailOp::AssertionAdded { index });
        self.invalidate_fp_cache();

        // Check if this is a boolean constant first
        if let Some(t) = manager.get(term) {
            match t.kind {
                TermKind::False => {
                    // Mark that we have a false assertion
                    if !self.has_false_assertion {
                        self.has_false_assertion = true;
                        self.trail.push(TrailOp::FalseAssertionSet);
                    }
                    if self.produce_unsat_cores {
                        let na_index = self.named_assertions.len();
                        self.named_assertions.push(NamedAssertion {
                            term,
                            name: None,
                            index: index as u32,
                        });
                        self.trail
                            .push(TrailOp::NamedAssertionAdded { index: na_index });
                    }
                    return;
                }
                TermKind::True => {
                    // True is always satisfied, no need to encode
                    if self.produce_unsat_cores {
                        let na_index = self.named_assertions.len();
                        self.named_assertions.push(NamedAssertion {
                            term,
                            name: None,
                            index: index as u32,
                        });
                        self.trail
                            .push(TrailOp::NamedAssertionAdded { index: na_index });
                    }
                    return;
                }
                _ => {}
            }
        }

        // Apply simplification if enabled
        let term_to_encode = if self.config.simplify {
            self.simplifier.simplify(term, manager)
        } else {
            term
        };

        // #397 — replace ground non-Bool `ite`s with fresh constants + Bool-ite
        // definitions BEFORE encoding (see `eliminate_term_ites`).
        let term_to_encode = self.eliminate_term_ites(term_to_encode, manager);

        // Check again if simplification produced a constant
        if let Some(t) = manager.get(term_to_encode) {
            match t.kind {
                TermKind::False => {
                    if !self.has_false_assertion {
                        self.has_false_assertion = true;
                        self.trail.push(TrailOp::FalseAssertionSet);
                    }
                    return;
                }
                TermKind::True => {
                    // Simplified to true, no need to encode
                    return;
                }
                _ => {}
            }
        }

        // Check for datatype constructor mutual exclusivity
        // If we see (= var Constructor), track it and check for conflicts
        if let Some(t) = manager.get(term_to_encode).cloned() {
            if let TermKind::Eq(lhs, rhs) = &t.kind {
                if let Some((var_term, constructor)) =
                    self.extract_dt_var_constructor(*lhs, *rhs, manager)
                {
                    if let Some(&existing_con) = self.dt_var_constructors.get(&var_term) {
                        if existing_con != constructor {
                            // Variable constrained to two different constructors - UNSAT
                            if !self.has_false_assertion {
                                self.has_false_assertion = true;
                                self.trail.push(TrailOp::FalseAssertionSet);
                            }
                            return;
                        }
                    } else {
                        self.dt_var_constructors.insert(var_term, constructor);
                        self.trail.push(TrailOp::DtVarConstructorAdded { var: var_term });
                    }
                }
            }
        }

        // Collect polarity information if polarity-aware encoding is enabled
        if self.polarity_aware {
            self.collect_polarities(term_to_encode, Polarity::Positive, manager);
        }

        // Encode the assertion immediately
        let lit = self.encode(term_to_encode, manager);
        self.sat.add_clause([lit]);

        // For Not(Eq(a,b)) assertions on arithmetic terms, eagerly add the
        // arithmetic disequality split (a<b OR a>b) so that ArithSolver assigns
        // distinct values from the very first SAT solve iteration.  Without this,
        // the ArithSolver may not enforce disequalities correctly.
        self.add_arith_diseq_split(term_to_encode, manager);

        // #429 — `(>= (str.len s) 0)` for every `str.len` subterm.
        self.add_str_len_domain_axioms(term_to_encode, manager);

        // Ground datatype exhaustiveness at the SAT level (#404 phase 2).
        self.add_dt_cover_axioms(term_to_encode, manager);

        // Ground selector-of-constructor reduction (#406).
        self.add_dt_selector_reduction_axioms(term_to_encode, manager);

        // Ground tester-of-constructor reduction (#406).
        self.add_dt_tester_reduction_axioms(term_to_encode, manager);

        if self.produce_unsat_cores {
            let na_index = self.named_assertions.len();
            self.named_assertions.push(NamedAssertion {
                term,
                name: None,
                index: index as u32,
            });
            self.trail
                .push(TrailOp::NamedAssertionAdded { index: na_index });
        }
    }

    /// #429 — the STRING↔ARITHMETIC interface axiom `(>= (str.len s) 0)`.
    ///
    /// `str.len` is an Int-sorted term produced by a NON-arithmetic theory. The
    /// arithmetic linearizer now carries it as a Nelson-Oppen interface
    /// variable (see `extract_linear_terms`'s catch-all), which is what makes
    /// `0 < (str.len s) < 1` correctly UNSAT — but an interface variable is
    /// *unconstrained* unless the producing theory states its domain, and
    /// nothing in this solver ever told arithmetic that a string length is
    /// non-negative. `(assert (< (str.len s) 0))` therefore read a confident
    /// `sat` (z3+cvc5: `unsat`).
    ///
    /// The axiom is emitted at assertion time, once per distinct `StrLen`
    /// subterm, using the house `dt_cover_done`/`TrailOp` idiom: the unit
    /// clause lives at the current SAT level, so the marker is trail-undone on
    /// `pop()` and a later scope re-emits it. Quantifier bodies are NOT
    /// descended — a `(str.len x)` under a binder is not a ground term and its
    /// instances pass through this same pass at their own assertion sites.
    ///
    /// Soundness: `len(s) ≥ 0` is valid in the SMT-LIB string theory, so the
    /// clause is entailed by every model and can never create a false UNSAT.
    fn add_str_len_domain_axioms(&mut self, root: TermId, manager: &mut TermManager) {
        let mut stack: Vec<TermId> = vec![root];
        let mut visited: FxHashSet<TermId> = FxHashSet::default();
        let mut pending: Vec<TermId> = Vec::new();
        while let Some(t) = stack.pop() {
            if !visited.insert(t) {
                continue;
            }
            let Some(td) = manager.get(t) else { continue };
            if matches!(td.kind, TermKind::Forall { .. } | TermKind::Exists { .. }) {
                continue;
            }
            for c in oxiz_core::ast::get_children(&td.kind) {
                stack.push(c);
            }
            if matches!(td.kind, TermKind::StrLen(_))
                && td.sort == manager.sorts.int_sort
                && !self.str_len_domain_done.contains(&t)
            {
                pending.push(t);
            }
        }
        for t in pending {
            if !self.str_len_domain_done.insert(t) {
                continue;
            }
            self.trail.push(TrailOp::StrLenDomainAdded { term: t });
            let zero = manager.mk_int(0);
            let ge = manager.mk_ge(t, zero);
            let lit = self.encode(ge, manager);
            self.sat.add_clause([lit]);
        }
    }

    /// #404 phase 2 (gap #3) — GROUND datatype exhaustiveness at the SAT level.
    ///
    /// The static `check_dt_constraints` pre-pass reads only top-level
    /// assertion polarity (And/Or/Not), so a constructor-shape disequality
    /// buried under `=>`/mixed structure — exactly the verus decreases-check
    /// goal shape — never reaches it, and the CDCL(T) search has no datatype
    /// theory to refute a model where a term is NO constructor's shape at
    /// all: the ground core reported a spurious `sat` where z3 says `unsat`.
    ///
    /// For every ground datatype-sorted subterm `t` of the asserted formula,
    /// encode two VALID axiom families over the same shape atoms
    /// `sᵢ ≔ (= t (Cᵢ (sel_{Cᵢ,0} t) …))`:
    ///   - COVER  (≥1 shape): `(or s₁ … sₙ)` — every datatype value is built
    ///     by SOME constructor, and rebuilding `t` from its own `Cᵢ`-fields
    ///     equals `t` exactly when `t` is `Cᵢ`-shaped;
    ///   - EXCLUSION (≤1 shape): `(not sᵢ) ∨ (not sⱼ)` pairwise — two shapes
    ///     at once would force `Cᵢ(…) = Cⱼ(…)`, impossible by constructor
    ///     distinctness. Without this a model can take BOTH shapes, which
    ///     falsifies every `¬is-Cₖ`-style axiom guard in sight and lets the
    ///     guarded facts silently vanish (the dm3 decreases-check escape).
    /// Validity makes both additions sound in BOTH directions.
    ///
    /// Each disjunct's constructor head uses `mk_dt_constructor` (the same
    /// `DtConstructor` node shape the parser builds for a user-written
    /// constructor application, so THAT part hash-cons-coincides directly).
    /// The rebuilt field accessors are still built as plain `Apply(sel,
    /// [t])` here (pre-#406 style), while a user-written `(sel t)` now
    /// parses to a dedicated `TermKind::DtSelector` node (#406) — so the two
    /// selector sub-terms are no longer the SAME TermId by hash-consing
    /// alone. They still collapse into the same EUF congruence class:
    /// `theory_manager::intern_term_deep`'s `DtSelector` arm keys itself by
    /// the selector's name spur exactly like `Apply`'s function-id key
    /// (`selector.into_inner().get() == func.into_inner().get()` for the
    /// same name), so a same-named `Apply` and `DtSelector` over the same
    /// argument are unified as soon as both are interned into EUF. The
    /// exhaustiveness conflict is therefore closed at the EUF-congruence
    /// level rather than by literal hash-cons identity, but it is still
    /// closed — see `dt_ground_completeness_regression.rs`'s
    /// `exhaustiveness_under_implication_is_unsat` /
    /// `exhaustiveness_across_branches_is_unsat`, both of which exercise
    /// user-written `(sel v)` syntax (now `DtSelector`) against this
    /// function's `Apply`-shaped rebuilt terms and stay `unsat`.
    ///
    /// The walk skips binder subtrees (a cover mentioning a bound variable
    /// would be ill-formed) and never walks the cover terms themselves (the
    /// rebuilt fields are datatype-sorted too — covering them recursively
    /// would diverge).
    fn add_dt_cover_axioms(&mut self, root: TermId, manager: &mut TermManager) {
        use oxiz_core::sort::SortId;

        let mut stack = vec![root];
        let mut visited: FxHashSet<TermId> = FxHashSet::default();
        #[allow(clippy::type_complexity)]
        let mut targets: Vec<(TermId, SortId, Vec<(String, Vec<(String, SortId)>)>)> = Vec::new();
        while let Some(t) = stack.pop() {
            if !visited.insert(t) {
                continue;
            }
            let Some(td) = manager.get(t) else { continue };
            if matches!(td.kind, TermKind::Forall { .. } | TermKind::Exists { .. }) {
                continue;
            }
            for c in oxiz_core::ast::get_children(&td.kind) {
                stack.push(c);
            }
            // A constructor application's own cover is trivially true.
            if matches!(td.kind, TermKind::DtConstructor { .. })
                || self.dt_cover_done.contains(&t)
            {
                continue;
            }
            let sort = td.sort;
            if let Some(layouts) = manager.sorts.datatype_ctor_layouts(sort) {
                if !layouts.is_empty() {
                    targets.push((t, sort, layouts));
                }
            }
        }
        for (t, sort, layouts) in targets {
            let dbg = std::env::var("OXIZ_MBQI_DBG").is_ok();
            let shape_lits: Vec<Lit> = layouts
                .iter()
                .map(|(ctor, fields)| {
                    let args: Vec<TermId> = fields
                        .iter()
                        .map(|(sel, fsort)| manager.mk_apply(sel, [t], *fsort))
                        .collect();
                    let app = manager.mk_dt_constructor(ctor, args, sort);
                    let eq = manager.mk_eq(t, app);
                    if dbg {
                        eprintln!("[mbqi-dbg] dt-cover: t={t:?} ctor={ctor} eq-atom={eq:?}");
                    }
                    self.encode(eq, manager)
                })
                .collect();
            // ≥1 shape: the cover clause itself.
            self.sat.add_clause(shape_lits.iter().copied());
            // ≤1 shape: pairwise exclusion — `t = Cᵢ(…) ∧ t = Cⱼ(…)` forces
            // `Cᵢ(…) = Cⱼ(…)`, impossible by constructor distinctness. Without
            // this the model can make a term BOTH shapes at once, which
            // falsifies every `¬is-Cₖ`-style axiom guard and lets the guarded
            // facts silently vanish (the dm3 decreases-check escape).
            for i in 0..shape_lits.len() {
                for j in (i + 1)..shape_lits.len() {
                    self.sat
                        .add_clause([shape_lits[i].negate(), shape_lits[j].negate()]);
                }
            }
            self.dt_cover_done.insert(t);
            self.trail.push(TrailOp::DtCoverAdded { term: t });
        }
    }

    /// #418 items 1 & 2 — structural + variable-binding resolution of a
    /// ground datatype-sorted term to a manifest `DtConstructor` application
    /// "normal form". This is the shared engine behind the generalized
    /// `add_dt_selector_reduction_axioms`/`add_dt_tester_reduction_axioms`
    /// below; see those functions' doc comments for how it closes the #418
    /// item 1 (selector/tester CHAIN, depth ≥ 2) and item 2 (selector/tester
    /// on a variable only shown equal to a constructor application via a
    /// SEPARATE ground equality, possibly through a chain of plain variable
    /// equalities) residuals from #406.
    ///
    /// Recursive rule (purely a function of the term DAG's own shape plus
    /// `var_ctor_bindings`, never of "what's possible" — every step below is
    /// either a syntactic identity or an already-established binding):
    ///   - `t` IS a `DtConstructor` application: normal form is `t` itself.
    ///   - `t` is a `Var` bound by `var_ctor_bindings` to some constructor
    ///     term `c` (see `check_dt.rs::collect_var_ctor_bindings` — already
    ///     transitively closed over plain variable-to-variable equalities,
    ///     so a chain `w = z, z = C(args…)` binds `w` too, no matter how many
    ///     var=var hops away): normal form is `resolve(c)`.
    ///   - `t` is `DtSelector { selector, arg }`, `resolve(arg) =
    ///     Some(C(cargs))`, and `selector` is one of `C`'s OWN fields at
    ///     index `i`: normal form is `resolve(cargs[i])` — recursing here is
    ///     exactly what closes a depth-N selector chain (e.g. `hd(tl(cons(a,
    ///     cons(b, c))))`): each step first pins down its OWN direct
    ///     argument's constructor shape (however many hops that itself
    ///     took), then asks whether the extracted field is ITSELF further
    ///     resolvable (another manifest constructor, another selector/tester
    ///     chain, or another bound variable). When the extracted field is
    ///     NOT itself datatype-sorted (e.g. an `Int` field, the common base
    ///     case), this recursive call simply returns `None` — which is fine:
    ///     the CALLER (one recursion level up, or the axiom-emission code
    ///     below) uses the RAW field value directly as the reduction target
    ///     regardless of whether it further resolves; `None` here only means
    ///     "can't simplify further", never "this field has no value".
    ///   - otherwise: `None` — this purely-static analysis has nothing to
    ///     say about `t`. NEVER treated as a conflict, only ever as "no axiom
    ///     to add here" (a missed completeness case stays unconstrained,
    ///     exactly like the pre-#418 one-level check already did).
    ///
    /// `var_ctor_bindings` may be the EMPTY map (pure structural resolution —
    /// safe and correct to run at per-assert encode time, since it depends on
    /// nothing but the term DAG already built by THIS assertion; this is what
    /// `add_dt_selector_reduction_axioms`/`_tester_` below pass) or the full
    /// check-sat-wide map built by `check_dt.rs::collect_var_ctor_bindings`
    /// (used by `add_dt_indirect_var_reduction_axioms`, run once per
    /// check-sat from `mod.rs::check_level`, since only THAT point has seen
    /// every currently-active assertion — a per-assert pass cannot see a
    /// binding established by a LATER assertion).
    ///
    /// `memo`/`in_progress` are supplied by the caller so repeated queries
    /// across many selector/tester nodes in the same pass share the cache.
    /// `in_progress` guards against a cycle in the recursion itself — a
    /// well-formed ground term DAG never has one (this is a purely defensive
    /// termination guard, not a soundness requirement).
    pub(super) fn resolve_dt_normal_form(
        term: TermId,
        var_ctor_bindings: &FxHashMap<TermId, TermId>,
        memo: &mut FxHashMap<TermId, Option<TermId>>,
        in_progress: &mut FxHashSet<TermId>,
        manager: &TermManager,
    ) -> Option<TermId> {
        if let Some(&cached) = memo.get(&term) {
            return cached;
        }
        if !in_progress.insert(term) {
            // Cycle in the recursion itself (shouldn't happen on a
            // well-formed ground DAG) -- bail rather than loop forever.
            return None;
        }
        let result =
            Self::resolve_dt_normal_form_step(term, var_ctor_bindings, memo, in_progress, manager);
        in_progress.remove(&term);
        memo.insert(term, result);
        result
    }

    fn resolve_dt_normal_form_step(
        term: TermId,
        var_ctor_bindings: &FxHashMap<TermId, TermId>,
        memo: &mut FxHashMap<TermId, Option<TermId>>,
        in_progress: &mut FxHashSet<TermId>,
        manager: &TermManager,
    ) -> Option<TermId> {
        let td = manager.get(term)?;
        match &td.kind {
            TermKind::DtConstructor { .. } => Some(term),
            TermKind::Var(_) => {
                let &bound = var_ctor_bindings.get(&term)?;
                Self::resolve_dt_normal_form(bound, var_ctor_bindings, memo, in_progress, manager)
            }
            TermKind::DtSelector { selector, arg } => {
                let selector = *selector;
                let arg = *arg;
                let resolved_arg = Self::resolve_dt_normal_form(
                    arg,
                    var_ctor_bindings,
                    memo,
                    in_progress,
                    manager,
                )?;
                let argd = manager.get(resolved_arg)?;
                let TermKind::DtConstructor {
                    constructor,
                    args: ctor_args,
                } = &argd.kind
                else {
                    return None;
                };
                let dt_sort = argd.sort;
                let layouts = manager.sorts.datatype_ctor_layouts(dt_sort)?;
                let ctor_name = manager.resolve_str(*constructor).to_string();
                let sel_name = manager.resolve_str(selector).to_string();
                let (_, fields) = layouts.iter().find(|(c, _)| *c == ctor_name)?;
                let idx = fields.iter().position(|(s, _)| *s == sel_name)?;
                let &field_term = ctor_args.get(idx)?;
                Self::resolve_dt_normal_form(
                    field_term,
                    var_ctor_bindings,
                    memo,
                    in_progress,
                    manager,
                )
            }
            _ => None,
        }
    }

    /// #406 (direct case) + #418 item 1 (chains) / item 2 (indirect
    /// variables, via `add_dt_indirect_var_reduction_axioms`) — ground
    /// selector-of-constructor reduction at the SAT level.
    ///
    /// The parser builds a real `TermKind::DtSelector` node for an applied
    /// selector symbol (e.g. `(hd v)`). For every ground `DtSelector {
    /// selector, arg }` subterm `t` among `roots`' descendants where
    /// `resolve_dt_normal_form(arg, var_ctor_bindings, …) = Some(C(cargs))`,
    /// look up (via the SAME `SortManager::datatype_ctor_layouts` used by
    /// `add_dt_cover_axioms`) whether `selector` names one of `C`'s fields:
    ///   - if so, at field index `i`, assert the VALID ground fact
    ///     `(= t cargs[i])` as a unit clause — the standard datatype selector
    ///     axiom, holds unconditionally;
    ///   - if `selector` is NOT one of that constructor's fields (e.g. `(hd
    ///     nil)`), the SMT-LIB semantics leaves the value arbitrary but
    ///     fixed, so NOTHING is asserted (never fabricate a value, never
    ///     forbid one — sound in both directions).
    ///
    /// `resolve_dt_normal_form` is what upgrades this past the OLD "arg is
    /// LITERALLY a manifest `DtConstructor` one level in" check: it chases
    /// through selector CHAINS (`hd(tl(cons(a, cons(b, c))))`, #418 item 1)
    /// and, when `var_ctor_bindings` is non-empty, through a variable bound
    /// to a constructor application by a SEPARATE assertion (#418 item 2).
    /// This function itself always passes the EMPTY map (pure structural
    /// resolution, safe at per-assert encode time since it depends only on
    /// the term DAG this one assertion already built) — see
    /// `add_dt_indirect_var_reduction_axioms` for the check-sat-wide pass
    /// that supplies the full binding map.
    ///
    /// Reuses the identical worklist/skip rules as `add_dt_cover_axioms`
    /// (skip binder bodies, hash-consed atoms) and the identical trail-undo
    /// idiom (`dt_selector_reduced` guard + `TrailOp::DtSelectorReduced`) so
    /// incremental push/pop stays sound; see `add_dt_selector_reduction_axioms_over`'s
    /// doc comment for why REUSING that one dedup set across both the
    /// per-assert and check-sat-wide callers is safe.
    fn add_dt_selector_reduction_axioms(&mut self, root: TermId, manager: &mut TermManager) {
        let empty_bindings: FxHashMap<TermId, TermId> = FxHashMap::default();
        self.add_dt_selector_reduction_axioms_over(&[root], &empty_bindings, manager);
    }

    /// Shared implementation behind `add_dt_selector_reduction_axioms`
    /// (per-assert, `var_ctor_bindings` empty) and
    /// `add_dt_indirect_var_reduction_axioms` (check-sat-wide, `roots` =
    /// every current assertion, `var_ctor_bindings` = the full check-sat map
    /// from `check_dt.rs::collect_var_ctor_bindings`).
    ///
    /// Reusing `dt_selector_reduced`/`TrailOp::DtSelectorReduced` for BOTH
    /// callers is sound: that set/trail-op is purely a re-derivation cache
    /// (never itself an asserted fact) whose sole job is to avoid re-adding
    /// the SAME unit clause redundantly. Whichever pass first resolves a
    /// given `DtSelector` term marks it; the other then skips it (no
    /// duplicate clause). On `pop()`, the marker is dropped in lock-step with
    /// the underlying SAT solver discarding the clause (`self.sat.pop()`),
    /// so a later scope — or a later check-sat in the SAME scope, once a
    /// binding becomes available — correctly re-derives and re-injects it.
    fn add_dt_selector_reduction_axioms_over(
        &mut self,
        roots: &[TermId],
        var_ctor_bindings: &FxHashMap<TermId, TermId>,
        manager: &mut TermManager,
    ) {
        let mut stack: Vec<TermId> = roots.to_vec();
        let mut visited: FxHashSet<TermId> = FxHashSet::default();
        let mut memo: FxHashMap<TermId, Option<TermId>> = FxHashMap::default();
        let mut in_progress: FxHashSet<TermId> = FxHashSet::default();
        // (selector_term, field_term) pairs to equate — collected during the
        // read-only walk, applied afterwards (mutating `manager`/`self.sat`
        // while `manager.get(..)` borrows are live would not typecheck).
        let mut reductions: Vec<(TermId, TermId)> = Vec::new();
        while let Some(t) = stack.pop() {
            if !visited.insert(t) {
                continue;
            }
            let Some(td) = manager.get(t) else { continue };
            if matches!(td.kind, TermKind::Forall { .. } | TermKind::Exists { .. }) {
                continue;
            }
            for c in oxiz_core::ast::get_children(&td.kind) {
                stack.push(c);
            }
            if self.dt_selector_reduced.contains(&t) {
                continue;
            }
            // Match by reference (`td` is `&Term`; `TermKind` is not `Copy`
            // because non-selector variants hold a `SmallVec`) and copy out
            // only the `Copy` fields we need.
            let (selector, arg) = match &td.kind {
                TermKind::DtSelector { selector, arg } => (*selector, *arg),
                _ => continue,
            };
            let Some(resolved_arg) = Self::resolve_dt_normal_form(
                arg,
                var_ctor_bindings,
                &mut memo,
                &mut in_progress,
                manager,
            ) else {
                continue;
            };
            let Some(argd) = manager.get(resolved_arg) else {
                continue;
            };
            let (dt_sort, constructor, ctor_args) = match &argd.kind {
                TermKind::DtConstructor { constructor, args } => (argd.sort, *constructor, args),
                _ => continue,
            };
            let Some(layouts) = manager.sorts.datatype_ctor_layouts(dt_sort) else {
                continue;
            };
            let ctor_name = manager.resolve_str(constructor).to_string();
            let sel_name = manager.resolve_str(selector).to_string();
            let Some((_, fields)) = layouts.iter().find(|(c, _)| *c == ctor_name) else {
                continue;
            };
            // `position` matches the selector name WITHIN this constructor's
            // own field list — a selector belonging to a DIFFERENT
            // constructor of the same datatype (e.g. `(hd nil)`) simply
            // won't be found here, and nothing is asserted (see doc comment).
            let Some(idx) = fields.iter().position(|(s, _)| *s == sel_name) else {
                continue;
            };
            if let Some(&field_term) = ctor_args.get(idx) {
                reductions.push((t, field_term));
            }
        }
        for (t, field_term) in reductions {
            if self.dt_selector_reduced.contains(&t) {
                continue;
            }
            let dbg = std::env::var("OXIZ_MBQI_DBG").is_ok();
            let eq = manager.mk_eq(t, field_term);
            if dbg {
                eprintln!("[mbqi-dbg] dt-selector-reduce: t={t:?} = {field_term:?} eq-atom={eq:?}");
            }
            let lit = self.encode(eq, manager);
            self.sat.add_clause([lit]);
            self.dt_selector_reduced.insert(t);
            self.trail.push(TrailOp::DtSelectorReduced { term: t });
        }
    }

    /// #406 (direct case) + #418 item 1 (chains) / item 2 (indirect
    /// variables) — ground tester-of-constructor reduction at the SAT
    /// level. Mirrors `add_dt_selector_reduction_axioms` exactly (see that
    /// function's doc comment for the shared `resolve_dt_normal_form`
    /// machinery); the only difference is that a tester of a resolved
    /// constructor application is ALWAYS decidable (constructors are
    /// pairwise distinct, so `is-Cⱼ(Cᵢ(args…))` is `true` iff `i = j`,
    /// `false` otherwise) — there is no "arbitrary but fixed" branch to
    /// leave unconstrained.
    fn add_dt_tester_reduction_axioms(&mut self, root: TermId, manager: &mut TermManager) {
        let empty_bindings: FxHashMap<TermId, TermId> = FxHashMap::default();
        self.add_dt_tester_reduction_axioms_over(&[root], &empty_bindings, manager);
    }

    /// Shared implementation behind `add_dt_tester_reduction_axioms`
    /// (per-assert) and `add_dt_indirect_var_reduction_axioms`
    /// (check-sat-wide) — see `add_dt_selector_reduction_axioms_over`'s doc
    /// comment for why reusing `dt_tester_reduced`/`TrailOp::DtTesterReduced`
    /// across both callers is sound.
    fn add_dt_tester_reduction_axioms_over(
        &mut self,
        roots: &[TermId],
        var_ctor_bindings: &FxHashMap<TermId, TermId>,
        manager: &mut TermManager,
    ) {
        let mut stack: Vec<TermId> = roots.to_vec();
        let mut visited: FxHashSet<TermId> = FxHashSet::default();
        let mut memo: FxHashMap<TermId, Option<TermId>> = FxHashMap::default();
        let mut in_progress: FxHashSet<TermId> = FxHashSet::default();
        // (tester_term, decided_value) pairs — collected during the
        // read-only walk, applied afterwards (see the selector-reduction
        // pass for why mutation is deferred to a second loop).
        let mut reductions: Vec<(TermId, bool)> = Vec::new();
        while let Some(t) = stack.pop() {
            if !visited.insert(t) {
                continue;
            }
            let Some(td) = manager.get(t) else { continue };
            if matches!(td.kind, TermKind::Forall { .. } | TermKind::Exists { .. }) {
                continue;
            }
            for c in oxiz_core::ast::get_children(&td.kind) {
                stack.push(c);
            }
            if self.dt_tester_reduced.contains(&t) {
                continue;
            }
            let (tester_ctor, arg) = match &td.kind {
                TermKind::DtTester { constructor, arg } => (*constructor, *arg),
                _ => continue,
            };
            let Some(resolved_arg) = Self::resolve_dt_normal_form(
                arg,
                var_ctor_bindings,
                &mut memo,
                &mut in_progress,
                manager,
            ) else {
                continue;
            };
            let Some(argd) = manager.get(resolved_arg) else {
                continue;
            };
            let arg_ctor = match &argd.kind {
                TermKind::DtConstructor { constructor, .. } => *constructor,
                _ => continue,
            };
            let tester_name = manager.resolve_str(tester_ctor).to_string();
            let arg_name = manager.resolve_str(arg_ctor).to_string();
            reductions.push((t, tester_name == arg_name));
        }
        for (t, decided_true) in reductions {
            if self.dt_tester_reduced.contains(&t) {
                continue;
            }
            let dbg = std::env::var("OXIZ_MBQI_DBG").is_ok();
            let lit = self.encode(t, manager);
            if dbg {
                eprintln!(
                    "[mbqi-dbg] dt-tester-reduce: t={t:?} decided={decided_true} lit={lit:?}"
                );
            }
            self.sat
                .add_clause([if decided_true { lit } else { lit.negate() }]);
            self.dt_tester_reduced.insert(t);
            self.trail.push(TrailOp::DtTesterReduced { term: t });
        }
    }

    /// #418 item 2 — re-derive selector/tester reductions across the WHOLE
    /// current assertion set using a check-sat-wide variable→constructor
    /// binding map (see `check_dt.rs::collect_var_ctor_bindings`), so a
    /// selector/tester whose argument is a VARIABLE only shown equal to a
    /// constructor application by a SEPARATE assertion — not the manifest
    /// structural case `add_dt_selector_reduction_axioms`/`_tester_` already
    /// cover at per-assert encode time — is still reduced. E.g. `(assert (=
    /// z (cons x y))) (assert (not (= (hd z) x)))` is `unsat`, but the
    /// per-assert pass alone can't see it: `z`'s binding to `cons(x, y)`
    /// arrives in a LATER assertion than `(hd z)`'s own encoding.
    ///
    /// Called once per check-sat from `mod.rs::check_level`, right after
    /// `check_dt_constraints` (which independently rebuilds the SAME
    /// `var_ctor_term_eqs`/`dt_var_equalities` facts for its own acyclicity
    /// check) — so this always sees the FULL current assertion set
    /// regardless of assertion order, and is naturally idempotent (re-run on
    /// every check-sat call) via the SAME `dt_selector_reduced`/
    /// `dt_tester_reduced` trail-undone dedup sets the per-assert passes
    /// already use (see `add_dt_selector_reduction_axioms_over`'s doc
    /// comment for why sharing those sets across both origins is sound).
    ///
    /// Push/pop safety: any axiom this injects is a `self.sat.add_clause(…)`
    /// at whatever the CURRENT scope is when check-sat runs; the underlying
    /// SAT solver's OWN push/pop (driven 1:1 by `Solver::push`/`Solver::pop`)
    /// discards that clause exactly when a `pop()` returns to a level before
    /// it was added — identical to how the per-assert passes' clauses are
    /// already scoped, and independent of the fact that `var_ctor_bindings`
    /// itself is rebuilt from scratch every call (a stale binding can never
    /// linger, because nothing here is trusted across calls except the SAT
    /// clauses already committed to the (correctly scoped) SAT solver).
    pub(super) fn add_dt_indirect_var_reduction_axioms(
        &mut self,
        var_ctor_bindings: &FxHashMap<TermId, TermId>,
        manager: &mut TermManager,
    ) {
        if var_ctor_bindings.is_empty() {
            // Nothing this pass could add that the per-assert structural
            // pass (#418 item 1) hasn't already covered -- skip the
            // (otherwise harmless but wasted) whole-assertion-set walk.
            return;
        }
        let roots: Vec<TermId> = self.assertions.clone();
        self.add_dt_selector_reduction_axioms_over(&roots, var_ctor_bindings, manager);
        self.add_dt_tester_reduction_axioms_over(&roots, var_ctor_bindings, manager);
    }

    /// #419 item 1 — the mechanism that actually closes the
    /// injectivity-transitivity repro (`x=cons(a,b); x=cons(c,d); (not (=
    /// (hd x) c))` → must be `unsat`).
    ///
    /// `check_dt.rs::compute_dt_equality_closure` already identifies every
    /// equivalence class with 2+ DISTINCT same-constructor ctor-term
    /// bindings (`extra_by_class`); its `primary_bindings` map picks
    /// arbitrarily ONE of them per class as the resolution hint
    /// `add_dt_indirect_var_reduction_axioms` already runs with. That alone
    /// is not enough: injecting a lone `(= (hd x) a)` fact says nothing
    /// about `c`, so `(not (= (hd x) c))` never conflicts with anything.
    ///
    /// The fix is NOT to hand-roll constructor-argument decomposition —
    /// it is to notice that `x` is not just equal to `cons(a,b)`, it is
    /// EQUALLY, SIMULTANEOUSLY, provably equal to `cons(c,d)` too, so the
    /// SAME audited selector-reduction walk
    /// (`add_dt_selector_reduction_axioms_over` /
    /// `resolve_dt_normal_form`) is re-run once per EXTRA binding, with
    /// that one class's entries in the resolution map overridden to the
    /// extra value. For the repro: the first run (via
    /// `add_dt_indirect_var_reduction_axioms`) derives `(= (hd x) a)`; this
    /// pass's run with `x -> cons(c,d)` derives `(= (hd x) c)` — a SEPARATE
    /// ground fact, injected as its own unit clause. That directly
    /// contradicts the user's `(not (= (hd x) c))` assertion — an ordinary
    /// SAT-level conflict the normal CDCL/theory-propagation loop finds on
    /// its own, no bespoke injectivity reasoning required. (Where the
    /// closure's `derived_ctor_eqs` ground fact `cons(a,b) = cons(c,d)`,
    /// injected separately by `inject_dt_derived_ctor_equalities`, is
    /// insufficient BY ITSELF: plain congruence closure only derives
    /// `f(a)=f(b)` FROM `a=b` — datatype constructors are not, in this
    /// solver, treated as axiomatically injective at the EUF level, so
    /// nothing derives `hd(cons(c,d))` from `cons(a,b)=cons(c,d)` unless
    /// `hd` is actually APPLIED to it somewhere, which this pass is what
    /// does.)
    ///
    /// # Why re-running the whole walk (not a narrower query) is safe
    ///
    /// Overriding ALL of a class's DT-variable synonyms together (not just
    /// the one variable that happened to receive the extra binding)
    /// ensures a selector applied to ANY synonym (`hd(y)` where `y = x`)
    /// is covered too. Every OTHER class keeps its normal primary binding
    /// in the override map, so this pass's resolution behaves IDENTICALLY
    /// to the primary pass for anything unrelated to the class being
    /// varied — it can only ADD extra, independently-sound ground facts
    /// (see `compute_dt_equality_closure`'s doc comment for why `x =
    /// extra_val` is just as true as `x = primary_val`; resolve_dt_normal_form
    /// never claims uniqueness, only that its result is SOME provably-equal
    /// value), never retract or alter anything the primary pass already
    /// established.
    ///
    /// # Scope
    ///
    /// A class with only 1 distinct binding (`extra_by_class` has no entry
    /// for it) is entirely unaffected — this pass is a no-op for the
    /// overwhelming majority of formulas, exactly the pre-#419 behavior.
    /// A combined scenario where TWO DIFFERENT classes each need their own
    /// extra pick selected SIMULTANEOUSLY to complete ONE selector chain
    /// (e.g. `hd(tl(x))` where BOTH `x`'s and `tl(x)`'s classes have
    /// multiple bindings) is not attempted — each extra pick from
    /// `extra_by_class` is tried independently, one class at a time. This
    /// is a deliberate, documented completeness boundary (never a soundness
    /// concern — an unexplored combination just means a case stays
    /// unconstrained, the always-safe direction), out of scope for the
    /// repros #419 was scoped against.
    pub(super) fn add_dt_multi_binding_selector_reduction_axioms(
        &mut self,
        primary_bindings: &FxHashMap<TermId, TermId>,
        extra_by_class: &[(Vec<TermId>, Vec<TermId>)],
        manager: &mut TermManager,
    ) {
        if extra_by_class.is_empty() {
            return;
        }
        let roots: Vec<TermId> = self.assertions.clone();
        for (class_vars, extras) in extra_by_class {
            for &extra_val in extras {
                let mut override_map = primary_bindings.clone();
                for &v in class_vars {
                    override_map.insert(v, extra_val);
                }
                self.add_dt_selector_reduction_axioms_extra(&roots, &override_map, manager);
            }
        }
    }

    /// Shared walk behind `add_dt_multi_binding_selector_reduction_axioms` —
    /// structurally identical to `add_dt_selector_reduction_axioms_over`
    /// (see that function's doc comment for the resolve/layout-matching
    /// logic this mirrors exactly), but keyed by a SEPARATE dedup
    /// set/trail-op (`dt_selector_extra_reduced` /
    /// `TrailOp::DtSelectorExtraReduced`), keyed by the PAIR `(selector_term,
    /// field_value)` rather than `selector_term` alone. This is the one
    /// deliberate divergence from the primary pass: the SAME selector term
    /// legitimately resolves to SEVERAL DIFFERENT, EQUALLY-TRUE field values
    /// here (one per extra binding tried), and every one of them needs its
    /// own ground fact injected — deduping by term alone (like the primary
    /// pass, which only ever has ONE resolution per term) would silently
    /// drop every reduction after the first.
    fn add_dt_selector_reduction_axioms_extra(
        &mut self,
        roots: &[TermId],
        var_ctor_bindings: &FxHashMap<TermId, TermId>,
        manager: &mut TermManager,
    ) {
        let mut stack: Vec<TermId> = roots.to_vec();
        let mut visited: FxHashSet<TermId> = FxHashSet::default();
        let mut memo: FxHashMap<TermId, Option<TermId>> = FxHashMap::default();
        let mut in_progress: FxHashSet<TermId> = FxHashSet::default();
        let mut reductions: Vec<(TermId, TermId)> = Vec::new();
        while let Some(t) = stack.pop() {
            if !visited.insert(t) {
                continue;
            }
            let Some(td) = manager.get(t) else { continue };
            if matches!(td.kind, TermKind::Forall { .. } | TermKind::Exists { .. }) {
                continue;
            }
            for c in oxiz_core::ast::get_children(&td.kind) {
                stack.push(c);
            }
            let (selector, arg) = match &td.kind {
                TermKind::DtSelector { selector, arg } => (*selector, *arg),
                _ => continue,
            };
            let Some(resolved_arg) = Self::resolve_dt_normal_form(
                arg,
                var_ctor_bindings,
                &mut memo,
                &mut in_progress,
                manager,
            ) else {
                continue;
            };
            let Some(argd) = manager.get(resolved_arg) else {
                continue;
            };
            let (dt_sort, constructor, ctor_args) = match &argd.kind {
                TermKind::DtConstructor { constructor, args } => (argd.sort, *constructor, args),
                _ => continue,
            };
            let Some(layouts) = manager.sorts.datatype_ctor_layouts(dt_sort) else {
                continue;
            };
            let ctor_name = manager.resolve_str(constructor).to_string();
            let sel_name = manager.resolve_str(selector).to_string();
            let Some((_, fields)) = layouts.iter().find(|(c, _)| *c == ctor_name) else {
                continue;
            };
            let Some(idx) = fields.iter().position(|(s, _)| *s == sel_name) else {
                continue;
            };
            if let Some(&field_term) = ctor_args.get(idx) {
                reductions.push((t, field_term));
            }
        }
        for (t, field_term) in reductions {
            let key = (t, field_term);
            if self.dt_selector_extra_reduced.contains(&key) {
                continue;
            }
            // A duplicate of what the PRIMARY pass already asserted (the
            // extra binding happened to produce the same field value) is
            // harmless — SAT solvers tolerate a repeated unit clause — so no
            // cross-check against `dt_selector_reduced` is needed here.
            let eq = manager.mk_eq(t, field_term);
            let lit = self.encode(eq, manager);
            self.sat.add_clause([lit]);
            self.dt_selector_extra_reduced.insert(key);
            self.trail.push(TrailOp::DtSelectorExtraReduced {
                term: t,
                field: field_term,
            });
        }
    }

    /// #419 item 1 — inject the ground equality axiom `(= binding1
    /// binding2)` for every DISTINCT pair of same-constructor ctor-term
    /// bindings `check_dt.rs::compute_dt_equality_closure` found within one
    /// equivalence class (`DtEqualityClosure::derived_ctor_eqs`). Always a
    /// SOUND consequence (see that struct's field doc for why) —
    /// unconditionally safe to assert.
    ///
    /// # Why this MUST go through the simplifier, not a bare `encode`
    ///
    /// `C(args1) = C(args2)` for two manifest, SAME-constructor applications
    /// is not itself something EUF's plain congruence closure decomposes —
    /// congruence closure only derives `f(a)=f(b)` FROM `a=b` (forward),
    /// never the reverse (general uninterpreted functions are not
    /// injective, so there is no generic "reverse congruence" rule to
    /// apply). What actually implements datatype-constructor injectivity in
    /// this codebase is a TERM-LEVEL REWRITE:
    /// `oxiz_core::rewrite::datatype::DatatypeRewriter::rewrite_constructor_eq`,
    /// registered in the default simplifier pipeline and applied by
    /// `Solver::assert`/`assert_named` via `self.simplifier.simplify(...)`
    /// BEFORE encoding — it rewrites `C(a1..an) = C(b1..bn)` directly into
    /// `a1=b1 ∧ … ∧ an=bn` (or `false` for two DIFFERENT constructors).
    /// Encoding the raw `Eq(a, b)` node directly (as an earlier version of
    /// this function did) skips that rewrite entirely: the equality becomes
    /// an opaque congruence fact between two "function applications" (the
    /// constructor name as the function symbol, per
    /// `theory_manager::intern_term_for_congruence`), and nothing under it
    /// is ever forced equal — silently losing the very case this function
    /// exists for whenever the repro mentions NO selector application at
    /// all (see the regression test
    /// `three_way_binding_bare_no_selector_forces_pairwise_equality`, which
    /// caught exactly this during verification: a bare `(not (= a e))`
    /// probe, with no `hd`/`tl` anywhere, stayed spuriously `sat` until this
    /// function started routing through `self.simplifier.simplify`).
    ///
    /// Trail-undone via a dedicated dedup set/trail-op
    /// (`dt_ctor_eq_injected` / `TrailOp::DtCtorEqInjected`), the same
    /// idiom as every other per-check-sat axiom-injection pass in this
    /// file.
    pub(super) fn inject_dt_derived_ctor_equalities(
        &mut self,
        derived_ctor_eqs: &[(TermId, TermId)],
        manager: &mut TermManager,
    ) {
        for &(a, b) in derived_ctor_eqs {
            if a == b {
                continue;
            }
            let key = if a.raw() <= b.raw() { (a, b) } else { (b, a) };
            if self.dt_ctor_eq_injected.contains(&key) {
                continue;
            }
            let eq = manager.mk_eq(key.0, key.1);
            let to_encode = if self.config.simplify {
                self.simplifier.simplify(eq, manager)
            } else {
                eq
            };
            match manager.get(to_encode).map(|t| &t.kind) {
                Some(TermKind::True) => {
                    // Rewritten to a tautology (e.g. two nullary-constructor
                    // bindings) — nothing left to assert.
                }
                Some(TermKind::False) => {
                    // The rewrite itself proved these two bindings can NEVER
                    // be equal (different constructors sharing a class) — a
                    // genuine ground conflict. Sound regardless: the rewrite
                    // is a validity-preserving equivalence, so `false` here
                    // means the ORIGINAL ground fact was already
                    // unsatisfiable, not that this pass fabricated anything.
                    if !self.has_false_assertion {
                        self.has_false_assertion = true;
                        self.trail.push(TrailOp::FalseAssertionSet);
                    }
                }
                _ => {
                    // Mirror `Solver::assert`'s pipeline for whatever the
                    // rewrite produced (e.g. the decomposed field-equality
                    // conjunction) so any FURTHER datatype structure it
                    // contains (nested datatypes in the fields) still gets
                    // cover/selector/tester axioms, exactly as if the user
                    // had written this fact directly.
                    let lit = self.encode(to_encode, manager);
                    self.sat.add_clause([lit]);
                    self.add_dt_cover_axioms(to_encode, manager);
                    self.add_dt_selector_reduction_axioms(to_encode, manager);
                    self.add_dt_tester_reduction_axioms(to_encode, manager);
                }
            }
            self.dt_ctor_eq_injected.insert(key);
            self.trail.push(TrailOp::DtCtorEqInjected {
                a: key.0,
                b: key.1,
            });
        }
    }

    /// Assert a named term (for unsat core tracking)
    pub fn assert_named(&mut self, term: TermId, name: &str, manager: &mut TermManager) {
        let index = self.assertions.len();
        self.assertions.push(term);
        self.trail.push(TrailOp::AssertionAdded { index });
        self.invalidate_fp_cache();

        // Check if this is a boolean constant first
        if let Some(t) = manager.get(term) {
            match t.kind {
                TermKind::False => {
                    // Mark that we have a false assertion
                    if !self.has_false_assertion {
                        self.has_false_assertion = true;
                        self.trail.push(TrailOp::FalseAssertionSet);
                    }
                    if self.produce_unsat_cores {
                        let na_index = self.named_assertions.len();
                        self.named_assertions.push(NamedAssertion {
                            term,
                            name: Some(name.to_string()),
                            index: index as u32,
                        });
                        self.trail
                            .push(TrailOp::NamedAssertionAdded { index: na_index });
                    }
                    return;
                }
                TermKind::True => {
                    // True is always satisfied, no need to encode
                    if self.produce_unsat_cores {
                        let na_index = self.named_assertions.len();
                        self.named_assertions.push(NamedAssertion {
                            term,
                            name: Some(name.to_string()),
                            index: index as u32,
                        });
                        self.trail
                            .push(TrailOp::NamedAssertionAdded { index: na_index });
                    }
                    return;
                }
                _ => {}
            }
        }

        // #397 — same ground term-ite elimination as `assert` (this named
        // path skips the simplifier but must not skip the ite lowering).
        let term_to_encode = self.eliminate_term_ites(term, manager);

        // Collect polarity information if polarity-aware encoding is enabled
        if self.polarity_aware {
            self.collect_polarities(term_to_encode, Polarity::Positive, manager);
        }

        // Encode the assertion immediately
        let lit = self.encode(term_to_encode, manager);
        self.sat.add_clause([lit]);

        // Eagerly add arith diseq split for Not(Eq(a,b)) assertions
        self.add_arith_diseq_split(term, manager);

        // #429 — `(>= (str.len s) 0)` for every `str.len` subterm.
        self.add_str_len_domain_axioms(term_to_encode, manager);

        // Ground datatype exhaustiveness at the SAT level (#404 phase 2).
        self.add_dt_cover_axioms(term_to_encode, manager);

        // Ground selector-of-constructor reduction (#406).
        self.add_dt_selector_reduction_axioms(term_to_encode, manager);

        // Ground tester-of-constructor reduction (#406).
        self.add_dt_tester_reduction_axioms(term_to_encode, manager);

        if self.produce_unsat_cores {
            let na_index = self.named_assertions.len();
            self.named_assertions.push(NamedAssertion {
                term,
                name: Some(name.to_string()),
                index: index as u32,
            });
            self.trail
                .push(TrailOp::NamedAssertionAdded { index: na_index });
        }
    }

    /// Get the unsat core (after check() returned Unsat)
    #[must_use]
    pub fn get_unsat_core(&self) -> Option<&UnsatCore> {
        self.unsat_core.as_ref()
    }

    /// Encode a term into SAT clauses using Tseitin transformation
    pub(super) fn encode(&mut self, term: TermId, manager: &mut TermManager) -> Lit {
        // Clone the term data to avoid borrowing issues
        let Some(t) = manager.get(term).cloned() else {
            let var = self.get_or_create_var(term);
            return Lit::pos(var);
        };

        match &t.kind {
            TermKind::True => {
                let var = self.get_or_create_var(manager.mk_true());
                self.sat.add_clause([Lit::pos(var)]);
                Lit::pos(var)
            }
            TermKind::False => {
                let var = self.get_or_create_var(manager.mk_false());
                self.sat.add_clause([Lit::neg(var)]);
                // The literal REPRESENTING `false` must be the one that is
                // *false* in the model — i.e. `var` itself (pinned false above),
                // NOT `¬var` (which evaluates TRUE). The old `Lit::neg(var)`
                // made `false`-as-a-subterm read as TRUE: e.g. `(distinct 5 3)`
                // encodes `¬(5=3)` = `¬false`; with the inverted literal the
                // disequality became unsatisfiable and the assertion spuriously
                // `unsat`. (Top-level `(assert false)` is short-circuited via
                // `has_false_assertion`, which masked this for years.)
                Lit::pos(var)
            }
            TermKind::Var(_) => {
                let var = self.get_or_create_var(term);
                // Track theory terms for model extraction
                let is_int = t.sort == manager.sorts.int_sort;
                let is_real = t.sort == manager.sorts.real_sort;

                if is_int || is_real {
                    self.arith.declare_sort(term, is_int); // #427
                    // Track arithmetic terms
                    if !self.arith_terms.contains(&term) {
                        self.arith_terms.insert(term);
                        self.trail.push(TrailOp::ArithTermAdded { term });
                        // Register with arithmetic solver
                        self.arith.intern(term);
                    }
                } else if let Some(sort) = manager.sorts.get(t.sort)
                    && sort.is_bitvec()
                    && !self.bv_terms.contains(&term)
                {
                    self.bv_terms.insert(term);
                    self.trail.push(TrailOp::BvTermAdded { term });
                    // Register with BV solver if not already registered
                    if let Some(width) = sort.bitvec_width() {
                        self.bv.new_bv(term, width);
                    }
                }
                Lit::pos(var)
            }
            TermKind::Not(arg) => {
                let arg_lit = self.encode(*arg, manager);
                arg_lit.negate()
            }
            TermKind::And(args) => {
                let result_var = self.get_or_create_var(term);
                let result = Lit::pos(result_var);

                let mut arg_lits: Vec<Lit> = Vec::new();
                for &arg in args {
                    arg_lits.push(self.encode(arg, manager));
                }

                // Get polarity for optimization
                let polarity = if self.polarity_aware {
                    self.polarities
                        .get(&term)
                        .copied()
                        .unwrap_or(Polarity::Both)
                } else {
                    Polarity::Both
                };

                // result => all args (needed when result is positive)
                // ~result or arg1, ~result or arg2, ...
                if polarity != Polarity::Negative {
                    for &arg in &arg_lits {
                        self.sat.add_clause([result.negate(), arg]);
                    }
                }

                // all args => result (needed when result is negative)
                // ~arg1 or ~arg2 or ... or result
                if polarity != Polarity::Positive {
                    let mut clause: Vec<Lit> = arg_lits.iter().map(|l| l.negate()).collect();
                    clause.push(result);
                    self.sat.add_clause(clause);
                }

                if std::env::var_os("OXIZ_MBQI_DBG").is_some() && polarity != Polarity::Both {
                    eprintln!(
                        "[mbqi-dbg] encode And {term:?}: polarity {polarity:?} (one Tseitin direction suppressed)"
                    );
                }

                result
            }
            TermKind::Or(args) => {
                let result_var = self.get_or_create_var(term);
                let result = Lit::pos(result_var);

                let mut arg_lits: Vec<Lit> = Vec::new();
                for &arg in args {
                    arg_lits.push(self.encode(arg, manager));
                }

                // Get polarity for optimization
                let polarity = if self.polarity_aware {
                    self.polarities
                        .get(&term)
                        .copied()
                        .unwrap_or(Polarity::Both)
                } else {
                    Polarity::Both
                };

                // result => some arg (needed when result is positive)
                // ~result or arg1 or arg2 or ...
                if polarity != Polarity::Negative {
                    let mut clause: Vec<Lit> = vec![result.negate()];
                    clause.extend(arg_lits.iter().copied());
                    self.sat.add_clause(clause);
                }

                // some arg => result (needed when result is negative)
                // ~arg1 or result, ~arg2 or result, ...
                if polarity != Polarity::Positive {
                    for &arg in &arg_lits {
                        self.sat.add_clause([arg.negate(), result]);
                    }
                }

                result
            }
            TermKind::Xor(lhs, rhs) => {
                let lhs_lit = self.encode(*lhs, manager);
                let rhs_lit = self.encode(*rhs, manager);

                let result_var = self.get_or_create_var(term);
                let result = Lit::pos(result_var);

                // result <=> (lhs xor rhs)
                // result <=> (lhs and ~rhs) or (~lhs and rhs)

                // result => (lhs or rhs)
                self.sat.add_clause([result.negate(), lhs_lit, rhs_lit]);
                // result => (~lhs or ~rhs)
                self.sat
                    .add_clause([result.negate(), lhs_lit.negate(), rhs_lit.negate()]);

                // (lhs and ~rhs) => result
                self.sat.add_clause([lhs_lit.negate(), rhs_lit, result]);
                // (~lhs and rhs) => result
                self.sat.add_clause([lhs_lit, rhs_lit.negate(), result]);

                result
            }
            TermKind::Implies(lhs, rhs) => {
                let lhs_lit = self.encode(*lhs, manager);
                let rhs_lit = self.encode(*rhs, manager);

                let result_var = self.get_or_create_var(term);
                let result = Lit::pos(result_var);

                // result <=> (~lhs or rhs)
                // result => ~lhs or rhs
                self.sat
                    .add_clause([result.negate(), lhs_lit.negate(), rhs_lit]);

                // (~lhs or rhs) => result
                // lhs or result, ~rhs or result
                self.sat.add_clause([lhs_lit, result]);
                self.sat.add_clause([rhs_lit.negate(), result]);

                result
            }
            TermKind::Ite(cond, then_br, else_br) => {
                let cond_lit = self.encode(*cond, manager);
                let then_lit = self.encode(*then_br, manager);
                let else_lit = self.encode(*else_br, manager);

                let result_var = self.get_or_create_var(term);
                let result = Lit::pos(result_var);

                // result <=> (cond ? then : else)
                // cond and result => then
                self.sat
                    .add_clause([cond_lit.negate(), result.negate(), then_lit]);
                // cond and then => result
                self.sat
                    .add_clause([cond_lit.negate(), then_lit.negate(), result]);

                // ~cond and result => else
                self.sat.add_clause([cond_lit, result.negate(), else_lit]);
                // ~cond and else => result
                self.sat.add_clause([cond_lit, else_lit.negate(), result]);

                result
            }
            TermKind::Eq(lhs, rhs) => {
                // Check if this is a boolean equality or theory equality
                let lhs_term = manager.get(*lhs);
                let is_bool_eq = lhs_term.is_some_and(|t| t.sort == manager.sorts.bool_sort);

                if is_bool_eq {
                    // Boolean equality: encode as iff
                    let lhs_lit = self.encode(*lhs, manager);
                    let rhs_lit = self.encode(*rhs, manager);

                    let result_var = self.get_or_create_var(term);
                    let result = Lit::pos(result_var);

                    // result <=> (lhs <=> rhs)
                    // result => (lhs => rhs) and (rhs => lhs)
                    self.sat
                        .add_clause([result.negate(), lhs_lit.negate(), rhs_lit]);
                    self.sat
                        .add_clause([result.negate(), rhs_lit.negate(), lhs_lit]);

                    // (lhs <=> rhs) => result
                    self.sat.add_clause([lhs_lit, rhs_lit, result]);
                    self.sat
                        .add_clause([lhs_lit.negate(), rhs_lit.negate(), result]);

                    result
                } else {
                    // Theory equality: create a fresh boolean variable
                    // Store the constraint for theory propagation
                    let var = self.get_or_create_var(term);
                    self.var_to_constraint
                        .insert(var, Constraint::Eq(*lhs, *rhs));
                    self.trail.push(TrailOp::ConstraintAdded { var });

                    // Track theory variables for model extraction
                    self.track_theory_vars(*lhs, manager);
                    self.track_theory_vars(*rhs, manager);

                    // Pre-parse arithmetic equality for ArithSolver
                    // Only for Int/Real sorts, not BitVec
                    let is_arith = lhs_term.is_some_and(|t| {
                        t.sort == manager.sorts.int_sort || t.sort == manager.sorts.real_sort
                    });
                    if is_arith {
                        // We use Le type as placeholder since equality will be asserted
                        // as both Le and Ge
                        if let Some(parsed) = self.parse_arith_comparison(
                            *lhs,
                            *rhs,
                            ArithConstraintType::Le,
                            term,
                            manager,
                            true,
                        ) {
                            self.var_to_parsed_arith.insert(var, parsed);
                        }

                        // Soundness: unconditionally add the trichotomy split
                        // `Eq(lhs,rhs) OR Lt(lhs,rhs) OR Gt(lhs,rhs)` (a tautology
                        // over Int/Real) right here, at the single choke-point
                        // where EVERY Int/Real equality atom is first given its
                        // Tseitin variable (`get_or_create_var` above hash-conses
                        // by `term`, so this fires exactly once per distinct atom).
                        //
                        // `process_constraint`'s negative-`Eq` branch
                        // (theory_manager.rs) only tells EUF about a disequality
                        // when this atom is later decided FALSE by the SAT
                        // search -- it never asserts `lhs != rhs` into the
                        // arithmetic (simplex) solver, because simplex has no
                        // native disequality primitive. The ONLY thing that makes
                        // a decided-false Eq atom actually constrain arithmetic is
                        // this trichotomy clause forcing `Lt` or `Gt` to become
                        // true by unit propagation once `Eq` is false -- and
                        // `Lt`/`Gt` DO reach the arithmetic solver via the normal
                        // `Constraint::Lt`/`Constraint::Gt` positive branch.
                        //
                        // Previously this split was added only by a fragile,
                        // syntactic AST pre-pass (`add_arith_diseq_split[_recursive]`,
                        // still called separately below/at each `assert`) that
                        // pattern-matches the *literal* shape `Not(Eq(a,b))`
                        // reachable through a hand-picked subset of connectives
                        // (`Not`, `And`, `Or`, the RHS of `Implies`, both branches
                        // of `Ite`). Any Eq atom that can be driven false WITHOUT
                        // that exact AST shape -- e.g. sitting bare as the
                        // ANTECEDENT of an `Implies` (`(=> (= a b) ...)`), as the
                        // CONDITION of an `Ite` (`(ite (= a b) ...)`), or bare
                        // inside an `Or` alongside another true disjunct
                        // (`(or (= a b) flag)` with `flag` true) -- was never
                        // split, so the arithmetic solver could silently pick
                        // `lhs = rhs` even though the SAT layer had decided the
                        // atom false, shipping a model that contradicts the
                        // solver's own Boolean assignment (confirmed false-`sat`,
                        // e.g. `(assert (= (+ X1 X0) (+ X2 X0)))` `(assert (=>
                        // (= X2 X1) (< 5 3)))`). Adding the split at the atom's
                        // single encode choke-point closes the gap for every
                        // syntactic position at once instead of enumerating more
                        // AST shapes into the old walker. The redundant split the
                        // old pass still (harmlessly) re-adds for the shapes it
                        // already covered is a duplicate-clause no-op.
                        //
                        // KNOWN COST (measured, accepted -- see the fix report):
                        // on quantifier-heavy corpus rows this feeds new ground
                        // `Lt`/`Gt` atoms into MBQI's own trigger-matching corpus,
                        // which can noticeably increase instantiation counts (one
                        // corpus row measured 510 -> 2206) and, on a formula that
                        // was already close to the default non-termination guard,
                        // downgrade a confirmed `unsat` to the (always sound)
                        // `unknown`. A LAZY variant (only split an atom once an
                        // accepted candidate model is caught actually violating
                        // it, wired into `check_level`'s main loop) was built and
                        // measured as an alternative: it cut the number of splits
                        // dramatically (27 vs blanket-all-atoms on that same row)
                        // but did NOT reliably converge faster in practice -- on
                        // the same corpus row it still did not reach a verdict
                        // within 120s (vs this eager version's ~27s with the
                        // guard raised), because each lazy split forces an
                        // immediate re-solve that perturbs the CDCL(T)+MBQI
                        // search trajectory on this search-order-sensitive row
                        // regardless of how few splits are actually injected.
                        // Given the eager version is simpler, keeps the fix
                        // entirely inside `encode.rs` (no change to the
                        // core `check_level` loop, one of this codebase's most
                        // sensitive/heavily-guarded paths), and empirically
                        // converges (just slower) rather than stalling, it is the
                        // one kept. `OXIZ_MBQI_GUARD_MS` recovers full behavior
                        // on rows this pushes past the default guard.
                        let eq_lit = Lit::pos(var);
                        let lt_term = manager.mk_lt(*lhs, *rhs);
                        let gt_term = manager.mk_gt(*lhs, *rhs);
                        let lt_lit = self.encode(lt_term, manager);
                        let gt_lit = self.encode(gt_term, manager);
                        self.sat.add_clause([eq_lit, lt_lit, gt_lit]);
                    }

                    Lit::pos(var)
                }
            }
            TermKind::Distinct(args) => {
                // Encode distinct as pairwise disequalities
                // distinct(a,b,c) <=> (a!=b) and (a!=c) and (b!=c)
                if args.len() <= 1 {
                    // trivially true
                    let var = self.get_or_create_var(manager.mk_true());
                    return Lit::pos(var);
                }

                let result_var = self.get_or_create_var(term);
                let result = Lit::pos(result_var);

                let mut diseq_lits = Vec::new();
                for i in 0..args.len() {
                    for j in (i + 1)..args.len() {
                        let eq = manager.mk_eq(args[i], args[j]);
                        let eq_lit = self.encode(eq, manager);
                        diseq_lits.push(eq_lit.negate());
                    }
                }

                // result => all disequalities
                for &diseq in &diseq_lits {
                    self.sat.add_clause([result.negate(), diseq]);
                }

                // all disequalities => result
                let mut clause: Vec<Lit> = diseq_lits.iter().map(|l| l.negate()).collect();
                clause.push(result);
                self.sat.add_clause(clause);

                result
            }
            TermKind::Let { bindings, body } => {
                // SMT-LIB `let`-bound names are eagerly substituted into the body
                // during parsing (see `parse_let`), so a *parsed* `Let` never
                // reaches the encoder. A `Let` built directly through the typed
                // API can still carry unsubstituted `Var(name)` occurrences in
                // its body, so substitute them here before encoding — otherwise
                // the bindings would be silently dropped (the old behaviour) and
                // every bound name left a fresh, unconstrained variable, which is
                // unsound: e.g. `(= (let ((y (+ c c))) (+ y 1)) (+ (+ c c) 2))`
                // (`1 = 2`, unsat) would encode an opaque `y` and report `sat`
                // (#345). `let` is non-recursive, so each value is substituted as
                // a whole and there is no capture to avoid here.
                let mut subst: FxHashMap<TermId, TermId> = FxHashMap::default();
                for (name, value) in bindings.iter() {
                    let sort = manager
                        .get(*value)
                        .map_or(manager.sorts.bool_sort, |v| v.sort);
                    let name = manager.resolve_str(*name).to_string();
                    let var = manager.mk_var(&name, sort);
                    subst.insert(var, *value);
                }
                let expanded = if subst.is_empty() {
                    *body
                } else {
                    manager.substitute(*body, &subst)
                };
                self.encode(expanded, manager)
            }
            // Theory atoms (arithmetic, bitvec, arrays, UF)
            // These get fresh boolean variables - the theory solver handles the semantics
            TermKind::IntConst(_) | TermKind::RealConst(_) | TermKind::BitVecConst { .. } => {
                // Constants are theory terms, not boolean formulas
                // Should not appear at top level in boolean context
                let var = self.get_or_create_var(term);
                Lit::pos(var)
            }
            TermKind::Neg(_)
            | TermKind::Add(_)
            | TermKind::Sub(_, _)
            | TermKind::Mul(_)
            | TermKind::Div(_, _)
            | TermKind::Mod(_, _) => {
                // Arithmetic terms - should not appear at boolean top level
                let var = self.get_or_create_var(term);
                Lit::pos(var)
            }
            TermKind::Lt(lhs, rhs) => {
                // Arithmetic predicate: lhs < rhs
                let var = self.get_or_create_var(term);
                self.var_to_constraint
                    .insert(var, Constraint::Lt(*lhs, *rhs));
                self.trail.push(TrailOp::ConstraintAdded { var });
                // Parse and store linear constraint for ArithSolver
                if let Some(parsed) =
                    self.parse_arith_comparison(*lhs, *rhs, ArithConstraintType::Lt, term, manager, true)
                {
                    self.var_to_parsed_arith.insert(var, parsed);
                }
                // Track theory variables for model extraction
                self.track_theory_vars(*lhs, manager);
                self.track_theory_vars(*rhs, manager);
                Lit::pos(var)
            }
            TermKind::Le(lhs, rhs) => {
                // Arithmetic predicate: lhs <= rhs
                let var = self.get_or_create_var(term);
                self.var_to_constraint
                    .insert(var, Constraint::Le(*lhs, *rhs));
                self.trail.push(TrailOp::ConstraintAdded { var });
                // Parse and store linear constraint for ArithSolver
                if let Some(parsed) =
                    self.parse_arith_comparison(*lhs, *rhs, ArithConstraintType::Le, term, manager, true)
                {
                    self.var_to_parsed_arith.insert(var, parsed);
                }
                // Track theory variables for model extraction
                self.track_theory_vars(*lhs, manager);
                self.track_theory_vars(*rhs, manager);
                Lit::pos(var)
            }
            TermKind::Gt(lhs, rhs) => {
                // Arithmetic predicate: lhs > rhs
                let var = self.get_or_create_var(term);
                self.var_to_constraint
                    .insert(var, Constraint::Gt(*lhs, *rhs));
                self.trail.push(TrailOp::ConstraintAdded { var });
                // Parse and store linear constraint for ArithSolver
                if let Some(parsed) =
                    self.parse_arith_comparison(*lhs, *rhs, ArithConstraintType::Gt, term, manager, true)
                {
                    self.var_to_parsed_arith.insert(var, parsed);
                }
                // Track theory variables for model extraction
                self.track_theory_vars(*lhs, manager);
                self.track_theory_vars(*rhs, manager);
                Lit::pos(var)
            }
            TermKind::Ge(lhs, rhs) => {
                // Arithmetic predicate: lhs >= rhs
                let var = self.get_or_create_var(term);
                self.var_to_constraint
                    .insert(var, Constraint::Ge(*lhs, *rhs));
                self.trail.push(TrailOp::ConstraintAdded { var });
                // Parse and store linear constraint for ArithSolver
                if let Some(parsed) =
                    self.parse_arith_comparison(*lhs, *rhs, ArithConstraintType::Ge, term, manager, true)
                {
                    self.var_to_parsed_arith.insert(var, parsed);
                }
                // Track theory variables for model extraction
                self.track_theory_vars(*lhs, manager);
                self.track_theory_vars(*rhs, manager);
                Lit::pos(var)
            }
            TermKind::BvConcat(_, _)
            | TermKind::BvExtract { .. }
            | TermKind::BvNot(_)
            | TermKind::BvAnd(_, _)
            | TermKind::BvOr(_, _)
            | TermKind::BvXor(_, _)
            | TermKind::BvAdd(_, _)
            | TermKind::BvSub(_, _)
            | TermKind::BvMul(_, _)
            | TermKind::BvShl(_, _)
            | TermKind::BvLshr(_, _)
            | TermKind::BvAshr(_, _) => {
                // Bitvector terms - should not appear at boolean top level
                let var = self.get_or_create_var(term);
                Lit::pos(var)
            }
            TermKind::BvUdiv(_, _)
            | TermKind::BvSdiv(_, _)
            | TermKind::BvUrem(_, _)
            | TermKind::BvSrem(_, _) => {
                // Bitvector arithmetic terms (division/remainder)
                // Mark that we have arithmetic BV ops for conflict checking
                self.has_bv_arith_ops = true;
                let var = self.get_or_create_var(term);
                Lit::pos(var)
            }
            TermKind::BvUlt(lhs, rhs) => {
                // Bitvector unsigned less-than: treat as integer comparison
                let var = self.get_or_create_var(term);
                self.var_to_constraint
                    .insert(var, Constraint::Lt(*lhs, *rhs));
                self.trail.push(TrailOp::ConstraintAdded { var });
                // Parse as arithmetic constraint (bitvector as bounded integer)
                if let Some(parsed) =
                    self.parse_arith_comparison(*lhs, *rhs, ArithConstraintType::Lt, term, manager, false)
                {
                    self.var_to_parsed_arith.insert(var, parsed);
                }
                // Track theory variables for model extraction
                self.track_theory_vars(*lhs, manager);
                self.track_theory_vars(*rhs, manager);
                Lit::pos(var)
            }
            TermKind::BvUle(lhs, rhs) => {
                // Bitvector unsigned less-than-or-equal: treat as integer comparison
                let var = self.get_or_create_var(term);
                self.var_to_constraint
                    .insert(var, Constraint::Le(*lhs, *rhs));
                self.trail.push(TrailOp::ConstraintAdded { var });
                if let Some(parsed) =
                    self.parse_arith_comparison(*lhs, *rhs, ArithConstraintType::Le, term, manager, false)
                {
                    self.var_to_parsed_arith.insert(var, parsed);
                }
                // Track theory variables for model extraction
                self.track_theory_vars(*lhs, manager);
                self.track_theory_vars(*rhs, manager);
                Lit::pos(var)
            }
            TermKind::BvSlt(lhs, rhs) => {
                // Bitvector SIGNED less-than.
                //
                // Deliberately NOT fed into `parse_arith_comparison` (unlike the
                // BvUlt/BvUle unsigned siblings below): `extract_linear_terms`
                // treats a `BitVecConst` as its raw bit pattern's UNSIGNED
                // magnitude (`value.to_i128()`, no two's-complement
                // reinterpretation) and a BV variable as an opaque
                // arbitrary-sign real/int variable. That mapping is exactly
                // right for the unsigned comparators (bit pattern == unsigned
                // magnitude, no ambiguity) but is UNSOUND here: a constant
                // with its sign bit set (e.g. 4-bit `0xd` means -3, not 13)
                // gets asserted to the arithmetic solver as its large
                // unsigned value, and there is no sound way to correct a
                // variable operand's contribution either (its sign is not
                // known at parse time). Feeding this wrong constraint into
                // the arithmetic solver let it derive a conflict from a
                // premise that does not hold under signed semantics whenever
                // that spurious "13 < x"-style fact combined with any other
                // asserted bound (signed or unsigned) — a spurious UNSAT
                // (confirmed via z3-differential: `(bvslt #xd x) (bvslt x
                // #x3)` on 4-bit BVs, i.e. `-3 <s x <s 3`, wrongly reported
                // Unsat). The embedded bit-blaster's `assert_slt`
                // (theory_manager.rs) already encodes signed order exactly
                // (sign-bit case split + unsigned compare on equal signs) and
                // is independently verified sound in isolation, so it alone
                // is the source of truth for signed comparisons.
                let var = self.get_or_create_var(term);
                self.var_to_constraint
                    .insert(var, Constraint::Lt(*lhs, *rhs));
                self.trail.push(TrailOp::ConstraintAdded { var });
                // Track theory variables for model extraction
                self.track_theory_vars(*lhs, manager);
                self.track_theory_vars(*rhs, manager);
                Lit::pos(var)
            }
            TermKind::BvSle(lhs, rhs) => {
                // Bitvector SIGNED less-than-or-equal — see `BvSlt` above for
                // why this is deliberately NOT routed through
                // `parse_arith_comparison`.
                let var = self.get_or_create_var(term);
                self.var_to_constraint
                    .insert(var, Constraint::Le(*lhs, *rhs));
                self.trail.push(TrailOp::ConstraintAdded { var });
                // Track theory variables for model extraction
                self.track_theory_vars(*lhs, manager);
                self.track_theory_vars(*rhs, manager);
                Lit::pos(var)
            }
            TermKind::Select(_, _) | TermKind::Store(_, _, _) => {
                // Array operations - theory terms
                let var = self.get_or_create_var(term);
                Lit::pos(var)
            }
            TermKind::Apply { .. } => {
                // Uninterpreted function application - theory term
                let var = self.get_or_create_var(term);
                // Register Bool-valued function applications as theory
                // constraints so that EUF congruence closure can detect
                // conflicts when the SAT solver assigns opposite polarities
                // to congruent applications (e.g., t(m)=true, t(co)=false,
                // but m=co implies t(m)=t(co)).
                if t.sort == manager.sorts.bool_sort {
                    self.var_to_constraint
                        .insert(var, Constraint::BoolApp(term));
                    self.trail.push(TrailOp::ConstraintAdded { var });
                }
                Lit::pos(var)
            }
            TermKind::Forall { .. } => {
                // Universal quantifiers are encoded as a single boolean proxy
                // literal; instantiation is the clean-room quantifier engine's
                // job (`clean_mbqi`), which rebuilds its own ground-term index
                // and pattern set from the asserted formula on each solve. No
                // encode-time MBQI/e-matching registration is needed (the legacy
                // `mbqi/` subsystem that consumed it was removed, #262).
                self.has_quantifiers = true;
                let var = self.get_or_create_var(term);
                Lit::pos(var)
            }
            TermKind::Exists { .. } => {
                // Existential quantifiers are likewise encoded as a boolean
                // proxy; the clean engine handles them from the assertion set.
                self.has_quantifiers = true;
                let var = self.get_or_create_var(term);
                Lit::pos(var)
            }
            // String operations - theory terms and predicates
            TermKind::StringLit(_)
            | TermKind::StrConcat(_, _)
            | TermKind::StrLen(_)
            | TermKind::StrSubstr(_, _, _)
            | TermKind::StrAt(_, _)
            | TermKind::StrReplace(_, _, _)
            | TermKind::StrReplaceAll(_, _, _)
            | TermKind::StrToInt(_)
            | TermKind::IntToStr(_)
            | TermKind::StrInRe(_, _) => {
                // String terms - theory solver handles these
                let var = self.get_or_create_var(term);
                Lit::pos(var)
            }
            TermKind::StrContains(_, _)
            | TermKind::StrPrefixOf(_, _)
            | TermKind::StrSuffixOf(_, _)
            | TermKind::StrIndexOf(_, _, _) => {
                // String predicates - theory atoms
                let var = self.get_or_create_var(term);
                Lit::pos(var)
            }
            // Floating-point constants and special values
            TermKind::FpLit { .. }
            | TermKind::FpPlusInfinity { .. }
            | TermKind::FpMinusInfinity { .. }
            | TermKind::FpPlusZero { .. }
            | TermKind::FpMinusZero { .. }
            | TermKind::FpNaN { .. } => {
                // FP constants - theory terms
                let var = self.get_or_create_var(term);
                Lit::pos(var)
            }
            // Floating-point operations
            TermKind::FpAbs(_)
            | TermKind::FpNeg(_)
            | TermKind::FpSqrt(_, _)
            | TermKind::FpRoundToIntegral(_, _)
            | TermKind::FpAdd(_, _, _)
            | TermKind::FpSub(_, _, _)
            | TermKind::FpMul(_, _, _)
            | TermKind::FpDiv(_, _, _)
            | TermKind::FpRem(_, _)
            | TermKind::FpMin(_, _)
            | TermKind::FpMax(_, _)
            | TermKind::FpFma(_, _, _, _) => {
                // FP operations - theory terms
                let var = self.get_or_create_var(term);
                Lit::pos(var)
            }
            // Floating-point predicates
            TermKind::FpLeq(_, _)
            | TermKind::FpLt(_, _)
            | TermKind::FpGeq(_, _)
            | TermKind::FpGt(_, _)
            | TermKind::FpEq(_, _)
            | TermKind::FpIsNormal(_)
            | TermKind::FpIsSubnormal(_)
            | TermKind::FpIsZero(_)
            | TermKind::FpIsInfinite(_)
            | TermKind::FpIsNaN(_)
            | TermKind::FpIsNegative(_)
            | TermKind::FpIsPositive(_) => {
                // FP predicates - theory atoms that return bool
                let var = self.get_or_create_var(term);
                Lit::pos(var)
            }
            // Floating-point conversions
            TermKind::FpToFp { .. }
            | TermKind::FpToSBV { .. }
            | TermKind::FpToUBV { .. }
            | TermKind::FpToReal(_)
            | TermKind::RealToFp { .. }
            | TermKind::SBVToFp { .. }
            | TermKind::UBVToFp { .. } => {
                // FP conversions - theory terms
                let var = self.get_or_create_var(term);
                Lit::pos(var)
            }
            // Datatype operations
            TermKind::DtConstructor { .. }
            | TermKind::DtTester { .. }
            | TermKind::DtSelector { .. } => {
                // Datatype operations - theory terms
                let var = self.get_or_create_var(term);
                Lit::pos(var)
            }
            // Match expressions on datatypes
            TermKind::Match { .. } => {
                // Match expressions - theory terms
                let var = self.get_or_create_var(term);
                Lit::pos(var)
            }
        }
    }

    /// Scan all Constraint::Eq entries in var_to_constraint that are currently
    /// assigned False by the SAT model and add arithmetic splits `(lhs < rhs)
    /// OR (lhs > rhs)` for each.  This ensures ArithSolver knows about
    /// disequalities that arise from SAT-level implication propagation (e.g.
    /// from MBQI-generated instantiations like `(=> (= f(a) f(b)) (= a b))`).
    #[allow(dead_code)]
    pub(super) fn add_arith_diseq_splits_for_sat_model(&mut self, manager: &mut TermManager) {
        use super::types::Constraint;
        use oxiz_sat::LBool;

        let pairs: Vec<(TermId, TermId)> = self
            .var_to_constraint
            .iter()
            .filter_map(|(&var, constraint)| {
                if let Constraint::Eq(lhs, rhs) = constraint {
                    // Only Int or Real sorts
                    let lhs_is_numeric = manager.get(*lhs).is_some_and(|lt| {
                        lt.sort == manager.sorts.int_sort || lt.sort == manager.sorts.real_sort
                    });
                    if lhs_is_numeric && self.sat.model_value(var) == LBool::False {
                        Some((*lhs, *rhs))
                    } else {
                        None
                    }
                } else {
                    None
                }
            })
            .collect();

        for (lhs, rhs) in pairs {
            let lt_term = manager.mk_lt(lhs, rhs);
            let gt_term = manager.mk_gt(lhs, rhs);
            // Only add if the clause isn't already a tautology or unit-forced
            let lt_lit = self.encode(lt_term, manager);
            let gt_lit = self.encode(gt_term, manager);
            self.sat.add_clause([lt_lit, gt_lit]);
        }
    }

    /// When a MBQI instantiation result is `(not (= a b))` where a and b have
    /// Int sort, add the arithmetic split `(a < b) OR (a > b)` as a SAT clause.
    /// This ensures the ArithSolver knows about the disequality and doesn't
    /// assign both a and b to equal values.
    pub(super) fn add_arith_diseq_split(&mut self, term: TermId, manager: &mut TermManager) {
        let mut visited = FxHashSet::default();
        self.add_arith_diseq_split_recursive(term, manager, &mut visited);
    }


    /// Recursively walk a term to find all `Not(Eq(a, b))` sub-terms with
    /// arithmetic sorts and add the split `(a < b) OR (a > b)` for each.
    ///
    /// This handles MBQI instantiation results that are implications like
    /// `(=> guard (not (= a b)))` where the disequality is nested inside
    /// the formula rather than at the top level.
    fn add_arith_diseq_split_recursive(
        &mut self,
        term: TermId,
        manager: &mut TermManager,
        visited: &mut FxHashSet<TermId>,
    ) {
        if !visited.insert(term) {
            return;
        }

        let Some(t) = manager.get(term).cloned() else {
            return;
        };

        match &t.kind {
            TermKind::Not(inner) => {
                let inner_id = *inner;
                if let Some(inner_t) = manager.get(inner_id).cloned() {
                    if let TermKind::Eq(lhs, rhs) = &inner_t.kind {
                        let lhs_is_numeric = manager.get(*lhs).is_some_and(|lt| {
                            lt.sort == manager.sorts.int_sort || lt.sort == manager.sorts.real_sort
                        });
                        if lhs_is_numeric {
                            let (l, r) = (*lhs, *rhs);
                            // Add the SOUND trichotomy `Eq(a,b) OR Lt(a,b) OR
                            // Gt(a,b)` — a tautology over Int/Real — NOT the bare
                            // `Lt OR Gt` disequality. The bare split forces a≠b
                            // unconditionally, which is unsound at any non-positive
                            // polarity: this recursion is syntactic (it walks
                            // through `Not`/`Implies`-rhs/`Ite`/`Or` blind to how
                            // many negations enclose the `Not(Eq)`), so a
                            // `Not(Eq(x,0))` sitting at EFFECTIVE positive-equality
                            // polarity — e.g. `(not (=> L (not (= x 0))))` = `L ∧
                            // (x = 0)` — would get `x≠0` forced and conflict with
                            // the formula's `x = 0` → spurious `unsat` (verus-fork
                            // 2026-06-17: `ensures x != 0` verified vacuously).
                            // The trichotomy keeps the intent (when SAT sets the Eq
                            // atom false, it derives `Lt OR Gt` for the ArithSolver)
                            // while adding NO constraint of its own.
                            let eq_lit = self.encode(inner_id, manager);
                            let lt_term = manager.mk_lt(l, r);
                            let gt_term = manager.mk_gt(l, r);
                            let lt_lit = self.encode(lt_term, manager);
                            let gt_lit = self.encode(gt_term, manager);
                            self.sat.add_clause([eq_lit, lt_lit, gt_lit]);
                        }
                    }
                }
                // Also recurse into the inner term
                self.add_arith_diseq_split_recursive(inner_id, manager, visited);
            }
            TermKind::And(args) => {
                let args_clone: Vec<TermId> = args.iter().copied().collect();
                for arg in args_clone {
                    self.add_arith_diseq_split_recursive(arg, manager, visited);
                }
            }
            TermKind::Or(args) => {
                let args_clone: Vec<TermId> = args.iter().copied().collect();
                for arg in args_clone {
                    self.add_arith_diseq_split_recursive(arg, manager, visited);
                }
            }
            TermKind::Implies(_, rhs) => {
                // Recurse into the consequent -- that's where the disequality
                // typically lives in quantifier instantiation lemmas
                let rhs_id = *rhs;
                self.add_arith_diseq_split_recursive(rhs_id, manager, visited);
            }
            TermKind::Ite(_, then_br, else_br) => {
                let (t, e) = (*then_br, *else_br);
                self.add_arith_diseq_split_recursive(t, manager, visited);
                self.add_arith_diseq_split_recursive(e, manager, visited);
            }
            _ => {}
        }
    }
}
