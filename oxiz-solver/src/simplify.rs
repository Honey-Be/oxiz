//! Formula simplification and preprocessing
//!
//! This module provides simplification passes that run before the main solver
//! to reduce problem size and improve solving performance.

// Allow these clippy lints for simplification code patterns
#![allow(clippy::map_entry)] // contains_key + insert pattern used for clarity
#![allow(clippy::only_used_in_recursion)] // recursive simplification intentional
#![allow(clippy::for_kv_map)] // iterating map keys with values pattern

#[allow(unused_imports)]
use crate::prelude::*;
use num_bigint::BigInt;
use num_traits::Zero;
use oxiz_core::ast::{TermId, TermKind, TermManager};

/// The value of `t` if it is an integer constant.
fn arith_int_const(manager: &TermManager, t: TermId) -> Option<BigInt> {
    match manager.get(t).map(|x| x.kind.clone()) {
        Some(TermKind::IntConst(n)) => Some(n),
        _ => None,
    }
}

/// Whether `t` is the arithmetic constant zero (Int or Real).
fn arith_is_zero(manager: &TermManager, t: TermId) -> bool {
    match manager.get(t).map(|x| x.kind.clone()) {
        Some(TermKind::IntConst(n)) => n.is_zero(),
        Some(TermKind::RealConst(r)) => r.is_zero(),
        _ => false,
    }
}

/// Simplification statistics
#[derive(Debug, Clone, Default)]
pub struct SimplifyStats {
    /// Number of constant propagations performed
    pub const_propagations: usize,
    /// Number of terms eliminated
    pub terms_eliminated: usize,
    /// Number of trivial equations detected
    pub trivial_equalities: usize,
    /// Number of contradictions found
    pub contradictions_found: usize,
    /// Number of nested operations flattened
    pub operations_flattened: usize,
    /// Number of duplicate literals eliminated
    pub duplicates_eliminated: usize,
    /// Number of tautologies detected
    pub tautologies_detected: usize,
}

/// Context-aware formula simplifier
///
/// Performs simplification passes including:
/// - Constant propagation
/// - Boolean simplification
/// - Trivial equality elimination
/// - Contradiction detection
#[derive(Debug)]
pub struct Simplifier {
    /// Cache of simplified terms
    cache: FxHashMap<TermId, TermId>,
    /// Statistics
    stats: SimplifyStats,
}

impl Simplifier {
    /// Create a new simplifier
    #[must_use]
    pub fn new() -> Self {
        Self {
            cache: FxHashMap::default(),
            stats: SimplifyStats::default(),
        }
    }

    /// Get simplification statistics
    #[must_use]
    #[allow(dead_code)]
    pub fn stats(&self) -> &SimplifyStats {
        &self.stats
    }

    /// Reset the simplifier state
    #[allow(dead_code)]
    pub fn reset(&mut self) {
        self.cache.clear();
        self.stats = SimplifyStats::default();
    }

    /// Simplify a term
    ///
    /// Returns a simplified version of the term, or the original if no simplification applies
    pub fn simplify(&mut self, term: TermId, manager: &mut TermManager) -> TermId {
        // Check cache first
        if let Some(&simplified) = self.cache.get(&term) {
            return simplified;
        }

        let result = self.simplify_impl(term, manager);
        self.cache.insert(term, result);
        result
    }

    fn simplify_impl(&mut self, term: TermId, manager: &mut TermManager) -> TermId {
        let Some(t) = manager.get(term).cloned() else {
            return term;
        };

        match &t.kind {
            // Boolean simplifications
            TermKind::True | TermKind::False => term,

            TermKind::Not(arg) => {
                let arg_simplified = self.simplify(*arg, manager);

                // not(true) => false
                if let Some(arg_term) = manager.get(arg_simplified) {
                    if matches!(arg_term.kind, TermKind::True) {
                        self.stats.const_propagations += 1;
                        return manager.mk_false();
                    }
                    // not(false) => true
                    if matches!(arg_term.kind, TermKind::False) {
                        self.stats.const_propagations += 1;
                        return manager.mk_true();
                    }
                    // not(not(x)) => x
                    if let TermKind::Not(inner) = arg_term.kind {
                        self.stats.terms_eliminated += 1;
                        return inner;
                    }
                }

                if arg_simplified == *arg {
                    term
                } else {
                    manager.mk_not(arg_simplified)
                }
            }

            TermKind::And(args) => {
                let mut simplified_args = Vec::new();
                let mut seen = FxHashMap::default();

                for &arg in args.iter() {
                    let simplified = self.simplify(arg, manager);

                    // and(..., false, ...) => false
                    if let Some(arg_term) = manager.get(simplified) {
                        if matches!(arg_term.kind, TermKind::False) {
                            self.stats.const_propagations += 1;
                            return manager.mk_false();
                        }
                        // Skip true literals
                        if matches!(arg_term.kind, TermKind::True) {
                            self.stats.terms_eliminated += 1;
                            continue;
                        }

                        // Flatten nested ANDs: and(and(a, b), c) => and(a, b, c)
                        if let TermKind::And(nested_args) = &arg_term.kind {
                            self.stats.operations_flattened += 1;
                            let nested_args_cloned = nested_args.clone();
                            for &nested_arg in &nested_args_cloned {
                                let nested_simplified = self.simplify(nested_arg, manager);
                                if !seen.contains_key(&nested_simplified) {
                                    seen.insert(nested_simplified, ());
                                    simplified_args.push(nested_simplified);
                                } else {
                                    self.stats.duplicates_eliminated += 1;
                                }
                            }
                            continue;
                        }
                    }

                    // Check for contradictions: and(x, not(x)) => false
                    if let Some(arg_term) = manager.get(simplified)
                        && let TermKind::Not(inner) = arg_term.kind
                        && (simplified_args.contains(&inner) || seen.contains_key(&inner))
                    {
                        self.stats.contradictions_found += 1;
                        return manager.mk_false();
                    }
                    // Check if we already have not(arg) in the list
                    let neg = manager.mk_not(simplified);
                    if simplified_args.contains(&neg) || seen.contains_key(&neg) {
                        self.stats.contradictions_found += 1;
                        return manager.mk_false();
                    }

                    // Eliminate duplicates
                    if !seen.contains_key(&simplified) {
                        seen.insert(simplified, ());
                        simplified_args.push(simplified);
                    } else {
                        self.stats.duplicates_eliminated += 1;
                    }
                }

                match simplified_args.len() {
                    0 => {
                        self.stats.const_propagations += 1;
                        manager.mk_true()
                    }
                    1 => {
                        self.stats.terms_eliminated += 1;
                        simplified_args[0]
                    }
                    _ => manager.mk_and(simplified_args),
                }
            }

            TermKind::Or(args) => {
                let mut simplified_args = Vec::new();
                let mut seen = FxHashMap::default();

                for &arg in args.iter() {
                    let simplified = self.simplify(arg, manager);

                    // or(..., true, ...) => true
                    if let Some(arg_term) = manager.get(simplified) {
                        if matches!(arg_term.kind, TermKind::True) {
                            self.stats.const_propagations += 1;
                            return manager.mk_true();
                        }
                        // Skip false literals
                        if matches!(arg_term.kind, TermKind::False) {
                            self.stats.terms_eliminated += 1;
                            continue;
                        }

                        // Flatten nested ORs: or(or(a, b), c) => or(a, b, c)
                        if let TermKind::Or(nested_args) = &arg_term.kind {
                            self.stats.operations_flattened += 1;
                            let nested_args_cloned = nested_args.clone();
                            for &nested_arg in &nested_args_cloned {
                                let nested_simplified = self.simplify(nested_arg, manager);
                                if !seen.contains_key(&nested_simplified) {
                                    seen.insert(nested_simplified, ());
                                    simplified_args.push(nested_simplified);
                                } else {
                                    self.stats.duplicates_eliminated += 1;
                                }
                            }
                            continue;
                        }
                    }

                    // Check for tautologies: or(x, not(x)) => true
                    if let Some(arg_term) = manager.get(simplified)
                        && let TermKind::Not(inner) = arg_term.kind
                        && (simplified_args.contains(&inner) || seen.contains_key(&inner))
                    {
                        self.stats.tautologies_detected += 1;
                        return manager.mk_true();
                    }
                    // Check if we already have not(arg) in the list
                    let neg = manager.mk_not(simplified);
                    if simplified_args.contains(&neg) || seen.contains_key(&neg) {
                        self.stats.tautologies_detected += 1;
                        return manager.mk_true();
                    }

                    // Eliminate duplicates
                    if !seen.contains_key(&simplified) {
                        seen.insert(simplified, ());
                        simplified_args.push(simplified);
                    } else {
                        self.stats.duplicates_eliminated += 1;
                    }
                }

                match simplified_args.len() {
                    0 => {
                        self.stats.const_propagations += 1;
                        manager.mk_false()
                    }
                    1 => {
                        self.stats.terms_eliminated += 1;
                        simplified_args[0]
                    }
                    _ => manager.mk_or(simplified_args),
                }
            }

            TermKind::Implies(lhs, rhs) => {
                let lhs_simplified = self.simplify(*lhs, manager);
                let rhs_simplified = self.simplify(*rhs, manager);

                // false => x  =  true
                if let Some(lhs_term) = manager.get(lhs_simplified)
                    && matches!(lhs_term.kind, TermKind::False)
                {
                    self.stats.const_propagations += 1;
                    return manager.mk_true();
                }

                // true => x  =  x
                if let Some(lhs_term) = manager.get(lhs_simplified)
                    && matches!(lhs_term.kind, TermKind::True)
                {
                    self.stats.terms_eliminated += 1;
                    return rhs_simplified;
                }

                // x => true  =  true
                if let Some(rhs_term) = manager.get(rhs_simplified)
                    && matches!(rhs_term.kind, TermKind::True)
                {
                    self.stats.const_propagations += 1;
                    return manager.mk_true();
                }

                // x => false  =  not(x)
                if let Some(rhs_term) = manager.get(rhs_simplified)
                    && matches!(rhs_term.kind, TermKind::False)
                {
                    self.stats.terms_eliminated += 1;
                    return manager.mk_not(lhs_simplified);
                }

                if lhs_simplified == *lhs && rhs_simplified == *rhs {
                    term
                } else {
                    manager.mk_implies(lhs_simplified, rhs_simplified)
                }
            }

            TermKind::Ite(cond, then_br, else_br) => {
                let cond_simplified = self.simplify(*cond, manager);
                let then_simplified = self.simplify(*then_br, manager);
                let else_simplified = self.simplify(*else_br, manager);

                // ite(true, x, y) => x
                if let Some(cond_term) = manager.get(cond_simplified)
                    && matches!(cond_term.kind, TermKind::True)
                {
                    self.stats.const_propagations += 1;
                    return then_simplified;
                }

                // ite(false, x, y) => y
                if let Some(cond_term) = manager.get(cond_simplified)
                    && matches!(cond_term.kind, TermKind::False)
                {
                    self.stats.const_propagations += 1;
                    return else_simplified;
                }

                // ite(c, x, x) => x
                if then_simplified == else_simplified {
                    self.stats.terms_eliminated += 1;
                    return then_simplified;
                }

                if cond_simplified == *cond
                    && then_simplified == *then_br
                    && else_simplified == *else_br
                {
                    term
                } else {
                    manager.mk_ite(cond_simplified, then_simplified, else_simplified)
                }
            }

            TermKind::Eq(lhs, rhs) => {
                let lhs_simplified = self.simplify(*lhs, manager);
                let rhs_simplified = self.simplify(*rhs, manager);

                // x = x  =>  true
                if lhs_simplified == rhs_simplified {
                    self.stats.trivial_equalities += 1;
                    return manager.mk_true();
                }

                // Check for constant simplifications
                if let (Some(lhs_term), Some(rhs_term)) =
                    (manager.get(lhs_simplified), manager.get(rhs_simplified))
                {
                    // Handle datatype constructor equalities:
                    // C1(args) = C2(args') => false (different constructors)
                    // C(args) = C(args') => args = args' (same constructor)
                    if let (
                        TermKind::DtConstructor {
                            constructor: lhs_con,
                            args: lhs_args,
                        },
                        TermKind::DtConstructor {
                            constructor: rhs_con,
                            args: rhs_args,
                        },
                    ) = (&lhs_term.kind, &rhs_term.kind)
                    {
                        if lhs_con != rhs_con {
                            // Different constructors cannot be equal
                            self.stats.contradictions_found += 1;
                            return manager.mk_false();
                        } else if lhs_args.is_empty() && rhs_args.is_empty() {
                            // Same nullary constructor
                            self.stats.trivial_equalities += 1;
                            return manager.mk_true();
                        } else if lhs_args.len() == rhs_args.len() {
                            // Same constructor: decompose to field equalities.
                            // Re-simplify each created equality — the args were
                            // already simplified, but the fresh `=` node was
                            // not, so a NESTED constructor equality (e.g.
                            // `succ(n) = zero` out of `succ(succ n) = succ
                            // zero`) would otherwise stay an opaque atom and
                            // the clash go unseen (spurious sat). Structural
                            // descent, so the recursion terminates.
                            self.stats.terms_eliminated += 1;
                            let lhs_args = lhs_args.clone();
                            let rhs_args = rhs_args.clone();
                            let equalities: Vec<_> = lhs_args
                                .iter()
                                .zip(rhs_args.iter())
                                .map(|(&a, &b)| {
                                    let eq = manager.mk_eq(a, b);
                                    self.simplify(eq, manager)
                                })
                                .collect();
                            return manager.mk_and(equalities);
                        }
                    }

                    // Handle boolean equalities with constants:
                    // x = true  => x
                    // x = false => NOT x
                    // true = x  => x
                    // false = x => NOT x
                    if lhs_term.sort == manager.sorts.bool_sort {
                        match (&lhs_term.kind, &rhs_term.kind) {
                            // Contradictory constants
                            (TermKind::True, TermKind::False)
                            | (TermKind::False, TermKind::True) => {
                                self.stats.contradictions_found += 1;
                                return manager.mk_false();
                            }
                            // Same constants
                            (TermKind::True, TermKind::True)
                            | (TermKind::False, TermKind::False) => {
                                self.stats.trivial_equalities += 1;
                                return manager.mk_true();
                            }
                            // x = true => x
                            (_, TermKind::True) => {
                                self.stats.terms_eliminated += 1;
                                return lhs_simplified;
                            }
                            // x = false => NOT x
                            (_, TermKind::False) => {
                                self.stats.terms_eliminated += 1;
                                return manager.mk_not(lhs_simplified);
                            }
                            // true = x => x
                            (TermKind::True, _) => {
                                self.stats.terms_eliminated += 1;
                                return rhs_simplified;
                            }
                            // false = x => NOT x
                            (TermKind::False, _) => {
                                self.stats.terms_eliminated += 1;
                                return manager.mk_not(rhs_simplified);
                            }
                            _ => {}
                        }
                    }
                }

                if lhs_simplified == *lhs && rhs_simplified == *rhs {
                    term
                } else {
                    manager.mk_eq(lhs_simplified, rhs_simplified)
                }
            }

            TermKind::Mul(args) => {
                // Constant-fold products. The load-bearing rule is `0 · _ = 0`: it
                // folds e.g. `(* 0 x x)` to `0` so a disequality `(distinct (* 0 x x)
                // 0)` = `0 ≠ 0` is decided UNSAT instead of the spurious sat (the
                // nonlinear `≠` path never evaluated the zero product). Integer
                // constant factors are also COMBINED (partial fold), so a residual
                // constant part can cancel elsewhere. Sound throughout.
                let orig: Vec<TermId> = args.to_vec();
                let simp: Vec<TermId> = orig.iter().map(|&a| self.simplify(a, manager)).collect();
                if simp.iter().copied().any(|a| arith_is_zero(manager, a)) {
                    self.stats.contradictions_found += 1;
                    return if t.sort == manager.sorts.real_sort {
                        manager.mk_real(num_rational::Rational64::from_integer(0))
                    } else {
                        manager.mk_int(0)
                    };
                }
                if t.sort == manager.sorts.int_sort {
                    let mut prod = BigInt::from(1);
                    let mut rest: Vec<TermId> = Vec::new();
                    for &a in &simp {
                        match arith_int_const(manager, a) {
                            Some(n) => prod *= n,
                            None => rest.push(a),
                        }
                    }
                    if rest.is_empty() {
                        return manager.mk_int(prod);
                    }
                    if prod == BigInt::from(1) {
                        return if rest.len() == 1 { rest[0] } else { manager.mk_mul(rest) };
                    }
                    let mut all = Vec::with_capacity(rest.len() + 1);
                    all.push(manager.mk_int(prod));
                    all.extend(rest);
                    return manager.mk_mul(all);
                }
                if simp == orig {
                    term
                } else {
                    manager.mk_mul(simp)
                }
            }

            TermKind::Add(args) => {
                // Recurse into addends (so nested `0·_` products fold) + COMBINE
                // integer constant addends (partial fold). Without recursion an
                // unhandled `Add` hides nested folds (`(+ (* 0 x) 0 (* 0 x y))` would
                // never reach `0`); without constant-combining, `(+ 2 (- 2) p)` keeps a
                // dangling `2 + -2` that a disequality cannot cancel. Sound.
                let orig: Vec<TermId> = args.to_vec();
                let simp: Vec<TermId> = orig.iter().map(|&a| self.simplify(a, manager)).collect();
                if t.sort == manager.sorts.int_sort {
                    let mut sum = BigInt::from(0);
                    let mut rest: Vec<TermId> = Vec::new();
                    for &a in &simp {
                        match arith_int_const(manager, a) {
                            Some(n) => sum += n,
                            None => rest.push(a),
                        }
                    }
                    if rest.is_empty() {
                        return manager.mk_int(sum);
                    }
                    if sum.is_zero() {
                        return if rest.len() == 1 { rest[0] } else { manager.mk_add(rest) };
                    }
                    let mut all = Vec::with_capacity(rest.len() + 1);
                    all.push(manager.mk_int(sum));
                    all.extend(rest);
                    return manager.mk_add(all);
                }
                let kept: Vec<TermId> =
                    simp.iter().copied().filter(|&a| !arith_is_zero(manager, a)).collect();
                if kept.is_empty() {
                    return manager.mk_real(num_rational::Rational64::from_integer(0));
                }
                if kept.len() == 1 {
                    return kept[0];
                }
                if kept == orig {
                    term
                } else {
                    manager.mk_add(kept)
                }
            }

            TermKind::Sub(a, b) => {
                let sa = self.simplify(*a, manager);
                let sb = self.simplify(*b, manager);
                if let (Some(na), Some(nb)) =
                    (arith_int_const(manager, sa), arith_int_const(manager, sb))
                {
                    return manager.mk_int(na - nb);
                }
                if arith_is_zero(manager, sb) {
                    return sa; // a - 0 = a
                }
                if sa == *a && sb == *b {
                    term
                } else {
                    manager.mk_sub(sa, sb)
                }
            }

            TermKind::Neg(a) => {
                let sa = self.simplify(*a, manager);
                if let Some(n) = arith_int_const(manager, sa) {
                    return manager.mk_int(-n);
                }
                if sa == *a {
                    term
                } else {
                    manager.mk_neg(sa)
                }
            }

            TermKind::Distinct(args) => {
                // `distinct(a₁..aₙ) ≡ ⋀_{i<j} ¬(aᵢ = aⱼ)`. Desugar to the DEFINITIONAL
                // pairwise-`(not (= ..))` form so it gets the SAME (correct) handling
                // as an explicit `(not (= ..))`, rather than the bespoke
                // result-variable encoding (`encode.rs`), which missed arith-equal
                // but non-SYNTACTICALLY-equal terms — e.g. `(distinct (* 0 x) 0)` is
                // `0 ≠ 0` (UNSAT) yet was reported sat. For uninterpreted sorts the
                // pairwise `¬(=)` is exactly the EUF disequality, so SAT cases (e.g.
                // `(distinct x y)`) are unchanged.
                let args: Vec<TermId> = args.to_vec();
                if args.len() <= 1 {
                    return manager.mk_true(); // distinct of ≤1 term is trivially true
                }
                let mut conj = Vec::with_capacity(args.len() * (args.len() - 1) / 2);
                for i in 0..args.len() {
                    for j in (i + 1)..args.len() {
                        let eq = manager.mk_eq(args[i], args[j]);
                        conj.push(manager.mk_not(eq));
                    }
                }
                let and = manager.mk_and(conj);
                self.simplify(and, manager)
            }

            // For other term kinds, just return the original
            _ => term,
        }
    }

    /// Simplify multiple assertions
    ///
    /// Returns simplified versions of all assertions and a flag indicating
    /// if a contradiction was found
    #[allow(dead_code)]
    pub fn simplify_assertions(
        &mut self,
        assertions: &[TermId],
        manager: &mut TermManager,
    ) -> (Vec<TermId>, bool) {
        let mut simplified = Vec::new();
        let mut found_false = false;

        // Track constructor constraints for each variable
        // If a variable is constrained to multiple different constructors, it's UNSAT
        let mut var_constructors: FxHashMap<TermId, oxiz_core::interner::Spur> =
            FxHashMap::default();

        for &assertion in assertions {
            let simp = self.simplify(assertion, manager);

            // Check if we found false
            if let Some(term) = manager.get(simp) {
                if matches!(term.kind, TermKind::False) {
                    found_false = true;
                }
                // Skip true assertions (they don't constrain anything)
                if matches!(term.kind, TermKind::True) {
                    continue;
                }

                // Check for datatype constructor mutual exclusivity
                // If we see (= var Constructor), track it
                if let TermKind::Eq(lhs, rhs) = &term.kind {
                    let (var, cons) = self.extract_var_constructor(*lhs, *rhs, manager);
                    if let Some((var_term, constructor)) = var.zip(cons) {
                        if let Some(&existing_con) = var_constructors.get(&var_term) {
                            if existing_con != constructor {
                                // Variable constrained to two different constructors - UNSAT
                                self.stats.contradictions_found += 1;
                                found_false = true;
                            }
                        } else {
                            var_constructors.insert(var_term, constructor);
                        }
                    }
                }
            }

            simplified.push(simp);
        }

        (simplified, found_false)
    }

    /// Extract (variable, constructor) pair from an equality if one side is a variable
    /// and the other is a DtConstructor
    fn extract_var_constructor(
        &self,
        lhs: TermId,
        rhs: TermId,
        manager: &TermManager,
    ) -> (Option<TermId>, Option<oxiz_core::interner::Spur>) {
        let lhs_term = manager.get(lhs);
        let rhs_term = manager.get(rhs);

        match (lhs_term, rhs_term) {
            (Some(lt), Some(rt)) => {
                // lhs is var, rhs is constructor
                if matches!(lt.kind, TermKind::Var(_)) {
                    if let TermKind::DtConstructor { constructor, .. } = &rt.kind {
                        return (Some(lhs), Some(*constructor));
                    }
                }
                // rhs is var, lhs is constructor
                if matches!(rt.kind, TermKind::Var(_)) {
                    if let TermKind::DtConstructor { constructor, .. } = &lt.kind {
                        return (Some(rhs), Some(*constructor));
                    }
                }
                (None, None)
            }
            _ => (None, None),
        }
    }

    /// Apply unit propagation at preprocessing level
    /// Returns simplified assertions after propagating unit clauses
    #[allow(dead_code)]
    pub fn unit_propagation(
        &mut self,
        assertions: &[TermId],
        manager: &mut TermManager,
    ) -> Vec<TermId> {
        let mut units = FxHashMap::default(); // Map from term to its assigned value (true/false)
        let mut result = Vec::new();

        // First pass: collect unit clauses (single literals)
        for &assertion in assertions {
            if let Some(term) = manager.get(assertion) {
                match &term.kind {
                    TermKind::True | TermKind::False => {
                        // Already handled by simplification
                        result.push(assertion);
                    }
                    TermKind::Not(inner) => {
                        // Unit clause: not(x)
                        units.insert(*inner, false);
                        result.push(assertion);
                    }
                    _ => {
                        // Check if it's a variable (also a unit clause)
                        if matches!(term.kind, TermKind::Var(_)) {
                            units.insert(assertion, true);
                        }
                        result.push(assertion);
                    }
                }
            } else {
                result.push(assertion);
            }
        }

        // If we found unit clauses, propagate them
        if !units.is_empty() {
            self.stats.const_propagations += units.len();
            result = result
                .into_iter()
                .map(|term| self.substitute_units(term, &units, manager))
                .collect();
        }

        result
    }

    /// Substitute unit assignments in a term
    fn substitute_units(
        &mut self,
        term: TermId,
        units: &FxHashMap<TermId, bool>,
        manager: &mut TermManager,
    ) -> TermId {
        // Check if this term has a unit assignment
        if let Some(&value) = units.get(&term) {
            return if value {
                manager.mk_true()
            } else {
                manager.mk_false()
            };
        }

        // Recursively substitute in subterms
        let Some(t) = manager.get(term).cloned() else {
            return term;
        };

        match &t.kind {
            TermKind::Not(arg) => {
                let arg_subst = self.substitute_units(*arg, units, manager);
                if arg_subst == *arg {
                    term
                } else {
                    manager.mk_not(arg_subst)
                }
            }
            TermKind::And(args) => {
                let mut changed = false;
                let new_args: Vec<_> = args
                    .iter()
                    .map(|&arg| {
                        let subst = self.substitute_units(arg, units, manager);
                        if subst != arg {
                            changed = true;
                        }
                        subst
                    })
                    .collect();
                if changed {
                    manager.mk_and(new_args)
                } else {
                    term
                }
            }
            TermKind::Or(args) => {
                let mut changed = false;
                let new_args: Vec<_> = args
                    .iter()
                    .map(|&arg| {
                        let subst = self.substitute_units(arg, units, manager);
                        if subst != arg {
                            changed = true;
                        }
                        subst
                    })
                    .collect();
                if changed {
                    manager.mk_or(new_args)
                } else {
                    term
                }
            }
            _ => term,
        }
    }

    /// Detect pure literals (literals that appear only in one polarity)
    /// Returns a map from pure literals to their polarity (true = positive, false = negative)
    #[allow(dead_code)]
    pub fn detect_pure_literals(
        &self,
        assertions: &[TermId],
        manager: &TermManager,
    ) -> FxHashMap<TermId, bool> {
        let mut positive = FxHashMap::default();
        let mut negative = FxHashMap::default();

        // Collect all literal occurrences
        for &assertion in assertions {
            self.collect_literals(assertion, true, &mut positive, &mut negative, manager);
        }

        // Find pure literals (appear only in one polarity)
        let mut pure_literals = FxHashMap::default();
        for (&lit, _) in &positive {
            if !negative.contains_key(&lit) {
                pure_literals.insert(lit, true);
            }
        }
        for (&lit, _) in &negative {
            if !positive.contains_key(&lit) {
                pure_literals.insert(lit, false);
            }
        }

        pure_literals
    }

    /// Collect literal occurrences with their polarities
    fn collect_literals(
        &self,
        term: TermId,
        polarity: bool,
        positive: &mut FxHashMap<TermId, ()>,
        negative: &mut FxHashMap<TermId, ()>,
        manager: &TermManager,
    ) {
        let Some(t) = manager.get(term) else {
            return;
        };

        match &t.kind {
            TermKind::Var(_) => {
                if polarity {
                    positive.insert(term, ());
                } else {
                    negative.insert(term, ());
                }
            }
            TermKind::Not(arg) => {
                self.collect_literals(*arg, !polarity, positive, negative, manager);
            }
            TermKind::And(args) | TermKind::Or(args) => {
                for &arg in args {
                    self.collect_literals(arg, polarity, positive, negative, manager);
                }
            }
            TermKind::Implies(lhs, rhs) => {
                self.collect_literals(*lhs, !polarity, positive, negative, manager);
                self.collect_literals(*rhs, polarity, positive, negative, manager);
            }
            TermKind::Ite(cond, then_br, else_br) => {
                // For ITE, both branches can be reached
                self.collect_literals(*cond, true, positive, negative, manager);
                self.collect_literals(*cond, false, positive, negative, manager);
                self.collect_literals(*then_br, polarity, positive, negative, manager);
                self.collect_literals(*else_br, polarity, positive, negative, manager);
            }
            _ => {}
        }
    }
}

impl Default for Simplifier {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_simplify_not() {
        let mut manager = TermManager::new();
        let mut simplifier = Simplifier::new();

        // not(true) => false
        let t = manager.mk_true();
        let not_t = manager.mk_not(t);
        let result = simplifier.simplify(not_t, &mut manager);
        assert!(matches!(
            manager.get(result).expect("key should exist in map").kind,
            TermKind::False
        ));

        // not(false) => true
        let f = manager.mk_false();
        let not_f = manager.mk_not(f);
        let result = simplifier.simplify(not_f, &mut manager);
        assert!(matches!(
            manager.get(result).expect("key should exist in map").kind,
            TermKind::True
        ));
    }

    #[test]
    fn test_simplify_and() {
        let mut manager = TermManager::new();
        let mut simplifier = Simplifier::new();

        let x = manager.mk_var("x", manager.sorts.bool_sort);
        let t = manager.mk_true();
        let f = manager.mk_false();

        // and(x, true) => x
        let and_x_true = manager.mk_and([x, t]);
        let result = simplifier.simplify(and_x_true, &mut manager);
        assert_eq!(result, x);

        // and(x, false) => false
        let and_x_false = manager.mk_and([x, f]);
        let result = simplifier.simplify(and_x_false, &mut manager);
        assert!(matches!(
            manager.get(result).expect("key should exist in map").kind,
            TermKind::False
        ));
    }

    #[test]
    fn test_simplify_or() {
        let mut manager = TermManager::new();
        let mut simplifier = Simplifier::new();

        let x = manager.mk_var("x", manager.sorts.bool_sort);
        let t = manager.mk_true();
        let f = manager.mk_false();

        // or(x, false) => x
        let or_x_false = manager.mk_or([x, f]);
        let result = simplifier.simplify(or_x_false, &mut manager);
        assert_eq!(result, x);

        // or(x, true) => true
        let or_x_true = manager.mk_or([x, t]);
        let result = simplifier.simplify(or_x_true, &mut manager);
        assert!(matches!(
            manager.get(result).expect("key should exist in map").kind,
            TermKind::True
        ));
    }

    #[test]
    fn test_simplify_implies() {
        let mut manager = TermManager::new();
        let mut simplifier = Simplifier::new();

        let x = manager.mk_var("x", manager.sorts.bool_sort);
        let t = manager.mk_true();
        let f = manager.mk_false();

        // false => x  =  true
        let imp = manager.mk_implies(f, x);
        let result = simplifier.simplify(imp, &mut manager);
        assert!(matches!(
            manager.get(result).expect("key should exist in map").kind,
            TermKind::True
        ));

        // true => x  =  x
        let imp = manager.mk_implies(t, x);
        let result = simplifier.simplify(imp, &mut manager);
        assert_eq!(result, x);
    }

    #[test]
    fn test_simplify_ite() {
        let mut manager = TermManager::new();
        let mut simplifier = Simplifier::new();

        let x = manager.mk_var("x", manager.sorts.bool_sort);
        let y = manager.mk_var("y", manager.sorts.bool_sort);
        let t = manager.mk_true();
        let f = manager.mk_false();

        // ite(true, x, y) => x
        let ite = manager.mk_ite(t, x, y);
        let result = simplifier.simplify(ite, &mut manager);
        assert_eq!(result, x);

        // ite(false, x, y) => y
        let ite = manager.mk_ite(f, x, y);
        let result = simplifier.simplify(ite, &mut manager);
        assert_eq!(result, y);

        // ite(cond, x, x) => x
        let ite = manager.mk_ite(x, y, y);
        let result = simplifier.simplify(ite, &mut manager);
        assert_eq!(result, y);
    }

    #[test]
    fn test_simplify_eq() {
        let mut manager = TermManager::new();
        let mut simplifier = Simplifier::new();

        let x = manager.mk_var("x", manager.sorts.bool_sort);
        let t = manager.mk_true();
        let f = manager.mk_false();

        // x = x  =>  true
        let eq = manager.mk_eq(x, x);
        let result = simplifier.simplify(eq, &mut manager);
        assert!(matches!(
            manager.get(result).expect("key should exist in map").kind,
            TermKind::True
        ));

        // true = false  =>  false
        let eq = manager.mk_eq(t, f);
        let result = simplifier.simplify(eq, &mut manager);
        assert!(matches!(
            manager.get(result).expect("key should exist in map").kind,
            TermKind::False
        ));
    }

    #[test]
    fn test_simplify_arith_fold_and_distinct() {
        // Regression for the constant-folding FALSE_SAT: `distinct`/arith atoms that
        // fold to a constant (in)equality must be decided, not left for a theory path
        // that missed them (e.g. `(distinct (* 0 x) 0)` was reported sat).
        let mut manager = TermManager::new();
        let mut simplifier = Simplifier::new();
        let int = manager.sorts.int_sort;
        let x = manager.mk_var("x", int);
        let zero = manager.mk_int(0);
        let f = manager.mk_false();

        // 0 · _ = 0, including the NONLINEAR product `(* 0 x x)`.
        let m = manager.mk_mul([zero, x]);
        assert_eq!(simplifier.simplify(m, &mut manager), zero, "(* 0 x) => 0");
        let m = manager.mk_mul([zero, x, x]);
        assert_eq!(simplifier.simplify(m, &mut manager), zero, "(* 0 x x) => 0");

        // Constant addends combine: (+ 2 (- 2) x) => x.
        let two = manager.mk_int(2);
        let neg2 = manager.mk_neg(two);
        let a = manager.mk_add([two, neg2, x]);
        assert_eq!(simplifier.simplify(a, &mut manager), x, "(+ 2 (- 2) x) => x");

        // The bug case: `(distinct (* 0 x) 0)` = `0 ≠ 0` => false.
        let m0 = manager.mk_mul([zero, x]);
        let d = manager.mk_distinct([m0, zero]);
        assert_eq!(simplifier.simplify(d, &mut manager), f, "(distinct (* 0 x) 0) => false");

        // ...but a genuine disequality stays satisfiable (desugars to `(not (= x 0))`,
        // NOT false) — no regression on the SAT direction.
        let d = manager.mk_distinct([x, zero]);
        let r = simplifier.simplify(d, &mut manager);
        assert_ne!(r, f, "(distinct x 0) must not fold to false");
    }

    #[test]
    fn test_simplify_assertions() {
        let mut manager = TermManager::new();
        let mut simplifier = Simplifier::new();

        let x = manager.mk_var("x", manager.sorts.bool_sort);
        let t = manager.mk_true();
        let f = manager.mk_false();

        // Simplify a list of assertions
        let assertions = vec![manager.mk_and([x, t]), manager.mk_or([x, f])];
        let (simplified, found_false) = simplifier.simplify_assertions(&assertions, &mut manager);

        assert!(!found_false);
        assert_eq!(simplified.len(), 2);
        assert_eq!(simplified[0], x); // and(x, true) => x
        assert_eq!(simplified[1], x); // or(x, false) => x

        // Test with a false assertion
        let assertions_with_false = vec![x, f];
        let (_, found_false) = simplifier.simplify_assertions(&assertions_with_false, &mut manager);
        assert!(found_false);
    }

    #[test]
    fn test_simplifier_reset() {
        let mut manager = TermManager::new();
        let mut simplifier = Simplifier::new();

        let x = manager.mk_var("x", manager.sorts.bool_sort);
        let y = manager.mk_var("y", manager.sorts.bool_sort);

        // Perform a simplification to populate the cache
        let eq = manager.mk_eq(x, x);
        let result1 = simplifier.simplify(eq, &mut manager);
        assert!(matches!(
            manager.get(result1).expect("key should exist in map").kind,
            TermKind::True
        ));

        // Create another term that would be cached
        let eq2 = manager.mk_eq(y, y);
        let result2 = simplifier.simplify(eq2, &mut manager);
        assert!(matches!(
            manager.get(result2).expect("key should exist in map").kind,
            TermKind::True
        ));

        // Reset the simplifier
        simplifier.reset();

        // Verify stats are cleared
        let stats_after_reset = simplifier.stats();
        assert_eq!(stats_after_reset.const_propagations, 0);
        assert_eq!(stats_after_reset.terms_eliminated, 0);
        assert_eq!(stats_after_reset.trivial_equalities, 0);
        assert_eq!(stats_after_reset.contradictions_found, 0);
    }
}
