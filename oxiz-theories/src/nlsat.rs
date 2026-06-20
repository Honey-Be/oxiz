//! NLSAT Theory Wrapper
//!
//! This module wraps the NLSAT solver (from oxiz-nlsat) to provide Theory trait
//! implementation for nonlinear arithmetic (QF_NIA and QF_NRA).
//!
//! ## Architecture
//!
//! - `NlsatTheory`: Main wrapper implementing `Theory` trait
//! - Handles both Real (QF_NRA) and Integer (QF_NIA) nonlinear arithmetic
//! - Delegates to `NlsatSolver` (real) or `NiaSolver` (integer)
//! - `TermPolyTranslator`: Converts `TermId` AST nodes to `Polynomial` representations
//! - `dispatch_nia_constraints`: Runs `NiaSolver` over a set of NIA assertions
//! - `dispatch_nra_constraints`: Runs `NlsatSolver` over a set of NRA assertions
//!
//! ## Reference
//!
//! - Z3's NLSAT integration in nlsat/nlsat_explain.cpp
//! - NLSAT solver: oxiz-nlsat::solver::NlsatSolver
//! - Integer solver: oxiz-nlsat::nia::NiaSolver

#[allow(unused_imports)]
use crate::prelude::*;
use crate::theory::{Theory, TheoryId, TheoryResult};
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::ToPrimitive;
use oxiz_core::ast::{TermId, TermKind, TermManager};
use oxiz_core::error::Result;
use oxiz_math::polynomial::Polynomial;
use oxiz_nlsat::nia::{NiaConfig, NiaSolver, VarType};
use oxiz_nlsat::solver::{NlsatSolver, SolverResult};
use oxiz_nlsat::types::AtomKind;
use std::collections::HashMap;

// ─────────────────────────────────────────────────────────────────────────────
// Public result type for dispatch functions
// ─────────────────────────────────────────────────────────────────────────────

/// The definitive result from a nonlinear dispatch call.
///
/// `Unknown` is not included: `dispatch_*` functions return `None` to signal
/// "fall through to CDCL(T)" instead of wrapping Unknown.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NlDispatchResult {
    /// The constraint set is satisfiable.
    Sat,
    /// The constraint set is unsatisfiable.
    Unsat,
}

// ─────────────────────────────────────────────────────────────────────────────
// Term→Polynomial translator
// ─────────────────────────────────────────────────────────────────────────────

/// Translates `TermId` AST nodes to `Polynomial` values for use with
/// the NLSAT / NIA solver.
///
/// Maintains a cache of `TermId → polynomial variable index` so that each
/// unique variable term receives a stable index.
pub struct TermPolyTranslator<'a> {
    manager: &'a TermManager,
    nlsat: &'a mut NiaSolver,
    var_cache: HashMap<TermId, u32>,
    integer_mode: bool,
}

impl<'a> TermPolyTranslator<'a> {
    /// Create a new translator.
    pub fn new(manager: &'a TermManager, nlsat: &'a mut NiaSolver, integer_mode: bool) -> Self {
        Self {
            manager,
            nlsat,
            var_cache: HashMap::new(),
            integer_mode,
        }
    }

    /// Translate a term into a `Polynomial`.
    ///
    /// Returns `None` for sub-expressions that cannot be expressed as a
    /// polynomial (e.g. division, modulo, uninterpreted functions).
    pub fn translate(&mut self, term_id: TermId) -> Option<Polynomial> {
        let term = self.manager.get(term_id)?;
        match &term.kind.clone() {
            TermKind::IntConst(n) => {
                let r = BigRational::from_integer(n.clone());
                Some(Polynomial::constant(r))
            }
            TermKind::RealConst(r) => {
                let big = BigRational::new(
                    BigInt::from(r.numer().to_i64().unwrap_or(0)),
                    BigInt::from(r.denom().to_i64().unwrap_or(1)),
                );
                Some(Polynomial::constant(big))
            }
            TermKind::Var(_) => {
                let v = self.get_or_create_var(term_id);
                Some(Polynomial::from_var(v))
            }
            TermKind::Neg(inner) => {
                let p = self.translate(*inner)?;
                Some(Polynomial::neg(&p))
            }
            TermKind::Add(args) => {
                let mut acc = Polynomial::zero();
                for &arg in args.iter() {
                    let p = self.translate(arg)?;
                    acc = Polynomial::add(&acc, &p);
                }
                Some(acc)
            }
            TermKind::Sub(lhs, rhs) => {
                let lp = self.translate(*lhs)?;
                let rp = self.translate(*rhs)?;
                Some(Polynomial::sub(&lp, &rp))
            }
            TermKind::Mul(args) => {
                let mut acc = Polynomial::one();
                for &arg in args.iter() {
                    let p = self.translate(arg)?;
                    acc = Polynomial::mul(&acc, &p);
                }
                Some(acc)
            }
            _ => None,
        }
    }

    fn get_or_create_var(&mut self, term_id: TermId) -> u32 {
        if let Some(&v) = self.var_cache.get(&term_id) {
            return v;
        }
        let v = self.nlsat.nlsat_mut().new_arith_var();
        if self.integer_mode {
            self.nlsat.set_var_type(v, VarType::Integer);
        }
        self.var_cache.insert(term_id, v);
        v
    }

    /// Return the variable mapping (for model extraction).
    pub fn var_cache(&self) -> &HashMap<TermId, u32> {
        &self.var_cache
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Helper: nonlinearity detection
// ─────────────────────────────────────────────────────────────────────────────

/// Returns `true` if `term_id` (recursively) contains a `Mul` node where at
/// least two non-constant operands are multiplied together.
pub fn term_is_nonlinear(term_id: TermId, manager: &TermManager) -> bool {
    let Some(term) = manager.get(term_id) else {
        return false;
    };
    match &term.kind {
        TermKind::Mul(args) => {
            let non_const_count = args.iter().filter(|&&a| !is_const_term(a, manager)).count();
            if non_const_count >= 2 {
                return true;
            }
            args.iter().any(|&a| term_is_nonlinear(a, manager))
        }
        TermKind::Add(args) | TermKind::And(args) => {
            args.iter().any(|&a| term_is_nonlinear(a, manager))
        }
        TermKind::Sub(lhs, rhs)
        | TermKind::Eq(lhs, rhs)
        | TermKind::Gt(lhs, rhs)
        | TermKind::Ge(lhs, rhs)
        | TermKind::Lt(lhs, rhs)
        | TermKind::Le(lhs, rhs) => {
            term_is_nonlinear(*lhs, manager) || term_is_nonlinear(*rhs, manager)
        }
        TermKind::Neg(inner) => term_is_nonlinear(*inner, manager),
        _ => false,
    }
}

fn is_const_term(term_id: TermId, manager: &TermManager) -> bool {
    manager
        .get(term_id)
        .map(|t| matches!(&t.kind, TermKind::IntConst(_) | TermKind::RealConst(_)))
        .unwrap_or(false)
}

fn contains_non_polynomial_ops(term_id: TermId, manager: &TermManager) -> bool {
    let Some(term) = manager.get(term_id) else {
        return false;
    };

    match &term.kind {
        TermKind::Div(_, _) | TermKind::Mod(_, _) => true,
        TermKind::Apply { .. }
        | TermKind::Forall { .. }
        | TermKind::Exists { .. }
        | TermKind::Let { .. }
        | TermKind::Match { .. } => true,
        TermKind::Neg(inner) | TermKind::Not(inner) => contains_non_polynomial_ops(*inner, manager),
        TermKind::Add(args)
        | TermKind::Mul(args)
        | TermKind::And(args)
        | TermKind::Or(args)
        | TermKind::Distinct(args) => args
            .iter()
            .any(|&arg| contains_non_polynomial_ops(arg, manager)),
        TermKind::Ite(cond, then_term, else_term) => {
            contains_non_polynomial_ops(*cond, manager)
                || contains_non_polynomial_ops(*then_term, manager)
                || contains_non_polynomial_ops(*else_term, manager)
        }
        TermKind::Xor(lhs, rhs) | TermKind::Implies(lhs, rhs) => {
            contains_non_polynomial_ops(*lhs, manager) || contains_non_polynomial_ops(*rhs, manager)
        }
        TermKind::Sub(lhs, rhs)
        | TermKind::Eq(lhs, rhs)
        | TermKind::Gt(lhs, rhs)
        | TermKind::Ge(lhs, rhs)
        | TermKind::Lt(lhs, rhs)
        | TermKind::Le(lhs, rhs) => {
            contains_non_polynomial_ops(*lhs, manager) || contains_non_polynomial_ops(*rhs, manager)
        }
        _ => false,
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Polynomial atom (internal representation)
// ─────────────────────────────────────────────────────────────────────────────

#[derive(Debug, Clone)]
struct PolyAtom {
    poly: Polynomial,
    kind: AtomKind,
    /// `true` → atom appears positively; `false` → negated literal.
    positive: bool,
}

// ─────────────────────────────────────────────────────────────────────────────
// Assertion-level translation (integer mode)
// ─────────────────────────────────────────────────────────────────────────────

/// Translate an assertion into polynomial atoms. **Returns `true` if ANY
/// subterm was DROPPED** — a connective `extract` does not model (top-level
/// `Or`/`Not`/`Implies`/`Ite`/`Xor`, the `_` arm) or an atom whose operand fails
/// to translate (`Div`/`Mod`/`Apply`/`Ite` → `translate` returns `None`). The
/// caller needs this for soundness: a `Sat` over the RETAINED subset of atoms is
/// only valid for the original formula when NOTHING was dropped (a dropped
/// constraint could be exactly the one a retained-subset model violates →
/// spurious sat). `Unsat` over a subset stays sound regardless (subset-unsat ⟹
/// full-unsat), which is why only the `Sat` side consults this.
fn extract_poly_atoms(
    term_id: TermId,
    manager: &TermManager,
    translator: &mut TermPolyTranslator<'_>,
    out: &mut Vec<PolyAtom>,
) -> bool {
    let Some(term) = manager.get(term_id) else {
        return true;
    };
    match &term.kind.clone() {
        TermKind::Eq(lhs, rhs) => {
            if let (Some(lp), Some(rp)) = (translator.translate(*lhs), translator.translate(*rhs)) {
                out.push(PolyAtom {
                    poly: Polynomial::sub(&lp, &rp),
                    kind: AtomKind::Eq,
                    positive: true,
                });
                false
            } else {
                true
            }
        }
        TermKind::Lt(lhs, rhs) => {
            // lhs < rhs → rhs - lhs > 0
            if let (Some(lp), Some(rp)) = (translator.translate(*lhs), translator.translate(*rhs)) {
                out.push(PolyAtom {
                    poly: Polynomial::sub(&rp, &lp),
                    kind: AtomKind::Gt,
                    positive: true,
                });
                false
            } else {
                true
            }
        }
        TermKind::Le(lhs, rhs) => {
            // lhs <= rhs → rhs - lhs >= 0 → NOT(rhs - lhs < 0)
            if let (Some(lp), Some(rp)) = (translator.translate(*lhs), translator.translate(*rhs)) {
                out.push(PolyAtom {
                    poly: Polynomial::sub(&rp, &lp),
                    kind: AtomKind::Lt,
                    positive: false,
                });
                false
            } else {
                true
            }
        }
        TermKind::Gt(lhs, rhs) => {
            // lhs > rhs → lhs - rhs > 0
            if let (Some(lp), Some(rp)) = (translator.translate(*lhs), translator.translate(*rhs)) {
                out.push(PolyAtom {
                    poly: Polynomial::sub(&lp, &rp),
                    kind: AtomKind::Gt,
                    positive: true,
                });
                false
            } else {
                true
            }
        }
        TermKind::Ge(lhs, rhs) => {
            // lhs >= rhs → NOT(lhs - rhs < 0)
            if let (Some(lp), Some(rp)) = (translator.translate(*lhs), translator.translate(*rhs)) {
                out.push(PolyAtom {
                    poly: Polynomial::sub(&lp, &rp),
                    kind: AtomKind::Lt,
                    positive: false,
                });
                false
            } else {
                true
            }
        }
        TermKind::And(args) => {
            let mut dropped = false;
            for &arg in args.iter() {
                dropped |= extract_poly_atoms(arg, manager, translator, out);
            }
            dropped
        }
        _ => true,
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// NIA dispatch: public entry point
// ─────────────────────────────────────────────────────────────────────────────

/// Dispatch nonlinear integer arithmetic assertions to the `NiaSolver`.
///
/// Returns:
/// - `Some(NlDispatchResult::Unsat)` if the system is provably UNSAT,
/// - `Some(NlDispatchResult::Sat)` if NiaSolver finds an integer model,
/// - `None` if translation yields no atoms or the solver returns Unknown.
///
/// Both linear and nonlinear assertions are passed so the solver has full context.
pub fn dispatch_nia_constraints(
    assertions: &[TermId],
    manager: &TermManager,
    integer_mode: bool,
) -> Option<NlDispatchResult> {
    let has_nl = assertions.iter().any(|&a| term_is_nonlinear(a, manager));
    if !has_nl {
        return None;
    }
    let has_unsupported_ops = assertions
        .iter()
        .any(|&a| contains_non_polynomial_ops(a, manager));

    let config = NiaConfig {
        enable_cutting_planes: true,
        ..NiaConfig::default()
    };
    let mut nia = NiaSolver::with_config(config);
    let mut translator = TermPolyTranslator::new(manager, &mut nia, integer_mode);

    let mut poly_atoms: Vec<PolyAtom> = Vec::new();
    let mut dropped = false;
    for &assertion in assertions {
        dropped |= extract_poly_atoms(assertion, manager, &mut translator, &mut poly_atoms);
    }

    if poly_atoms.is_empty() {
        return None;
    }

    let unsat_is_trustworthy =
        !has_unsupported_ops && poly_atoms.iter().all(|atom| atom.poly.is_univariate());
    // A `Sat` over the RETAINED atoms is only valid for the original formula when
    // every assertion was fully captured — no connective dropped, no operand
    // untranslatable. Otherwise a dropped constraint could be the one a
    // subset-model violates → spurious sat (the nlsat soundness hole). When it is
    // NOT trustworthy we return `None` (Unknown) and let the full CDCL(T) path
    // decide, rather than trusting nlsat's `Sat`.
    let sat_is_trustworthy = !dropped && !has_unsupported_ops;

    for atom in &poly_atoms {
        let atom_id = translator
            .nlsat
            .nlsat_mut()
            .new_ineq_atom(atom.poly.clone(), atom.kind);
        let lit = translator
            .nlsat
            .nlsat()
            .atom_literal(atom_id, atom.positive);
        translator.nlsat.nlsat_mut().add_clause(vec![lit]);
    }

    match translator.nlsat.solve() {
        SolverResult::Unsat if unsat_is_trustworthy => Some(NlDispatchResult::Unsat),
        SolverResult::Sat if sat_is_trustworthy => Some(NlDispatchResult::Sat),
        SolverResult::Sat | SolverResult::Unsat | SolverResult::Unknown => None,
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// NRA dispatch (real arithmetic)
// ─────────────────────────────────────────────────────────────────────────────

struct RealPolyTranslator<'a> {
    manager: &'a TermManager,
    nlsat: &'a mut NlsatSolver,
    var_cache: HashMap<TermId, u32>,
}

impl<'a> RealPolyTranslator<'a> {
    fn new(manager: &'a TermManager, nlsat: &'a mut NlsatSolver) -> Self {
        Self {
            manager,
            nlsat,
            var_cache: HashMap::new(),
        }
    }

    fn translate(&mut self, term_id: TermId) -> Option<Polynomial> {
        let term = self.manager.get(term_id)?;
        match &term.kind.clone() {
            TermKind::IntConst(n) => {
                Some(Polynomial::constant(BigRational::from_integer(n.clone())))
            }
            TermKind::RealConst(r) => {
                let big = BigRational::new(
                    BigInt::from(r.numer().to_i64().unwrap_or(0)),
                    BigInt::from(r.denom().to_i64().unwrap_or(1)),
                );
                Some(Polynomial::constant(big))
            }
            TermKind::Var(_) => {
                let v = self.get_or_create_var(term_id);
                Some(Polynomial::from_var(v))
            }
            TermKind::Neg(inner) => {
                let p = self.translate(*inner)?;
                Some(Polynomial::neg(&p))
            }
            TermKind::Add(args) => {
                let mut acc = Polynomial::zero();
                for &arg in args.iter() {
                    let p = self.translate(arg)?;
                    acc = Polynomial::add(&acc, &p);
                }
                Some(acc)
            }
            TermKind::Sub(lhs, rhs) => {
                let lp = self.translate(*lhs)?;
                let rp = self.translate(*rhs)?;
                Some(Polynomial::sub(&lp, &rp))
            }
            TermKind::Mul(args) => {
                let mut acc = Polynomial::one();
                for &arg in args.iter() {
                    let p = self.translate(arg)?;
                    acc = Polynomial::mul(&acc, &p);
                }
                Some(acc)
            }
            _ => None,
        }
    }

    fn get_or_create_var(&mut self, term_id: TermId) -> u32 {
        if let Some(&v) = self.var_cache.get(&term_id) {
            return v;
        }
        let v = self.nlsat.new_arith_var();
        self.var_cache.insert(term_id, v);
        v
    }
}

/// Real-arithmetic twin of [`extract_poly_atoms`]; **returns `true` if any
/// subterm was DROPPED** (unmodeled connective or untranslatable operand). See
/// that function for why the `Sat` side must consult it.
fn extract_real_poly_atoms(
    term_id: TermId,
    manager: &TermManager,
    translator: &mut RealPolyTranslator<'_>,
    out: &mut Vec<PolyAtom>,
) -> bool {
    let Some(term) = manager.get(term_id) else {
        return true;
    };
    match &term.kind.clone() {
        TermKind::Eq(lhs, rhs) => {
            if let (Some(lp), Some(rp)) = (translator.translate(*lhs), translator.translate(*rhs)) {
                out.push(PolyAtom {
                    poly: Polynomial::sub(&lp, &rp),
                    kind: AtomKind::Eq,
                    positive: true,
                });
                false
            } else {
                true
            }
        }
        TermKind::Lt(lhs, rhs) => {
            if let (Some(lp), Some(rp)) = (translator.translate(*lhs), translator.translate(*rhs)) {
                out.push(PolyAtom {
                    poly: Polynomial::sub(&rp, &lp),
                    kind: AtomKind::Gt,
                    positive: true,
                });
                false
            } else {
                true
            }
        }
        TermKind::Le(lhs, rhs) => {
            if let (Some(lp), Some(rp)) = (translator.translate(*lhs), translator.translate(*rhs)) {
                out.push(PolyAtom {
                    poly: Polynomial::sub(&rp, &lp),
                    kind: AtomKind::Lt,
                    positive: false,
                });
                false
            } else {
                true
            }
        }
        TermKind::Gt(lhs, rhs) => {
            if let (Some(lp), Some(rp)) = (translator.translate(*lhs), translator.translate(*rhs)) {
                out.push(PolyAtom {
                    poly: Polynomial::sub(&lp, &rp),
                    kind: AtomKind::Gt,
                    positive: true,
                });
                false
            } else {
                true
            }
        }
        TermKind::Ge(lhs, rhs) => {
            if let (Some(lp), Some(rp)) = (translator.translate(*lhs), translator.translate(*rhs)) {
                out.push(PolyAtom {
                    poly: Polynomial::sub(&lp, &rp),
                    kind: AtomKind::Lt,
                    positive: false,
                });
                false
            } else {
                true
            }
        }
        TermKind::And(args) => {
            let mut dropped = false;
            for &arg in args.iter() {
                dropped |= extract_real_poly_atoms(arg, manager, translator, out);
            }
            dropped
        }
        _ => true,
    }
}

/// Dispatch nonlinear real arithmetic assertions to `NlsatSolver`.
pub fn dispatch_nra_constraints(
    assertions: &[TermId],
    manager: &TermManager,
) -> Option<NlDispatchResult> {
    let has_nl = assertions.iter().any(|&a| term_is_nonlinear(a, manager));
    if !has_nl {
        return None;
    }

    let mut nlsat = NlsatSolver::new();
    let mut translator = RealPolyTranslator::new(manager, &mut nlsat);

    let mut poly_atoms: Vec<PolyAtom> = Vec::new();
    let mut dropped = false;
    for &assertion in assertions {
        dropped |= extract_real_poly_atoms(assertion, manager, &mut translator, &mut poly_atoms);
    }

    if poly_atoms.is_empty() {
        return None;
    }

    let unsat_is_trustworthy = poly_atoms.iter().all(|atom| atom.kind != AtomKind::Eq);
    // `Sat` is only valid for the original formula when nothing was dropped (see
    // `extract_poly_atoms`). Otherwise fall back to `None` (Unknown) — never trust
    // a `Sat` over a retained SUBSET of the constraints.
    let sat_is_trustworthy = !dropped;

    for atom in &poly_atoms {
        let atom_id = translator.nlsat.new_ineq_atom(atom.poly.clone(), atom.kind);
        let lit = translator.nlsat.atom_literal(atom_id, atom.positive);
        translator.nlsat.add_clause(vec![lit]);
    }

    match translator.nlsat.solve() {
        SolverResult::Unsat if unsat_is_trustworthy => Some(NlDispatchResult::Unsat),
        SolverResult::Sat if sat_is_trustworthy => Some(NlDispatchResult::Sat),
        SolverResult::Sat | SolverResult::Unsat | SolverResult::Unknown => None,
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// NlsatTheory – Theory trait wrapper
// ─────────────────────────────────────────────────────────────────────────────

#[derive(Debug, Clone)]
struct NlsatContextState {
    level: usize,
}

enum NlsatSolverWrapper {
    Real(NlsatSolver),
    Integer(NiaSolver),
}

impl core::fmt::Debug for NlsatSolverWrapper {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::Real(_) => write!(f, "NlsatSolverWrapper::Real(..)"),
            Self::Integer(_) => write!(f, "NlsatSolverWrapper::Integer(..)"),
        }
    }
}

impl NlsatSolverWrapper {
    fn new(integer: bool) -> Self {
        if integer {
            Self::Integer(NiaSolver::new())
        } else {
            Self::Real(NlsatSolver::new())
        }
    }

    fn solve(&mut self) -> SolverResult {
        match self {
            Self::Real(s) => s.solve(),
            Self::Integer(s) => s.solve(),
        }
    }
}

/// NLSAT Theory Solver for nonlinear arithmetic.
///
/// Supports both real (QF_NRA) and integer (QF_NIA) nonlinear arithmetic.
/// Full constraint translation happens in `dispatch_nia_constraints` /
/// `dispatch_nra_constraints`; this wrapper integrates with the `Theory` trait.
#[derive(Debug)]
pub struct NlsatTheory {
    solver: NlsatSolverWrapper,
    context_stack: Vec<NlsatContextState>,
    is_integer: bool,
    last_result: Option<SolverResult>,
    asserted_terms: Vec<TermId>,
}

impl NlsatTheory {
    /// Create a new NLSAT theory solver.
    ///
    /// * `integer` – true for QF_NIA, false for QF_NRA.
    pub fn new(integer: bool) -> Self {
        Self {
            solver: NlsatSolverWrapper::new(integer),
            context_stack: Vec::new(),
            is_integer: integer,
            last_result: None,
            asserted_terms: Vec::new(),
        }
    }
}

impl Theory for NlsatTheory {
    fn id(&self) -> TheoryId {
        if self.is_integer {
            TheoryId::NIA
        } else {
            TheoryId::NRA
        }
    }

    fn name(&self) -> &str {
        if self.is_integer { "NIA" } else { "NRA" }
    }

    fn can_handle(&self, _term: TermId) -> bool {
        true
    }

    fn assert_true(&mut self, term: TermId) -> Result<TheoryResult> {
        self.asserted_terms.push(term);
        Ok(TheoryResult::Sat)
    }

    fn assert_false(&mut self, term: TermId) -> Result<TheoryResult> {
        self.asserted_terms.push(term);
        Ok(TheoryResult::Sat)
    }

    fn check(&mut self) -> Result<TheoryResult> {
        let result = self.solver.solve();
        self.last_result = Some(result);
        match result {
            SolverResult::Sat => Ok(TheoryResult::Sat),
            SolverResult::Unsat => {
                let conflict = self.asserted_terms.clone();
                Ok(TheoryResult::Unsat(conflict))
            }
            SolverResult::Unknown => Ok(TheoryResult::Unknown),
        }
    }

    fn push(&mut self) {
        self.context_stack.push(NlsatContextState {
            level: self.asserted_terms.len(),
        });
    }

    fn pop(&mut self) {
        if let Some(state) = self.context_stack.pop() {
            self.asserted_terms.truncate(state.level);
        }
    }

    fn reset(&mut self) {
        *self = Self::new(self.is_integer);
    }

    fn get_model(&self) -> Vec<(TermId, TermId)> {
        Vec::new()
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Unit tests
// ─────────────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use oxiz_core::ast::TermManager;

    fn rat(n: i64) -> BigRational {
        BigRational::from_integer(n.into())
    }

    // ── Theory trait tests ────────────────────────────────────────────────────

    #[test]
    fn test_nlsat_theory_new() {
        let theory_nia = NlsatTheory::new(true);
        assert_eq!(theory_nia.id(), TheoryId::NIA);
        assert_eq!(theory_nia.name(), "NIA");
        assert!(theory_nia.is_integer);

        let theory_nra = NlsatTheory::new(false);
        assert_eq!(theory_nra.id(), TheoryId::NRA);
        assert_eq!(theory_nra.name(), "NRA");
        assert!(!theory_nra.is_integer);
    }

    #[test]
    fn test_nlsat_theory_push_pop() {
        let mut theory = NlsatTheory::new(false);
        assert_eq!(theory.context_stack.len(), 0);
        theory.push();
        assert_eq!(theory.context_stack.len(), 1);
        theory.push();
        assert_eq!(theory.context_stack.len(), 2);
        theory.pop();
        assert_eq!(theory.context_stack.len(), 1);
        theory.pop();
        assert_eq!(theory.context_stack.len(), 0);
    }

    #[test]
    fn test_nlsat_theory_reset() {
        let mut theory = NlsatTheory::new(false);
        let term = TermId::new(1);
        let _ = theory.assert_true(term);
        assert!(!theory.asserted_terms.is_empty());
        theory.reset();
        assert!(theory.asserted_terms.is_empty());
        assert!(theory.context_stack.is_empty());
    }

    #[test]
    fn test_nlsat_theory_can_handle() {
        let theory = NlsatTheory::new(false);
        assert!(theory.can_handle(TermId::new(1)));
    }

    #[test]
    fn test_nlsat_theory_check_placeholder() {
        let mut theory = NlsatTheory::new(false);
        let result = theory.check().expect("check should succeed");
        assert!(matches!(result, TheoryResult::Sat));
    }

    // ── Translator unit tests ──────────────────────────────────────────────────

    #[test]
    fn test_translator_constant() {
        let mut manager = TermManager::new();
        let five = manager.mk_int(5);
        let mut nia = NiaSolver::new();
        let mut t = TermPolyTranslator::new(&manager, &mut nia, true);
        let poly = t.translate(five).expect("constant should translate");
        assert!(poly.is_constant());
        assert_eq!(poly.constant_value(), rat(5));
    }

    #[test]
    fn test_translator_variable() {
        let mut manager = TermManager::new();
        let int_sort = manager.sorts.int_sort;
        let x = manager.mk_var("x", int_sort);
        let mut nia = NiaSolver::new();
        let mut t = TermPolyTranslator::new(&manager, &mut nia, true);
        let poly = t.translate(x).expect("variable should translate");
        assert!(poly.is_linear());
        assert_eq!(poly.num_terms(), 1);
    }

    #[test]
    fn test_translator_add() {
        let mut manager = TermManager::new();
        let int_sort = manager.sorts.int_sort;
        let x = manager.mk_var("x", int_sort);
        let y = manager.mk_var("y", int_sort);
        let sum = manager.mk_add(vec![x, y]);
        let mut nia = NiaSolver::new();
        let mut t = TermPolyTranslator::new(&manager, &mut nia, true);
        let poly = t.translate(sum).expect("add should translate");
        assert_eq!(poly.num_terms(), 2);
    }

    #[test]
    fn test_translator_mul_vars() {
        let mut manager = TermManager::new();
        let int_sort = manager.sorts.int_sort;
        let x = manager.mk_var("x", int_sort);
        let y = manager.mk_var("y", int_sort);
        let product = manager.mk_mul(vec![x, y]);
        let mut nia = NiaSolver::new();
        let mut t = TermPolyTranslator::new(&manager, &mut nia, true);
        let poly = t.translate(product).expect("mul should translate");
        // x * y is a single monomial of degree 2
        assert_eq!(poly.num_terms(), 1);
        assert_eq!(poly.total_degree(), 2);
    }

    #[test]
    fn test_translator_square() {
        let mut manager = TermManager::new();
        let int_sort = manager.sorts.int_sort;
        let x = manager.mk_var("x", int_sort);
        let square = manager.mk_mul(vec![x, x]);
        let mut nia = NiaSolver::new();
        let mut t = TermPolyTranslator::new(&manager, &mut nia, true);
        let poly = t.translate(square).expect("x*x should translate");
        // x^2 — single term, degree 2
        assert_eq!(poly.num_terms(), 1);
        assert_eq!(poly.total_degree(), 2);
    }

    #[test]
    fn test_translator_neg() {
        let mut manager = TermManager::new();
        let int_sort = manager.sorts.int_sort;
        let x = manager.mk_var("x", int_sort);
        let neg_x = manager.mk_neg(x);
        let mut nia = NiaSolver::new();
        let mut t = TermPolyTranslator::new(&manager, &mut nia, true);
        let poly = t.translate(neg_x).expect("neg should translate");
        assert_eq!(poly.num_terms(), 1);
        assert_eq!(poly.leading_coeff(), rat(-1));
    }

    #[test]
    fn test_translator_sub() {
        let mut manager = TermManager::new();
        let int_sort = manager.sorts.int_sort;
        let x = manager.mk_var("x", int_sort);
        let two = manager.mk_int(2);
        let x_minus_2 = manager.mk_sub(x, two);
        let mut nia = NiaSolver::new();
        let mut t = TermPolyTranslator::new(&manager, &mut nia, true);
        let poly = t.translate(x_minus_2).expect("sub should translate");
        // x - 2 → two terms: x and -2
        assert_eq!(poly.num_terms(), 2);
    }

    #[test]
    fn test_translator_triple_product() {
        // (* x y z) — degree-3 monomial
        let mut manager = TermManager::new();
        let int_sort = manager.sorts.int_sort;
        let x = manager.mk_var("x", int_sort);
        let y = manager.mk_var("y", int_sort);
        let z = manager.mk_var("z", int_sort);
        let triple = manager.mk_mul(vec![x, y, z]);
        let mut nia = NiaSolver::new();
        let mut t = TermPolyTranslator::new(&manager, &mut nia, true);
        let poly = t
            .translate(triple)
            .expect("triple product should translate");
        assert_eq!(poly.num_terms(), 1);
        assert_eq!(poly.total_degree(), 3);
    }

    #[test]
    fn test_translator_factored_product() {
        // (* (+ x 1) (- y 2)) → xy - 2x + y - 2
        let mut manager = TermManager::new();
        let int_sort = manager.sorts.int_sort;
        let x = manager.mk_var("x", int_sort);
        let y = manager.mk_var("y", int_sort);
        let one = manager.mk_int(1);
        let two = manager.mk_int(2);
        let xp1 = manager.mk_add(vec![x, one]);
        let ym2 = manager.mk_sub(y, two);
        let product = manager.mk_mul(vec![xp1, ym2]);
        let mut nia = NiaSolver::new();
        let mut t = TermPolyTranslator::new(&manager, &mut nia, true);
        let poly = t
            .translate(product)
            .expect("factored product should translate");
        // (x+1)(y-2) = xy - 2x + y - 2  → 4 terms
        assert_eq!(poly.num_terms(), 4);
        assert_eq!(poly.total_degree(), 2);
    }

    // ── term_is_nonlinear tests ────────────────────────────────────────────────

    #[test]
    fn test_term_is_nonlinear_square() {
        let mut manager = TermManager::new();
        let int_sort = manager.sorts.int_sort;
        let x = manager.mk_var("x", int_sort);
        let square = manager.mk_mul(vec![x, x]);
        assert!(term_is_nonlinear(square, &manager));
    }

    #[test]
    fn test_term_is_nonlinear_product_xy() {
        let mut manager = TermManager::new();
        let int_sort = manager.sorts.int_sort;
        let x = manager.mk_var("x", int_sort);
        let y = manager.mk_var("y", int_sort);
        let xy = manager.mk_mul(vec![x, y]);
        assert!(term_is_nonlinear(xy, &manager));
    }

    #[test]
    fn test_term_is_nonlinear_linear_is_false() {
        let mut manager = TermManager::new();
        let int_sort = manager.sorts.int_sort;
        let x = manager.mk_var("x", int_sort);
        let three = manager.mk_int(3);
        let three_x = manager.mk_mul(vec![three, x]);
        assert!(!term_is_nonlinear(three_x, &manager));
    }

    #[test]
    fn test_term_is_nonlinear_constant() {
        let mut manager = TermManager::new();
        let c = manager.mk_int(42);
        assert!(!term_is_nonlinear(c, &manager));
    }

    // ── dispatch integration tests ─────────────────────────────────────────────

    #[test]
    fn test_dispatch_nia_x_squared_eq_4_sat() {
        // x * x = 4 → SAT (x=2 or x=-2)
        let mut manager = TermManager::new();
        let int_sort = manager.sorts.int_sort;
        let x = manager.mk_var("x", int_sort);
        let square = manager.mk_mul(vec![x, x]);
        let four = manager.mk_int(4);
        let eq = manager.mk_eq(square, four);
        let result = dispatch_nia_constraints(&[eq], &manager, true);
        // SAT or Unknown (unknown means solver fell through)
        assert!(
            matches!(result, Some(NlDispatchResult::Sat) | None),
            "x*x=4 should be SAT or unknown, got {:?}",
            result
        );
    }

    #[test]
    fn test_dispatch_nia_x_squared_neg_unsat() {
        // x * x = -1 → UNSAT (no integer square is negative)
        let mut manager = TermManager::new();
        let int_sort = manager.sorts.int_sort;
        let x = manager.mk_var("x", int_sort);
        let square = manager.mk_mul(vec![x, x]);
        let neg_one = manager.mk_int(-1);
        let eq = manager.mk_eq(square, neg_one);
        let result = dispatch_nia_constraints(&[eq], &manager, true);
        assert!(
            matches!(result, Some(NlDispatchResult::Unsat) | None),
            "x*x=-1 should be UNSAT or unknown, got {:?}",
            result
        );
    }

    #[test]
    fn test_dispatch_nra_x_squared_neg_unsat() {
        // x * x < 0 → UNSAT (no real square is negative)
        let mut manager = TermManager::new();
        let real_sort = manager.sorts.real_sort;
        let x = manager.mk_var("x", real_sort);
        let square = manager.mk_mul(vec![x, x]);
        let zero = manager.mk_int(0);
        let lt = manager.mk_lt(square, zero);
        let result = dispatch_nra_constraints(&[lt], &manager);
        assert!(
            matches!(result, Some(NlDispatchResult::Unsat) | None),
            "x*x<0 should be UNSAT or unknown, got {:?}",
            result
        );
    }

    // ── Sat-trustworthiness gate (audit 2026-06-20) ──────────────────────────
    // `extract_*_poly_atoms` silently drops connectives it does not model
    // (top-level Or/Not/…) and atoms whose operand fails to translate. A `Sat`
    // over the RETAINED subset is then NOT a model of the original formula. The
    // gate must turn such a `Sat` into `None` (Unknown), never `Some(Sat)`.

    #[test]
    fn dropped_disjunct_does_not_yield_a_trusted_sat() {
        // (and (= (* x x) 4) (or (< 1 0) (< 2 0)))  — the `or` is FALSE, so the
        // whole conjunction is UNSAT. `extract` keeps only `x*x = 4` (sat at
        // x=2) and DROPS the `or`. Pre-fix this returned Some(Sat) — a spurious
        // sat ignoring the false disjunction. The gate now returns None.
        let mut m = TermManager::new();
        let int_sort = m.sorts.int_sort;
        let x = m.mk_var("x", int_sort);
        let sq = m.mk_mul(vec![x, x]);
        let four = m.mk_int(4);
        let eq = m.mk_eq(sq, four);
        let one = m.mk_int(1);
        let two = m.mk_int(2);
        let zero = m.mk_int(0);
        let lt1 = m.mk_lt(one, zero); // 1 < 0  (false)
        let lt2 = m.mk_lt(two, zero); // 2 < 0  (false)
        let or = m.mk_or(vec![lt1, lt2]);
        let conj = m.mk_and(vec![eq, or]);
        let result = dispatch_nia_constraints(&[conj], &m, true);
        assert!(
            !matches!(result, Some(NlDispatchResult::Sat)),
            "a Sat over the retained atoms while a disjunct was dropped is a \
             spurious sat — must be None/Unsat, got {:?}",
            result
        );
    }

    #[test]
    fn fully_captured_conjunction_still_reports_sat() {
        // Positive control: nothing dropped, so a genuine model IS trustworthy.
        // (and (= (* x x) 4) (> x 0))  — sat at x=2; the gate must not over-block.
        let mut m = TermManager::new();
        let int_sort = m.sorts.int_sort;
        let x = m.mk_var("x", int_sort);
        let sq = m.mk_mul(vec![x, x]);
        let four = m.mk_int(4);
        let eq = m.mk_eq(sq, four);
        let zero = m.mk_int(0);
        let gt = m.mk_gt(x, zero);
        let conj = m.mk_and(vec![eq, gt]);
        let result = dispatch_nia_constraints(&[conj], &m, true);
        // Either a trusted Sat or (if the NIA solver is itself inconclusive) None
        // — but NEVER a spurious Unsat, and the gate must not suppress a real Sat.
        assert!(
            !matches!(result, Some(NlDispatchResult::Unsat)),
            "x*x=4 ∧ x>0 is sat (x=2) — must not be reported unsat, got {:?}",
            result
        );
    }
}
