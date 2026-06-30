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
use num_traits::{ToPrimitive, Zero};
use oxiz_core::ast::{TermId, TermKind, TermManager};
use oxiz_core::error::Result;
use oxiz_math::polynomial::Polynomial;
use oxiz_nlsat::discriminant::{AtomCmp, quadratic_atom_is_unsat, quadratic_form_is_unsat};
use oxiz_nlsat::nia::{NiaConfig, NiaSolver, VarType};
use oxiz_nlsat::solver::{Model, NlsatSolver, SolverResult};
use oxiz_nlsat::types::AtomKind;
use std::collections::HashMap;

use crate::fd_core;

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
    /// Set the moment `integer_mode` integerizes a **real-sorted** variable (see
    /// `get_or_create_var`). Integerizing a real var STRENGTHENS its constraint
    /// (ℤ ⊂ ℝ), so a verdict over the integerized atoms is unsound for the real
    /// problem — the `fd_core` add-on declines to trust its `Unsat`/`Sat` when this
    /// is set. (The legacy `NiaSolver` path was incidentally protected by its
    /// `total_degree ≤ 1` gate; `fd_core` removes that gate, so it needs this
    /// explicit guard.)
    integerized_real: bool,
}

impl<'a> TermPolyTranslator<'a> {
    /// Create a new translator.
    pub fn new(manager: &'a TermManager, nlsat: &'a mut NiaSolver, integer_mode: bool) -> Self {
        Self {
            manager,
            nlsat,
            var_cache: HashMap::new(),
            integer_mode,
            integerized_real: false,
        }
    }

    /// Whether a real-sorted variable was integerized during translation (the
    /// `fd_core` add-on must not trust its verdict if so).
    #[must_use]
    pub fn integerized_real(&self) -> bool {
        self.integerized_real
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
            // Flag the unsound case: integerizing a genuinely real-sorted variable
            // (the fd_core add-on reads this and declines to trust its verdict).
            if self.manager.get(term_id).map(|t| t.sort) == Some(self.manager.sorts.real_sort) {
                self.integerized_real = true;
            }
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
        TermKind::Add(args)
        | TermKind::And(args)
        | TermKind::Or(args)
        // A `distinct`/`Or` (and a negated comparison, below) can carry a nonlinear
        // arith atom too — they MUST be recursed so `has_nl` is set, else the
        // dispatch returns before the (sound) fd_core consult ever sees the atom.
        // This is what let `x=0 ∧ x²≠0` (= `0≠0` under the absorbing element) reach
        // CDCL(T) and be wrongly reported sat.
        | TermKind::Distinct(args) => args.iter().any(|&a| term_is_nonlinear(a, manager)),
        TermKind::Sub(lhs, rhs)
        | TermKind::Eq(lhs, rhs)
        | TermKind::Gt(lhs, rhs)
        | TermKind::Ge(lhs, rhs)
        | TermKind::Lt(lhs, rhs)
        | TermKind::Le(lhs, rhs)
        | TermKind::Implies(lhs, rhs)
        | TermKind::Xor(lhs, rhs) => {
            term_is_nonlinear(*lhs, manager) || term_is_nonlinear(*rhs, manager)
        }
        TermKind::Neg(inner) | TermKind::Not(inner) => term_is_nonlinear(*inner, manager),
        TermKind::Ite(c, t, e) => {
            term_is_nonlinear(*c, manager)
                || term_is_nonlinear(*t, manager)
                || term_is_nonlinear(*e, manager)
        }
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
        TermKind::Not(inner) => {
            // A negated arith comparison surfaces as the polarity-FLIPPED atom, so
            // disequalities `¬(=)` (and negated inequalities) REACH the engine — which
            // then decides them via its zero-absorbing interval evaluation: a factor
            // forced to 0 makes the whole product 0, refuting e.g. `x²≠0` under `x=0`
            // (`0·_ = 0` in any ring). `¬(And/Or/…)` is not a single atom — drop it.
            let is_cmp = matches!(
                manager.get(*inner).map(|term| &term.kind),
                Some(
                    TermKind::Eq(_, _)
                        | TermKind::Lt(_, _)
                        | TermKind::Le(_, _)
                        | TermKind::Gt(_, _)
                        | TermKind::Ge(_, _)
                )
            );
            if is_cmp {
                let before = out.len();
                let dropped = extract_poly_atoms(*inner, manager, translator, out);
                for atom in out.iter_mut().skip(before) {
                    atom.positive = !atom.positive;
                }
                dropped
            } else {
                true
            }
        }
        TermKind::Distinct(args) => {
            // `distinct(a₁..aₙ)` = pairwise `aᵢ ≠ aⱼ`; each is a `≠ 0` atom on
            // `aᵢ − aⱼ` (the shape the simplifier's desugar also produces — handled
            // here too in case an unsimplified `distinct` reaches the dispatch).
            let args: Vec<TermId> = args.to_vec();
            let mut dropped = false;
            for i in 0..args.len() {
                for j in (i + 1)..args.len() {
                    if let (Some(lp), Some(rp)) =
                        (translator.translate(args[i]), translator.translate(args[j]))
                    {
                        out.push(PolyAtom {
                            poly: Polynomial::sub(&lp, &rp),
                            kind: AtomKind::Eq,
                            positive: false, // aᵢ ≠ aⱼ
                        });
                    } else {
                        dropped = true;
                    }
                }
            }
            dropped
        }
        _ => true,
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Reduction-KB rule §G — definite-sign by discriminant (univariate quadratic)
// ─────────────────────────────────────────────────────────────────────────────

/// Map a built [`PolyAtom`] (its `kind` + `positive` flag) to the comparison the
/// literal asserts on `atom.poly` in canonical `poly OP 0` form — the input shape
/// [`quadratic_atom_is_unsat`] expects. Returns `None` for a literal §G does not
/// model (a negated equality `poly ≠ 0`, which a non-constant quadratic always
/// satisfies somewhere, or a root atom), so the caller declines that atom.
fn poly_atom_cmp(atom: &PolyAtom) -> Option<AtomCmp> {
    match (atom.kind, atom.positive) {
        (AtomKind::Eq, true) => Some(AtomCmp::Eq),  // poly = 0
        (AtomKind::Gt, true) => Some(AtomCmp::Gt),  // poly > 0
        (AtomKind::Gt, false) => Some(AtomCmp::Le), // ¬(poly > 0) ≡ poly ≤ 0
        (AtomKind::Lt, true) => Some(AtomCmp::Lt),  // poly < 0
        (AtomKind::Lt, false) => Some(AtomCmp::Ge), // ¬(poly < 0) ≡ poly ≥ 0
        _ => None,
    }
}

/// Map a built [`PolyAtom`] to the [`fd_core`](crate::fd_core) comparison on
/// `atom.poly` in canonical `poly OP 0` form. Total over the kinds
/// [`extract_poly_atoms`] produces (`Eq`/`Gt`/`Lt` × polarity, covering `≠` via
/// `¬(=)`); `None` for any other kind (a `Root*` atom), which the caller treats as
/// "fd cannot model this atom" (it drops that atom, weakening the conjunction —
/// sound for `Unsat`, and forbidden for `Sat`).
fn poly_atom_to_fd(atom: &PolyAtom) -> Option<(Polynomial, fd_core::FdCmp)> {
    use fd_core::FdCmp;
    let op = match (atom.kind, atom.positive) {
        (AtomKind::Eq, true) => FdCmp::Eq,
        (AtomKind::Eq, false) => FdCmp::Ne,
        (AtomKind::Gt, true) => FdCmp::Gt,
        (AtomKind::Gt, false) => FdCmp::Le,
        (AtomKind::Lt, true) => FdCmp::Lt,
        (AtomKind::Lt, false) => FdCmp::Ge,
        _ => return None,
    };
    Some((atom.poly.clone(), op))
}

/// Reduction-KB rule §G: definite-sign completeness pre-check.
///
/// Every [`PolyAtom`] in `poly_atoms` is a TOP-LEVEL CONJUNCT of the (focused)
/// assertion set — both `extract_poly_atoms` and `extract_real_poly_atoms` only
/// descend into `And` and the comparison atoms (every other connective hits the
/// dropped `_` arm), so every pushed atom is ENTAILED by the conjunction. If a
/// single entailed atom is itself unsatisfiable over ℝ — a quadratic whose asserted
/// sign is impossible — the whole conjunction is UNSAT. Two recognisers, both exact
/// and one-sided:
/// - [`quadratic_atom_is_unsat`] — the UNIVARIATE quadratic by its discriminant
///   `D = b²−4ac`, e.g. `x²−2x+1 < 0` (a perfect square is never negative); the
///   primitive `x² ≥ 0` is the `a=1,b=0,c=0` instance.
/// - [`quadratic_form_is_unsat`] — the MULTIVARIATE quadratic form by its Gram
///   matrix (PSD / SOS), e.g. `(x−y)² < 0` (`x²−2xy+y² < 0`) is UNSAT because the
///   Gram matrix `[[1,−1],[−1,1]]` is positive-semidefinite.
///
/// SOUNDNESS: returns `true` ONLY for a genuine real-domain UNSAT atom (exact
/// rationals; indefinite / non-quadratic / too-wide forms decline). A real-domain
/// UNSAT is a fortiori an integer-domain UNSAT (`∀ real x` ⟹ `∀ int x`), so this
/// is sound for BOTH the NRA and the NIA dispatch. It never reports Sat and never a
/// wrong Unsat; being a single-conjunct witness, it stays valid even when other
/// atoms were dropped (subset-unsat ⟹ full-unsat).
fn definite_sign_unsat(poly_atoms: &[PolyAtom]) -> bool {
    poly_atoms.iter().any(|atom| {
        poly_atom_cmp(atom)
            .map(|op| {
                quadratic_atom_is_unsat(&atom.poly, op)
                    || quadratic_form_is_unsat(&atom.poly, op)
            })
            .unwrap_or(false)
    })
}

/// Evaluate `poly` at a model's rational assignment, mirroring
/// [`Polynomial::eval`] but returning `None` (instead of panicking) when any
/// variable of `poly` is UNASSIGNED in the model — an incomplete model that the
/// caller must NOT trust.
fn eval_poly_at_model(poly: &Polynomial, model: &Model) -> Option<BigRational> {
    let mut acc = BigRational::zero();
    for term in poly.terms() {
        let mut v = term.coeff.clone();
        for vp in term.monomial.vars() {
            let val = model.arith_value(vp.var)?;
            v *= val.pow(vp.power as i32);
        }
        acc += v;
    }
    Some(acc)
}

/// Does `model` actually satisfy EVERY retained atom? A SAT verdict from the core
/// nlsat/nia solver is only trustworthy when its returned model genuinely makes
/// each atom literal true — the core is known to over-report `Sat` on some
/// multivariate strict-inequality / integer-infeasible shapes (e.g. it hands back
/// a boundary point that violates a strict `<`/`>`, or a non-integer relaxation).
/// This re-checks the model EXACTLY over the rationals; an incomplete model (a
/// poly var unassigned), or an algebraic value only present as a rational
/// APPROXIMATION (`arith_values` holds the interval midpoint — so an `Eq` may not
/// hold exactly) conservatively fails the check → the caller downgrades the `Sat`
/// to `None` (Unknown). This NEVER turns a `Sat` into `Unsat`, so it cannot
/// introduce a false `unsat`; it only refuses to vouch for an unverified model.
fn model_satisfies_atoms(model: &Model, atoms: &[PolyAtom]) -> bool {
    atoms.iter().all(|atom| {
        let Some(val) = eval_poly_at_model(&atom.poly, model) else {
            return false;
        };
        let zero = BigRational::zero();
        let holds = match atom.kind {
            AtomKind::Eq => val == zero,
            AtomKind::Lt => val < zero,
            AtomKind::Gt => val > zero,
            // Root atoms (RootEq/RootLt/RootGt) are not produced by the
            // extractors and not modeled here — refuse to vouch.
            _ => return false,
        };
        if atom.positive { holds } else { !holds }
    })
}

// ─────────────────────────────────────────────────────────────────────────────
// Sound nonlinear oracle: oxiz-nl2
// ─────────────────────────────────────────────────────────────────────────────

/// Map a local `(AtomKind, positive)` literal to oxiz-nl2's `AtomCmp`.
/// Returns `None` for the `Root*` kinds (which oxiz-nl2 does not model as a
/// plain `p ⋈ 0` comparison, and which the extractors never produce anyway).
fn nl2_atom_cmp(kind: AtomKind, positive: bool) -> Option<oxiz_nl2::AtomCmp> {
    use oxiz_nl2::AtomCmp as C;
    Some(match (kind, positive) {
        (AtomKind::Eq, true) => C::Eq,
        (AtomKind::Eq, false) => C::Ne,
        (AtomKind::Lt, true) => C::Lt,
        (AtomKind::Lt, false) => C::Ge,
        (AtomKind::Gt, true) => C::Gt,
        (AtomKind::Gt, false) => C::Le,
        _ => return None, // Root* — never produced by the extractors
    })
}

/// Consult **oxiz-nl2** (the clean-room sound nonlinear solver) on the
/// conjunction `poly_atoms`. Both of nl2's verdicts are runtime-verified —
/// `Sat` by **G-SAT** (an exact model re-check) and `Unsat` by **G-UNSAT** (a
/// covering re-verify), giving `FALSE_SAT = FALSE_UNSAT = 0` by construction —
/// so they are trusted directly, REPLACING the legacy `NlsatSolver`/`NiaSolver`
/// nonlinear verdicts a z3-differential proved broadly unsound:
///
///   * `Unsat` ⇒ `Some(Unsat)` — sound for the full formula even if a subterm
///     was `dropped` (a sub-core's unsat ⟹ full unsat).
///   * `Sat`   ⇒ `Some(Sat)` ONLY when `!dropped`: G-SAT verifies the model
///     against the RETAINED atoms, so a dropped constraint could be exactly the
///     one a retained-subset model violates.
///   * `Unknown` (or `Sat` with a dropped atom, or a `Root*` atom nl2 cannot
///     model) ⇒ `None`: fall through to the caller's remaining logic.
///
/// `sort` is `Integer` on the NIA path and `Real` on the NRA path; the caller
/// must NOT pass `Integer` when a real-sorted variable was integerized (the
/// strengthened ℤ-system's verdict is unsound for the original ℝ-problem).
fn nl2_dispatch(
    poly_atoms: &[PolyAtom],
    dropped: bool,
    sort: oxiz_nl2::VarSort,
) -> Option<NlDispatchResult> {
    let mut atoms = Vec::with_capacity(poly_atoms.len());
    for (i, a) in poly_atoms.iter().enumerate() {
        let op = nl2_atom_cmp(a.kind, a.positive)?; // Root* ⇒ bail the oracle
        atoms.push(oxiz_nl2::PolyAtom::new(
            a.poly.clone(),
            op,
            sort,
            oxiz_nl2::OriginId(i as u32),
        ));
    }
    match oxiz_nl2::check(&atoms) {
        oxiz_nl2::Verdict::Unsat(_) => Some(NlDispatchResult::Unsat),
        oxiz_nl2::Verdict::Sat(_) if !dropped => Some(NlDispatchResult::Sat),
        _ => None,
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

    // Reduction-KB rule §G (definite-sign by discriminant): a univariate-quadratic
    // conjunct whose asserted sign is impossible (e.g. the perfect square
    // `(x−1)² < 0`) makes the whole conjunction UNSAT — decided exactly from a
    // single `b²−4ac`, no root isolation. Real-domain UNSAT ⟹ integer-domain
    // UNSAT, so this is sound on the NIA (integer) path.
    if definite_sign_unsat(&poly_atoms) {
        return Some(NlDispatchResult::Unsat);
    }

    // Sound nonlinear oracle (oxiz-nl2): trust both runtime-verified verdicts,
    // replacing the legacy `NiaSolver` nonlinear `unsat`/`sat` below. On the
    // integer path, skip when a real-sorted variable was integerized — the
    // strengthened ℤ-system's verdict is unsound for the original ℝ-problem (same
    // guard fd_core uses).
    let nl2_sort = if integer_mode {
        oxiz_nl2::VarSort::Integer
    } else {
        oxiz_nl2::VarSort::Real
    };
    if (!integer_mode || !translator.integerized_real())
        && let Some(v) = nl2_dispatch(&poly_atoms, dropped, nl2_sort)
    {
        return Some(v);
    }

    // SOUNDNESS — the legacy `NiaSolver`'s `Unsat` is no longer trusted at all (the
    // old `total_degree ≤ 1` linear-fragment band-aid was itself unsound — see the
    // `solve()` match below). Sound integer `unsat` is provided by §G/§G-SOS
    // (`definite_sign_unsat`, above), nl2, and fd_core; integer-specific unsat
    // (`x² = 3`, not a perfect square) by `check_nonlinear_constraints`.
    // A `Sat` over the RETAINED atoms is only valid for the original formula when
    // every assertion was fully captured — no connective dropped, no operand
    // untranslatable. Otherwise a dropped constraint could be the one a
    // subset-model violates → spurious sat (the nlsat soundness hole). When it is
    // NOT trustworthy we return `None` (Unknown) and let the full CDCL(T) path
    // decide, rather than trusting nlsat's `Sat`.
    let sat_is_trustworthy = !dropped && !has_unsupported_ops;

    // ── Sound nonlinear-integer add-on: fd_core (the oxiz-nl2 `fdlcg` engine) ──
    // The legacy `NiaSolver` is broadly unsound on nonlinear `unsat`, so
    // `unsat_is_trustworthy` blocks every total-degree ≥ 2 refutation above. The
    // `fd_core` finite-domain engine decides nonlinear-integer `unsat` SOUNDLY
    // (interval over-approximation + G-UNSAT re-verify), filling exactly that gap.
    // It runs only in integer mode (fd_core is integer-only) and BEFORE the
    // NiaSolver solve — a definitive verdict short-circuits it (like §G above).
    //
    //   * `Unsat` is trusted unconditionally: `fd_atoms ⊆ poly_atoms ⊆` the
    //     original constraints, and subset-unsat ⟹ full-unsat (adding constraints
    //     only shrinks feasibility) — the same argument `definite_sign_unsat` uses.
    //   * `Sat` is trusted ONLY when the conjunction is the WHOLE problem
    //     (`sat_is_trustworthy` ∧ every poly atom mapped to fd) — a dropped
    //     constraint could be the one a subset-model violates.
    //
    // GUARD: skip fd entirely if the translator integerized a real-sorted variable
    // — those integer atoms are a STRENGTHENING of the real constraints (ℤ ⊂ ℝ), so
    // neither fd's `Unsat` (the strengthened system can be unsat while the real one
    // is sat — a false UNSAT) nor its `Sat` would be sound. The legacy path below
    // is incidentally protected by its `total_degree ≤ 1` trust gate; fd has none,
    // so it needs this explicit check. (Found by an adversarial soundness review.)
    if integer_mode && !translator.integerized_real() {
        let mut fd_atoms = Vec::with_capacity(poly_atoms.len());
        let mut fd_all_mapped = true;
        for atom in &poly_atoms {
            match poly_atom_to_fd(atom) {
                Some(fa) => fd_atoms.push(fa),
                None => fd_all_mapped = false, // a Root* atom fd can't model
            }
        }
        if !fd_atoms.is_empty() {
            match fd_core::decide(&fd_atoms) {
                fd_core::FdDecision::Unsat => return Some(NlDispatchResult::Unsat),
                fd_core::FdDecision::Sat(_) if sat_is_trustworthy && fd_all_mapped => {
                    return Some(NlDispatchResult::Sat);
                }
                _ => {} // Open / untrusted Sat → fall through to the NiaSolver path
            }
        }
    }

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
        // The legacy `NiaSolver`'s UNSAT is NEVER trusted. The old
        // `unsat_is_trustworthy = total_degree ≤ 1` band-aid assumed it was sound
        // at least on the LINEAR fragment, but it false-`unsat`s even there once a
        // SYNTACTICALLY nonlinear problem cancels to linear (`x=y ∧ 2x=−5z ∧ y≥18`:
        // the `y²` cancels, the poly set is degree 1, the term is routed here as
        // nonlinear, and `NiaSolver` decided a spurious `unsat` the band-aid
        // trusted). Sound integer `unsat` comes from §G (`definite_sign_unsat`),
        // nl2, and fd_core (each above — exact / `g_unsat_reverify`'d); a legacy
        // `unsat` falls through to `None` so the CDCL(T)/ArithSolver path decides.
        // Only the model-verified `Sat` is taken from the legacy solver: trust it
        // only when the returned model genuinely satisfies every atom (the NIA
        // branch-and-bound over-reports `Sat` on integer-infeasible shapes like
        // `x²=3`). Unverified / incomplete model → `None` (Unknown).
        SolverResult::Sat if sat_is_trustworthy => {
            match translator.nlsat.nlsat().get_model() {
                Some(m) if model_satisfies_atoms(&m, &poly_atoms) => {
                    Some(NlDispatchResult::Sat)
                }
                _ => None,
            }
        }
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

    // Reduction-KB rule §G (definite-sign by discriminant): a univariate-quadratic
    // conjunct whose asserted sign is impossible (e.g. `(x−1)² < 0`) makes the
    // whole conjunction UNSAT — decided exactly from `b²−4ac`, no root isolation.
    if definite_sign_unsat(&poly_atoms) {
        return Some(NlDispatchResult::Unsat);
    }

    // Sound nonlinear oracle (oxiz-nl2): trust both runtime-verified verdicts,
    // replacing the legacy `NlsatSolver` nonlinear `unsat`/`sat` below.
    if let Some(v) = nl2_dispatch(&poly_atoms, dropped, oxiz_nl2::VarSort::Real) {
        return Some(v);
    }

    // SOUNDNESS — an `Unsat` from the core real `NlsatSolver` is trustworthy ONLY
    // when every retained atom is LINEAR. A z3-differential exposed the core as
    // broadly UNSOUND on nonlinear `unsat` at EVERY degree (single-atom false-
    // `unsat` rates: deg-2 13%, deg-3 32%, deg-4 16% — e.g. `3x² < 5` ⟺
    // `x² < 5/3` is decided a spurious `unsat`), and on the bilinear `x*y > 5`.
    // Only the linear fragment (where the verdict is LRA's) is reliable. The SOUND
    // nonlinear `unsat` is supplied UP-FRONT, before this gate, by §G/§G-SOS
    // (`definite_sign_unsat` — univariate-quadratic discriminant + multivariate
    // PSD form) and by the trichotomy/bound-infeasibility pre-check
    // (`check_term_bound_infeasible`). A nonlinear `unsat` the core alone would
    // claim is DISTRUSTED → `None` → the sound `Unknown`/Sat fallback (never a
    // false `unsat`; the verus-dangerous direction is closed).
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
        // The core real `NlsatSolver`'s UNSAT is NEVER trusted: a z3-differential
        // proved it broadly unsound on nonlinear `unsat` (every degree), and the
        // old `total_degree ≤ 1` linear-fragment band-aid is unsound too (the NIA
        // twin false-`unsat`s linear-after-cancellation systems). Sound nonlinear
        // `unsat` is supplied UP-FRONT by §G/§G-SOS (`definite_sign_unsat`), nl2,
        // and the trichotomy/bound pre-check; a core `unsat` falls through to `None`
        // (the sound `Unknown`/Sat fallback). Only the model-verified `Sat` is
        // taken: trust it only when the returned model genuinely satisfies every
        // atom (the core over-reports `Sat` on some multivariate strict
        // inequalities — a boundary point violating a strict `<`/`>`). Unverified /
        // incomplete model → `None` (Unknown).
        SolverResult::Sat if sat_is_trustworthy => {
            match translator.nlsat.get_model() {
                Some(m) if model_satisfies_atoms(&m, &poly_atoms) => {
                    Some(NlDispatchResult::Sat)
                }
                _ => None,
            }
        }
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

    #[test]
    fn fd_addon_skips_when_real_var_integerized() {
        // `x*x = 4 ∧ 0 ≤ x ≤ 3 ∧ 1 < y < 2` with x:Int, y:Real is SAT (x=2, y=1.5).
        // Translating with integer_mode=true integerizes the real var y, so the
        // integer view `1 < y < 2` is empty — fd_core would refute the strengthened
        // system, a FALSE UNSAT. The `integerized_real` guard must make the fd
        // consult DECLINE (returning `None`/Unknown here), never a false `Unsat`.
        // (Regression for the adversarial-review finding; without the guard this
        // returns `Some(Unsat)`.)
        let mut m = TermManager::new();
        let int = m.sorts.int_sort;
        let real = m.sorts.real_sort;
        let x = m.mk_var("x", int);
        let y = m.mk_var("y", real);
        let sq = m.mk_mul([x, x]);
        let four = m.mk_int(4);
        let eq = m.mk_eq(sq, four); // x*x = 4
        let zero = m.mk_int(0);
        let three = m.mk_int(3);
        let xlo = m.mk_ge(x, zero);
        let xhi = m.mk_le(x, three);
        let one = m.mk_real(num_rational::Rational64::from_integer(1));
        let two = m.mk_real(num_rational::Rational64::from_integer(2));
        let ylo = m.mk_gt(y, one); // 1 < y
        let yhi = m.mk_lt(y, two); // y < 2

        let r = dispatch_nia_constraints(&[eq, xlo, xhi, ylo, yhi], &m, true);
        assert_ne!(
            r,
            Some(NlDispatchResult::Unsat),
            "integerizing a real var must NOT yield a false UNSAT (the fd guard must decline)"
        );
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

    // ── Reduction-KB rule §G: definite-sign by discriminant (dispatch wiring) ──
    // The completeness rule the verus perfect-square lead asked for. These check
    // the WIRING (PolyAtom → AtomCmp → `quadratic_atom_is_unsat`) in both
    // dispatch entry points; the recogniser's own classification is unit-tested
    // in `oxiz_nlsat::discriminant`. The DECISIVE cases must be `Some(Unsat)`
    // (the rule is exact, not best-effort); the SOUNDNESS cases must never be
    // `Some(Unsat)` (a definite-sign rule that fires on a satisfiable atom is a
    // false verdict on the whole verus nonlinear path).

    /// Build `x² − 2x + 1` (= `(x−1)²`) over `sort` as `Add(Sub(x*x, 2x), 1)`.
    fn perfect_square(m: &mut TermManager, x: TermId) -> TermId {
        let xx = m.mk_mul(vec![x, x]);
        let two = m.mk_int(2);
        let two_x = m.mk_mul(vec![two, x]);
        let diff = m.mk_sub(xx, two_x);
        let one = m.mk_int(1);
        m.mk_add(vec![diff, one])
    }

    #[test]
    fn nra_bilinear_strict_inequality_not_false_unsat() {
        // SOUNDNESS (the pre-existing core-NRA bilinear hole this gate closes):
        // `x*y > 5` is SATISFIABLE (x=10, y=½) but the core real `NlsatSolver`
        // decides it a spurious `unsat`. The `unsat_is_trustworthy` gate now
        // requires every atom to be UNIVARIATE, so a bivariate atom's `unsat` is
        // distrusted → `None` (sound Unknown), NEVER a false `unsat`.
        let mut m = TermManager::new();
        let real_sort = m.sorts.real_sort;
        let x = m.mk_var("x", real_sort);
        let y = m.mk_var("y", real_sort);
        let xy = m.mk_mul(vec![x, y]);
        let five = m.mk_int(5);
        let gt = m.mk_gt(xy, five);
        assert_ne!(
            dispatch_nra_constraints(&[gt], &m),
            Some(NlDispatchResult::Unsat),
            "x*y > 5 is satisfiable — the NRA gate must not trust the core's spurious unsat"
        );
        // And `x*y < 0` (also satisfiable, x=1,y=−1) — same.
        let zero = m.mk_int(0);
        let lt = m.mk_lt(xy, zero);
        assert_ne!(
            dispatch_nra_constraints(&[lt], &m),
            Some(NlDispatchResult::Unsat),
            "x*y < 0 is satisfiable — must not be a false unsat"
        );
    }

    #[test]
    fn nia_integer_infeasible_square_not_false_sat() {
        // SOUNDNESS (Sat-model backstop): `x*x = 3` over the integers is UNSAT (3
        // is not a perfect square), but the NIA branch-and-bound over-reports
        // `Sat`. The model-verification backstop re-checks the returned model and,
        // finding it does not satisfy `x²=3` exactly, downgrades the `Sat` to
        // `None` (Unknown) — never `Some(Sat)`.
        let mut m = TermManager::new();
        let int_sort = m.sorts.int_sort;
        let x = m.mk_var("x", int_sort);
        let xx = m.mk_mul(vec![x, x]);
        let three = m.mk_int(3);
        let eq = m.mk_eq(xx, three);
        assert_ne!(
            dispatch_nia_constraints(&[eq], &m, true),
            Some(NlDispatchResult::Sat),
            "x*x = 3 over integers is unsatisfiable — the backstop must not trust a \
             spurious sat (its model does not satisfy x²=3)"
        );
    }

    #[test]
    fn nia_perfect_square_eq_still_sat() {
        // POSITIVE control: `x*x = 4` IS sat (x=±2); the backstop must NOT
        // over-block — the returned integer model satisfies `x²=4` exactly.
        let mut m = TermManager::new();
        let int_sort = m.sorts.int_sort;
        let x = m.mk_var("x", int_sort);
        let xx = m.mk_mul(vec![x, x]);
        let four = m.mk_int(4);
        let eq = m.mk_eq(xx, four);
        // Sat (verified model) or None if the core is inconclusive — but NEVER a
        // spurious Unsat, and the backstop must not suppress a genuine model.
        assert_ne!(
            dispatch_nia_constraints(&[eq], &m, true),
            Some(NlDispatchResult::Unsat),
            "x*x = 4 is sat (x=2) — must not be reported unsat"
        );
    }

    #[test]
    fn g_perfect_square_lt_zero_is_unsat_nia() {
        // THE BAR (verus `x*x - 2*x + 1 >= 0`, negated goal): `(x−1)² < 0` is
        // UNSAT (D=0, a>0 ⇒ f ≥ 0 ∀x). Must be DECISIVELY unsat now.
        let mut m = TermManager::new();
        let int_sort = m.sorts.int_sort;
        let x = m.mk_var("x", int_sort);
        let f = perfect_square(&mut m, x);
        let zero = m.mk_int(0);
        let lt = m.mk_lt(f, zero);
        assert_eq!(
            dispatch_nia_constraints(&[lt], &m, true),
            Some(NlDispatchResult::Unsat),
            "(x-1)^2 < 0 is unsatisfiable — §G must decide it unsat"
        );
    }

    #[test]
    fn g_perfect_square_lt_zero_is_unsat_nra() {
        // Same, real-sorted: `(x−1)² < 0` UNSAT over the reals.
        let mut m = TermManager::new();
        let real_sort = m.sorts.real_sort;
        let x = m.mk_var("x", real_sort);
        let f = perfect_square(&mut m, x);
        let zero = m.mk_int(0);
        let lt = m.mk_lt(f, zero);
        assert_eq!(
            dispatch_nra_constraints(&[lt], &m),
            Some(NlDispatchResult::Unsat),
            "(x-1)^2 < 0 is unsatisfiable over the reals — §G must decide it unsat"
        );
    }

    #[test]
    fn g_x_squared_lt_zero_is_unsat() {
        // The `x² ≥ 0` primitive, as the negated goal `x² < 0` (a=1,b=0,c=0).
        let mut m = TermManager::new();
        let int_sort = m.sorts.int_sort;
        let x = m.mk_var("x", int_sort);
        let xx = m.mk_mul(vec![x, x]);
        let zero = m.mk_int(0);
        let lt = m.mk_lt(xx, zero);
        assert_eq!(
            dispatch_nia_constraints(&[lt], &m, true),
            Some(NlDispatchResult::Unsat),
            "x^2 < 0 is unsatisfiable — §G must decide it unsat (the x^2>=0 primitive)"
        );
    }

    #[test]
    fn g_x_squared_plus_one_le_zero_is_unsat() {
        // `x² + 1 ≤ 0` is UNSAT (D=−4<0, a>0 ⇒ f > 0 ∀x). Negated goal of the
        // valid `x² + 1 > 0`.
        let mut m = TermManager::new();
        let real_sort = m.sorts.real_sort;
        let x = m.mk_var("x", real_sort);
        let xx = m.mk_mul(vec![x, x]);
        let one = m.mk_int(1);
        let f = m.mk_add(vec![xx, one]);
        let zero = m.mk_int(0);
        let le = m.mk_le(f, zero);
        assert_eq!(
            dispatch_nra_constraints(&[le], &m),
            Some(NlDispatchResult::Unsat),
            "x^2 + 1 <= 0 is unsatisfiable — §G must decide it unsat"
        );
    }

    #[test]
    fn g_does_not_falsely_decide_x_squared_gt_zero() {
        // SOUNDNESS: `x² > 0` is SATISFIABLE (x=1). D=0, a>0 ⇒ f ≥ 0 — but `> 0`
        // is NOT impossible (only `< 0` is). §G must DECLINE, never report unsat.
        let mut m = TermManager::new();
        let int_sort = m.sorts.int_sort;
        let x = m.mk_var("x", int_sort);
        let xx = m.mk_mul(vec![x, x]);
        let zero = m.mk_int(0);
        let gt = m.mk_gt(xx, zero);
        assert!(
            !matches!(
                dispatch_nia_constraints(&[gt], &m, true),
                Some(NlDispatchResult::Unsat)
            ),
            "x^2 > 0 is satisfiable (x=1) — §G must not report a false unsat"
        );
    }

    #[test]
    fn g_does_not_falsely_decide_x_squared_le_zero() {
        // SOUNDNESS: `x² ≤ 0` is SATISFIABLE (x=0). Must not be a false unsat.
        let mut m = TermManager::new();
        let int_sort = m.sorts.int_sort;
        let x = m.mk_var("x", int_sort);
        let xx = m.mk_mul(vec![x, x]);
        let zero = m.mk_int(0);
        let le = m.mk_le(xx, zero);
        assert!(
            !matches!(
                dispatch_nia_constraints(&[le], &m, true),
                Some(NlDispatchResult::Unsat)
            ),
            "x^2 <= 0 is satisfiable (x=0) — §G must not report a false unsat"
        );
    }

    #[test]
    fn g_does_not_decide_indefinite_quadratic() {
        // SOUNDNESS: `x² − 1 < 0` has D=4>0 (indefinite, satisfiable at x=0).
        // §G must DECLINE (D>0 falls through), never a false unsat.
        let mut m = TermManager::new();
        let real_sort = m.sorts.real_sort;
        let x = m.mk_var("x", real_sort);
        let xx = m.mk_mul(vec![x, x]);
        let one = m.mk_int(1);
        let f = m.mk_sub(xx, one);
        let zero = m.mk_int(0);
        let lt = m.mk_lt(f, zero);
        assert!(
            !matches!(
                dispatch_nra_constraints(&[lt], &m),
                Some(NlDispatchResult::Unsat)
            ),
            "x^2 - 1 < 0 is satisfiable (x=0, D>0) — §G must not decide it unsat"
        );
    }

    #[test]
    fn g_does_not_fire_on_multivariate_quadratic() {
        // SOUNDNESS: `x² + y < 0` is NOT a quadratic FORM (the `y` term is linear,
        // degree-1) — but it IS satisfiable (x=0, y=−1), so neither §G recogniser
        // may fire. (The form recogniser sees total_degree 2 but `x²+y` is
        // indefinite as a form ⇒ declines.)
        let mut m = TermManager::new();
        let real_sort = m.sorts.real_sort;
        let x = m.mk_var("x", real_sort);
        let y = m.mk_var("y", real_sort);
        let xx = m.mk_mul(vec![x, x]);
        let f = m.mk_add(vec![xx, y]);
        let zero = m.mk_int(0);
        let lt = m.mk_lt(f, zero);
        assert!(
            !matches!(
                dispatch_nra_constraints(&[lt], &m),
                Some(NlDispatchResult::Unsat)
            ),
            "x^2 + y < 0 is satisfiable — §G must not fire"
        );
    }

    // ── Reduction-KB rule §G-SOS: multivariate quadratic form (PSD) ──────────
    // `(x − y)² ≥ 0` is the verus SOS lead; its negation `(x − y)² < 0` =
    // `x² − 2xy + y² < 0` is UNSAT because the Gram matrix `[[1,−1],[−1,1]]` is PSD.

    /// Build `x² − 2xy + y²` (= `(x − y)²`) over `x`, `y`.
    fn diff_of_squares_form(m: &mut TermManager, x: TermId, y: TermId) -> TermId {
        let xx = m.mk_mul(vec![x, x]);
        let yy = m.mk_mul(vec![y, y]);
        let xy = m.mk_mul(vec![x, y]);
        let two = m.mk_int(2);
        let two_xy = m.mk_mul(vec![two, xy]);
        let sum = m.mk_add(vec![xx, yy]);
        m.mk_sub(sum, two_xy)
    }

    #[test]
    fn g_sos_perfect_square_form_lt_zero_is_unsat_nra() {
        // THE SOS BAR (verus `(x − y)² ≥ 0`, negated): `x² − 2xy + y² < 0` UNSAT.
        let mut m = TermManager::new();
        let real_sort = m.sorts.real_sort;
        let x = m.mk_var("x", real_sort);
        let y = m.mk_var("y", real_sort);
        let f = diff_of_squares_form(&mut m, x, y);
        let zero = m.mk_int(0);
        let lt = m.mk_lt(f, zero);
        assert_eq!(
            dispatch_nra_constraints(&[lt], &m),
            Some(NlDispatchResult::Unsat),
            "(x-y)² < 0 is unsatisfiable — §G-SOS must decide it unsat"
        );
    }

    #[test]
    fn g_sos_perfect_square_form_lt_zero_is_unsat_nia() {
        // Same over integers (real-PSD ⟹ integer-UNSAT).
        let mut m = TermManager::new();
        let int_sort = m.sorts.int_sort;
        let x = m.mk_var("x", int_sort);
        let y = m.mk_var("y", int_sort);
        let f = diff_of_squares_form(&mut m, x, y);
        let zero = m.mk_int(0);
        let lt = m.mk_lt(f, zero);
        assert_eq!(
            dispatch_nia_constraints(&[lt], &m, true),
            Some(NlDispatchResult::Unsat),
            "(x-y)² < 0 over integers is unsatisfiable — §G-SOS must decide it unsat"
        );
    }

    #[test]
    fn g_sos_does_not_decide_indefinite_form() {
        // SOUNDNESS: `x² − y² < 0` (indefinite Gram, satisfiable at x=0,y=1) must
        // NOT be a false unsat — the PSD rule declines.
        let mut m = TermManager::new();
        let real_sort = m.sorts.real_sort;
        let x = m.mk_var("x", real_sort);
        let y = m.mk_var("y", real_sort);
        let xx = m.mk_mul(vec![x, x]);
        let yy = m.mk_mul(vec![y, y]);
        let f = m.mk_sub(xx, yy);
        let zero = m.mk_int(0);
        let lt = m.mk_lt(f, zero);
        assert!(
            !matches!(
                dispatch_nra_constraints(&[lt], &m),
                Some(NlDispatchResult::Unsat)
            ),
            "x² − y² < 0 is satisfiable — §G-SOS must not report a false unsat"
        );
    }

    #[test]
    fn g_sos_does_not_decide_satisfiable_le_zero() {
        // SOUNDNESS: `(x − y)² ≤ 0` is SATISFIABLE (at x = y) — must NOT be unsat.
        let mut m = TermManager::new();
        let real_sort = m.sorts.real_sort;
        let x = m.mk_var("x", real_sort);
        let y = m.mk_var("y", real_sort);
        let f = diff_of_squares_form(&mut m, x, y);
        let zero = m.mk_int(0);
        let le = m.mk_le(f, zero);
        assert!(
            !matches!(
                dispatch_nra_constraints(&[le], &m),
                Some(NlDispatchResult::Unsat)
            ),
            "(x-y)² ≤ 0 is satisfiable (x=y) — §G-SOS must not report a false unsat"
        );
    }
}
