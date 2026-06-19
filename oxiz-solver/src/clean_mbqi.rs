//! OxiZ host for the clean-room quantifier engine (`oxiz-mbqi`).
//!
//! Implements `oxiz_mbqi::TermLang` for OxiZ terms via a local newtype
//! `OxizHost` (the orphan rule forbids impl'ing the foreign trait on the
//! foreign `TermManager` directly). This is the M4 port surface: the engine,
//! developed and z3-cross-checked standalone, drives OxiZ terms with no
//! engine change.
//!
//! Substitution note: `substitute` delegates to `TermManager::substitute`,
//! which recurses through the full FO/UF/LIA fragment (uninterpreted
//! applications, the boolean connectives, linear arithmetic) — the fragment
//! the verus prelude's quantifier bodies live in, and the only fragment the
//! clean engine is wired for today. (A latent OxiZ bug had `substitute`
//! silently no-op on `Apply`, so `(P x)[x↦c]` stayed `(P x)` — an instance
//! over the BOUND variable, vacuous; fixed in
//! `oxiz-core/.../query.rs::substitute_cached`.)
//!
//! LIMITATION (completeness, not soundness): a bound variable inside a
//! BV/string node or a NESTED quantifier is still left unsubstituted by the
//! host `substitute`, so the produced "instance" would retain a free variable.
//! The wiring guards against this — `Solver::check` DROPS any instance whose
//! body is not variable-free (`free_vars(phi)` non-empty) — so such a body
//! simply yields no lemma (sound, just incomplete). Broadening
//! `substitute_cached` to BV/string/nested-quantifier bodies (to RECOVER that
//! completeness) is a follow-up.
//!
//! The `view`/`children` structural mapping may also be partial — an unmapped
//! `TermKind` becomes `Opaque` (a leaf atom), a missed candidate at worst,
//! never a spurious instance or spurious unsat.

use oxiz_core::ast::{TermId, TermKind, TermManager};
use oxiz_core::interner::Spur;
use oxiz_core::sort::SortId;
use oxiz_mbqi::{Binding, ModelEval, Sig, TermLang, TermView};
use num_traits::ToPrimitive;
use rustc_hash::{FxHashMap, FxHashSet};

// Reserved syms for structured connectives/operators. A `Spur` is a
// `NonZeroU32` (< 2^32), so any value with bit 60 set never collides with an
// `Apply` function symbol.
const OP: u64 = 1 << 60;
const OP_NOT: u64 = OP | 1;
const OP_AND: u64 = OP | 2;
const OP_OR: u64 = OP | 3;
const OP_XOR: u64 = OP | 4;
const OP_IMPLIES: u64 = OP | 5;
const OP_ITE: u64 = OP | 6;
const OP_EQ: u64 = OP | 7;
const OP_DISTINCT: u64 = OP | 8;
const OP_NEG: u64 = OP | 9;
const OP_ADD: u64 = OP | 10;
const OP_SUB: u64 = OP | 11;
const OP_MUL: u64 = OP | 12;
const OP_DIV: u64 = OP | 13;
const OP_MOD: u64 = OP | 14;
const OP_LT: u64 = OP | 15;
const OP_LE: u64 = OP | 16;
const OP_GT: u64 = OP | 17;
const OP_GE: u64 = OP | 18;
const OP_SELECT: u64 = OP | 19;
const OP_STORE: u64 = OP | 20;

#[inline]
fn spur_sym(s: Spur) -> u64 {
    s.into_inner().get() as u64
}

/// The lifetime-free identity signature for OxiZ terms. The clean engine's
/// persistent state is keyed on this (`Engine<OxizSig>`, `GroundIndex<OxizSig>`,
/// …), so it carries no borrow and can live on `Solver` across `check()`
/// rounds. The borrowing behavior lives on [`OxizHost`], which impls
/// [`TermLang`] with `type Sig = OxizSig` and is re-created (borrowing the
/// `TermManager`) once per round.
pub struct OxizSig;

impl Sig for OxizSig {
    type Term = TermId;
    type Sort = SortId;
    type VarName = Spur;
    type Sym = u64;
}

/// A short-lived wrapper around the persistent `TermManager`, created per
/// engine round. Holds `&mut` so the engine can intern instance terms.
pub struct OxizHost<'a> {
    tm: &'a mut TermManager,
    /// Top-level `(= const literal)` map (`const_term → IntConst_term`), used by
    /// [`OxizHost::bounded_var_domains`] to resolve a SYMBOLIC guard bound (e.g.
    /// `(< i n)` with `(= n 5)` asserted) to a concrete one before extracting
    /// the finite domain. Empty unless built with [`OxizHost::with_int_consts`].
    int_consts: FxHashMap<TermId, TermId>,
}

impl<'a> OxizHost<'a> {
    /// Wrap a mutable borrow of the term manager for one engine round.
    pub fn new(tm: &'a mut TermManager) -> Self {
        OxizHost { tm, int_consts: FxHashMap::default() }
    }
    /// As [`OxizHost::new`], plus a `const → literal` map for symbolic-bound
    /// resolution in `bounded_var_domains`.
    pub fn with_int_consts(tm: &'a mut TermManager, int_consts: FxHashMap<TermId, TermId>) -> Self {
        OxizHost { tm, int_consts }
    }
    #[inline]
    fn m(&self) -> &TermManager {
        &*self.tm
    }
}

/// Scan top-level `(= term literal)` equalities (through conjunctions) and map
/// each non-literal side to its `IntConst` literal term — the concrete values
/// of declared integer constants like `(= n 5)`, for symbolic-bound resolution.
pub fn collect_int_consts(
    m: &TermManager,
    assertions: &[TermId],
    out: &mut FxHashMap<TermId, TermId>,
) {
    for &a in assertions {
        collect_const_eqs(m, a, out);
    }
}

fn collect_const_eqs(m: &TermManager, t: TermId, out: &mut FxHashMap<TermId, TermId>) {
    match m.get(t).map(|x| &x.kind) {
        Some(TermKind::And(args)) => {
            for &c in args.iter() {
                collect_const_eqs(m, c, out);
            }
        }
        Some(TermKind::Eq(a, b)) => {
            let (a, b) = (*a, *b);
            let a_lit = matches!(m.get(a).map(|x| &x.kind), Some(TermKind::IntConst(_)));
            let b_lit = matches!(m.get(b).map(|x| &x.kind), Some(TermKind::IntConst(_)));
            if a_lit && !b_lit {
                out.insert(b, a);
            } else if b_lit && !a_lit {
                out.insert(a, b);
            }
        }
        _ => {}
    }
}

/// Push negations inward to the QUANTIFIER BOUNDARIES so the clean engine's
/// (polarity-blind) `collect_quants` — which records `universal: forall`
/// syntactically — sees every quantifier at its TRUE polarity. A quantifier
/// under an odd number of negations is semantically flipped (`¬∀ ≡ ∃¬`,
/// `¬∃ ≡ ∀¬`); left unflipped, a negated `∃` is collected as an (inactive)
/// existential and never instantiated, so `(not (exists y. (= (f y) 0)))` with
/// `(= (f 5) 0)` asserted — an unsat the engine should reach by instantiating
/// the implied `∀y. f(y)≠0` at the ground term `f(5)` — silently came back
/// `sat`. After this pass that assertion is `(forall y. (not (= (f y) 0)))`, a
/// positive universal the engine enumerates at `5` → `f(5)≠0` → conflict.
///
/// SURGICAL, and BODY-OPAQUE. (1) Only the boolean spine that actually reaches a
/// quantifier is rewritten (`has_quant` gate); a quantifier-free subterm is kept
/// verbatim (positive) or wrapped in one `not` (negative), so ground structure
/// and theory atoms never churn. (2) A quantifier's BODY is left untouched — a
/// flipped quantifier wraps its body in a SINGLE `not` rather than recursively
/// NNF-ing it — because the validity/bounded-domain recognizers
/// ([`SolverModel::body_is_valid`]'s congruence/transitivity arms,
/// [`OxizHost::bounded_var_domains`]) pattern-match on the body's `=>` shape and
/// would stop matching if the body were rewritten. Two-polarity contexts
/// (`ite`/`xor`/bool-`=`) carrying a quantifier are left verbatim (sound, merely
/// unnormalized there). Composes before [`fold_valid_quantifiers`] (now-positive
/// valid quantifiers fold) and [`skolemize_unbounded_existentials`] (the `∃`
/// that a `¬∀` becomes gets skolemized).
pub fn nnf_push_negations(m: &mut TermManager, t: TermId) -> TermId {
    to_nnf(m, t, true)
}

/// Does `t` contain a quantifier anywhere in its boolean structure? (Quantifiers
/// are `Bool`-sorted, so they can only sit under boolean connectives — an
/// arithmetic/UF atom is a leaf for this purpose.)
fn has_quant(m: &TermManager, t: TermId) -> bool {
    let kids: Vec<TermId> = match m.get(t) {
        Some(term) => match &term.kind {
            TermKind::Forall { .. } | TermKind::Exists { .. } => return true,
            TermKind::Not(a) => vec![*a],
            TermKind::And(v) | TermKind::Or(v) => v.to_vec(),
            TermKind::Implies(a, b) | TermKind::Xor(a, b) | TermKind::Eq(a, b) => vec![*a, *b],
            TermKind::Ite(a, b, c) => vec![*a, *b, *c],
            _ => return false,
        },
        None => return false,
    };
    kids.iter().any(|&c| has_quant(m, c))
}

fn to_nnf(m: &mut TermManager, t: TermId, positive: bool) -> TermId {
    if !has_quant(m, t) {
        return if positive { t } else { m.mk_not(t) };
    }
    let kind = match m.get(t) {
        Some(x) => x.kind.clone(),
        None => return if positive { t } else { m.mk_not(t) },
    };
    match kind {
        TermKind::Not(a) => to_nnf(m, a, !positive),
        TermKind::And(args) => {
            let v: Vec<TermId> = args.iter().map(|&a| to_nnf(m, a, positive)).collect();
            // De Morgan: ¬⋀ = ⋁¬.
            if positive { m.mk_and(v) } else { m.mk_or(v) }
        }
        TermKind::Or(args) => {
            let v: Vec<TermId> = args.iter().map(|&a| to_nnf(m, a, positive)).collect();
            if positive { m.mk_or(v) } else { m.mk_and(v) }
        }
        TermKind::Implies(a, b) => {
            if positive {
                // a ⇒ b ≡ ¬a ∨ b
                let na = to_nnf(m, a, false);
                let b2 = to_nnf(m, b, true);
                m.mk_or(vec![na, b2])
            } else {
                // ¬(a ⇒ b) ≡ a ∧ ¬b
                let a2 = to_nnf(m, a, true);
                let nb = to_nnf(m, b, false);
                m.mk_and(vec![a2, nb])
            }
        }
        TermKind::Forall { vars, body, .. } => {
            if positive {
                t // keep; body opaque (preserves the recognizers + bounded_var_domains)
            } else {
                let nb = m.mk_not(body); // ¬∀x.φ ≡ ∃x.¬φ
                mk_quant_dropping_patterns(m, &vars, nb, false)
            }
        }
        TermKind::Exists { vars, body, .. } => {
            if positive {
                t
            } else {
                let nb = m.mk_not(body); // ¬∃x.φ ≡ ∀x.¬φ
                mk_quant_dropping_patterns(m, &vars, nb, true)
            }
        }
        // ite/xor/bool-= carrying a quantifier: two-polarity, leave verbatim.
        _ => {
            if positive {
                t
            } else {
                m.mk_not(t)
            }
        }
    }
}

/// Rebuild a quantifier from `vars` + a rewritten `body`, DROPPING the original
/// patterns (they targeted the pre-rewrite body). Used by NNF (to materialise a
/// polarity-flipped quantifier) and by skolemization (to rebuild a `∀` whose
/// body had a nested `∃` lowered to a Skolem function).
fn mk_quant_dropping_patterns(
    m: &mut TermManager,
    vars: &[(Spur, SortId)],
    body: TermId,
    forall: bool,
) -> TermId {
    let named: Vec<(String, SortId)> = vars
        .iter()
        .map(|(s, sort)| (m.resolve_str(*s).to_string(), *sort))
        .collect();
    let it = named.iter().map(|(s, sort)| (s.as_str(), *sort));
    if forall {
        m.mk_forall(it, body)
    } else {
        m.mk_exists(it, body)
    }
}

/// Constant-fold a quantifier whose matrix is a recognized *tautology* to the
/// literal `true` — POLARITY-INDEPENDENTLY, anywhere it appears in the boolean
/// structure of an assertion. A valid body makes the whole quantifier valid:
/// `∀x̄. φ` with `φ` valid is true, and `∃x̄. φ` with `φ` valid is true as well
/// (SMT sorts are non-empty, so a witness always exists). Replacing such a node
/// with `true` is therefore meaning-preserving in *every* context.
///
/// Why a rewrite and not just the model check. The clean engine already
/// recognizes these tautologies via [`SolverModel::body_is_valid`] — but only
/// on the POSITIVE path, as the `eval_forall` verdict for an *active*
/// quantifier. Under a negation the quantifier node is asserted false, so the
/// SAT core marks it inactive, `eval_forall` is never consulted, and the
/// validity goes unnoticed: `(not (forall ((x Int)) (= x x)))` wrongly comes
/// back `sat` instead of `unsat`. Folding the valid quantifier to `true` up
/// front closes that gap — `(not (forall x. x=x))` becomes `(not true)` →
/// `false` → the sound `unsat` — and as a bonus removes the quantifier from the
/// SAT core entirely on the positive path too.
///
/// Recurses only through the boolean connectives (`not`/`and`/`or`/`=>`/`ite`),
/// since a quantifier (being `Bool`-sorted) can nest only there. Reuses the
/// SAME validity recognizer the positive path trusts, so it inherits its
/// corpus-validated exactness — a false positive here would be a spurious
/// `unsat` (via `not(true)=false`), exactly the bar `body_is_valid` already
/// meets. Covers the *tautology* subset only; a negated CONTINGENT quantifier
/// (`(not (exists y. (= (f y) 0)))` with `(= (f 5) 0)` asserted, unsat only
/// because of the ground fact) is NOT a validity question and still needs
/// polarity-aware instantiation.
pub fn fold_valid_quantifiers(m: &mut TermManager, t: TermId) -> TermId {
    let kind = match m.get(t) {
        Some(x) => x.kind.clone(),
        None => return t,
    };
    match kind {
        TermKind::Forall { body, .. } | TermKind::Exists { body, .. } => {
            let true_id = m.mk_bool(true);
            let false_id = m.mk_bool(false);
            let valid = {
                let model = SolverModel::new(FxHashMap::default(), true_id, false_id);
                let host = OxizHost::new(m);
                model.body_is_valid(&host, body, 64)
            };
            if valid { true_id } else { t }
        }
        TermKind::Not(a) => {
            let a2 = fold_valid_quantifiers(m, a);
            m.mk_not(a2)
        }
        TermKind::And(args) => {
            let v: Vec<TermId> = args.iter().map(|&a| fold_valid_quantifiers(m, a)).collect();
            m.mk_and(v)
        }
        TermKind::Or(args) => {
            let v: Vec<TermId> = args.iter().map(|&a| fold_valid_quantifiers(m, a)).collect();
            m.mk_or(v)
        }
        TermKind::Implies(a, b) => {
            let a2 = fold_valid_quantifiers(m, a);
            let b2 = fold_valid_quantifiers(m, b);
            m.mk_implies(a2, b2)
        }
        TermKind::Ite(c, a, b) => {
            let c2 = fold_valid_quantifiers(m, c);
            let a2 = fold_valid_quantifiers(m, a);
            let b2 = fold_valid_quantifiers(m, b);
            m.mk_ite(c2, a2, b2)
        }
        _ => t,
    }
}

/// Skolemize POSITIVE existentials. Replacing `∃ȳ. φ` (sitting inside the scope
/// of universals `x̄`) with `φ[ȳ ↦ sk(x̄)]` for fresh Skolem *functions* `sk` is
/// *equisatisfiable* — a model of the Skolemized form extends to a model of the
/// original by reading each witness off `sk`, and vice versa — so doing it to an
/// asserted formula never changes the answer. It turns goals the clean MBQI
/// engine (which never fabricates witnesses) would leave `Unknown` into pure
/// universals / ground facts it can instantiate:
///   * a top-level `∃y. f(y)=0` (empty scope) → `f(c)=0` for a fresh CONSTANT
///     `c` (the nullary Skolem function) — surjectivity goals;
///   * a nested `∀x. ∃y. φ(x,y)` → `∀x. φ(x, sk(x))` for a fresh unary Skolem
///     FUNCTION `sk` — e.g. `∀x.∃y.f(x,y)>0` with `∀x,y.f(x,y)≤0` becomes
///     refutable by instantiating both universals at the same `x`.
///
/// Only POSITIVE occurrences are Skolemized: descends through `and`/`or`
/// (polarity-preserving), the CONSEQUENT of `=>`, and `∀` bodies (extending the
/// Skolem scope with the universal's variables). A `∃` under `not` or in an `=>`
/// ANTECEDENT — where it is effectively a `∀` — is left untouched (Skolemizing a
/// negative `∃` would be unsound). A BOUNDED top-level `∃` is left for the
/// engine's finite disjunction ([`Engine::emit_existential_disjunction`], #279);
/// leaving any existential for the engine is always sound (at worst `Unknown`).
///
/// `tag` makes the minted Skolem names unique across assertions.
pub fn skolemize_unbounded_existentials(m: &mut TermManager, t: TermId, tag: &str) -> TermId {
    let mut counter: usize = 0;
    skolemize_rec(m, t, &[], tag, &mut counter)
}

fn skolemize_rec(
    m: &mut TermManager,
    t: TermId,
    scope: &[(Spur, SortId)],
    tag: &str,
    counter: &mut usize,
) -> TermId {
    let kind = match m.get(t) {
        Some(x) => x.kind.clone(),
        None => return t,
    };
    match kind {
        TermKind::Exists { vars, body, .. } => {
            // A BOUNDED top-level ∃ stays for the engine's finite disjunction
            // (#279). Nested existentials are always Skolemized (the disjunction
            // does not reach inside a universal anyway).
            if scope.is_empty() {
                let bounded = {
                    let mut host = OxizHost::new(m);
                    let doms = host.bounded_var_domains(t);
                    !doms.is_empty() && doms.iter().all(Option::is_some)
                };
                if bounded {
                    return t;
                }
            }
            // Resolve the enclosing-universal names ONCE (the Skolem function's
            // argument list `x̄`); `mk_var(name, sort)` re-interns each as the
            // exact `Var` the body references.
            let scope_named: Vec<(String, SortId)> = scope
                .iter()
                .map(|(s, sort)| (m.resolve_str(*s).to_string(), *sort))
                .collect();
            let mut map: FxHashMap<TermId, TermId> = FxHashMap::default();
            for (name, sort) in vars.iter() {
                let nm = m.resolve_str(*name).to_string();
                let var_term = m.mk_var(&nm, *sort);
                *counter += 1;
                let skname = format!("sk!{tag}!{}!{nm}", *counter);
                let sk = if scope_named.is_empty() {
                    m.mk_var(&skname, *sort) // nullary Skolem = a fresh constant
                } else {
                    let args: Vec<TermId> =
                        scope_named.iter().map(|(n, s)| m.mk_var(n, *s)).collect();
                    m.mk_apply(&skname, args, *sort) // sk(x̄)
                };
                map.insert(var_term, sk);
            }
            let body2 = m.substitute(body, &map);
            // The body may itself hold more positive structure / existentials.
            skolemize_rec(m, body2, scope, tag, counter)
        }
        TermKind::Forall { vars, body, .. } => {
            // Descend to reach nested existentials, extending the Skolem scope
            // with this universal's variables. Rebuild only if the body changed
            // (else keep `t` verbatim — preserves patterns + identity).
            let mut scope2 = scope.to_vec();
            scope2.extend(vars.iter().copied());
            let body2 = skolemize_rec(m, body, &scope2, tag, counter);
            if body2 == body {
                t
            } else {
                mk_quant_dropping_patterns(m, &vars, body2, true)
            }
        }
        TermKind::And(args) => {
            let new: Vec<TermId> = args
                .iter()
                .map(|&a| skolemize_rec(m, a, scope, tag, counter))
                .collect();
            m.mk_and(new)
        }
        TermKind::Or(args) => {
            let new: Vec<TermId> = args
                .iter()
                .map(|&a| skolemize_rec(m, a, scope, tag, counter))
                .collect();
            m.mk_or(new)
        }
        TermKind::Implies(a, b) => {
            // Only the CONSEQUENT is positive; the antecedent's polarity is
            // flipped, so a `∃` there must not be Skolemized.
            let b2 = skolemize_rec(m, b, scope, tag, counter);
            if b2 == b {
                t
            } else {
                m.mk_implies(a, b2)
            }
        }
        _ => t,
    }
}

impl<'a> TermLang for OxizHost<'a> {
    type Sig = OxizSig;

    fn view(&self, t: TermId) -> TermView<'_, OxizSig> {
        let Some(term) = self.m().get(t) else {
            return TermView::Opaque;
        };
        match &term.kind {
            TermKind::Var(s) => TermView::Var { name: *s },
            TermKind::Forall { vars, body, .. } => TermView::Quant {
                forall: true,
                vars: &vars[..],
                body: *body,
            },
            TermKind::Exists { vars, body, .. } => TermView::Quant {
                forall: false,
                vars: &vars[..],
                body: *body,
            },
            TermKind::Apply { func, .. } => TermView::App {
                sym: spur_sym(*func),
            },
            TermKind::Not(_) => TermView::App { sym: OP_NOT },
            TermKind::And(_) => TermView::App { sym: OP_AND },
            TermKind::Or(_) => TermView::App { sym: OP_OR },
            TermKind::Xor(..) => TermView::App { sym: OP_XOR },
            TermKind::Implies(..) => TermView::App { sym: OP_IMPLIES },
            TermKind::Ite(..) => TermView::App { sym: OP_ITE },
            TermKind::Eq(..) => TermView::App { sym: OP_EQ },
            TermKind::Distinct(_) => TermView::App { sym: OP_DISTINCT },
            TermKind::Neg(_) => TermView::App { sym: OP_NEG },
            TermKind::Add(_) => TermView::App { sym: OP_ADD },
            TermKind::Sub(..) => TermView::App { sym: OP_SUB },
            TermKind::Mul(_) => TermView::App { sym: OP_MUL },
            TermKind::Div(..) => TermView::App { sym: OP_DIV },
            TermKind::Mod(..) => TermView::App { sym: OP_MOD },
            TermKind::Lt(..) => TermView::App { sym: OP_LT },
            TermKind::Le(..) => TermView::App { sym: OP_LE },
            TermKind::Gt(..) => TermView::App { sym: OP_GT },
            TermKind::Ge(..) => TermView::App { sym: OP_GE },
            TermKind::Select(..) => TermView::App { sym: OP_SELECT },
            TermKind::Store(..) => TermView::App { sym: OP_STORE },
            // Leaf constants and anything not mapped above → opaque atom.
            _ => TermView::Opaque,
        }
    }

    fn children(&self, t: TermId) -> Vec<TermId> {
        let Some(term) = self.m().get(t) else {
            return Vec::new();
        };
        match &term.kind {
            TermKind::Apply { args, .. } => args.to_vec(),
            TermKind::And(a) | TermKind::Or(a) | TermKind::Add(a) | TermKind::Mul(a)
            | TermKind::Distinct(a) => a.to_vec(),
            TermKind::Not(a) | TermKind::Neg(a) => vec![*a],
            TermKind::Xor(a, b)
            | TermKind::Implies(a, b)
            | TermKind::Eq(a, b)
            | TermKind::Sub(a, b)
            | TermKind::Div(a, b)
            | TermKind::Mod(a, b)
            | TermKind::Lt(a, b)
            | TermKind::Le(a, b)
            | TermKind::Gt(a, b)
            | TermKind::Ge(a, b)
            | TermKind::Select(a, b) => vec![*a, *b],
            TermKind::Ite(a, b, c) | TermKind::Store(a, b, c) => vec![*a, *b, *c],
            _ => Vec::new(),
        }
    }

    fn patterns(&self, quant: TermId) -> Vec<Vec<TermId>> {
        match self.m().get(quant).map(|t| &t.kind) {
            Some(TermKind::Forall { patterns, .. } | TermKind::Exists { patterns, .. }) => {
                patterns.iter().map(|g| g.to_vec()).collect()
            }
            _ => Vec::new(),
        }
    }

    fn sort_of(&self, t: TermId) -> SortId {
        self.m().get(t).map(|x| x.sort).unwrap_or(self.m().sorts.bool_sort)
    }

    fn substitute(&mut self, body: TermId, binding: &Binding<OxizSig>) -> TermId {
        // Map the binding's bound-var NAMES to the actual `Var` TermIds in the
        // body, then delegate to the manager's (capture-free) substitute.
        let fvs = self.m().free_vars(body);
        let mut map: FxHashMap<TermId, TermId> = FxHashMap::default();
        for v in fvs {
            if let Some(TermKind::Var(s)) = self.m().get(v).map(|t| &t.kind) {
                if let Some(repl) = binding.get(*s) {
                    map.insert(v, repl);
                }
            }
        }
        self.tm.substitute(body, &map)
    }

    fn mk_implies(&mut self, a: TermId, b: TermId) -> TermId {
        self.tm.mk_implies(a, b)
    }

    fn mk_or(&mut self, args: Vec<TermId>) -> TermId {
        self.tm.mk_or(args)
    }

    fn bounded_var_domains(&mut self, quant: TermId) -> Vec<Option<Vec<TermId>>> {
        // Bound variables + matrix of the quantifier, plus whether it is an
        // existential. For a `∀` the guarded shape is `(=> guard φ)`; for a
        // bounded `∃` it is `(and guard… φ)` — both pin the bound vars to a
        // finite integer range we can enumerate.
        let (bound, body, is_exists) = match self.m().get(quant).map(|t| &t.kind) {
            Some(TermKind::Forall { vars, body, .. }) => {
                (vars.iter().map(|(n, _)| *n).collect::<Vec<Spur>>(), *body, false)
            }
            Some(TermKind::Exists { vars, body, .. }) => {
                (vars.iter().map(|(n, _)| *n).collect::<Vec<Spur>>(), *body, true)
            }
            _ => return Vec::new(),
        };
        // `∀`: the range lives in the `(=> guard φ)` ANTECEDENT (out-of-range ⇒
        // vacuous). `∃`: the range lives in the `(and guard… φ)` body itself
        // (out-of-range ⇒ no witness); using the whole conjunction as the
        // "guard" lets `collect_int_bounds` pick out the bound-var comparisons
        // and ignore the non-bound conjuncts (`collect_int_bounds` only records
        // bounds for the quantifier's OWN variables). For a `∀` we must NOT
        // treat an `(and …)` body as a guard — that would unsoundly restrict a
        // non-guarded universal — so the And path is existential-only.
        let guard = if is_exists {
            body
        } else {
            match self.m().get(body).map(|t| &t.kind) {
                Some(TermKind::Implies(g, _)) => *g,
                _ => return Vec::new(),
            }
        };
        // Resolve SYMBOLIC bounds: substitute every declared integer constant the
        // top-level equalities pin (e.g. `(= n 5)` ⇒ `n ↦ 5`) so a guard like
        // `(< i n)` becomes `(< i 5)` and `collect_int_bounds` can read a concrete
        // range. Sound: a top-level `(= n 5)` holds in every model, so the guard
        // with `n` is equivalent to the guard with `5`.
        let guard = if self.int_consts.is_empty() {
            guard
        } else {
            let consts = self.int_consts.clone();
            self.tm.substitute(guard, &consts)
        };
        // Tightest concrete (lower, upper) integer bound per bound var.
        let mut lo: FxHashMap<Spur, i128> = FxHashMap::default();
        let mut hi: FxHashMap<Spur, i128> = FxHashMap::default();
        collect_int_bounds(self.m(), guard, &bound, &mut lo, &mut hi);
        // Finite literal domain for each fully + tightly bounded var; a huge or
        // half-open range falls back to `None` (enumerate over the ground index).
        const MAX_RANGE: i128 = 1024;
        bound
            .iter()
            .map(|name| match (lo.get(name).copied(), hi.get(name).copied()) {
                (Some(l), Some(u)) if l <= u && u - l < MAX_RANGE => {
                    Some((l..=u).map(|v| self.tm.mk_int(v)).collect())
                }
                _ => None,
            })
            .collect()
    }
}

/// One comparison's contribution to a bound variable's integer range.
enum Cmp {
    Ge,
    Le,
    Gt,
    Lt,
    Eq,
}

#[inline]
fn update_lo(lo: &mut FxHashMap<Spur, i128>, x: Spur, v: i128) {
    lo.entry(x).and_modify(|e| *e = (*e).max(v)).or_insert(v);
}
#[inline]
fn update_hi(hi: &mut FxHashMap<Spur, i128>, x: Spur, v: i128) {
    hi.entry(x).and_modify(|e| *e = (*e).min(v)).or_insert(v);
}

fn as_bound_var(m: &TermManager, t: TermId, bound: &[Spur]) -> Option<Spur> {
    match m.get(t).map(|x| &x.kind) {
        Some(TermKind::Var(s)) if bound.contains(s) => Some(*s),
        _ => None,
    }
}
fn as_int_const(m: &TermManager, t: TermId) -> Option<i128> {
    match m.get(t).map(|x| &x.kind) {
        Some(TermKind::IntConst(b)) => b.to_i128(),
        _ => None,
    }
}

/// Walk a guard (a conjunction of comparisons) and record, per bound variable,
/// the concrete integer lower/upper bounds it pins. Only `And` of simple
/// `var ⋈ const` / `const ⋈ var` comparisons contributes; `Or`/`Not`/anything
/// else is conservatively ignored (no bound ⇒ that var stays unrestricted).
fn collect_int_bounds(
    m: &TermManager,
    t: TermId,
    bound: &[Spur],
    lo: &mut FxHashMap<Spur, i128>,
    hi: &mut FxHashMap<Spur, i128>,
) {
    let Some(term) = m.get(t) else { return };
    let (a, b, cmp) = match &term.kind {
        TermKind::And(args) => {
            for &c in args.iter() {
                collect_int_bounds(m, c, bound, lo, hi);
            }
            return;
        }
        TermKind::Ge(a, b) => (*a, *b, Cmp::Ge),
        TermKind::Le(a, b) => (*a, *b, Cmp::Le),
        TermKind::Gt(a, b) => (*a, *b, Cmp::Gt),
        TermKind::Lt(a, b) => (*a, *b, Cmp::Lt),
        TermKind::Eq(a, b) => (*a, *b, Cmp::Eq),
        _ => return,
    };
    // `var ⋈ const`
    if let (Some(x), Some(k)) = (as_bound_var(m, a, bound), as_int_const(m, b)) {
        match cmp {
            Cmp::Ge => update_lo(lo, x, k),
            Cmp::Le => update_hi(hi, x, k),
            Cmp::Gt => update_lo(lo, x, k + 1),
            Cmp::Lt => update_hi(hi, x, k - 1),
            Cmp::Eq => {
                update_lo(lo, x, k);
                update_hi(hi, x, k);
            }
        }
        return;
    }
    // `const ⋈ var` (flip the relation)
    if let (Some(k), Some(x)) = (as_int_const(m, a), as_bound_var(m, b, bound)) {
        match cmp {
            Cmp::Ge => update_hi(hi, x, k),       // k ≥ x ⟺ x ≤ k
            Cmp::Le => update_lo(lo, x, k),       // k ≤ x ⟺ x ≥ k
            Cmp::Gt => update_hi(hi, x, k - 1),   // k > x ⟺ x ≤ k-1
            Cmp::Lt => update_lo(lo, x, k + 1),   // k < x ⟺ x ≥ k+1
            Cmp::Eq => {
                update_lo(lo, x, k);
                update_hi(hi, x, k);
            }
        }
    }
}

/// The model oracle the engine consults for CDQI (`eval_bool`), relevance
/// gating (`is_active`), and model-based verification (`eval_forall`).
///
/// Built per round from the solver's current model. Holds a CLONE of the
/// model's `term → value` assignments (so it does not alias the manager the
/// host borrows mutably) plus the True/False term ids. Every method is
/// CONSERVATIVE: a wrong `eval_bool`/`is_active` can only cost completeness
/// (a missed CDQI conflict, an extra instantiation), never soundness — the
/// engine emits sound lemmas regardless, and verdicts are the host core's.
pub struct SolverModel {
    /// `term → value` assignments from the current model (cloned).
    assign: FxHashMap<TermId, TermId>,
    true_id: TermId,
    false_id: TermId,
    /// Model-INDEPENDENT facts about the whole asserted formula, for the
    /// `eval_forall` M3 model-completion recognizers. `None` ⇒ those
    /// recognizers are disabled (only the structural-tautology fragment runs);
    /// always sound, just less complete.
    facts: Option<CompletionFacts>,
}

impl SolverModel {
    /// Build the oracle from a snapshot of the solver's `term → value`
    /// assignments plus the interned `true`/`false` term ids.
    pub fn new(assign: FxHashMap<TermId, TermId>, true_id: TermId, false_id: TermId) -> Self {
        SolverModel {
            assign,
            true_id,
            false_id,
            facts: None,
        }
    }

    /// Attach model-completion facts computed from the full assertion set.
    /// Enables the M3 definitional / pure-polarity / function-completion
    /// recognizers in [`SolverModel::eval_forall`]. Only worth computing when
    /// the problem has quantifiers; cheap (one linear walk of the assertions).
    pub fn with_completion_facts(mut self, manager: &TermManager, assertions: &[TermId]) -> Self {
        self.facts = Some(CompletionFacts::analyze(manager, assertions));
        self
    }

    /// The model value of `t` (the assignment, else `t` itself if it is its
    /// own value — a constant).
    #[inline]
    fn value(&self, t: TermId) -> TermId {
        self.assign.get(&t).copied().unwrap_or(t)
    }

    /// Resolve `t` to a CONCRETE integer under the model, following the
    /// `term → value` chain to an `IntConst` (bounded, so a cyclic/length model
    /// cannot loop). `None` if it does not bottom out at a literal integer —
    /// the arithmetic fold then stays the sound `undetermined`.
    fn int_of(&self, lang: &OxizHost<'_>, t: TermId) -> Option<num_bigint::BigInt> {
        let mut cur = t;
        for _ in 0..8 {
            if let Some(TermKind::IntConst(b)) = lang.m().get(cur).map(|x| &x.kind) {
                return Some(b.clone());
            }
            let next = self.value(cur);
            if next == cur {
                return None;
            }
            cur = next;
        }
        None
    }
}

/// Model-independent facts about the whole asserted formula, used by the
/// `eval_forall` model-completion recognizers (M3). Conservative everywhere — a
/// missed fact only costs completeness, never soundness.
#[derive(Default)]
struct CompletionFacts {
    /// Quantifier body-roots that are a conservative DEFINITION
    /// `∀x̄. (= (f x̄) rhs)`: `f` uninterpreted, applied to exactly the distinct
    /// bound vars, not occurring in `rhs`, and occurring NOWHERE else in the
    /// problem. Such an axiom is always satisfiable (define `f := λx̄. rhs`), so
    /// it never blocks `Sat`.
    definitional_quants: FxHashSet<TermId>,
    /// Polarity of each uninterpreted **predicate** symbol across all
    /// NON-definitional assertions (a definition does not constrain the symbols
    /// in its rhs). A symbol in `occurs_pos` but neither `occurs_neg` nor
    /// `occurs_mixed` occurs only positively ⇒ can be set true; symmetric for
    /// `occurs_neg`. `occurs_mixed` = appears in a non-monotone context
    /// (Eq/Xor/Ite/arith/term position) ⇒ NOT freely settable.
    occurs_pos: FxHashSet<u64>,
    occurs_neg: FxHashSet<u64>,
    occurs_mixed: FxHashSet<u64>,
    /// How many DISTINCT non-definitional quantifier bodies mention each
    /// uninterpreted symbol (the single-function range-completion gate requires
    /// exactly one). Keyed on the `view`-style `u64` symbol (`spur_sym`).
    quant_count: FxHashMap<u64, u32>,
    /// Every GROUND application (no variable anywhere in its subtree) of each
    /// uninterpreted function, keyed on the `view`-style `u64` symbol. These are
    /// the points a constant range-completion of `f` must NOT violate. Unlike
    /// the model's `assign` map, this includes applications constrained only by
    /// an INEQUALITY (e.g. `(< (f 5) 0)` pins no concrete value into `assign`
    /// yet still forbids completing `f(5)` to a constant ≥ 0) — missing them was
    /// the #260 spurious-`sat` hole.
    ground_apps: FxHashMap<u64, Vec<TermId>>,
    /// For each ground term that a TOP-LEVEL equation pins (`(= lhs rhs)` not
    /// under any disjunction/negation/quantifier), the other side(s) of that
    /// equation. The function-completion verify resolves these to a concrete
    /// integer — the only value the model reflects faithfully for a ground
    /// `f`-application (its own `assign` entry is a poisoned default when it is
    /// merely inequality-constrained). Keyed by the pinned term's `TermId`.
    eq_pins: FxHashMap<TermId, Vec<TermId>>,
    /// Global occurrence count of every uninterpreted `Apply` head (Pass 0).
    /// The monotone order-extension uses it as an accounting guard: a function is
    /// safe to model only if EVERY one of its applications is accounted for by
    /// the axiom itself plus the handled ground bounds below.
    global_occ: FxHashMap<u64, u32>,
    /// Tightest numeric lower / upper bound on a ground function application,
    /// from the WEAK shapes `(= app c)` / `(>= app c)` / `(<= app c)` only.
    mono_lo: FxHashMap<TermId, num_rational::BigRational>,
    mono_hi: FxHashMap<TermId, num_rational::BigRational>,
    /// Relational `(<= app1 app2)` between two ground applications.
    mono_rels: Vec<(TermId, TermId)>,
    /// Count of `Apply` heads that appear inside a HANDLED ground bound/relation
    /// above (so the accounting guard can confirm nothing else constrains `f`).
    mono_handled_occ: FxHashMap<u64, u32>,
}

impl CompletionFacts {
    fn analyze(m: &TermManager, assertions: &[TermId]) -> Self {
        let mut f = CompletionFacts::default();

        // Pass 0: global occurrence count of every uninterpreted symbol, so a
        // definitional head can be confirmed to occur NOWHERE else.
        let mut global_occ: FxHashMap<u64, u32> = FxHashMap::default();
        for &a in assertions {
            count_syms(m, a, &mut global_occ);
        }
        f.global_occ = global_occ.clone();

        // Pass 1: identify definitional axioms `∀x̄. (= (f x̄) rhs)` with `f`
        // occurring exactly once globally (so only as this defining head).
        for &a in assertions {
            if let Some(f_sym) = definitional_head(m, a) {
                if global_occ.get(&f_sym).copied() == Some(1) {
                    f.definitional_quants.insert(a);
                }
            }
        }

        // Pass 2: polarity + per-quantifier mention counts over NON-definitional
        // assertions (a definition constrains nothing but its own fresh head).
        for &a in assertions {
            if f.definitional_quants.contains(&a) {
                continue;
            }
            walk_polarity(m, a, true, &mut f);
            if matches!(
                m.get(a).map(|t| &t.kind),
                Some(TermKind::Forall { .. } | TermKind::Exists { .. })
            ) {
                let mut occ: FxHashMap<u64, u32> = FxHashMap::default();
                count_syms(m, a, &mut occ);
                for s in occ.into_keys() {
                    *f.quant_count.entry(s).or_insert(0) += 1;
                }
            }
        }

        // Pass 3: collect every GROUND function application across ALL
        // assertions (a ground `f`-point constrains `f` regardless of where it
        // appears). The function-completion verify scans these — not just the
        // model's concretely-assigned points — so an inequality-only constraint
        // such as `(< (f 5) 0)` is not silently ignored.
        for &a in assertions {
            collect_ground_apps(m, a, &mut f.ground_apps);
        }

        // Pass 4: collect TOP-LEVEL equality pins (`(= lhs rhs)` reached through
        // conjunctions only — never under a disjunction, negation, or
        // quantifier, where the equation is not unconditionally true). These are
        // the faithful concrete values for the function-completion verify.
        for &a in assertions {
            collect_eq_pins(m, a, &mut f.eq_pins);
        }

        // Pass 5: a definitional axiom `∀x̄. (= (f x̄) rhs)` whose head `f` ALSO
        // appears in GROUND facts is rejected by Pass 1's once-globally guard —
        // yet it is still satisfiable by `f := λx̄. rhs` AS LONG AS those ground
        // facts AGREE with the definition (e.g. `∀x. f(x)=x` with `f(3)=3`).
        // Accept it when: `f` occurs in no OTHER quantifier, and every ground
        // `f`-application is eq-pinned to exactly the value the definition
        // predicts. A non-pinned app (e.g. `(< (f 5) 0)`) or a disagreeing pin
        // ⇒ NOT added (sound: the engine then instantiates `f(t)=rhs[t]` and the
        // ground core refutes the inconsistency, never a spurious `sat`).
        for &a in assertions {
            if f.definitional_quants.contains(&a) {
                continue;
            }
            let Some(fsym) = definitional_head(m, a) else {
                continue;
            };
            let in_other_quant = assertions.iter().any(|&b| {
                b != a
                    && matches!(
                        m.get(b).map(|t| &t.kind),
                        Some(TermKind::Forall { .. } | TermKind::Exists { .. })
                    )
                    && {
                        let mut occ: FxHashMap<u64, u32> = FxHashMap::default();
                        count_syms(m, b, &mut occ);
                        occ.contains_key(&fsym)
                    }
            });
            if in_other_quant {
                continue;
            }
            if let Some((lhs_args, rhs)) = definitional_lhs_rhs(m, a) {
                if definitional_ground_consistent(m, &lhs_args, rhs, fsym, &f.ground_apps, &f.eq_pins)
                {
                    f.definitional_quants.insert(a);
                }
            }
        }

        // Pass 6: ground numeric bounds + relations on function applications, for
        // the monotone order-extension recognizer. Only the WEAK shapes `(= app
        // c)`/`(>= app c)`/`(<= app c)` (numeric `c`) and `(<= app1 app2)` are
        // recorded; every `Apply` head they touch is tallied in `mono_handled_occ`
        // so the recognizer can verify (via `global_occ`) that NOTHING ELSE
        // constrains the function — a strict bound or an `f`-app in any other
        // context is simply not tallied, so the accounting check fails and the
        // recognizer conservatively declines.
        for &a in assertions {
            collect_mono_facts(m, a, &mut f);
        }
        f
    }

    #[inline]
    fn is_pure_pos(&self, s: u64) -> bool {
        self.occurs_pos.contains(&s) && !self.occurs_neg.contains(&s) && !self.occurs_mixed.contains(&s)
    }
    #[inline]
    fn is_pure_neg(&self, s: u64) -> bool {
        self.occurs_neg.contains(&s) && !self.occurs_pos.contains(&s) && !self.occurs_mixed.contains(&s)
    }
}

/// All immediate sub-terms of `t` (including a quantifier's body), for the
/// recursive `count_syms` / `mark_mixed` walks. Mirrors `OxizHost::children`
/// but over `TermKind` directly and descends into quantifier bodies.
fn subterms(m: &TermManager, t: TermId) -> Vec<TermId> {
    let Some(term) = m.get(t) else { return Vec::new() };
    match &term.kind {
        TermKind::Apply { args, .. } => args.to_vec(),
        TermKind::And(a) | TermKind::Or(a) | TermKind::Add(a) | TermKind::Mul(a)
        | TermKind::Distinct(a) => a.to_vec(),
        TermKind::Not(a) | TermKind::Neg(a) => vec![*a],
        TermKind::Xor(a, b)
        | TermKind::Implies(a, b)
        | TermKind::Eq(a, b)
        | TermKind::Sub(a, b)
        | TermKind::Div(a, b)
        | TermKind::Mod(a, b)
        | TermKind::Lt(a, b)
        | TermKind::Le(a, b)
        | TermKind::Gt(a, b)
        | TermKind::Ge(a, b)
        | TermKind::Select(a, b) => vec![*a, *b],
        TermKind::Ite(a, b, c) | TermKind::Store(a, b, c) => vec![*a, *b, *c],
        TermKind::Forall { body, .. } | TermKind::Exists { body, .. } => vec![*body],
        _ => Vec::new(),
    }
}

/// Count occurrences of each uninterpreted `Apply` head (keyed on the
/// `view`-style `u64` symbol) in `t` and all its sub-terms.
fn count_syms(m: &TermManager, t: TermId, out: &mut FxHashMap<u64, u32>) {
    if let Some(TermKind::Apply { func, .. }) = m.get(t).map(|x| &x.kind) {
        *out.entry(spur_sym(*func)).or_insert(0) += 1;
    }
    for c in subterms(m, t) {
        count_syms(m, c, out);
    }
}

/// Record every GROUND function application (one whose entire subtree contains
/// no variable) under its `view`-style symbol, returning whether `t` itself is
/// ground. Descends through quantifier bodies, but an application that mentions
/// a bound variable (e.g. `(f x)` under `∀x`) is non-ground and therefore NOT
/// recorded — exactly the pinned/free split the completion verify needs.
fn collect_ground_apps(m: &TermManager, t: TermId, out: &mut FxHashMap<u64, Vec<TermId>>) -> bool {
    let Some(term) = m.get(t) else {
        return true; // a missing node carries no variable
    };
    if let TermKind::Var(_) = &term.kind {
        return false;
    }
    // Recurse into EVERY child (so nested ground apps are recorded even when the
    // parent is non-ground); `t` is ground iff all children are.
    let mut ground = true;
    for c in subterms(m, t) {
        if !collect_ground_apps(m, c, out) {
            ground = false;
        }
    }
    if ground {
        if let TermKind::Apply { func, .. } = &term.kind {
            out.entry(spur_sym(*func)).or_default().push(t);
        }
    }
    ground
}

/// Record TOP-LEVEL equality pins: for `(= a b)` reached through conjunctions
/// only (never under a disjunction, negation, quantifier, or other non-monotone
/// context, where the equation is not unconditionally true), pin each side to
/// the other. Such an equation holds in EVERY model, so following the pins to a
/// literal yields a faithful concrete value. We descend only through `And` and
/// stop at `Eq`, so every term reached is at top level — outside any quantifier,
/// hence any `Var` here is a free constant, never a bound variable; that is why
/// no groundness gate is needed.
fn collect_eq_pins(m: &TermManager, t: TermId, out: &mut FxHashMap<TermId, Vec<TermId>>) {
    match m.get(t).map(|x| &x.kind) {
        Some(TermKind::And(args)) => {
            for &c in args.iter() {
                collect_eq_pins(m, c, out);
            }
        }
        Some(TermKind::Eq(a, b)) => {
            let (a, b) = (*a, *b);
            out.entry(a).or_default().push(b);
            out.entry(b).or_default().push(a);
        }
        // Any other shape (Or / Not / Implies / Ite / quantifier / inequality /
        // …) is NOT an unconditionally-true equation — do not descend.
        _ => {}
    }
}

/// Resolve `t` to a concrete integer using ONLY equality pins and integer
/// literals — NEVER the model's `assign` map, which defaults an
/// inequality-constrained term (UF application OR plain constant) to a poisoned
/// `0`. Follows `(= t k)` chains to an `IntConst`; `None` if it does not bottom
/// out at one. Depth-bounded against equality cycles.
fn resolve_eq_concrete(
    m: &TermManager,
    t: TermId,
    eq_pins: &FxHashMap<TermId, Vec<TermId>>,
    depth: u32,
) -> Option<num_bigint::BigInt> {
    if depth == 0 {
        return None;
    }
    match m.get(t).map(|x| &x.kind) {
        Some(TermKind::IntConst(b)) => Some(b.clone()),
        Some(TermKind::Neg(x)) => resolve_eq_concrete(m, *x, eq_pins, depth - 1).map(|v| -v),
        _ => eq_pins
            .get(&t)?
            .iter()
            .find_map(|&p| resolve_eq_concrete(m, p, eq_pins, depth - 1)),
    }
}

/// Mark every uninterpreted symbol in `t`'s subtree as non-monotone (`mixed`):
/// it sits in a term / non-monotone context where it cannot be freely set.
fn mark_mixed(m: &TermManager, t: TermId, f: &mut CompletionFacts) {
    if let Some(TermKind::Apply { func, .. }) = m.get(t).map(|x| &x.kind) {
        f.occurs_mixed.insert(spur_sym(*func));
    }
    for c in subterms(m, t) {
        mark_mixed(m, c, f);
    }
}

/// If `a` is a conservative definition `∀x̄. (= (f x̄) rhs)` — `f` uninterpreted,
/// applied to exactly the distinct bound vars, not occurring in `rhs` — return
/// `f`'s `view`-style symbol. (The caller still checks `f` occurs nowhere else.)
///
/// The application may sit on EITHER side of the equation: `TermManager` builds
/// `Eq` with its operands in a canonical order, so for `∀x. (= (f x) x)` the
/// bound var (interned earlier than the application) becomes the lhs and `(f x)`
/// the rhs — both orderings are tried.
fn definitional_head(m: &TermManager, a: TermId) -> Option<u64> {
    let (_, _, fsym) = definitional_match(m, a)?;
    Some(fsym)
}

/// Extract `(lhs argument terms, rhs, f-symbol)` of a definitional axiom
/// `∀x̄. (= (f x̄) rhs)` (operand order canonicalised — see [`definitional_head`]).
/// The argument terms are the bound-var occurrences `Var(x_i)`.
fn definitional_match(m: &TermManager, a: TermId) -> Option<(Vec<TermId>, TermId, u64)> {
    let TermKind::Forall { vars, body, .. } = &m.get(a)?.kind else {
        return None;
    };
    let TermKind::Eq(o1, o2) = &m.get(*body)?.kind else {
        return None;
    };
    let (o1, o2) = (*o1, *o2);
    let bound: Vec<Spur> = vars.iter().map(|(n, _)| *n).collect();
    // The defining application is whichever side is `(f x̄)` over the distinct
    // bound vars; the other side is the rhs.
    definitional_side(m, o1, o2, &bound).or_else(|| definitional_side(m, o2, o1, &bound))
}

/// If `app` is `(f x̄)` applied to exactly the distinct `bound` vars and `f` does
/// not occur in `rhs`, return `(app's argument terms, rhs, f-symbol)`.
fn definitional_side(
    m: &TermManager,
    app: TermId,
    rhs: TermId,
    bound: &[Spur],
) -> Option<(Vec<TermId>, TermId, u64)> {
    let TermKind::Apply { func, args } = &m.get(app)?.kind else {
        return None;
    };
    if args.len() != bound.len() {
        return None;
    }
    let mut seen: FxHashSet<Spur> = FxHashSet::default();
    for &arg in args.iter() {
        let TermKind::Var(s) = &m.get(arg)?.kind else {
            return None;
        };
        if !bound.contains(s) || !seen.insert(*s) {
            return None;
        }
    }
    let fsym = spur_sym(*func);
    let mut rhs_occ: FxHashMap<u64, u32> = FxHashMap::default();
    count_syms(m, rhs, &mut rhs_occ);
    if rhs_occ.contains_key(&fsym) {
        return None;
    }
    Some((args.to_vec(), rhs, fsym))
}

/// Extract the `(lhs argument terms, rhs)` of a definitional axiom (order-agnostic).
fn definitional_lhs_rhs(m: &TermManager, a: TermId) -> Option<(Vec<TermId>, TermId)> {
    let (args, rhs, _) = definitional_match(m, a)?;
    Some((args, rhs))
}

/// Does `f := λx̄. rhs` agree with every GROUND `f`-application? Sound only for
/// an `rhs` we can evaluate at the ground arguments WITHOUT interning: a
/// projection onto one bound var (`f(x̄) = x_i`, so `f(t̄) = t_i`) or a literal
/// constant (`f(x̄) = c`). Any other `rhs`, a non-eq-pinned application, or a
/// pin that disagrees ⇒ `false` (the caller then leaves the axiom for the engine
/// to instantiate — the sound `Unknown`/`unsat`, never a guessed `sat`).
fn definitional_ground_consistent(
    m: &TermManager,
    lhs_args: &[TermId],
    rhs: TermId,
    fsym: u64,
    ground_apps: &FxHashMap<u64, Vec<TermId>>,
    eq_pins: &FxHashMap<TermId, Vec<TermId>>,
) -> bool {
    let Some(apps) = ground_apps.get(&fsym) else {
        return true; // no ground applications → the definition constrains nothing else
    };
    enum Rhs {
        Proj(usize),
        Const(TermId),
        Other,
    }
    let rhs_class = if let Some(i) = lhs_args.iter().position(|&la| la == rhs) {
        Rhs::Proj(i)
    } else if matches!(
        m.get(rhs).map(|t| &t.kind),
        Some(TermKind::IntConst(_) | TermKind::RealConst(_))
    ) {
        Rhs::Const(rhs)
    } else {
        Rhs::Other
    };
    for &app in apps {
        let Some(TermKind::Apply { args, .. }) = m.get(app).map(|t| &t.kind) else {
            return false;
        };
        let predicted = match &rhs_class {
            Rhs::Proj(i) => match args.get(*i) {
                Some(&t) => t,
                None => return false,
            },
            Rhs::Const(c) => *c,
            Rhs::Other => return false,
        };
        match eq_pins.get(&app) {
            Some(vals) if vals.contains(&predicted) => {}
            _ => return false,
        }
    }
    true
}

// ───────────────────────── monotonicity knowledge base ─────────────────────
//
// A SOUND, structural certifier for the monotonicity of an arithmetic expression
// as a function of one variable — the "monotonicity KB". Every rule is a
// theorem, so a positive certificate is sound to feed a VALIDITY judgement: an
// implication `(x ⊴ y) ⇒ (E[x] ⊴ E[y])` is valid in EVERY interpretation when
// `E` is monotone in the matching direction (no model needed). Used by
// [`SolverModel::body_is_valid`] via [`is_monotone_implication`].

/// Monotonicity direction of an expression in one variable (`Const` = does not
/// depend on it).
#[derive(Clone, Copy, PartialEq, Eq)]
enum MonoDir {
    Inc,
    Dec,
    Const,
}

/// `(direction, strict)`. `strict` = `<`-monotone (injective ⇒ invertible),
/// vs merely `≤`-monotone; `Const` is never strict.
type Mono = (MonoDir, bool);

#[inline]
fn mono_flip((d, s): Mono) -> Mono {
    match d {
        MonoDir::Inc => (MonoDir::Dec, s),
        MonoDir::Dec => (MonoDir::Inc, s),
        MonoDir::Const => (MonoDir::Const, false),
    }
}

/// Scale by a scalar of the given sign: `>0` preserves, `<0` flips, `0` ⇒ `Const`.
fn mono_scale(sign: i32, inner: Mono) -> Mono {
    match sign.cmp(&0) {
        std::cmp::Ordering::Greater => inner,
        std::cmp::Ordering::Less => mono_flip(inner),
        std::cmp::Ordering::Equal => (MonoDir::Const, false),
    }
}

/// Combine the addends of a sum: `↑+↑=↑`, `↓+↓=↓`, `Const` is the identity, a
/// mix of `↑` and `↓` is undetermined (`None`). Strict if any same-direction
/// addend is strict.
fn mono_sum(parts: &[Mono]) -> Option<Mono> {
    let mut dir = MonoDir::Const;
    let mut strict = false;
    for &(d, s) in parts {
        match (dir, d) {
            (_, MonoDir::Const) => {}
            (MonoDir::Const, _) => {
                dir = d;
                strict = s;
            }
            (a, b) if a == b => strict |= s,
            _ => return None,
        }
    }
    Some((dir, strict))
}

/// Sign of a literal constant term (`+1`/`-1`/`0`), or `None` if not a literal.
fn literal_sign(m: &TermManager, t: TermId) -> Option<i32> {
    match m.get(t).map(|x| &x.kind)? {
        TermKind::IntConst(b) => Some(match b.sign() {
            num_bigint::Sign::Plus => 1,
            num_bigint::Sign::Minus => -1,
            num_bigint::Sign::NoSign => 0,
        }),
        TermKind::RealConst(r) => Some((r.numer().signum()) as i32),
        TermKind::Neg(a) => literal_sign(m, *a).map(|s| -s),
        _ => None,
    }
}

/// Does the subtree of `t` mention the variable `var`?
fn term_mentions_var(m: &TermManager, t: TermId, var: Spur) -> bool {
    match m.get(t).map(|x| &x.kind) {
        Some(TermKind::Var(s)) => *s == var,
        Some(_) => subterms(m, t).iter().any(|&c| term_mentions_var(m, c, var)),
        None => false,
    }
}

/// Certify the monotonicity of `e` in `var`. Tries the fast structural
/// sign-algebra first, then falls back to the symbolic-calculus engine
/// ([`crate::calculus`]) — translating `e` to a calculus expression and running
/// the first-derivative test over all reals. Both are sound; the calculus engine
/// covers shapes (powers, and — once the symbols exist — the transcendental KB)
/// the affine sign-algebra alone cannot.
fn monotonicity(m: &TermManager, e: TermId, var: Spur, depth: u32) -> Option<Mono> {
    monotonicity_structural(m, e, var, depth).or_else(|| monotonicity_via_calculus(m, e, var))
}

/// Translate an OxiZ arithmetic term to a single-variable [`calculus::Expr`]
/// (the bound `var` becomes the calculus variable; literals become constants).
/// `None` if any subterm is outside the translatable fragment (another variable
/// — an unknown-sign constant w.r.t. `var` — or an uninterpreted application).
fn term_to_calculus(m: &TermManager, t: TermId, var: Spur) -> Option<crate::calculus::Expr> {
    use crate::calculus::Expr as E;
    match m.get(t).map(|x| x.kind.clone())? {
        TermKind::Var(s) => {
            if s == var {
                Some(E::X)
            } else {
                None // another variable: its sign w.r.t. `var` is unknown
            }
        }
        TermKind::IntConst(b) => Some(E::Const(num_rational::BigRational::from_integer(b))),
        TermKind::RealConst(r) => Some(E::Const(num_rational::BigRational::new(
            num_bigint::BigInt::from(*r.numer()),
            num_bigint::BigInt::from(*r.denom()),
        ))),
        TermKind::Neg(a) => Some(E::Neg(Box::new(term_to_calculus(m, a, var)?))),
        TermKind::Add(args) => {
            let xs: Option<Vec<E>> = args.iter().map(|&a| term_to_calculus(m, a, var)).collect();
            Some(E::Add(xs?))
        }
        TermKind::Mul(args) => {
            let xs: Option<Vec<E>> = args.iter().map(|&a| term_to_calculus(m, a, var)).collect();
            Some(E::Mul(xs?))
        }
        TermKind::Sub(a, b) => Some(E::Add(vec![
            term_to_calculus(m, a, var)?,
            E::Neg(Box::new(term_to_calculus(m, b, var)?)),
        ])),
        _ => None,
    }
}

/// The calculus-engine fallback for [`monotonicity`]: translate + first-derivative
/// test over all reals, mapping the verdict back to the local [`Mono`].
fn monotonicity_via_calculus(m: &TermManager, e: TermId, var: Spur) -> Option<Mono> {
    let expr = term_to_calculus(m, e, var)?;
    let (dir, strict) = expr.monotonicity_strict(&crate::calculus::Domain::all())?;
    let local = match dir {
        crate::calculus::MonoDir::Inc => MonoDir::Inc,
        crate::calculus::MonoDir::Dec => MonoDir::Dec,
        crate::calculus::MonoDir::Const => MonoDir::Const,
    };
    Some((local, strict))
}

/// Certify the monotonicity of arithmetic expression `e` in `var` using only
/// sound structural rules. `None` when no rule applies (caller stays
/// conservative). `depth`-bounded against pathological nesting.
fn monotonicity_structural(m: &TermManager, e: TermId, var: Spur, depth: u32) -> Option<Mono> {
    if depth == 0 {
        return None;
    }
    if !term_mentions_var(m, e, var) {
        return Some((MonoDir::Const, false));
    }
    match m.get(e).map(|x| x.kind.clone())? {
        TermKind::Var(s) => Some(if s == var {
            (MonoDir::Inc, true)
        } else {
            (MonoDir::Const, false)
        }),
        TermKind::Neg(a) => Some(mono_flip(monotonicity_structural(m, a, var, depth - 1)?)),
        TermKind::Add(args) => {
            let parts: Option<Vec<Mono>> = args
                .iter()
                .map(|&a| monotonicity_structural(m, a, var, depth - 1))
                .collect();
            mono_sum(&parts?)
        }
        TermKind::Sub(a, b) => {
            let ma = monotonicity_structural(m, a, var, depth - 1)?;
            let mb = mono_flip(monotonicity_structural(m, b, var, depth - 1)?);
            mono_sum(&[ma, mb])
        }
        TermKind::Mul(args) => {
            // At most one factor may mention `var`; the rest must be literal
            // constants whose sign product is the scaling.
            let mut var_factor: Option<TermId> = None;
            let mut sign = 1i32;
            for &a in args.iter() {
                if term_mentions_var(m, a, var) {
                    if var_factor.is_some() {
                        return None; // x·x and the like — not handled soundly here
                    }
                    var_factor = Some(a);
                } else {
                    sign *= literal_sign(m, a)?;
                }
            }
            Some(mono_scale(sign, monotonicity_structural(m, var_factor?, var, depth - 1)?))
        }
        TermKind::Div(a, b) => {
            // `a / c` for a nonzero literal `c` = scale by sign(c).
            if term_mentions_var(m, b, var) {
                return None;
            }
            let sign = literal_sign(m, b)?;
            if sign == 0 {
                return None;
            }
            Some(mono_scale(sign, monotonicity_structural(m, a, var, depth - 1)?))
        }
        _ => None,
    }
}

/// Is `l == E[x]` and `r == E[y]` for a common one-hole context `E` whose hole
/// is exactly the variable `x` (resp. `y`)? Commutative `Add`/`Mul` children are
/// matched up to permutation (the `TermManager` canonicalises operand order by
/// `TermId`, so `E[x]` and `E[y]` can list their operands differently).
fn anti_unify_hole(m: &TermManager, l: TermId, r: TermId, x: Spur, y: Spur, depth: u32) -> bool {
    if depth == 0 {
        return false;
    }
    if l == r {
        // Identical subtree: a hole-free constant part — sound only if it does
        // not itself mention the hole var (else it would have had to change).
        return !term_mentions_var(m, l, x);
    }
    let (lk, rk) = match (m.get(l), m.get(r)) {
        (Some(a), Some(b)) => (&a.kind, &b.kind),
        _ => return false,
    };
    // The hole: `Var(x)` on the left aligns with `Var(y)` on the right.
    if let (TermKind::Var(a), TermKind::Var(b)) = (lk, rk) {
        return *a == x && *b == y;
    }
    // Same operator: an application needs the SAME function head.
    if let (TermKind::Apply { func: f1, .. }, TermKind::Apply { func: f2, .. }) = (lk, rk) {
        if f1 != f2 {
            return false;
        }
    } else if std::mem::discriminant(lk) != std::mem::discriminant(rk) {
        return false;
    }
    let lc = subterms(m, l);
    let rc = subterms(m, r);
    if lc.len() != rc.len() {
        return false;
    }
    // Two DISTINCT leaves (`l != r`, established above) with no children — e.g.
    // the constants `5` and `7`, or two unrelated vars — are NOT a common
    // context: they differ but neither is the hole. (Without this, `(+ x 7)` and
    // `(+ y 5)` would vacuously "anti-unify", certifying the INVALID
    // `x≤y ⇒ x+7 ≤ y+5` — a spurious sat.)
    if lc.is_empty() {
        return false;
    }
    // Match children up to permutation (greedy bijection): every left child must
    // anti-unify with a distinct right child.
    let mut used = vec![false; rc.len()];
    for &lci in &lc {
        let mut matched = false;
        for (j, &rcj) in rc.iter().enumerate() {
            if !used[j] && anti_unify_hole(m, lci, rcj, x, y, depth - 1) {
                used[j] = true;
                matched = true;
                break;
            }
        }
        if !matched {
            return false;
        }
    }
    true
}

/// Recognise a VALID monotonicity implication `(x ⊴ y) ⇒ (E[x] ⊵ E[y])`: the
/// guard orders two distinct bound vars, the consequent compares `E` at those
/// vars, and `E` is certifiably monotone in the matching direction. Valid in
/// every interpretation, so sound to treat the universal closure as `Sat`.
fn is_monotone_implication(m: &TermManager, guard: TermId, conseq: TermId) -> bool {
    // guard: `(≤ x y)` / `(< x y)` over two distinct bound vars (the order).
    let (gx, gy, guard_strict) = match m.get(guard).map(|t| &t.kind) {
        Some(TermKind::Le(a, b)) => (*a, *b, false),
        Some(TermKind::Lt(a, b)) => (*a, *b, true),
        _ => return false,
    };
    let (x, y) = match (m.get(gx).map(|t| &t.kind), m.get(gy).map(|t| &t.kind)) {
        (Some(TermKind::Var(a)), Some(TermKind::Var(b))) if a != b => (*a, *b),
        _ => return false,
    };
    // consequent: `(⊴ L R)` with `L = E[x]`, `R = E[y]`. Direction + strictness.
    let (l, r, conseq_strict, need_dir) = match m.get(conseq).map(|t| &t.kind) {
        Some(TermKind::Le(l, r)) => (*l, *r, false, MonoDir::Inc),
        Some(TermKind::Lt(l, r)) => (*l, *r, true, MonoDir::Inc),
        Some(TermKind::Ge(l, r)) => (*l, *r, false, MonoDir::Dec),
        Some(TermKind::Gt(l, r)) => (*l, *r, true, MonoDir::Dec),
        _ => return false,
    };
    if !anti_unify_hole(m, l, r, x, y, 64) {
        return false;
    }
    let Some((dir, strict)) = monotonicity(m, l, x, 64) else {
        return false;
    };
    if conseq_strict {
        // `E[x] < E[y]` from `x ⊴ y` needs a STRICT antecedent (`x < y`, else
        // `x = y` gives `E[x] = E[y]`) AND strictly-monotone `E` in `need_dir`.
        guard_strict && strict && dir == need_dir
    } else {
        // `E[x] ≤ E[y]`: weak monotone in `need_dir`, or a constant `E`
        // (`E[x] = E[y]`, reflexively `≤`).
        dir == need_dir || dir == MonoDir::Const
    }
}

// ─────────────────── monotone order-extension (uninterpreted f) ─────────────
//
// A bare monotonicity axiom `∀x,y. (x⊴y) ⇒ (f(x)⊵f(y))` over an UNINTERPRETED
// `f` is satisfiable together with the ground facts about `f` iff those facts
// admit a MONOTONE total extension — a standard order-extension theorem. The
// recognizer collects the ground `f`-points' numeric bounds (Pass 6) and greedily
// checks a monotone selection exists; if so the axiom is sound to report `Sat`
// (a model exists). It declines (→ `None`) whenever any `f`-constraint is outside
// the handled WEAK shapes (accounting guard) — sound: an unmodeled constraint
// could forbid the extension, so a guessed `Sat` is never emitted.

/// A constant term as an exact rational, or `None` if not a literal.
fn term_to_rational(m: &TermManager, t: TermId) -> Option<num_rational::BigRational> {
    use num_bigint::BigInt;
    use num_rational::BigRational;
    match m.get(t).map(|x| &x.kind)? {
        TermKind::IntConst(b) => Some(BigRational::from_integer(b.clone())),
        TermKind::RealConst(r) => {
            Some(BigRational::new(BigInt::from(*r.numer()), BigInt::from(*r.denom())))
        }
        TermKind::Neg(a) => term_to_rational(m, *a).map(|v| -v),
        _ => None,
    }
}

#[inline]
fn is_apply(m: &TermManager, t: TermId) -> bool {
    matches!(m.get(t).map(|x| &x.kind), Some(TermKind::Apply { .. }))
}

/// Record a tightest lower / upper bound on the ground application `app`, and
/// tally its `Apply` head into `mono_handled_occ`.
fn mono_record_bound(
    m: &TermManager,
    app: TermId,
    lo: Option<num_rational::BigRational>,
    hi: Option<num_rational::BigRational>,
    f: &mut CompletionFacts,
) {
    if let Some(TermKind::Apply { func, .. }) = m.get(app).map(|x| &x.kind) {
        *f.mono_handled_occ.entry(spur_sym(*func)).or_insert(0) += 1;
    }
    if let Some(l) = lo {
        f.mono_lo
            .entry(app)
            .and_modify(|e| {
                if l > *e {
                    *e = l.clone();
                }
            })
            .or_insert(l);
    }
    if let Some(h) = hi {
        f.mono_hi
            .entry(app)
            .and_modify(|e| {
                if h < *e {
                    *e = h.clone();
                }
            })
            .or_insert(h);
    }
}

/// Pass 6 worker: record ground numeric bounds / relations on `Apply`s through
/// the top-level conjunction. Only `(= app c)`, `(>= app c)`, `(<= app c)` (with
/// numeric `c`) and `(<= app1 app2)` are handled — every other shape is left
/// untallied so the recognizer's accounting guard rejects the function.
fn collect_mono_facts(m: &TermManager, t: TermId, f: &mut CompletionFacts) {
    match m.get(t).map(|x| x.kind.clone()) {
        Some(TermKind::And(args)) => {
            for c in args.iter() {
                collect_mono_facts(m, *c, f);
            }
        }
        Some(TermKind::Eq(a, b)) => {
            // `app = c` (either order) ⇒ lo = hi = c.
            if is_apply(m, a) {
                if let Some(v) = term_to_rational(m, b) {
                    mono_record_bound(m, a, Some(v.clone()), Some(v), f);
                }
            } else if is_apply(m, b) {
                if let Some(v) = term_to_rational(m, a) {
                    mono_record_bound(m, b, Some(v.clone()), Some(v), f);
                }
            }
        }
        Some(TermKind::Le(a, b)) => {
            // a ≤ b.
            if is_apply(m, a) && is_apply(m, b) {
                if let (Some(TermKind::Apply { func: fa, .. }), Some(TermKind::Apply { func: fb, .. })) =
                    (m.get(a).map(|x| &x.kind), m.get(b).map(|x| &x.kind))
                {
                    *f.mono_handled_occ.entry(spur_sym(*fa)).or_insert(0) += 1;
                    *f.mono_handled_occ.entry(spur_sym(*fb)).or_insert(0) += 1;
                }
                f.mono_rels.push((a, b));
            } else if is_apply(m, a) {
                if let Some(v) = term_to_rational(m, b) {
                    mono_record_bound(m, a, None, Some(v), f); // app ≤ c
                }
            } else if is_apply(m, b) {
                if let Some(v) = term_to_rational(m, a) {
                    mono_record_bound(m, b, Some(v), None, f); // c ≤ app
                }
            }
        }
        Some(TermKind::Ge(a, b)) => {
            // a ≥ b  ⟺  b ≤ a.
            if is_apply(m, a) && is_apply(m, b) {
                if let (Some(TermKind::Apply { func: fa, .. }), Some(TermKind::Apply { func: fb, .. })) =
                    (m.get(a).map(|x| &x.kind), m.get(b).map(|x| &x.kind))
                {
                    *f.mono_handled_occ.entry(spur_sym(*fa)).or_insert(0) += 1;
                    *f.mono_handled_occ.entry(spur_sym(*fb)).or_insert(0) += 1;
                }
                f.mono_rels.push((b, a));
            } else if is_apply(m, a) {
                if let Some(v) = term_to_rational(m, b) {
                    mono_record_bound(m, a, Some(v), None, f); // app ≥ c
                }
            } else if is_apply(m, b) {
                if let Some(v) = term_to_rational(m, a) {
                    mono_record_bound(m, b, None, Some(v), f); // c ≥ app
                }
            }
        }
        _ => {}
    }
}

/// Recognise a satisfiable bare monotonicity axiom `∀x,y. (x⊴y) ⇒ (f(x)⊵f(y))`
/// over an uninterpreted unary `f` by checking the ground `f`-points admit a
/// monotone extension. Returns `true` (⇒ `Sat`) only when sound.
fn try_monotone_extension(m: &TermManager, facts: &CompletionFacts, body: TermId) -> bool {
    use num_rational::BigRational;
    // body = `(=> (⊴ x y) conseq)`.
    let (guard, conseq) = match m.get(body).map(|t| &t.kind) {
        Some(TermKind::Implies(g, c)) => (*g, *c),
        _ => return false,
    };
    let (gx, gy) = match m.get(guard).map(|t| &t.kind) {
        Some(TermKind::Le(a, b)) | Some(TermKind::Lt(a, b)) => (*a, *b),
        _ => return false,
    };
    if !matches!(m.get(gx).map(|t| &t.kind), Some(TermKind::Var(_)))
        || !matches!(m.get(gy).map(|t| &t.kind), Some(TermKind::Var(_)))
        || gx == gy
    {
        return false;
    }
    // conseq = `(⊴ f(·) f(·))`. Extract the two applications + the comparison's
    // increasing/decreasing sense.
    let (cl, cr, conseq_inc) = match m.get(conseq).map(|t| &t.kind) {
        Some(TermKind::Le(l, r)) => (*l, *r, true),
        Some(TermKind::Ge(l, r)) => (*l, *r, false),
        _ => return false,
    };
    // Both sides must be `f(var)` for the SAME uninterpreted unary `f`, one over
    // `gx` and the other over `gy`.
    let (fsym, increasing) = match (m.get(cl).map(|t| &t.kind), m.get(cr).map(|t| &t.kind)) {
        (
            Some(TermKind::Apply { func: f1, args: a1 }),
            Some(TermKind::Apply { func: f2, args: a2 }),
        ) if f1 == f2 && a1.len() == 1 && a2.len() == 1 => {
            let (l_over_x, l_over_y) = (a1[0] == gx, a1[0] == gy);
            let (r_over_x, r_over_y) = (a2[0] == gx, a2[0] == gy);
            // `f(gx)`/`f(gy)` must appear once each across the two sides.
            if !((l_over_x && r_over_y) || (l_over_y && r_over_x)) {
                return false;
            }
            // `conseq_inc` = the consequent is `(<= cl cr)`. With the guard `gx≤gy`,
            // `f(gx) ≤ f(gy)` (lhs over `gx`) is INCREASING; lhs over `gy` flips it.
            let increasing = if l_over_x { conseq_inc } else { !conseq_inc };
            (spur_sym(*f1), increasing)
        }
        _ => return false,
    };

    // Accounting guard: every `f`-application must be in the axiom (2) or the
    // handled ground bounds — otherwise some unmodeled constraint exists.
    let axiom_occ = 2u32; // f(x), f(y)
    let handled = facts.mono_handled_occ.get(&fsym).copied().unwrap_or(0);
    if facts.global_occ.get(&fsym).copied().unwrap_or(0) != axiom_occ + handled {
        return false;
    }
    let Some(apps) = facts.ground_apps.get(&fsym) else {
        return true; // no ground points: the empty partial function is monotone
    };

    // Build (arg → merged [lo, hi]) for the ground points; bail on a non-literal
    // argument (cannot place it on the order).
    let mut points: std::collections::BTreeMap<BigRational, (Option<BigRational>, Option<BigRational>)> =
        std::collections::BTreeMap::new();
    for &app in apps {
        let Some(TermKind::Apply { args, .. }) = m.get(app).map(|t| &t.kind) else {
            return false;
        };
        if args.len() != 1 {
            return false;
        }
        let Some(arg) = term_to_rational(m, args[0]) else {
            return false;
        };
        let lo = facts.mono_lo.get(&app).cloned();
        let hi = facts.mono_hi.get(&app).cloned();
        let entry = points.entry(arg).or_insert((None, None));
        // Merge (intersect) bounds for the same argument (congruence).
        if let Some(l) = lo {
            entry.0 = Some(match &entry.0 {
                Some(e) if *e > l => e.clone(),
                _ => l,
            });
        }
        if let Some(h) = hi {
            entry.1 = Some(match &entry.1 {
                Some(e) if *e < h => e.clone(),
                _ => h,
            });
        }
    }

    // Relations `(<= p q)` between two `f`-apps must be IMPLIED by monotonicity
    // (so they add nothing); a non-implied relation could forbid the extension.
    for &(p, q) in &facts.mono_rels {
        let (hp, hq) = (
            m.get(p).and_then(|t| if let TermKind::Apply { func, .. } = &t.kind { Some(spur_sym(*func)) } else { None }),
            m.get(q).and_then(|t| if let TermKind::Apply { func, .. } = &t.kind { Some(spur_sym(*func)) } else { None }),
        );
        if hp != Some(fsym) || hq != Some(fsym) {
            continue;
        }
        let (ap, aq) = match (
            m.get(p).map(|t| t.kind.clone()),
            m.get(q).map(|t| t.kind.clone()),
        ) {
            (Some(TermKind::Apply { args: a1, .. }), Some(TermKind::Apply { args: a2, .. }))
                if a1.len() == 1 && a2.len() == 1 =>
            {
                match (term_to_rational(m, a1[0]), term_to_rational(m, a2[0])) {
                    (Some(x), Some(y)) => (x, y),
                    _ => return false,
                }
            }
            _ => return false,
        };
        // `f(ap) ≤ f(aq)` implied by INC iff ap ≤ aq; by DEC iff ap ≥ aq.
        let implied = if increasing { ap <= aq } else { ap >= aq };
        if !implied {
            return false;
        }
    }

    // Greedy feasibility over the sorted points.
    if increasing {
        let mut prev: Option<BigRational> = None; // −∞
        for (_arg, (lo, hi)) in points.iter() {
            let v: Option<BigRational> = match (lo, &prev) {
                (Some(l), Some(p)) => Some(if l > p { l.clone() } else { p.clone() }),
                (Some(l), None) => Some(l.clone()),
                (None, Some(p)) => Some(p.clone()),
                (None, None) => None,
            };
            if let (Some(vv), Some(h)) = (&v, hi) {
                if vv > h {
                    return false;
                }
            }
            if v.is_some() {
                prev = v;
            }
        }
    } else {
        let mut prev: Option<BigRational> = None; // +∞
        for (_arg, (lo, hi)) in points.iter() {
            let v: Option<BigRational> = match (hi, &prev) {
                (Some(h), Some(p)) => Some(if h < p { h.clone() } else { p.clone() }),
                (Some(h), None) => Some(h.clone()),
                (None, Some(p)) => Some(p.clone()),
                (None, None) => None,
            };
            if let (Some(vv), Some(l)) = (&v, lo) {
                if vv < l {
                    return false;
                }
            }
            if v.is_some() {
                prev = v;
            }
        }
    }
    true
}

// ───────────────────────── idempotent axiom `f∘f = f` ──────────────────────
//
// `∀x. f(f(x)) = f(x)` over an uninterpreted `f` is satisfiable together with
// its ground facts iff those facts are IDEMPOTENCY-CONSISTENT: instantiating the
// axiom at a pinned point `f(t)=v` forces `f(v)=f(f(t))=f(t)=v`, so every pinned
// value must itself be a fixed point. When that holds, an idempotent total
// model exists (identity off the pinned points, which already map into their own
// fixed points), so the axiom is sound to report `Sat`.

/// If `ffx`/`fx` are `(f (f x))`/`(f x)` for the SAME uninterpreted unary `f`
/// over the bound var `x`, return `f`'s symbol.
fn idempotent_sides(m: &TermManager, ffx: TermId, fx: TermId, x: Spur) -> Option<u64> {
    let TermKind::Apply { func: f1, args: a1 } = m.get(ffx)?.kind.clone() else {
        return None;
    };
    if a1.len() != 1 || a1[0] != fx {
        return None;
    }
    let TermKind::Apply { func: f2, args: a2 } = m.get(fx)?.kind.clone() else {
        return None;
    };
    if f1 != f2 || a2.len() != 1 {
        return None;
    }
    let TermKind::Var(s) = m.get(a2[0])?.kind else {
        return None;
    };
    if s != x {
        return None;
    }
    Some(spur_sym(f1))
}

/// Recognise a satisfiable idempotent axiom `∀x. f(f(x)) = f(x)` by checking the
/// ground `f`-points are idempotency-consistent. Sound — declines (→ `false`)
/// unless `f` is confined to this axiom + eq-pinned ground points.
fn try_idempotent(m: &TermManager, facts: &CompletionFacts, body: TermId, bound: &[Spur]) -> bool {
    if bound.len() != 1 {
        return false;
    }
    let x = bound[0];
    let TermKind::Eq(o1, o2) = (match m.get(body) {
        Some(t) => t.kind.clone(),
        None => return false,
    }) else {
        return false;
    };
    let Some(fsym) = idempotent_sides(m, o1, o2, x).or_else(|| idempotent_sides(m, o2, o1, x))
    else {
        return false;
    };
    // `f` must occur in no OTHER quantifier (this axiom contributes 1).
    if facts.quant_count.get(&fsym).copied().unwrap_or(0) > 1 {
        return false;
    }
    let Some(apps) = facts.ground_apps.get(&fsym) else {
        return true; // no ground points → identity is an idempotent model
    };
    // Map each pinned application's ARGUMENT term → its pinned VALUE term. Every
    // ground application must be eq-pinned (an unpinned one — e.g. in an
    // inequality — could break idempotency, so we cannot certify).
    let mut argval: FxHashMap<TermId, TermId> = FxHashMap::default();
    for &app in apps {
        let TermKind::Apply { args, .. } = (match m.get(app) {
            Some(t) => t.kind.clone(),
            None => return false,
        }) else {
            return false;
        };
        if args.len() != 1 {
            return false;
        }
        match facts.eq_pins.get(&app).and_then(|v| v.first()) {
            Some(&val) => {
                argval.insert(args[0], val);
            }
            None => return false, // unpinned ground application
        }
    }
    // Idempotency-consistency: for each `f(arg)=val`, if `val` is itself the
    // argument of a pinned application, that application must map `val → val`.
    for (_arg, &val) in &argval {
        if let Some(&w) = argval.get(&val) {
            if w != val {
                return false;
            }
        }
    }
    true
}

// ───────────────────── fresh-Skolem equality-witness recognizer ─────────────
//
// The `∀∃` "anchorless" case. A formula `∀x̄. ∃ȳ. φ` skolemizes
// ([`skolemize_unbounded_existentials`]) to `∀x̄. φ[ȳ ↦ sk(x̄)]` for a fresh
// Skolem function `sk`. When `φ` is an EQUALITY `L = f(ȳ)` — e.g.
// `∀x.∃y. g(x)=f(y)` → `∀x. g(x)=f(sk(x))` — neither the pure-predicate nor the
// single-function-completion recognizer fires (both sides mention `x`), yet the
// axiom is satisfiable by a free choice of the Skolem witness. This recognizer
// closes exactly that gap.

/// Free **variable names** (Spurs) occurring in `t`, built from the manager's
/// capture-free `free_vars`.
fn free_var_spurs(m: &TermManager, t: TermId) -> FxHashSet<Spur> {
    m.free_vars(t)
        .into_iter()
        .filter_map(|v| match m.get(v).map(|x| &x.kind) {
            Some(TermKind::Var(s)) => Some(*s),
            _ => None,
        })
        .collect()
}

/// Is `t` an application of a FRESH Skolem function — one minted by
/// [`skolemize_unbounded_existentials`] (name `sk!…`)?  Each such name is unique
/// per existential, so the symbol occurs in exactly the one axiom it was
/// introduced for and in no ground fact: its interpretation is entirely the
/// model-builder's to choose.  Returns the skolem's `view`-symbol on a match.
fn fresh_skolem_head(m: &TermManager, t: TermId) -> Option<u64> {
    let TermKind::Apply { func, .. } = &m.get(t)?.kind else {
        return None;
    };
    m.resolve_str(*func).starts_with("sk!").then(|| spur_sym(*func))
}

/// **M3 recognizer — fresh-Skolem equality witness** (the `∀∃` anchorless case
/// after skolemization).  Body `∀x̄. (= L R)` where one side is `(f … sk(x̄) …)`:
///   * `f` is uninterpreted and constrained by NO other quantifier
///     (`quant_count[f] == 1`) — so the REST of the formula pins `f` only at
///     finitely many GROUND points;
///   * `sk` is a fresh Skolem function (name `sk!…`, single-quantifier) whose
///     arguments cover EVERY bound variable — so `x̄ ↦ sk(x̄)` is injective and
///     its values are the model-builder's free choice, all of which can be kept
///     distinct from the (finitely many) ground `f`-points;
///   * the OTHER side `L` does NOT mention `f` — so `L`'s value is fixed by any
///     model of the rest, with no circular dependence on the points we define.
///
/// Then for every `x̄` pick a fresh integer `sk(x̄)` outside the ground
/// `f`-points and set `f(sk(x̄)) := L(x̄)`: the equation holds and no term of the
/// rest of the formula changes value (`sk` occurs nowhere else, the ground
/// `f`-points are untouched).  A CONSERVATIVE EXTENSION over `f` and `sk` — sound
/// `Sat`.  Declines (sound `None`/`Unknown`) on any unmet guard.
///
/// Example (`skolem_test`): `∀x. (g x) = (f (sk x))` with ground `g 0 = 10`,
/// `f 5 = 10`, `g 1 = 20`, `f 7 = 20` — witnessed by `sk 0 = 5`, `sk 1 = 7`.
fn try_skolem_witness_eq(
    m: &TermManager,
    facts: &CompletionFacts,
    body: TermId,
    bound: &[Spur],
) -> bool {
    if bound.is_empty() {
        return false;
    }
    let TermKind::Eq(o1, o2) = (match m.get(body) {
        Some(t) => t.kind.clone(),
        None => return false,
    }) else {
        return false;
    };
    // Try each orientation: (witness side `f(…sk(x̄)…)`, other side `L`).
    skolem_witness_side(m, facts, o1, o2, bound) || skolem_witness_side(m, facts, o2, o1, bound)
}

/// One orientation of [`try_skolem_witness_eq`]: `w` is the candidate witness
/// side `f(… sk(x̄) …)`, `o` the other side `L`.
fn skolem_witness_side(
    m: &TermManager,
    facts: &CompletionFacts,
    w: TermId,
    o: TermId,
    bound: &[Spur],
) -> bool {
    // `w` = an application of an uninterpreted function `f`.
    let TermKind::Apply { func: f_func, args: f_args } = (match m.get(w) {
        Some(t) => t.kind.clone(),
        None => return false,
    }) else {
        return false;
    };
    let fsym = spur_sym(f_func);
    if fsym & OP != 0 {
        return false; // a builtin op, not an uninterpreted function (defensive)
    }
    // `f` must be this axiom's SOLE universal constraint — the rest of the
    // formula then pins `f` only at finitely many ground points, all distinct
    // from the fresh skolem witness points we are about to define.
    if facts.quant_count.get(&fsym).copied().unwrap_or(0) != 1 {
        return false;
    }
    // The other side must NOT mention `f`: defining `f` at the (fresh) witness
    // points must not feed back into the value `L` we are matching it to.
    let mut osyms: FxHashMap<u64, u32> = FxHashMap::default();
    count_syms(m, o, &mut osyms);
    if osyms.contains_key(&fsym) {
        return false;
    }
    // Some argument of `f` is a fresh Skolem application `sk(…)` whose arguments
    // cover EVERY bound variable (so `x̄ ↦ sk(x̄)` is injective) and which is
    // itself single-quantifier (fresh ⇒ free to choose).
    let want: FxHashSet<Spur> = bound.iter().copied().collect();
    f_args.iter().any(|&a| match fresh_skolem_head(m, a) {
        Some(sksym) => {
            facts.quant_count.get(&sksym).copied().unwrap_or(0) == 1
                && want.is_subset(&free_var_spurs(m, a))
        }
        None => false,
    })
}

// ───────────────────── constant range-completion recognizer ─────────────────
//
// The DENSE-ORDER (Real / Int) analog of the single-comparison function
// completion (recognizer 4). A universal `∀x̄. ⋀ᵢ cmpᵢ(f(x̄), cᵢ)` bounding ONE
// uninterpreted `f` against ground constants intersects to an interval `[lo,hi]`;
// when it is nonempty (a dense order always has an interior point) and `f` is
// constrained by no other quantifier, completing `f` to any constant in `[lo,hi]`
// on every non-ground argument satisfies the body — a CONSERVATIVE EXTENSION over
// `f` (the ground points keep their verified-in-range values, the completed
// points appear in no other constraint).  This is exactly how a model-based
// solver assigns an uninterpreted `f` a finite graph plus an `else` (default)
// value (cf. z3's `as-array` / `else` model representation).

/// Resolve `t` to an exact rational by following top-level equality pins
/// (`(= t k)`), the rational analog of [`resolve_eq_concrete`].  `None` for
/// anything not pinned to a concrete literal (an inequality- or
/// unconstrained point ⇒ the caller bails conservatively).
fn resolve_eq_rational(
    m: &TermManager,
    t: TermId,
    eq_pins: &FxHashMap<TermId, Vec<TermId>>,
    depth: u32,
) -> Option<num_rational::BigRational> {
    if depth == 0 {
        return None;
    }
    if let Some(v) = term_to_rational(m, t) {
        return Some(v);
    }
    eq_pins
        .get(&t)?
        .iter()
        .find_map(|&p| resolve_eq_rational(m, p, eq_pins, depth - 1))
}

/// One side of an interval: `(value, strict)` where `strict` is `<`/`>` (vs
/// `≤`/`≥`).  `None` = unbounded on that side.
type IntervalBound = Option<(num_rational::BigRational, bool)>;

/// Tighten a LOWER bound with `value` (keep the larger; a tie keeps strict if
/// either is strict).
fn tighten_lo(cur: &mut IntervalBound, value: num_rational::BigRational, strict: bool) {
    match cur {
        None => *cur = Some((value, strict)),
        Some((v, s)) => {
            if value > *v {
                *v = value;
                *s = strict;
            } else if value == *v {
                *s = *s || strict;
            }
        }
    }
}

/// Tighten an UPPER bound with `value` (keep the smaller; strict-on-tie).
fn tighten_hi(cur: &mut IntervalBound, value: num_rational::BigRational, strict: bool) {
    match cur {
        None => *cur = Some((value, strict)),
        Some((v, s)) => {
            if value < *v {
                *v = value;
                *s = strict;
            } else if value == *v {
                *s = *s || strict;
            }
        }
    }
}

/// Is `[lo, hi]` nonempty over a DENSE order?  Empty iff `lo > hi`, or `lo == hi`
/// with either side strict (an unbounded side is always nonempty).
fn interval_nonempty(lo: &IntervalBound, hi: &IntervalBound) -> bool {
    match (lo, hi) {
        (Some((l, ls)), Some((h, hs))) => l < h || (l == h && !ls && !hs),
        _ => true,
    }
}

/// Does `v` satisfy `[lo, hi]` (per-side strictness)?
fn in_interval(v: &num_rational::BigRational, lo: &IntervalBound, hi: &IntervalBound) -> bool {
    if let Some((l, s)) = lo {
        if (*s && v <= l) || (!*s && v < l) {
            return false;
        }
    }
    if let Some((h, s)) = hi {
        if (*s && v >= h) || (!*s && v > h) {
            return false;
        }
    }
    true
}

/// `flip` a comparison op (so a `c <rel> f(x̄)` atom can be read as `f(x̄) <rel'> c`).
fn flip_rel(sym: u64) -> u64 {
    match sym {
        OP_LE => OP_GE,
        OP_GE => OP_LE,
        OP_LT => OP_GT,
        OP_GT => OP_LT,
        other => other, // OP_EQ
    }
}

/// `f`'s `view`-symbol if `t` is a bare application of an uninterpreted `f` that
/// mentions at least one bound (`want`) variable; else `None`.
fn app_over_bound(m: &TermManager, t: TermId, want: &FxHashSet<Spur>) -> Option<u64> {
    let TermKind::Apply { func, .. } = m.get(t)?.kind.clone() else {
        return None;
    };
    let fsym = spur_sym(func);
    if fsym & OP != 0 {
        return None;
    }
    let fv = free_var_spurs(m, t);
    want.iter().any(|s| fv.contains(s)).then_some(fsym)
}

/// `t` as a concrete rational, but ONLY if it is ground w.r.t. the bound vars
/// (mentions no `want` variable).
fn ground_rational(
    m: &TermManager,
    t: TermId,
    want: &FxHashSet<Spur>,
) -> Option<num_rational::BigRational> {
    let fv = free_var_spurs(m, t);
    if want.iter().any(|s| fv.contains(s)) {
        return None;
    }
    term_to_rational(m, t)
}

/// Parse one comparison atom of a range body — `cmp(f(x̄), c)` or `cmp(c, f(x̄))`
/// with one side a bare uninterpreted application mentioning a bound var and the
/// other a ground concrete rational.  Returns `(f-symbol, lo-update, hi-update)`
/// reading the relation as `f <rel> c`.
fn range_atom(
    m: &TermManager,
    atom: TermId,
    want: &FxHashSet<Spur>,
) -> Option<(u64, IntervalBound, IntervalBound)> {
    let (sym, l, r) = match m.get(atom).map(|t| &t.kind)? {
        TermKind::Le(a, b) => (OP_LE, *a, *b),
        TermKind::Lt(a, b) => (OP_LT, *a, *b),
        TermKind::Ge(a, b) => (OP_GE, *a, *b),
        TermKind::Gt(a, b) => (OP_GT, *a, *b),
        TermKind::Eq(a, b) => (OP_EQ, *a, *b),
        _ => return None,
    };
    let (fsym, c, f_on_left) = match (app_over_bound(m, l, want), app_over_bound(m, r, want)) {
        (Some(f), None) => (f, ground_rational(m, r, want)?, true),
        (None, Some(f)) => (f, ground_rational(m, l, want)?, false),
        _ => return None, // not exactly one `f(x̄)` side over a ground constant
    };
    let rel = if f_on_left { sym } else { flip_rel(sym) };
    let (lo, hi) = match rel {
        OP_LE => (None, Some((c, false))),
        OP_LT => (None, Some((c, true))),
        OP_GE => (Some((c, false)), None),
        OP_GT => (Some((c, true)), None),
        OP_EQ => (Some((c.clone(), false)), Some((c, false))),
        _ => return None,
    };
    Some((fsym, lo, hi))
}

/// **M3 recognizer — constant range completion** (dense Real / Int).  Body
/// `∀x̄. ⋀ᵢ cmpᵢ(f(x̄), cᵢ)`: a conjunction of comparison atoms each bounding ONE
/// uninterpreted `f` (applied to the bound vars) against a ground concrete
/// constant — e.g. `∀x. (and (>= (f x) 0.0) (<= (f x) 1.0))`.  The atoms
/// intersect to an interval `[lo, hi]`; when it is nonempty and `f` is this
/// axiom's SOLE universal constraint (`quant_count[f]==1`), complete `f` to any
/// constant in `[lo, hi]` on every non-ground argument.  Verified against the
/// ground `f`-points (each eq-pinned, in range — the #260 gate), this is a
/// CONSERVATIVE EXTENSION over `f`, hence sound `Sat`.  An empty interval means
/// the universal is itself unsatisfiable, so we decline to the sound `Unknown`.
fn try_range_completion(
    m: &TermManager,
    facts: &CompletionFacts,
    body: TermId,
    bound: &[Spur],
) -> bool {
    if bound.is_empty() {
        return false;
    }
    let want: FxHashSet<Spur> = bound.iter().copied().collect();
    // Top-level conjunction (a single atom is a one-conjunct body).
    let conjuncts: Vec<TermId> = match m.get(body).map(|t| &t.kind) {
        Some(TermKind::And(a)) => a.to_vec(),
        Some(_) => vec![body],
        None => return false,
    };
    if conjuncts.is_empty() {
        return false;
    }
    let mut fsym: Option<u64> = None;
    let mut lo: IntervalBound = None;
    let mut hi: IntervalBound = None;
    for &atom in &conjuncts {
        let Some((f, lo_u, hi_u)) = range_atom(m, atom, &want) else {
            return false; // a conjunct we cannot read as a single-`f` bound
        };
        match fsym {
            None => fsym = Some(f),
            Some(p) if p != f => return false, // a second function ⇒ not a single-`f` range
            _ => {}
        }
        if let Some((v, s)) = lo_u {
            tighten_lo(&mut lo, v, s);
        }
        if let Some((v, s)) = hi_u {
            tighten_hi(&mut hi, v, s);
        }
    }
    let Some(fsym) = fsym else {
        return false;
    };
    // `f` must be this axiom's SOLE universal constraint (no other quantifier
    // could forbid the constant completion).
    if facts.quant_count.get(&fsym).copied().unwrap_or(0) != 1 {
        return false;
    }
    // ACCOUNTING GUARD. The constant completion is sound only if EVERY `f`
    // application is either inside THIS body (a `f(x̄)`, handled by the
    // completion) or a LITERAL ground point we verify below. A `f`-application at
    // a SYMBOLIC argument — e.g. `f(c)` for a free constant `c` (`real_unsat`:
    // `∀x.f(x)≤1` with `f(c)>1`) — is NOT recorded as a ground point (its arg is
    // a variable, not a literal), so the verify loop would miss the constraint it
    // carries and the completion could violate it. `range_atom` guarantees the
    // body's only `f`-apps are the bound-var `f(x̄)`, so the body's count plus the
    // literal ground points must exhaust every occurrence; any shortfall is an
    // unaccounted symbolic application ⇒ decline to the sound `Unknown`.
    let mut body_occ: FxHashMap<u64, u32> = FxHashMap::default();
    count_syms(m, body, &mut body_occ);
    let accounted =
        body_occ.get(&fsym).copied().unwrap_or(0) + facts.ground_apps.get(&fsym).map_or(0, |p| p.len() as u32);
    if facts.global_occ.get(&fsym).copied().unwrap_or(0) != accounted {
        return false;
    }
    // A nonempty interval is required: an empty one means `∀x̄. body` is itself
    // unsatisfiable, which we must not certify as `Sat`.
    if !interval_nonempty(&lo, &hi) {
        return false;
    }
    // VERIFY the ground `f`-points (the #260 gate): each must be eq-pinned to a
    // concrete rational that lies in `[lo, hi]`, else asserting the universal at
    // that argument would refute — an `unsat` we must never hide behind `Sat`.
    if let Some(points) = facts.ground_apps.get(&fsym) {
        for &k in points {
            let Some(v) = resolve_eq_rational(m, k, &facts.eq_pins, 16) else {
                return false; // value not faithfully known ⇒ conservative bail
            };
            if !in_interval(&v, &lo, &hi) {
                return false;
            }
        }
    }
    true
}

// ─────────────────── bounded-oscillation recognizer (§3.2) ──────────────────
//
// A Lipschitz-style bound `∀x,y∈G. |f(x)−f(y)| ≤ B` (encoded as the two-sided
// `f(x)−f(y) ≤ B ∧ f(y)−f(x) ≤ B`) over an uninterpreted `f`. The model is again
// the `else`-value `δ ≡ const`: between two non-pinned points the difference is
// `0 ≤ B`; between a non-pinned and a pinned point it is `|δ−vᵢ|`; between two
// pinned points it is `|vᵢ−vⱼ|`. Choosing `δ = min vᵢ` makes every gap `≤
// (max vᵢ − min vᵢ)`, so the axiom is `Sat` iff the pinned `f`-values lie in an
// interval of width `≤ B`. (Pinned points outside the guard are conservatively
// included — that can only make the recognizer DECLINE, never wrongly certify.)

/// `(f-symbol, var)` if `t` is `(f v)` for an uninterpreted `f` and a single
/// bound variable `v`.
fn fapp_of_var(m: &TermManager, t: TermId, want: &FxHashSet<Spur>) -> Option<(u64, Spur)> {
    let TermKind::Apply { func, args } = m.get(t)?.kind.clone() else {
        return None;
    };
    let fsym = spur_sym(func);
    if fsym & OP != 0 || args.len() != 1 {
        return None;
    }
    let TermKind::Var(s) = m.get(args[0])?.kind.clone() else {
        return None;
    };
    want.contains(&s).then_some((fsym, s))
}

/// Parse a difference-bound atom `(<= (- (f a) (f b)) B)` — `a`,`b` bound vars,
/// `f` one uninterpreted function, `B` a ground rational. Returns `(f, a, b, B)`.
fn diff_bound_atom(
    m: &TermManager,
    atom: TermId,
    want: &FxHashSet<Spur>,
) -> Option<(u64, Spur, Spur, num_rational::BigRational)> {
    let TermKind::Le(lhs, rhs) = m.get(atom)?.kind.clone() else {
        return None;
    };
    let b = ground_rational(m, rhs, want)?;
    let TermKind::Sub(p, q) = m.get(lhs)?.kind.clone() else {
        return None;
    };
    let (fp, ap) = fapp_of_var(m, p, want)?;
    let (fq, aq) = fapp_of_var(m, q, want)?;
    if fp != fq {
        return None;
    }
    Some((fp, ap, aq, b))
}

/// **M3 recognizer — bounded oscillation** (§3.2). Body
/// `∀x,y. [guard ⇒] (and (<= (- (f x)(f y)) B) (<= (- (f y)(f x)) B))`. Complete
/// `f` to the constant `δ = min pinned value`; the axiom holds iff the pinned
/// `f`-values lie in an interval of width `≤ B` (`max − min ≤ B`). Same soundness
/// gates as the range completion (single-quantifier + accounting); `B ≥ 0` is
/// required (the diagonal `x=y` forces `0 ≤ B`).
fn try_bounded_oscillation(
    m: &TermManager,
    facts: &CompletionFacts,
    body: TermId,
    bound: &[Spur],
) -> bool {
    if bound.len() != 2 {
        return false;
    }
    let want: FxHashSet<Spur> = bound.iter().copied().collect();
    // Peel an optional guard (`(=> guard matrix)`); out-of-guard pairs are vacuous.
    let matrix = match m.get(body).map(|t| t.kind.clone()) {
        Some(TermKind::Implies(_, c)) => c,
        Some(_) => body,
        None => return false,
    };
    // The matrix is the two-sided pair `(and (f(x)−f(y) ≤ B) (f(y)−f(x) ≤ B))`.
    let TermKind::And(conj) = (match m.get(matrix) {
        Some(t) => t.kind.clone(),
        None => return false,
    }) else {
        return false;
    };
    if conj.len() != 2 {
        return false;
    }
    let (Some((f1, a1, b1, bd1)), Some((f2, a2, b2, bd2))) = (
        diff_bound_atom(m, conj[0], &want),
        diff_bound_atom(m, conj[1], &want),
    ) else {
        return false;
    };
    // Same `f`, same bound, opposite arg order over two DISTINCT bound vars.
    if f1 != f2 || bd1 != bd2 || a1 != b2 || b1 != a2 || a1 == b1 {
        return false;
    }
    let fsym = f1;
    let bnd = bd1;
    // `B ≥ 0` — the diagonal `x=y` instance forces `0 ≤ B`, so a negative bound is
    // unsatisfiable (decline; the engine then refutes via instantiation).
    if bnd < num_rational::BigRational::from_integer(num_bigint::BigInt::from(0)) {
        return false;
    }
    // `f` must be this axiom's SOLE universal constraint.
    if facts.quant_count.get(&fsym).copied() != Some(1) {
        return false;
    }
    // ACCOUNTING GUARD (as in `try_range_completion`): every `f`-application must
    // be one of the body's `f(x)`/`f(y)` or a literal ground point we verify — a
    // symbolic `f(c)` could carry an oscillation-violating value we cannot see.
    let mut body_occ: FxHashMap<u64, u32> = FxHashMap::default();
    count_syms(m, body, &mut body_occ);
    let accounted = body_occ.get(&fsym).copied().unwrap_or(0)
        + facts.ground_apps.get(&fsym).map_or(0, |p| p.len() as u32);
    if facts.global_occ.get(&fsym).copied().unwrap_or(0) != accounted {
        return false;
    }
    // VERIFY: collect the pinned `f`-values; their spread must be `≤ B`. A ground
    // point not eq-pinned to a concrete rational ⇒ value unknown ⇒ decline.
    let Some(points) = facts.ground_apps.get(&fsym) else {
        return true; // no ground points ⇒ the constant model has oscillation 0 ≤ B
    };
    let mut lo: Option<num_rational::BigRational> = None;
    let mut hi: Option<num_rational::BigRational> = None;
    for &k in points {
        let Some(v) = resolve_eq_rational(m, k, &facts.eq_pins, 16) else {
            return false;
        };
        if lo.as_ref().is_none_or(|l| &v < l) {
            lo = Some(v.clone());
        }
        if hi.as_ref().is_none_or(|h| &v > h) {
            hi = Some(v);
        }
    }
    match (lo, hi) {
        (Some(l), Some(h)) => h - l <= bnd,
        _ => true,
    }
}

// ────────────────── variable-relative bound recognizer (§3.3) ───────────────
//
// A bound that compares `f` to the VARIABLE itself: `∀r[∈G]. f(r) ⋛ r` (e.g. the
// Archimedean `ceil(r) ≥ r`). A constant default cannot dominate an unbounded
// `r`, but for the NON-STRICT relations the IDENTITY default `f(r) := r` makes
// the body reflexively true (`r ≥ r` / `r ≤ r`) everywhere — so the guard is
// irrelevant and no constant is needed. The pinned points keep their values and
// are verified against the relation directly. (Strict `>`/`<` would need the
// guard's sup/inf as the default; deferred until a case needs it.)

/// **M3 recognizer — variable-relative bound** (§3.3). Body `∀r. [guard ⇒]
/// (f(r) rel r)` with `rel ∈ {≥, ≤}` and the non-`f` side exactly the bound
/// variable. The identity completion `f(r) := r` satisfies the body on every
/// non-pinned `r`; the pinned points `f(p)=v` are verified to satisfy `rel(v, p)`
/// (each `p` a literal, `v` eq-pinned). Same single-quantifier + accounting gates.
fn try_var_relative_bound(
    m: &TermManager,
    facts: &CompletionFacts,
    body: TermId,
    bound: &[Spur],
) -> bool {
    if bound.len() != 1 {
        return false;
    }
    let r = bound[0];
    let want: FxHashSet<Spur> = [r].into_iter().collect();
    let matrix = match m.get(body).map(|t| t.kind.clone()) {
        Some(TermKind::Implies(_, c)) => c,
        Some(_) => body,
        None => return false,
    };
    let (sym, l, rr) = match m.get(matrix).map(|t| t.kind.clone()) {
        Some(TermKind::Ge(a, b)) => (OP_GE, a, b),
        Some(TermKind::Le(a, b)) => (OP_LE, a, b),
        _ => return false,
    };
    // One side is `(f r)`, the other exactly the bound variable `r`. Normalize to
    // `f(r) rel r`.
    let (fsym, rel) = match (fapp_of_var(m, l, &want), fapp_of_var(m, rr, &want)) {
        (Some((f, _)), None) if is_var_term(m, rr, r) => (f, sym),
        (None, Some((f, _))) if is_var_term(m, l, r) => (f, flip_rel(sym)),
        _ => return false,
    };
    if !matches!(rel, OP_GE | OP_LE) {
        return false;
    }
    if facts.quant_count.get(&fsym).copied() != Some(1) {
        return false;
    }
    // ACCOUNTING GUARD (as in `try_range_completion`).
    let mut body_occ: FxHashMap<u64, u32> = FxHashMap::default();
    count_syms(m, body, &mut body_occ);
    let accounted = body_occ.get(&fsym).copied().unwrap_or(0)
        + facts.ground_apps.get(&fsym).map_or(0, |p| p.len() as u32);
    if facts.global_occ.get(&fsym).copied().unwrap_or(0) != accounted {
        return false;
    }
    // VERIFY each pinned point `f(p)=v` against `rel(v, p)` (`p` a literal, `v`
    // eq-pinned); the identity default covers every non-pinned `r`.
    if let Some(points) = facts.ground_apps.get(&fsym) {
        for &k in points {
            let TermKind::Apply { args, .. } = (match m.get(k) {
                Some(t) => t.kind.clone(),
                None => return false,
            }) else {
                return false;
            };
            if args.len() != 1 {
                return false;
            }
            let (Some(p), Some(v)) = (
                term_to_rational(m, args[0]),
                resolve_eq_rational(m, k, &facts.eq_pins, 16),
            ) else {
                return false;
            };
            let ok = match rel {
                OP_GE => v >= p,
                _ => v <= p, // OP_LE
            };
            if !ok {
                return false;
            }
        }
    }
    true
}

// ────────────────── commuting-functions recognizer (§3.4) ───────────────────
//
// A commutativity axiom `∀x[∈G]. f(g(x)) = g(f(x))` over two uninterpreted unary
// functions. The model is RELATIONAL: identify `g ≡ f` (one shared graph). Then
// `f(g(x)) = f(f(x))` and `g(f(x)) = f(f(x))`, equal by construction for EVERY
// `x` — guard-irrelevant. Sound when `f` and `g` agree on every shared pinned
// point (so the merge breaks no ground fact) and both are otherwise local (the
// single-quantifier + accounting gates, applied to BOTH functions).

/// `(outer, inner)` if `t` is `outer(inner(x))` for two uninterpreted unary
/// functions applied to the bound variable `x`.
fn compose_of_var(m: &TermManager, t: TermId, x: Spur) -> Option<(u64, u64)> {
    let TermKind::Apply { func: outer, args: oargs } = m.get(t)?.kind.clone() else {
        return None;
    };
    let osym = spur_sym(outer);
    if osym & OP != 0 || oargs.len() != 1 {
        return None;
    }
    let want: FxHashSet<Spur> = [x].into_iter().collect();
    let (isym, _) = fapp_of_var(m, oargs[0], &want)?;
    Some((osym, isym))
}

/// Build the `arg → value` rational map for a unary function's ground points,
/// or `None` if any point's argument is not a literal or its value is not
/// eq-pinned to a concrete (⇒ the merge cannot be confirmed ⇒ decline).
fn resolve_app_map(
    m: &TermManager,
    facts: &CompletionFacts,
    fsym: u64,
) -> Option<FxHashMap<num_rational::BigRational, num_rational::BigRational>> {
    let mut map = FxHashMap::default();
    if let Some(points) = facts.ground_apps.get(&fsym) {
        for &k in points {
            let TermKind::Apply { args, .. } = m.get(k)?.kind.clone() else {
                return None;
            };
            if args.len() != 1 {
                return None;
            }
            let arg = term_to_rational(m, args[0])?;
            let val = resolve_eq_rational(m, k, &facts.eq_pins, 16)?;
            map.insert(arg, val);
        }
    }
    Some(map)
}

/// **M3 recognizer — commuting functions** (§3.4). Body `∀x. [guard ⇒]
/// (= (f (g x)) (g (f x)))` for two DISTINCT uninterpreted unary `f`, `g`.
/// The `g ≡ f` collapse satisfies it structurally; sound when both functions are
/// single-quantifier + fully accounted and agree on every shared pinned point.
fn try_commuting_functions(
    m: &TermManager,
    facts: &CompletionFacts,
    body: TermId,
    bound: &[Spur],
) -> bool {
    if bound.len() != 1 {
        return false;
    }
    let x = bound[0];
    let matrix = match m.get(body).map(|t| t.kind.clone()) {
        Some(TermKind::Implies(_, c)) => c,
        Some(_) => body,
        None => return false,
    };
    let TermKind::Eq(s1, s2) = (match m.get(matrix) {
        Some(t) => t.kind.clone(),
        None => return false,
    }) else {
        return false;
    };
    let (Some((a_out, a_in)), Some((b_out, b_in))) =
        (compose_of_var(m, s1, x), compose_of_var(m, s2, x))
    else {
        return false;
    };
    // The two sides are `f∘g` and `g∘f` for two DISTINCT functions.
    if !(a_out == b_in && a_in == b_out && a_out != a_in) {
        return false;
    }
    let (f, g) = (a_out, a_in);
    // Both functions must be single-quantifier and fully accounted (body + literal
    // ground points) — so neither carries an unmodeled or symbolic constraint
    // that the `g ≡ f` merge could break.
    let mut occ: FxHashMap<u64, u32> = FxHashMap::default();
    count_syms(m, body, &mut occ);
    for sym in [f, g] {
        if facts.quant_count.get(&sym).copied() != Some(1) {
            return false;
        }
        let accounted = occ.get(&sym).copied().unwrap_or(0)
            + facts.ground_apps.get(&sym).map_or(0, |p| p.len() as u32);
        if facts.global_occ.get(&sym).copied().unwrap_or(0) != accounted {
            return false;
        }
    }
    // AGREEMENT: every point pinned in BOTH `f` and `g` must carry the same value,
    // else `g ≡ f` would contradict a ground fact.
    let (Some(fmap), Some(gmap)) = (resolve_app_map(m, facts, f), resolve_app_map(m, facts, g))
    else {
        return false;
    };
    for (arg, fv) in &fmap {
        if let Some(gv) = gmap.get(arg) {
            if fv != gv {
                return false;
            }
        }
    }
    true
}

// ─────────────────────────── array axiom recognizers ───────────────────────
//
// Two array axioms are VALID consequences of an asserted array equality, so a
// universal asserting one is automatically satisfied (sound `Sat`):
//   * extensionality premise `∀i. select(a,i)=select(b,i)` is entailed by
//     `a = b` (function congruence);
//   * read-over-write `∀i. i≠k ⇒ select(b,i)=select(a,i)` is entailed by
//     `b = store(a,k,v)` (the select-store axiom).

/// If `t` is `(select c (Var i))`, return the array `c`.
fn select_over_var(m: &TermManager, t: TermId, i: Spur) -> Option<TermId> {
    let TermKind::Select(arr, idx) = m.get(t)?.kind.clone() else {
        return None;
    };
    match m.get(idx)?.kind {
        TermKind::Var(s) if s == i => Some(arr),
        _ => None,
    }
}

#[inline]
fn is_var_term(m: &TermManager, t: TermId, v: Spur) -> bool {
    matches!(m.get(t).map(|x| &x.kind), Some(TermKind::Var(s)) if *s == v)
}

/// Is `c1 = c2` asserted at the top level (in either pin direction)?
fn terms_eq_pinned(facts: &CompletionFacts, c1: TermId, c2: TermId) -> bool {
    facts.eq_pins.get(&c1).is_some_and(|v| v.contains(&c2))
        || facts.eq_pins.get(&c2).is_some_and(|v| v.contains(&c1))
}

/// Is `b` asserted equal to `(store a k _)` for some value?
fn array_is_store_of(m: &TermManager, facts: &CompletionFacts, b: TermId, a: TermId, k: TermId) -> bool {
    facts.eq_pins.get(&b).is_some_and(|pins| {
        pins.iter().any(|&p| {
            matches!(m.get(p).map(|t| t.kind.clone()),
                Some(TermKind::Store(sa, sk, _)) if sa == a && sk == k)
        })
    })
}

/// `∀i. select(a,i) = select(b,i)` — valid when `a = b` is asserted (congruence).
fn try_array_extensionality(m: &TermManager, facts: &CompletionFacts, body: TermId, bound: &[Spur]) -> bool {
    if bound.len() != 1 {
        return false;
    }
    let i = bound[0];
    let TermKind::Eq(o1, o2) = (match m.get(body) {
        Some(t) => t.kind.clone(),
        None => return false,
    }) else {
        return false;
    };
    match (select_over_var(m, o1, i), select_over_var(m, o2, i)) {
        (Some(c1), Some(c2)) => terms_eq_pinned(facts, c1, c2),
        _ => false,
    }
}

/// `∀i. i≠k ⇒ select(b,i) = select(a,i)` — valid when `b = store(a,k,v)`.
fn try_array_store(m: &TermManager, facts: &CompletionFacts, body: TermId, bound: &[Spur]) -> bool {
    if bound.len() != 1 {
        return false;
    }
    let i = bound[0];
    let TermKind::Implies(guard, conseq) = (match m.get(body) {
        Some(t) => t.kind.clone(),
        None => return false,
    }) else {
        return false;
    };
    // guard = (not (= i k)) → extract k.
    let TermKind::Not(eq) = (match m.get(guard) {
        Some(t) => t.kind.clone(),
        None => return false,
    }) else {
        return false;
    };
    let TermKind::Eq(g1, g2) = (match m.get(eq) {
        Some(t) => t.kind.clone(),
        None => return false,
    }) else {
        return false;
    };
    let k = if is_var_term(m, g1, i) {
        g2
    } else if is_var_term(m, g2, i) {
        g1
    } else {
        return false;
    };
    // conseq = (= (select b i) (select a i)).
    let TermKind::Eq(c1, c2) = (match m.get(conseq) {
        Some(t) => t.kind.clone(),
        None => return false,
    }) else {
        return false;
    };
    let (Some(arr1), Some(arr2)) = (select_over_var(m, c1, i), select_over_var(m, c2, i)) else {
        return false;
    };
    // Either array may be the store of the other (read-over-write either order).
    array_is_store_of(m, facts, arr1, arr2, k) || array_is_store_of(m, facts, arr2, arr1, k)
}

/// Walk the boolean skeleton of `t` recording each uninterpreted PREDICATE
/// symbol's polarity (`pos`/`neg`); a symbol reached in a non-monotone context
/// (Eq/Xor/Ite/Distinct/arith comparison) or in term (argument) position is
/// marked `mixed` and is therefore never set by the pure-polarity recognizer.
fn walk_polarity(m: &TermManager, t: TermId, pos: bool, f: &mut CompletionFacts) {
    let Some(term) = m.get(t) else { return };
    match &term.kind {
        TermKind::Not(a) => walk_polarity(m, *a, !pos, f),
        TermKind::And(args) | TermKind::Or(args) => {
            for &c in args.iter() {
                walk_polarity(m, c, pos, f);
            }
        }
        TermKind::Implies(a, b) => {
            walk_polarity(m, *a, !pos, f);
            walk_polarity(m, *b, pos, f);
        }
        TermKind::Forall { body, .. } | TermKind::Exists { body, .. } => {
            walk_polarity(m, *body, pos, f);
        }
        TermKind::Apply { func, args } => {
            // A predicate atom in the boolean skeleton: its head takes the
            // current polarity; its arguments are TERMS (data, not settable).
            let s = spur_sym(*func);
            if pos {
                f.occurs_pos.insert(s);
            } else {
                f.occurs_neg.insert(s);
            }
            for &c in args.iter() {
                mark_mixed(m, c, f);
            }
        }
        // Non-monotone boolean atoms / arithmetic comparisons: every
        // uninterpreted symbol inside is in a non-monotone or term position.
        TermKind::Eq(..)
        | TermKind::Distinct(..)
        | TermKind::Xor(..)
        | TermKind::Ite(..)
        | TermKind::Lt(..)
        | TermKind::Le(..)
        | TermKind::Gt(..)
        | TermKind::Ge(..) => mark_mixed(m, t, f),
        // Leaves (True/False/Var/literals) carry no uninterpreted symbol.
        _ => mark_mixed(m, t, f),
    }
}

impl<'a> ModelEval<OxizHost<'a>> for SolverModel {
    fn eval_bool(&self, lang: &OxizHost<'a>, t: TermId) -> Option<bool> {
        // Direct true/false constant or assignment.
        if t == self.true_id {
            return Some(true);
        }
        if t == self.false_id {
            return Some(false);
        }
        if let Some(&v) = self.assign.get(&t) {
            if v == self.true_id {
                return Some(true);
            }
            if v == self.false_id {
                return Some(false);
            }
        }
        // Structural fallback over the connectives (conservative: `None` when
        // any operand is undetermined).
        match lang.view(t) {
            TermView::App { sym } => {
                let args = lang.children(t);
                match sym {
                    OP_NOT => self.eval_bool(lang, args[0]).map(|b| !b),
                    OP_AND => {
                        let mut all_true = true;
                        for &a in &args {
                            match self.eval_bool(lang, a) {
                                Some(false) => return Some(false),
                                Some(true) => {}
                                None => all_true = false,
                            }
                        }
                        all_true.then_some(true).or(None)
                    }
                    OP_OR => {
                        let mut all_false = true;
                        for &a in &args {
                            match self.eval_bool(lang, a) {
                                Some(true) => return Some(true),
                                Some(false) => {}
                                None => all_false = false,
                            }
                        }
                        all_false.then_some(false).or(None)
                    }
                    OP_IMPLIES => {
                        let a = self.eval_bool(lang, args[0]);
                        let b = self.eval_bool(lang, args[1]);
                        match (a, b) {
                            (Some(false), _) | (_, Some(true)) => Some(true),
                            (Some(true), Some(false)) => Some(false),
                            _ => None,
                        }
                    }
                    OP_EQ => {
                        let (va, vb) = (self.value(args[0]), self.value(args[1]));
                        if va == vb {
                            Some(true)
                        } else if let (Some(x), Some(y)) =
                            (self.int_of(lang, args[0]), self.int_of(lang, args[1]))
                        {
                            // Both sides resolve to concrete integers ⇒ decide.
                            Some(x == y)
                        } else {
                            None // distinct (non-numeric) values may still be model-equal; stay safe
                        }
                    }
                    // Arithmetic comparisons: fold when BOTH operands resolve to
                    // concrete integers under the model (the M3 oracle, #260).
                    // Undetermined otherwise — never a guess.
                    OP_LT | OP_LE | OP_GT | OP_GE => {
                        match (self.int_of(lang, args[0]), self.int_of(lang, args[1])) {
                            (Some(x), Some(y)) => Some(match sym {
                                OP_LT => x < y,
                                OP_LE => x <= y,
                                OP_GT => x > y,
                                _ => x >= y, // OP_GE
                            }),
                            _ => None,
                        }
                    }
                    // An uninterpreted boolean atom not in the assignment, or
                    // any operator we do not fold: undetermined.
                    _ => None,
                }
            }
            _ => None,
        }
    }

    fn is_active(&self, _lang: &OxizHost<'a>, quant: TermId) -> bool {
        // Active unless the quantifier's literal is explicitly false in the
        // model (then its guard is off → skip). Unassigned ⇒ active
        // (conservative: never skip something that might constrain).
        self.assign.get(&quant) != Some(&self.false_id)
    }

    /// **M3 model-based verification (tautology fragment).** Returns `Some(true)`
    /// only when the quantifier *body* is a logical TAUTOLOGY — valid in every
    /// interpretation, for every value of the bound variables — recognised
    /// purely structurally (see [`SolverModel::body_is_valid`]). It never
    /// consults the model's sampled function values, so it cannot mistake
    /// "agrees on the sampled points" for "holds universally": a body like
    /// `∀x. f(x)=g(x)` that merely happens to hold on the current model's
    /// witnesses stays `None`. That firewall is what keeps `Some(true)` sound —
    /// the engine turns it straight into a `Saturated`/`Sat` verdict.
    ///
    /// `None` otherwise (the engine reports the quantifier unverified →
    /// `Unknown`, never a guess). This recovers the completeness lost by the
    /// conservative `clean_mbqi` default on the trivially-valid cases (e.g.
    /// `∀x. f(x)=f(x)`, a reflexive-equality axiom) without admitting any
    /// model-sample-based (unsound) `sat`.
    fn eval_forall(&self, lang: &OxizHost<'a>, quant: TermId) -> Option<bool> {
        let TermView::Quant { body, vars, .. } = lang.view(quant) else {
            return None;
        };
        // (1) Structural tautology — valid in every interpretation. Monotone
        // under universal closure: if `body` is valid for all valuations then so
        // is `∀x̄. body`. Model-independent, always sound.
        if self.body_is_valid(lang, body, 64) {
            return Some(true);
        }
        // (2..4) M3 model-completion recognizers. Each builds (a fragment of) a
        // model that satisfies the axiom, GUARDED by global facts about the
        // whole formula so the per-quantifier `Some(true)`s compose into one
        // consistent model. Disabled (→ sound `None`) when facts are absent.
        let Some(facts) = &self.facts else {
            return None;
        };
        let bound: Vec<Spur> = vars.iter().map(|(n, _)| *n).collect();
        // (2) Definitional axiom `∀x̄. (= (f x̄) rhs)`, `f` fresh ⇒ conservative
        // extension (define `f := λx̄. rhs`), always satisfiable.
        if facts.definitional_quants.contains(&quant) {
            return Some(true);
        }
        // (3) Pure-polarity predicate: a single-literal body whose uninterpreted
        // predicate occurs ONLY positively (resp. negatively) everywhere ⇒ set
        // it ≡ true (resp. false). Composes: a pure-positive symbol is never
        // needed false by any axiom.
        if let Some(b) = self.try_pure_predicate(lang, body, facts) {
            return Some(b);
        }
        // (4) Single-function range completion: the bound vars feed ONLY one
        // uninterpreted function `f` (constrained by no other quantifier), the
        // other operand is ground, and the atom is satisfiable for some value of
        // `f`'s result ⇒ complete `f` to that constant off the (already
        // consistent) ground points.
        if self.try_function_completion(lang, body, &bound, facts) {
            return Some(true);
        }
        // (4b) Constant RANGE completion (dense Real/Int): a conjunction of
        // comparison atoms bounding one uninterpreted `f` against ground
        // constants `∀x̄. ⋀ cmp(f(x̄), cᵢ)` — complete `f` to a constant in the
        // intersected interval (e.g. `∀x. 0 ≤ f(x) ≤ 1`).
        if try_range_completion(lang.m(), facts, body, &bound) {
            return Some(true);
        }
        // (4c) Bounded oscillation (§3.2): a Lipschitz-style `∀x,y∈G. |f(x)−f(y)|
        // ≤ B` — complete `f` to a constant when the pinned values span ≤ B.
        if try_bounded_oscillation(lang.m(), facts, body, &bound) {
            return Some(true);
        }
        // (4d) Variable-relative bound (§3.3): `∀r. f(r) ⋛ r` (e.g. `ceil(r)≥r`)
        // — the identity completion `f(r):=r` makes the body reflexively true.
        if try_var_relative_bound(lang.m(), facts, body, &bound) {
            return Some(true);
        }
        // (4e) Commuting functions (§3.4): `∀x. f(g(x))=g(f(x))` — the `g≡f`
        // collapse satisfies it structurally when the two functions agree.
        if try_commuting_functions(lang.m(), facts, body, &bound) {
            return Some(true);
        }
        // (5) Bare monotonicity axiom over an uninterpreted `f`: satisfiable when
        // the ground `f`-points admit a monotone extension (order-extension
        // theorem). Sound — declines unless every `f`-constraint is accounted for.
        if try_monotone_extension(lang.m(), facts, body) {
            return Some(true);
        }
        // (6) Idempotent axiom `∀x. f(f(x)) = f(x)`: satisfiable when the ground
        // f-points are idempotency-consistent (each `f(t)=v` needs `f(v)=v`).
        if try_idempotent(lang.m(), facts, body, &bound) {
            return Some(true);
        }
        // (7) Array axioms that are VALID consequences of an asserted array
        // equality: extensionality premise (`a=b`) and read-over-write
        // (`b=store(a,k,v)`).
        if try_array_extensionality(lang.m(), facts, body, &bound)
            || try_array_store(lang.m(), facts, body, &bound)
        {
            return Some(true);
        }
        // (8) Fresh-Skolem equality witness: a skolemized `∀x̄.∃ȳ. L = f(ȳ)`
        // (body `∀x̄. L = f(…sk(x̄)…)`), satisfiable by a free choice of the
        // Skolem witness when `f` is single-quantifier and `L` is `f`-free.
        if try_skolem_witness_eq(lang.m(), facts, body, &bound) {
            return Some(true);
        }
        None
    }
}

impl SolverModel {
    /// Read-only, model-INDEPENDENT structural tautology check: is `t` true in
    /// every interpretation, for every value of any free (bound) variable it
    /// contains?  Every arm below is a logical validity, so a `true` result is
    /// sound to hand to [`SolverModel::eval_forall`] (and thence to a `Sat`
    /// verdict).  Anything not provably valid this way returns `false`
    /// (conservative — the caller then yields the sound `Unknown`).
    ///
    /// `depth` bounds the DAG recursion so a deeply-nested body cannot blow the
    /// stack; running out of budget returns `false` (sound under-approximation).
    fn body_is_valid(&self, lang: &OxizHost<'_>, t: TermId, depth: u32) -> bool {
        if depth == 0 {
            return false;
        }
        if t == self.true_id {
            return true;
        }
        match lang.view(t) {
            TermView::App { sym } => {
                let args = lang.children(t);
                match sym {
                    // Reflexivity: `a = a`, `a ≤ a`, `a ≥ a` hold for all `a`
                    // (NOT `<`/`>`, which are irreflexive).
                    OP_EQ | OP_LE | OP_GE if args.len() == 2 && args[0] == args[1] => true,
                    // `¬φ` is valid iff `φ` is a contradiction.
                    OP_NOT if args.len() == 1 => self.body_is_unsat(lang, args[0], depth - 1),
                    // `∧` of valid conjuncts is valid.
                    OP_AND => args.iter().all(|&a| self.body_is_valid(lang, a, depth - 1)),
                    // `∨` is valid if any disjunct is valid.
                    OP_OR => args.iter().any(|&a| self.body_is_valid(lang, a, depth - 1)),
                    // `a ⇒ b` is valid if `b` is valid or `a` is a contradiction
                    // (covers `p ⇒ p` via `args[0] == args[1]` too) — or if it is
                    // the CONGRUENCE axiom `(⋀ aᵢ=bᵢ) ⇒ f(ā)=f(b̄)` (valid for any
                    // function `f`; UF's congruence closure makes the explicit
                    // axiom redundant, so recognising it avoids instantiating it —
                    // an unbounded `∀x,y.(=x y)⇒(=(f x)(f y))` otherwise spirals
                    // into an `f`-tower matching loop that OOMs the EUF solver).
                    OP_IMPLIES if args.len() == 2 => {
                        args[0] == args[1]
                            || self.body_is_valid(lang, args[1], depth - 1)
                            || self.body_is_unsat(lang, args[0], depth - 1)
                            || self.is_congruence_axiom(lang, args[0], args[1])
                            || self.is_order_transitivity(lang, args[0], args[1])
                            || is_monotone_implication(lang.m(), args[0], args[1])
                    }
                    // `ite(c, t, e)` is valid when both branches are valid.
                    OP_ITE if args.len() == 3 => {
                        self.body_is_valid(lang, args[1], depth - 1)
                            && self.body_is_valid(lang, args[2], depth - 1)
                    }
                    _ => false,
                }
            }
            _ => false,
        }
    }

    /// Recognise the CONGRUENCE axiom `(⋀ᵢ aᵢ = bᵢ) ⇒ (= (f a₁…aₙ) (f b₁…bₙ))`
    /// for an uninterpreted function `f`. This is VALID in every interpretation
    /// (a function maps equal inputs to equal outputs), so handing it back as a
    /// tautology is sound — and it is exactly redundant with the EUF solver's
    /// built-in congruence closure, so recognising it lets the engine SKIP
    /// instantiating it (the unbounded `∀x,y.(=x y)⇒(=(f x)(f y))` otherwise
    /// enumerates `f`-of-`f` towers without bound).
    fn is_congruence_axiom(&self, lang: &OxizHost<'_>, guard: TermId, conseq: TermId) -> bool {
        // conseq must be `(= (f ā) (f b̄))` with `f` the SAME uninterpreted function.
        let TermView::App { sym: ceq } = lang.view(conseq) else {
            return false;
        };
        if ceq != OP_EQ {
            return false;
        }
        let cargs = lang.children(conseq);
        if cargs.len() != 2 {
            return false;
        }
        let (TermView::App { sym: f1 }, TermView::App { sym: f2 }) =
            (lang.view(cargs[0]), lang.view(cargs[1]))
        else {
            return false;
        };
        if f1 != f2 || f1 & OP != 0 {
            return false; // different heads, or a builtin op (not an uninterpreted `f`)
        }
        let fa = lang.children(cargs[0]);
        let fb = lang.children(cargs[1]);
        if fa.is_empty() || fa.len() != fb.len() {
            return false;
        }
        // The guard must assert `aᵢ = bᵢ` for EVERY argument position (or `aᵢ`
        // is syntactically `bᵢ`). Collect the equalities the guard provides.
        let mut pairs: Vec<(TermId, TermId)> = Vec::new();
        Self::collect_eq_pairs(lang, guard, &mut pairs, 32);
        fa.iter().zip(fb.iter()).all(|(&a, &b)| {
            a == b || pairs.iter().any(|&(p, q)| (p == a && q == b) || (p == b && q == a))
        })
    }

    /// Collect the `(lhs, rhs)` of every equality atom reachable through a
    /// conjunction (`(= a b)` or `(and (= a₁ b₁) …)`), for the congruence check.
    fn collect_eq_pairs(
        lang: &OxizHost<'_>,
        t: TermId,
        out: &mut Vec<(TermId, TermId)>,
        depth: u32,
    ) {
        if depth == 0 {
            return;
        }
        match lang.view(t) {
            TermView::App { sym: OP_EQ } => {
                let a = lang.children(t);
                if a.len() == 2 {
                    out.push((a[0], a[1]));
                }
            }
            TermView::App { sym: OP_AND } => {
                for c in lang.children(t) {
                    Self::collect_eq_pairs(lang, c, out, depth - 1);
                }
            }
            _ => {}
        }
    }

    /// Recognise TRANSITIVITY of `≤`: `(A ≤ B ∧ B ≤ C) ⇒ A ≤ C`. `≤` is a
    /// transitive relation in every interpretation, so the implication is VALID
    /// (e.g. the `trans_simple` axiom `(f(x)≤f(y) ∧ f(y)≤f(z)) ⇒ f(x)≤f(z)`).
    /// Recognising it lets the engine skip instantiating the (unbounded,
    /// trigger-free) transitivity axiom.
    fn is_order_transitivity(&self, lang: &OxizHost<'_>, guard: TermId, conseq: TermId) -> bool {
        // conseq must be `(<= A C)`.
        let TermView::App { sym: OP_LE } = lang.view(conseq) else {
            return false;
        };
        let cc = lang.children(conseq);
        if cc.len() != 2 {
            return false;
        }
        let (a, c) = (cc[0], cc[1]);
        // The guard must give `(<= A B)` and `(<= B C)` for some intermediate `B`.
        let mut le: Vec<(TermId, TermId)> = Vec::new();
        Self::collect_le_pairs(lang, guard, &mut le, 32);
        le.iter()
            .any(|&(p, q)| p == a && le.iter().any(|&(r, s)| r == q && s == c))
    }

    /// Collect the `(lhs, rhs)` of every `(<= a b)` atom reachable through a
    /// conjunction, for the transitivity check.
    fn collect_le_pairs(
        lang: &OxizHost<'_>,
        t: TermId,
        out: &mut Vec<(TermId, TermId)>,
        depth: u32,
    ) {
        if depth == 0 {
            return;
        }
        match lang.view(t) {
            TermView::App { sym: OP_LE } => {
                let a = lang.children(t);
                if a.len() == 2 {
                    out.push((a[0], a[1]));
                }
            }
            TermView::App { sym: OP_AND } => {
                for c in lang.children(t) {
                    Self::collect_le_pairs(lang, c, out, depth - 1);
                }
            }
            _ => {}
        }
    }

    /// Dual of [`Self::body_is_valid`]: is `t` false in every interpretation?
    /// Used only to discharge `¬φ` / `a ⇒ φ`. Conservative `false` when unsure.
    fn body_is_unsat(&self, lang: &OxizHost<'_>, t: TermId, depth: u32) -> bool {
        if depth == 0 {
            return false;
        }
        if t == self.false_id {
            return true;
        }
        match lang.view(t) {
            TermView::App { sym } => {
                let args = lang.children(t);
                match sym {
                    // `a < a`, `a > a`, `distinct(a, a)` are unsatisfiable.
                    OP_LT | OP_GT | OP_DISTINCT if args.len() == 2 && args[0] == args[1] => true,
                    // `¬φ` is a contradiction iff `φ` is valid.
                    OP_NOT if args.len() == 1 => self.body_is_valid(lang, args[0], depth - 1),
                    // `∧` is unsat if any conjunct is unsat.
                    OP_AND => args.iter().any(|&a| self.body_is_unsat(lang, a, depth - 1)),
                    // `∨` is unsat only if every disjunct is unsat.
                    OP_OR => args.iter().all(|&a| self.body_is_unsat(lang, a, depth - 1)),
                    _ => false,
                }
            }
            _ => false,
        }
    }

    /// **M3 recognizer — pure-polarity predicate.** A single-literal body that
    /// is an uninterpreted predicate atom `(P …)` whose symbol occurs ONLY
    /// positively across the whole (non-definitional) formula ⇒ the model with
    /// `P ≡ true` satisfies every occurrence, so `∀x̄.(P …)` holds. Symmetric for
    /// `(not (P …))` with `P` purely negative ⇒ `P ≡ false`. Compositional: a
    /// purely-positive symbol is never required false by any axiom, so setting
    /// it true cannot break another quantifier's `Some(true)`.
    fn try_pure_predicate(
        &self,
        lang: &OxizHost<'_>,
        body: TermId,
        facts: &CompletionFacts,
    ) -> Option<bool> {
        let TermView::App { sym } = lang.view(body) else {
            return None;
        };
        if sym & OP == 0 {
            // Bare uninterpreted predicate atom (the quantifier body is Bool, so
            // `P` is a predicate). Pure-positive ⇒ set `P ≡ true`.
            return facts.is_pure_pos(sym).then_some(true);
        }
        if sym == OP_NOT {
            let args = lang.children(body);
            if let Some(&inner) = args.first() {
                if let TermView::App { sym: isym } = lang.view(inner) {
                    if isym & OP == 0 && facts.is_pure_neg(isym) {
                        return Some(true);
                    }
                }
            }
        }
        None
    }

    /// **M3 recognizer — single-function range completion.** A comparison atom
    /// `(cmp (f x̄) g)` (or `(cmp g (f x̄))`) where `g` is ground, `f` is
    /// uninterpreted, the bound vars feed ONLY that one application, and `f` is
    /// constrained by NO other quantifier. The atom is satisfiable for some
    /// value of `(f x̄)` (the operands are distinct terms), so `f` can be
    /// completed to a constant meeting it on every non-ground argument — the
    /// ground arguments are already consistent (the engine reached saturation
    /// with no conflict). Hence `∀x̄. body` holds.
    fn try_function_completion(
        &self,
        lang: &OxizHost<'_>,
        body: TermId,
        bound: &[Spur],
        facts: &CompletionFacts,
    ) -> bool {
        if bound.is_empty() {
            return false;
        }
        let TermView::App { sym } = lang.view(body) else {
            return false;
        };
        if !matches!(sym, OP_LT | OP_LE | OP_GT | OP_GE | OP_EQ) {
            return false;
        }
        let args = lang.children(body);
        if args.len() != 2 {
            return false;
        }
        let (l, r) = (args[0], args[1]);
        // Exactly one operand mentions the bound vars; the other must be ground.
        let app_side = match (
            self.has_bound(lang, l, bound, 256),
            self.has_bound(lang, r, bound, 256),
        ) {
            (true, false) => l,
            (false, true) => r,
            _ => return false,
        };
        // The bound side must be a single application of one uninterpreted
        // function (so a constant completion of `f` makes its value uniform).
        let TermView::App { sym: fsym } = lang.view(app_side) else {
            return false;
        };
        if fsym & OP != 0 {
            return false; // a builtin op, not an uninterpreted function
        }
        // `f` must be this axiom's SOLE universal constraint (no cross-quantifier
        // requirement that a single constant completion could violate).
        if facts.quant_count.get(&fsym).copied() != Some(1) {
            return false;
        }
        // ACCOUNTING GUARD (the symbolic-point companion to the #260 ground gate
        // below). The `ground_apps` verify covers only LITERAL ground points; a
        // `f`-application at a SYMBOLIC argument — `f(c)` for a free constant `c`
        // (`∀x.f(x)≤1` with `f(c)>1`) — has a variable argument, so it is NOT
        // recorded as a ground point and its constraint would be missed, letting
        // the constant completion violate it. The body's single `f(x̄)` plus the
        // literal ground points must exhaust every `f`-occurrence; any shortfall
        // is an unaccounted symbolic application ⇒ decline to the sound `Unknown`.
        let mut body_occ: FxHashMap<u64, u32> = FxHashMap::default();
        count_syms(lang.m(), body, &mut body_occ);
        let accounted = body_occ.get(&fsym).copied().unwrap_or(0)
            + facts.ground_apps.get(&fsym).map_or(0, |p| p.len() as u32);
        if facts.global_occ.get(&fsym).copied().unwrap_or(0) != accounted {
            return false;
        }
        // VERIFY (the #260 soundness gate). The constant completion is valid only
        // if every GROUND `f`-application the FORMULA constrains already
        // satisfies the comparison — otherwise asserting that instance would
        // refute (an `unsat` we must never hide behind a `Some(true)`). Scan the
        // formula's ground `f`-points (`facts.ground_apps`, NOT the model's
        // `assign` map): an inequality-only constraint such as `(< (f 5) 0)`
        // pins no concrete value into `assign`, yet still forbids completing
        // `f(5)` to a constant ≥ 0 — scanning `assign` alone silently dropped it
        // (the #260 spurious-`sat`). Arith-fold `cmp(·, g)` on each; bail (do not
        // certify) on any FALSE or any value we cannot resolve to a concrete
        // integer (a constrained point we cannot evaluate ⇒ conservative). The
        // yet-to-be-generated `f`-tower terms never appear ground in the formula,
        // so they impose no obligation — exactly why completing `f` to a constant
        // is sound. This is independent of CDQI's tuple budget, so it cannot miss
        // a pinned conflict.
        let g = if app_side == l { r } else { l };
        let app_is_left = app_side == l;
        let Some(gv) = resolve_eq_concrete(lang.m(), g, &facts.eq_pins, 16) else {
            return false; // ground operand not a concrete (eq-pinned) integer ⇒ cannot verify
        };
        let Some(points) = facts.ground_apps.get(&fsym) else {
            return true; // no ground `f`-point constrains `f` ⇒ free to complete
        };
        // Each ground `f`-point must be EQUALITY-pinned, at top level, to a
        // concrete value that satisfies the comparison. We deliberately do NOT
        // read the point's own model value: an inequality-constrained UF
        // application (e.g. `(< (f 5) 0)`) is poisoned to a DEFAULT (0) in the
        // model's `assign` — its EUF representative carries no arithmetic value —
        // so trusting it certified `0 ≥ 0` and hid the refuting instance (the
        // #260 spurious-`sat`). A top-level equation `(= (f t̄) k)` is the only
        // value the model reflects faithfully; anything else (an inequality, an
        // unconstrained point, a pin we cannot resolve to a concrete) is bailed
        // conservatively — the engine then enumerates and the theory refutes
        // (or, for the rare consistent-inequality case, reports the sound
        // `Unknown`).
        for &k in points {
            let Some(av) = resolve_eq_concrete(lang.m(), k, &facts.eq_pins, 16) else {
                return false; // not equality-pinned to a concrete ⇒ value not faithfully known
            };
            let (lo, hi) = if app_is_left { (av, gv.clone()) } else { (gv.clone(), av) };
            let holds = match sym {
                OP_LT => lo < hi,
                OP_LE => lo <= hi,
                OP_GT => lo > hi,
                OP_GE => lo >= hi,
                _ => lo == hi, // OP_EQ
            };
            if !holds {
                return false;
            }
        }
        true
    }

    /// Does `t` mention any of the `bound` variable names? Depth-bounded;
    /// running out returns `true` (conservative — never under-reports a bound
    /// variable, which would unsoundly classify a side as "ground").
    fn has_bound(&self, lang: &OxizHost<'_>, t: TermId, bound: &[Spur], depth: u32) -> bool {
        if depth == 0 {
            return true;
        }
        match lang.view(t) {
            TermView::Var { name } => bound.contains(&name),
            TermView::App { .. } => lang
                .children(t)
                .iter()
                .any(|&c| self.has_bound(lang, c, bound, depth - 1)),
            TermView::Quant { body, .. } => self.has_bound(lang, body, bound, depth - 1),
            TermView::Opaque => false,
        }
    }
}
