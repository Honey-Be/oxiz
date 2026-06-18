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
}

impl<'a> OxizHost<'a> {
    /// Wrap a mutable borrow of the term manager for one engine round.
    pub fn new(tm: &'a mut TermManager) -> Self {
        OxizHost { tm }
    }
    #[inline]
    fn m(&self) -> &TermManager {
        &*self.tm
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

    fn bounded_var_domains(&mut self, quant: TermId) -> Vec<Option<Vec<TermId>>> {
        // Bound variables + matrix of the (universal) quantifier.
        let (bound, body) = match self.m().get(quant).map(|t| &t.kind) {
            Some(TermKind::Forall { vars, body, .. }) => {
                (vars.iter().map(|(n, _)| *n).collect::<Vec<Spur>>(), *body)
            }
            _ => return Vec::new(),
        };
        // Only the guarded shape `(=> guard φ)` carries a concrete range.
        let guard = match self.m().get(body).map(|t| &t.kind) {
            Some(TermKind::Implies(g, _)) => *g,
            _ => return Vec::new(),
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
fn definitional_head(m: &TermManager, a: TermId) -> Option<u64> {
    let TermKind::Forall { vars, body, .. } = &m.get(a)?.kind else {
        return None;
    };
    let TermKind::Eq(lhs, rhs) = &m.get(*body)?.kind else {
        return None;
    };
    let (lhs, rhs) = (*lhs, *rhs);
    let TermKind::Apply { func, args } = &m.get(lhs)?.kind else {
        return None;
    };
    if args.len() != vars.len() {
        return None;
    }
    let bound: Vec<Spur> = vars.iter().map(|(n, _)| *n).collect();
    let mut seen: FxHashSet<Spur> = FxHashSet::default();
    for &arg in args.iter() {
        let TermKind::Var(s) = &m.get(arg)?.kind else {
            return None;
        };
        if !bound.contains(s) || !seen.insert(*s) {
            return None;
        }
    }
    // `f` must not occur in the rhs (else the equation constrains `f`).
    let fsym = spur_sym(*func);
    let mut rhs_occ: FxHashMap<u64, u32> = FxHashMap::default();
    count_syms(m, rhs, &mut rhs_occ);
    if rhs_occ.contains_key(&fsym) {
        return None;
    }
    Some(fsym)
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
                    // (covers `p ⇒ p` via `args[0] == args[1]` too).
                    OP_IMPLIES if args.len() == 2 => {
                        args[0] == args[1]
                            || self.body_is_valid(lang, args[1], depth - 1)
                            || self.body_is_unsat(lang, args[0], depth - 1)
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
