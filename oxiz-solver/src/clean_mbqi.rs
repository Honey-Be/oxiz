//! OxiZ host for the clean-room quantifier engine (`oxiz-mbqi`).
//!
//! Implements `oxiz_mbqi::TermLang` for OxiZ terms via a local newtype
//! `OxizHost` (the orphan rule forbids impl'ing the foreign trait on the
//! foreign `TermManager` directly). This is the M4 port surface: the engine,
//! developed and z3-cross-checked standalone, drives OxiZ terms with no
//! engine change.
//!
//! Soundness note: `substitute` delegates to `TermManager::substitute` (always
//! correct for every `TermKind`), so the instance bodies are exact. Only the
//! `view`/`children` structural mapping is allowed to be partial — an
//! unmapped `TermKind` becomes `Opaque` (a leaf atom), which can only cost
//! COMPLETENESS (a ground subterm not indexed ⇒ a missed candidate ⇒ a missed
//! instantiation), never soundness (no spurious instance, no spurious unsat).

use oxiz_core::ast::{TermId, TermKind, TermManager};
use oxiz_core::interner::Spur;
use oxiz_core::sort::SortId;
use oxiz_mbqi::{Binding, ModelEval, TermLang, TermView};
use rustc_hash::FxHashMap;

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

/// A short-lived wrapper around the persistent `TermManager`, created per
/// engine round. Holds `&mut` so the engine can intern instance terms.
pub struct OxizHost<'a> {
    tm: &'a mut TermManager,
}

impl<'a> OxizHost<'a> {
    pub fn new(tm: &'a mut TermManager) -> Self {
        OxizHost { tm }
    }
    #[inline]
    fn m(&self) -> &TermManager {
        &*self.tm
    }
}

impl<'a> TermLang for OxizHost<'a> {
    type Term = TermId;
    type Sort = SortId;
    type VarName = Spur;
    type Sym = u64;

    fn view(&self, t: TermId) -> TermView<'_, Self> {
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

    fn substitute(&mut self, body: TermId, binding: &Binding<Self>) -> TermId {
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
}

impl SolverModel {
    pub fn new(assign: FxHashMap<TermId, TermId>, true_id: TermId, false_id: TermId) -> Self {
        SolverModel {
            assign,
            true_id,
            false_id,
        }
    }

    /// The model value of `t` (the assignment, else `t` itself if it is its
    /// own value — a constant).
    #[inline]
    fn value(&self, t: TermId) -> TermId {
        self.assign.get(&t).copied().unwrap_or(t)
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
                        } else {
                            None // distinct values may still be model-equal; stay safe
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

    // eval_forall: v1 leaves trigger-free quantifiers unverified (`None` ⇒ the
    // engine reports `Inconclusive` ⇒ host `Unknown`). Sound (matches native
    // lu-smt / z3-times-out); a model-completion verifier that returns
    // `Some(true)` for satisfiable definitional axioms (to reach `Sat`) is a
    // follow-up. The default `None` is inherited.
}
