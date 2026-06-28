//! Term query, analysis, substitution and simplification for TermManager

use super::super::term::{MatchCase, TermId, TermKind};
use super::super::traversal::{get_children, transform_children};
use crate::interner::Spur;
use crate::sort::SortId;
#[allow(unused_imports)]
use crate::prelude::*;
use num_bigint::BigInt;
use smallvec::SmallVec;

use super::TermManager;

impl TermManager {
    // ===== Term Analysis =====

    /// Compute the size (number of nodes) of a term
    #[must_use]
    pub fn term_size(&self, id: TermId) -> usize {
        self.term_size_cached(id, &mut FxHashMap::default())
    }

    /// Compute the size with memoization
    fn term_size_cached(&self, id: TermId, cache: &mut FxHashMap<TermId, usize>) -> usize {
        if let Some(&size) = cache.get(&id) {
            return size;
        }

        let size = match self.get(id).map(|t| &t.kind) {
            None => 1,
            Some(
                TermKind::True
                | TermKind::False
                | TermKind::IntConst(_)
                | TermKind::RealConst(_)
                | TermKind::BitVecConst { .. }
                | TermKind::StringLit(_)
                | TermKind::Var(_),
            ) => 1,
            Some(
                TermKind::Not(arg)
                | TermKind::Neg(arg)
                | TermKind::BvNot(arg)
                | TermKind::StrLen(arg)
                | TermKind::StrToInt(arg)
                | TermKind::IntToStr(arg),
            ) => 1 + self.term_size_cached(*arg, cache),
            Some(TermKind::BvExtract { arg, .. }) => 1 + self.term_size_cached(*arg, cache),
            Some(
                TermKind::And(args)
                | TermKind::Or(args)
                | TermKind::Add(args)
                | TermKind::Mul(args)
                | TermKind::Distinct(args),
            ) => {
                1 + args
                    .iter()
                    .map(|&a| self.term_size_cached(a, cache))
                    .sum::<usize>()
            }
            Some(
                TermKind::Implies(a, b)
                | TermKind::Xor(a, b)
                | TermKind::Eq(a, b)
                | TermKind::Sub(a, b)
                | TermKind::Div(a, b)
                | TermKind::Mod(a, b)
                | TermKind::Lt(a, b)
                | TermKind::Le(a, b)
                | TermKind::Gt(a, b)
                | TermKind::Ge(a, b)
                | TermKind::Select(a, b)
                | TermKind::StrConcat(a, b)
                | TermKind::StrAt(a, b)
                | TermKind::StrContains(a, b)
                | TermKind::StrPrefixOf(a, b)
                | TermKind::StrSuffixOf(a, b)
                | TermKind::StrInRe(a, b)
                | TermKind::BvConcat(a, b)
                | TermKind::BvAnd(a, b)
                | TermKind::BvOr(a, b)
                | TermKind::BvXor(a, b)
                | TermKind::BvAdd(a, b)
                | TermKind::BvSub(a, b)
                | TermKind::BvMul(a, b)
                | TermKind::BvUdiv(a, b)
                | TermKind::BvSdiv(a, b)
                | TermKind::BvUrem(a, b)
                | TermKind::BvSrem(a, b)
                | TermKind::BvShl(a, b)
                | TermKind::BvLshr(a, b)
                | TermKind::BvAshr(a, b)
                | TermKind::BvUlt(a, b)
                | TermKind::BvUle(a, b)
                | TermKind::BvSlt(a, b)
                | TermKind::BvSle(a, b),
            ) => 1 + self.term_size_cached(*a, cache) + self.term_size_cached(*b, cache),
            Some(
                TermKind::Ite(c, t, e)
                | TermKind::Store(c, t, e)
                | TermKind::StrSubstr(c, t, e)
                | TermKind::StrIndexOf(c, t, e)
                | TermKind::StrReplace(c, t, e)
                | TermKind::StrReplaceAll(c, t, e),
            ) => {
                1 + self.term_size_cached(*c, cache)
                    + self.term_size_cached(*t, cache)
                    + self.term_size_cached(*e, cache)
            }
            Some(TermKind::Apply { args, .. }) => {
                1 + args
                    .iter()
                    .map(|&a| self.term_size_cached(a, cache))
                    .sum::<usize>()
            }
            Some(TermKind::Forall { body, .. } | TermKind::Exists { body, .. }) => {
                1 + self.term_size_cached(*body, cache)
            }
            Some(TermKind::Let { bindings, body }) => {
                1 + bindings
                    .iter()
                    .map(|(_, t)| self.term_size_cached(*t, cache))
                    .sum::<usize>()
                    + self.term_size_cached(*body, cache)
            }
            // Floating-point operations - calculate size recursively
            Some(_) => self.get(id).map_or(0, |term| {
                1 + get_children(&term.kind)
                    .iter()
                    .map(|&child| self.term_size_cached(child, cache))
                    .sum::<usize>()
            }),
        };

        cache.insert(id, size);
        size
    }

    /// Compute the depth of a term
    #[must_use]
    pub fn term_depth(&self, id: TermId) -> usize {
        self.term_depth_cached(id, &mut FxHashMap::default())
    }

    /// Compute the depth with memoization
    fn term_depth_cached(&self, id: TermId, cache: &mut FxHashMap<TermId, usize>) -> usize {
        if let Some(&depth) = cache.get(&id) {
            return depth;
        }

        let depth = match self.get(id).map(|t| &t.kind) {
            None => 0,
            Some(
                TermKind::True
                | TermKind::False
                | TermKind::IntConst(_)
                | TermKind::RealConst(_)
                | TermKind::BitVecConst { .. }
                | TermKind::StringLit(_)
                | TermKind::Var(_),
            ) => 0,
            Some(
                TermKind::Not(arg)
                | TermKind::Neg(arg)
                | TermKind::BvNot(arg)
                | TermKind::StrLen(arg)
                | TermKind::StrToInt(arg)
                | TermKind::IntToStr(arg),
            ) => 1 + self.term_depth_cached(*arg, cache),
            Some(TermKind::BvExtract { arg, .. }) => 1 + self.term_depth_cached(*arg, cache),
            Some(
                TermKind::And(args)
                | TermKind::Or(args)
                | TermKind::Add(args)
                | TermKind::Mul(args)
                | TermKind::Distinct(args),
            ) => {
                1 + args
                    .iter()
                    .map(|&a| self.term_depth_cached(a, cache))
                    .max()
                    .unwrap_or(0)
            }
            Some(
                TermKind::Implies(a, b)
                | TermKind::Xor(a, b)
                | TermKind::Eq(a, b)
                | TermKind::Sub(a, b)
                | TermKind::Div(a, b)
                | TermKind::Mod(a, b)
                | TermKind::Lt(a, b)
                | TermKind::Le(a, b)
                | TermKind::Gt(a, b)
                | TermKind::Ge(a, b)
                | TermKind::Select(a, b)
                | TermKind::StrConcat(a, b)
                | TermKind::StrAt(a, b)
                | TermKind::StrContains(a, b)
                | TermKind::StrPrefixOf(a, b)
                | TermKind::StrSuffixOf(a, b)
                | TermKind::StrInRe(a, b)
                | TermKind::BvConcat(a, b)
                | TermKind::BvAnd(a, b)
                | TermKind::BvOr(a, b)
                | TermKind::BvXor(a, b)
                | TermKind::BvAdd(a, b)
                | TermKind::BvSub(a, b)
                | TermKind::BvMul(a, b)
                | TermKind::BvUdiv(a, b)
                | TermKind::BvSdiv(a, b)
                | TermKind::BvUrem(a, b)
                | TermKind::BvSrem(a, b)
                | TermKind::BvShl(a, b)
                | TermKind::BvLshr(a, b)
                | TermKind::BvAshr(a, b)
                | TermKind::BvUlt(a, b)
                | TermKind::BvUle(a, b)
                | TermKind::BvSlt(a, b)
                | TermKind::BvSle(a, b),
            ) => {
                1 + self
                    .term_depth_cached(*a, cache)
                    .max(self.term_depth_cached(*b, cache))
            }
            Some(
                TermKind::Ite(c, t, e)
                | TermKind::Store(c, t, e)
                | TermKind::StrSubstr(c, t, e)
                | TermKind::StrIndexOf(c, t, e)
                | TermKind::StrReplace(c, t, e)
                | TermKind::StrReplaceAll(c, t, e),
            ) => {
                1 + self
                    .term_depth_cached(*c, cache)
                    .max(self.term_depth_cached(*t, cache))
                    .max(self.term_depth_cached(*e, cache))
            }
            Some(TermKind::Apply { args, .. }) => {
                1 + args
                    .iter()
                    .map(|&a| self.term_depth_cached(a, cache))
                    .max()
                    .unwrap_or(0)
            }
            Some(TermKind::Forall { body, .. } | TermKind::Exists { body, .. }) => {
                1 + self.term_depth_cached(*body, cache)
            }
            Some(TermKind::Let { bindings, body }) => {
                let binding_depth = bindings
                    .iter()
                    .map(|(_, t)| self.term_depth_cached(*t, cache))
                    .max()
                    .unwrap_or(0);
                1 + binding_depth.max(self.term_depth_cached(*body, cache))
            }
            // Floating-point operations - calculate depth recursively
            Some(_) => self.get(id).map_or(0, |term| {
                1 + get_children(&term.kind)
                    .iter()
                    .map(|&child| self.term_depth_cached(child, cache))
                    .max()
                    .unwrap_or(0)
            }),
        };

        cache.insert(id, depth);
        depth
    }

    /// Substitute variables in a term according to a mapping
    pub fn substitute(&mut self, id: TermId, subst: &FxHashMap<TermId, TermId>) -> TermId {
        self.substitute_cached(id, subst, &mut FxHashMap::default())
    }

    /// Substitute with memoization
    pub(super) fn substitute_cached(
        &mut self,
        id: TermId,
        subst: &FxHashMap<TermId, TermId>,
        cache: &mut FxHashMap<TermId, TermId>,
    ) -> TermId {
        // Check if this term is directly substituted
        if let Some(&replacement) = subst.get(&id) {
            return replacement;
        }

        // Check cache
        if let Some(&result) = cache.get(&id) {
            return result;
        }

        let result = match self.get(id).map(|t| t.kind.clone()) {
            None => id,
            Some(
                TermKind::True
                | TermKind::False
                | TermKind::IntConst(_)
                | TermKind::RealConst(_)
                | TermKind::BitVecConst { .. }
                | TermKind::Var(_),
            ) => id,
            Some(TermKind::Not(arg)) => {
                let new_arg = self.substitute_cached(arg, subst, cache);
                if new_arg == arg {
                    id
                } else {
                    self.mk_not(new_arg)
                }
            }
            Some(TermKind::And(args)) => {
                let new_args: SmallVec<[TermId; 4]> = args
                    .iter()
                    .map(|&a| self.substitute_cached(a, subst, cache))
                    .collect();
                if new_args.iter().zip(args.iter()).all(|(a, b)| a == b) {
                    id
                } else {
                    self.mk_and(new_args)
                }
            }
            Some(TermKind::Or(args)) => {
                let new_args: SmallVec<[TermId; 4]> = args
                    .iter()
                    .map(|&a| self.substitute_cached(a, subst, cache))
                    .collect();
                if new_args.iter().zip(args.iter()).all(|(a, b)| a == b) {
                    id
                } else {
                    self.mk_or(new_args)
                }
            }
            Some(TermKind::Implies(lhs, rhs)) => {
                let new_lhs = self.substitute_cached(lhs, subst, cache);
                let new_rhs = self.substitute_cached(rhs, subst, cache);
                if new_lhs == lhs && new_rhs == rhs {
                    id
                } else {
                    self.mk_implies(new_lhs, new_rhs)
                }
            }
            Some(TermKind::Eq(lhs, rhs)) => {
                let new_lhs = self.substitute_cached(lhs, subst, cache);
                let new_rhs = self.substitute_cached(rhs, subst, cache);
                if new_lhs == lhs && new_rhs == rhs {
                    id
                } else {
                    self.mk_eq(new_lhs, new_rhs)
                }
            }
            Some(TermKind::Ite(cond, then_br, else_br)) => {
                let new_cond = self.substitute_cached(cond, subst, cache);
                let new_then = self.substitute_cached(then_br, subst, cache);
                let new_else = self.substitute_cached(else_br, subst, cache);
                if new_cond == cond && new_then == then_br && new_else == else_br {
                    id
                } else {
                    self.mk_ite(new_cond, new_then, new_else)
                }
            }
            Some(TermKind::Add(args)) => {
                let new_args: SmallVec<[TermId; 4]> = args
                    .iter()
                    .map(|&a| self.substitute_cached(a, subst, cache))
                    .collect();
                if new_args.iter().zip(args.iter()).all(|(a, b)| a == b) {
                    id
                } else {
                    self.mk_add(new_args)
                }
            }
            Some(TermKind::Sub(lhs, rhs)) => {
                let new_lhs = self.substitute_cached(lhs, subst, cache);
                let new_rhs = self.substitute_cached(rhs, subst, cache);
                if new_lhs == lhs && new_rhs == rhs {
                    id
                } else {
                    self.mk_sub(new_lhs, new_rhs)
                }
            }
            Some(TermKind::Mul(args)) => {
                let new_args: SmallVec<[TermId; 4]> = args
                    .iter()
                    .map(|&a| self.substitute_cached(a, subst, cache))
                    .collect();
                if new_args.iter().zip(args.iter()).all(|(a, b)| a == b) {
                    id
                } else {
                    self.mk_mul(new_args)
                }
            }
            Some(TermKind::Lt(lhs, rhs)) => {
                let new_lhs = self.substitute_cached(lhs, subst, cache);
                let new_rhs = self.substitute_cached(rhs, subst, cache);
                if new_lhs == lhs && new_rhs == rhs {
                    id
                } else {
                    self.mk_lt(new_lhs, new_rhs)
                }
            }
            Some(TermKind::Le(lhs, rhs)) => {
                let new_lhs = self.substitute_cached(lhs, subst, cache);
                let new_rhs = self.substitute_cached(rhs, subst, cache);
                if new_lhs == lhs && new_rhs == rhs {
                    id
                } else {
                    self.mk_le(new_lhs, new_rhs)
                }
            }
            Some(TermKind::Gt(lhs, rhs)) => {
                let new_lhs = self.substitute_cached(lhs, subst, cache);
                let new_rhs = self.substitute_cached(rhs, subst, cache);
                if new_lhs == lhs && new_rhs == rhs {
                    id
                } else {
                    self.mk_gt(new_lhs, new_rhs)
                }
            }
            Some(TermKind::Ge(lhs, rhs)) => {
                let new_lhs = self.substitute_cached(lhs, subst, cache);
                let new_rhs = self.substitute_cached(rhs, subst, cache);
                if new_lhs == lhs && new_rhs == rhs {
                    id
                } else {
                    self.mk_ge(new_lhs, new_rhs)
                }
            }
            Some(TermKind::Select(arr, idx)) => {
                let new_arr = self.substitute_cached(arr, subst, cache);
                let new_idx = self.substitute_cached(idx, subst, cache);
                if new_arr == arr && new_idx == idx {
                    id
                } else {
                    self.mk_select(new_arr, new_idx)
                }
            }
            Some(TermKind::Store(arr, idx, val)) => {
                let new_arr = self.substitute_cached(arr, subst, cache);
                let new_idx = self.substitute_cached(idx, subst, cache);
                let new_val = self.substitute_cached(val, subst, cache);
                if new_arr == arr && new_idx == idx && new_val == val {
                    id
                } else {
                    self.mk_store(new_arr, new_idx, new_val)
                }
            }
            // Uninterpreted function/predicate application. Substituting into
            // the arguments is essential for quantifier instantiation — without
            // it, `(P x)[x↦c]` silently stays `(P x)`, so an instance lemma is
            // produced over the BOUND variable instead of the ground term (a
            // missed instantiation / vacuous guard). The sort is preserved by
            // substitution, so the original term's sort is reused exactly.
            Some(TermKind::Apply { func, args }) => {
                let new_args: SmallVec<[TermId; 4]> = args
                    .iter()
                    .map(|&a| self.substitute_cached(a, subst, cache))
                    .collect();
                if new_args.iter().zip(args.iter()).all(|(a, b)| a == b) {
                    id
                } else {
                    let sort = self.get(id).map(|t| t.sort).unwrap_or(self.sorts.bool_sort);
                    self.intern(TermKind::Apply { func, args: new_args }, sort)
                }
            }
            Some(TermKind::Distinct(args)) => {
                let new_args: SmallVec<[TermId; 4]> = args
                    .iter()
                    .map(|&a| self.substitute_cached(a, subst, cache))
                    .collect();
                if new_args.iter().zip(args.iter()).all(|(a, b)| a == b) {
                    id
                } else {
                    let sort = self.get(id).map(|t| t.sort).unwrap_or(self.sorts.bool_sort);
                    self.intern(TermKind::Distinct(new_args), sort)
                }
            }
            Some(TermKind::Neg(arg)) => {
                let new_arg = self.substitute_cached(arg, subst, cache);
                if new_arg == arg {
                    id
                } else {
                    self.mk_neg(new_arg)
                }
            }
            Some(TermKind::Xor(a, b)) => {
                let na = self.substitute_cached(a, subst, cache);
                let nb = self.substitute_cached(b, subst, cache);
                if na == a && nb == b {
                    id
                } else {
                    self.mk_xor(na, nb)
                }
            }
            Some(TermKind::Div(a, b)) => {
                let na = self.substitute_cached(a, subst, cache);
                let nb = self.substitute_cached(b, subst, cache);
                if na == a && nb == b {
                    id
                } else {
                    self.mk_div(na, nb)
                }
            }
            Some(TermKind::Mod(a, b)) => {
                let na = self.substitute_cached(a, subst, cache);
                let nb = self.substitute_cached(b, subst, cache);
                if na == a && nb == b {
                    id
                } else {
                    self.mk_mod(na, nb)
                }
            }
            // Quantifiers: substitute into the body for the FREE variables only.
            // Omitting this silently left `(∀z. … x …)[x↦t]` unchanged — so a
            // nested-quantifier instantiation kept the bound variable, and
            // skolemizing `∀x.∃y.∀z. φ` leaked `y` into the inner `∀z` (the
            // `nested_quantifiers` Unknown). `subst_under_binder` drops shadowed
            // keys and BAILS (leaves the body untouched) on capture, so it is
            // never unsound; patterns are preserved (triggers are advisory).
            Some(TermKind::Forall { vars, body, patterns }) => {
                let nb = self.subst_under_binder(&vars, body, subst);
                if nb == body {
                    id
                } else {
                    self.intern(
                        TermKind::Forall { vars, body: nb, patterns },
                        self.sorts.bool_sort,
                    )
                }
            }
            Some(TermKind::Exists { vars, body, patterns }) => {
                let nb = self.subst_under_binder(&vars, body, subst);
                if nb == body {
                    id
                } else {
                    self.intern(
                        TermKind::Exists { vars, body: nb, patterns },
                        self.sorts.bool_sort,
                    )
                }
            }
            // `let`: a BINDER — substituted by INLINING (let-elimination). SMT-LIB
            // `let` is parallel, so
            //   `(let ((y_i v_i)) body)[σ]  ≡  body[ (σ minus the y_i) ∪ {y_i ↦ v_i[σ]} ]`.
            // Inlining (rather than rebuilding a `Let` node) is deliberate: OxiZ's
            // theory layer does NOT reduce a `Let` node — it treats it as an opaque
            // value — so a substituted-in `Let` would be an instance the engine
            // can't match/decide → a spurious `sat` (the let-normalization gap).
            // Producing the let-FREE inlined body instead keeps the instance usable
            // AND closes the leak. (OxiZ already inlines lets at PARSE time —
            // `parse_symbol` resolves a let-bound name to its term — so a
            // parser-built body has no `y_i` and the `y_i ↦ v_i[σ]` entries are
            // inert; the full inline keeps it correct for any internally-built
            // non-inlined `Let` as well.) Sound: `let` is definitional.
            Some(TermKind::Let { bindings, body }) => {
                let bound: FxHashSet<Spur> = bindings.iter().map(|&(n, _)| n).collect();
                let mut combined: FxHashMap<TermId, TermId> = FxHashMap::default();
                for (&k, &v) in subst {
                    // drop a key the `let` shadows
                    if let Some(TermKind::Var(s)) = self.get(k).map(|t| &t.kind) {
                        if bound.contains(s) {
                            continue;
                        }
                    }
                    combined.insert(k, v);
                }
                for &(n, v) in &bindings {
                    let v_sub = self.substitute_cached(v, subst, cache);
                    let sort = self.get(v).map_or(self.sorts.bool_sort, |t| t.sort);
                    let name = self.resolve_str(n).to_string();
                    let y_var = self.mk_var(&name, sort);
                    combined.insert(y_var, v_sub);
                }
                self.substitute_cached(body, &combined, &mut FxHashMap::default())
            }
            // `match`: a BINDER. The scrutinee is in scope; each case body binds
            // that case's pattern variables, which are shadowed per case.
            Some(TermKind::Match { scrutinee, cases }) => {
                let new_scrut = self.substitute_cached(scrutinee, subst, cache);
                let mut changed = new_scrut != scrutinee;
                let mut new_cases: SmallVec<[MatchCase; 4]> = SmallVec::new();
                for c in &cases {
                    let bound: FxHashSet<Spur> = c.bindings.iter().copied().collect();
                    let nb = self.subst_under_bound_names(&bound, c.body, subst);
                    if nb != c.body {
                        changed = true;
                    }
                    new_cases.push(MatchCase {
                        constructor: c.constructor,
                        bindings: c.bindings.clone(),
                        body: nb,
                    });
                }
                if !changed {
                    id
                } else {
                    let sort = self.get(id).map(|t| t.sort).unwrap_or(self.sorts.bool_sort);
                    self.intern(TermKind::Match { scrutinee: new_scrut, cases: new_cases }, sort)
                }
            }
            // TOTAL substitution for every REMAINING kind — the capture-free
            // structural ops (String / FP / BV / `Dt*` / …). Recurse into each
            // direct child (`get_children`) and rebuild faithfully
            // (`transform_children`, exhaustive). This closes the **CCFV E/F leak**:
            // the former `Some(_) => id` drop arm returned these kinds UNCHANGED, so
            // an instance body wrapping a bound variable under e.g. a bitvector or
            // string op RETAINED that bound var. Soundness used to rest on the
            // fragile, UNASSERTED coupling "`OxizHost::view`-Opaque set ≡ this drop
            // set" (a dropped kind had to also be a non-descended `Opaque` leaf, or
            // `GroundIndex` would register a bare bound `Var` as ground). With the
            // substitution now TOTAL the bound var is always substituted away, so
            // the coupling is no longer load-bearing and adding a kind to `view`-App
            // is safe. (All four binders — Forall/Exists/Let/Match — are handled
            // above with shadowing, so only capture-free kinds reach here.)
            Some(other) => {
                let children = get_children(&other);
                let mut local: FxHashMap<TermId, TermId> = FxHashMap::default();
                let mut changed = false;
                for &c in &children {
                    let nc = self.substitute_cached(c, subst, cache);
                    if nc != c {
                        changed = true;
                    }
                    local.insert(c, nc);
                }
                if !changed {
                    id
                } else {
                    let sort = self.get(id).map(|t| t.sort).unwrap_or(self.sorts.bool_sort);
                    let new_kind = transform_children(&other, &local);
                    self.intern(new_kind, sort)
                }
            }
        };

        cache.insert(id, result);
        result
    }

    /// Substitute into a quantifier `body` whose own bound variables are `vars`.
    /// Shadowed substitution keys (a `vars` variable) are dropped, and the whole
    /// substitution is ABORTED (body returned unchanged) if any live replacement
    /// would be captured by a bound variable — so the result is always
    /// capture-free. Uses a fresh cache because the effective substitution
    /// (after shadow-filtering) differs from the caller's.
    fn subst_under_binder(
        &mut self,
        vars: &[(Spur, SortId)],
        body: TermId,
        subst: &FxHashMap<TermId, TermId>,
    ) -> TermId {
        let bound: FxHashSet<Spur> = vars.iter().map(|(n, _)| *n).collect();
        self.subst_under_bound_names(&bound, body, subst)
    }

    /// The capture-avoiding core of [`Self::subst_under_binder`], parameterised by
    /// the set of `bound` names a binder introduces — shared by the quantifier,
    /// `let`, and `match`-case arms of [`Self::substitute_cached`]. Drops keys the
    /// binder shadows and BAILS (body unchanged) if any live replacement would be
    /// captured, so the result is always capture-free.
    fn subst_under_bound_names(
        &mut self,
        bound: &FxHashSet<Spur>,
        body: TermId,
        subst: &FxHashMap<TermId, TermId>,
    ) -> TermId {
        let mentions_bound = |me: &Self, t: TermId| -> bool {
            me.free_vars(t).into_iter().any(|fv| {
                matches!(me.get(fv).map(|x| &x.kind), Some(TermKind::Var(s)) if bound.contains(s))
            })
        };
        let mut filtered: FxHashMap<TermId, TermId> = FxHashMap::default();
        for (&k, &v) in subst {
            // Drop a key shadowed by this quantifier's own binder.
            if let Some(TermKind::Var(s)) = self.get(k).map(|t| &t.kind) {
                if bound.contains(s) {
                    continue;
                }
            }
            // Capture: a live replacement names a bound variable ⇒ leave the body
            // untouched rather than risk an unsound capture.
            if mentions_bound(self, v) {
                return body;
            }
            filtered.insert(k, v);
        }
        if filtered.is_empty() {
            return body;
        }
        self.substitute_cached(body, &filtered, &mut FxHashMap::default())
    }

    /// Simplify a term by applying rewrite rules
    ///
    /// This performs bottom-up simplification including:
    /// - Constant folding for arithmetic
    /// - Boolean simplifications
    /// - Identity/annihilator rules
    pub fn simplify(&mut self, id: TermId) -> TermId {
        let mut cache = FxHashMap::default();
        self.simplify_cached(id, &mut cache)
    }

    fn simplify_cached(&mut self, id: TermId, cache: &mut FxHashMap<TermId, TermId>) -> TermId {
        if let Some(&result) = cache.get(&id) {
            return result;
        }

        let result = match self.get(id).map(|t| t.kind.clone()) {
            None
            | Some(
                TermKind::True
                | TermKind::False
                | TermKind::IntConst(_)
                | TermKind::RealConst(_)
                | TermKind::BitVecConst { .. }
                | TermKind::Var(_),
            ) => id,

            Some(TermKind::Not(arg)) => {
                let new_arg = self.simplify_cached(arg, cache);
                self.mk_not(new_arg)
            }
            Some(TermKind::And(args)) => {
                let new_args: SmallVec<[TermId; 4]> = args
                    .iter()
                    .map(|&a| self.simplify_cached(a, cache))
                    .collect();
                self.mk_and(new_args)
            }
            Some(TermKind::Or(args)) => {
                let new_args: SmallVec<[TermId; 4]> = args
                    .iter()
                    .map(|&a| self.simplify_cached(a, cache))
                    .collect();
                self.mk_or(new_args)
            }
            Some(TermKind::Implies(lhs, rhs)) => {
                let new_lhs = self.simplify_cached(lhs, cache);
                let new_rhs = self.simplify_cached(rhs, cache);
                self.mk_implies(new_lhs, new_rhs)
            }
            Some(TermKind::Eq(lhs, rhs)) => {
                let new_lhs = self.simplify_cached(lhs, cache);
                let new_rhs = self.simplify_cached(rhs, cache);
                self.mk_eq(new_lhs, new_rhs)
            }
            Some(TermKind::Ite(cond, then_br, else_br)) => {
                let new_cond = self.simplify_cached(cond, cache);
                let new_then = self.simplify_cached(then_br, cache);
                let new_else = self.simplify_cached(else_br, cache);
                self.mk_ite(new_cond, new_then, new_else)
            }
            Some(TermKind::Add(args)) => {
                let new_args: SmallVec<[TermId; 4]> = args
                    .iter()
                    .map(|&a| self.simplify_cached(a, cache))
                    .collect();
                self.simplify_add(new_args)
            }
            Some(TermKind::Sub(lhs, rhs)) => {
                let new_lhs = self.simplify_cached(lhs, cache);
                let new_rhs = self.simplify_cached(rhs, cache);
                self.simplify_sub(new_lhs, new_rhs)
            }
            Some(TermKind::Mul(args)) => {
                let new_args: SmallVec<[TermId; 4]> = args
                    .iter()
                    .map(|&a| self.simplify_cached(a, cache))
                    .collect();
                self.simplify_mul(new_args)
            }
            Some(TermKind::Neg(arg)) => {
                let new_arg = self.simplify_cached(arg, cache);
                self.simplify_neg(new_arg)
            }
            Some(TermKind::Lt(lhs, rhs)) => {
                let new_lhs = self.simplify_cached(lhs, cache);
                let new_rhs = self.simplify_cached(rhs, cache);
                self.simplify_lt(new_lhs, new_rhs)
            }
            Some(TermKind::Le(lhs, rhs)) => {
                let new_lhs = self.simplify_cached(lhs, cache);
                let new_rhs = self.simplify_cached(rhs, cache);
                self.simplify_le(new_lhs, new_rhs)
            }
            Some(TermKind::Gt(lhs, rhs)) => {
                let new_lhs = self.simplify_cached(lhs, cache);
                let new_rhs = self.simplify_cached(rhs, cache);
                self.simplify_gt(new_lhs, new_rhs)
            }
            Some(TermKind::Ge(lhs, rhs)) => {
                let new_lhs = self.simplify_cached(lhs, cache);
                let new_rhs = self.simplify_cached(rhs, cache);
                self.simplify_ge(new_lhs, new_rhs)
            }
            // For other terms, just return as-is
            Some(_) => id,
        };

        cache.insert(id, result);
        result
    }

    /// Simplify addition with constant folding
    fn simplify_add(&mut self, args: SmallVec<[TermId; 4]>) -> TermId {
        let mut constant_sum = BigInt::from(0);
        let mut other_args: SmallVec<[TermId; 4]> = SmallVec::new();

        for arg in args {
            if let Some(TermKind::IntConst(n)) = self.get(arg).map(|t| &t.kind) {
                constant_sum += n;
            } else {
                other_args.push(arg);
            }
        }

        let zero = BigInt::from(0);
        if other_args.is_empty() {
            return self.intern(TermKind::IntConst(constant_sum), self.sorts.int_sort);
        }

        if constant_sum != zero {
            other_args.push(self.intern(TermKind::IntConst(constant_sum), self.sorts.int_sort));
        }

        if other_args.len() == 1 {
            return other_args[0];
        }

        self.mk_add(other_args)
    }

    /// Simplify subtraction with constant folding
    fn simplify_sub(&mut self, lhs: TermId, rhs: TermId) -> TermId {
        let zero = BigInt::from(0);
        match (
            self.get(lhs).map(|t| t.kind.clone()),
            self.get(rhs).map(|t| t.kind.clone()),
        ) {
            (Some(TermKind::IntConst(a)), Some(TermKind::IntConst(b))) => {
                self.intern(TermKind::IntConst(a - b), self.sorts.int_sort)
            }
            (_, Some(TermKind::IntConst(n))) if n == zero => lhs,
            (Some(TermKind::IntConst(n)), _) if n == zero => self.simplify_neg(rhs),
            _ => self.mk_sub(lhs, rhs),
        }
    }

    /// Simplify multiplication with constant folding
    fn simplify_mul(&mut self, args: SmallVec<[TermId; 4]>) -> TermId {
        let mut constant_product = BigInt::from(1);
        let mut other_args: SmallVec<[TermId; 4]> = SmallVec::new();
        let zero = BigInt::from(0);
        let one = BigInt::from(1);

        for arg in args {
            if let Some(TermKind::IntConst(n)) = self.get(arg).map(|t| &t.kind) {
                if *n == zero {
                    return self.mk_int(0);
                }
                constant_product *= n;
            } else {
                other_args.push(arg);
            }
        }

        if other_args.is_empty() {
            return self.intern(TermKind::IntConst(constant_product), self.sorts.int_sort);
        }

        if constant_product == zero {
            return self.mk_int(0);
        }

        if constant_product != one {
            other_args.insert(
                0,
                self.intern(TermKind::IntConst(constant_product), self.sorts.int_sort),
            );
        }

        if other_args.len() == 1 {
            return other_args[0];
        }

        self.mk_mul(other_args)
    }

    /// Simplify negation
    fn simplify_neg(&mut self, arg: TermId) -> TermId {
        match self.get(arg).map(|t| t.kind.clone()) {
            Some(TermKind::IntConst(n)) => self.intern(TermKind::IntConst(-n), self.sorts.int_sort),
            Some(TermKind::Neg(inner)) => inner,
            _ => {
                let sort = self.get(arg).map_or(self.sorts.int_sort, |t| t.sort);
                self.intern(TermKind::Neg(arg), sort)
            }
        }
    }

    /// Simplify less-than with constant comparison and reflexivity
    fn simplify_lt(&mut self, lhs: TermId, rhs: TermId) -> TermId {
        // Reflexivity: a < a is always False
        if lhs == rhs {
            return self.false_id;
        }
        match (
            self.get(lhs).map(|t| t.kind.clone()),
            self.get(rhs).map(|t| t.kind.clone()),
        ) {
            (Some(TermKind::IntConst(a)), Some(TermKind::IntConst(b))) => self.mk_bool(a < b),
            _ => self.mk_lt(lhs, rhs),
        }
    }

    /// Simplify less-or-equal with constant comparison and reflexivity
    fn simplify_le(&mut self, lhs: TermId, rhs: TermId) -> TermId {
        // Reflexivity: a <= a is always True
        if lhs == rhs {
            return self.true_id;
        }
        match (
            self.get(lhs).map(|t| t.kind.clone()),
            self.get(rhs).map(|t| t.kind.clone()),
        ) {
            (Some(TermKind::IntConst(a)), Some(TermKind::IntConst(b))) => self.mk_bool(a <= b),
            _ => self.mk_le(lhs, rhs),
        }
    }

    /// Simplify greater-than with constant comparison and reflexivity
    fn simplify_gt(&mut self, lhs: TermId, rhs: TermId) -> TermId {
        // Reflexivity: a > a is always False
        if lhs == rhs {
            return self.false_id;
        }
        match (
            self.get(lhs).map(|t| t.kind.clone()),
            self.get(rhs).map(|t| t.kind.clone()),
        ) {
            (Some(TermKind::IntConst(a)), Some(TermKind::IntConst(b))) => self.mk_bool(a > b),
            _ => self.mk_gt(lhs, rhs),
        }
    }

    /// Simplify greater-or-equal with constant comparison and reflexivity
    fn simplify_ge(&mut self, lhs: TermId, rhs: TermId) -> TermId {
        // Reflexivity: a >= a is always True
        if lhs == rhs {
            return self.true_id;
        }
        match (
            self.get(lhs).map(|t| t.kind.clone()),
            self.get(rhs).map(|t| t.kind.clone()),
        ) {
            (Some(TermKind::IntConst(a)), Some(TermKind::IntConst(b))) => self.mk_bool(a >= b),
            _ => self.mk_ge(lhs, rhs),
        }
    }

    /// Collect all free variables in a term
    pub fn free_vars(&self, id: TermId) -> Vec<TermId> {
        let mut vars = Vec::new();
        let mut visited = FxHashMap::default();
        self.collect_free_vars(id, &mut vars, &mut visited);
        vars
    }

    fn collect_free_vars(
        &self,
        id: TermId,
        vars: &mut Vec<TermId>,
        visited: &mut FxHashMap<TermId, ()>,
    ) {
        if visited.contains_key(&id) {
            return;
        }
        visited.insert(id, ());

        match self.get(id).map(|t| &t.kind) {
            None => {}
            Some(TermKind::Var(_)) if !vars.contains(&id) => {
                vars.push(id);
            }
            Some(
                TermKind::True
                | TermKind::False
                | TermKind::IntConst(_)
                | TermKind::RealConst(_)
                | TermKind::BitVecConst { .. }
                | TermKind::StringLit(_),
            ) => {}
            Some(
                TermKind::Not(arg)
                | TermKind::Neg(arg)
                | TermKind::BvNot(arg)
                | TermKind::StrLen(arg)
                | TermKind::StrToInt(arg)
                | TermKind::IntToStr(arg),
            ) => {
                self.collect_free_vars(*arg, vars, visited);
            }
            Some(TermKind::BvExtract { arg, .. }) => {
                self.collect_free_vars(*arg, vars, visited);
            }
            Some(
                TermKind::And(args)
                | TermKind::Or(args)
                | TermKind::Add(args)
                | TermKind::Mul(args)
                | TermKind::Distinct(args),
            ) => {
                for &arg in args {
                    self.collect_free_vars(arg, vars, visited);
                }
            }
            Some(
                TermKind::Implies(a, b)
                | TermKind::Xor(a, b)
                | TermKind::Eq(a, b)
                | TermKind::Sub(a, b)
                | TermKind::Div(a, b)
                | TermKind::Mod(a, b)
                | TermKind::Lt(a, b)
                | TermKind::Le(a, b)
                | TermKind::Gt(a, b)
                | TermKind::Ge(a, b)
                | TermKind::Select(a, b)
                | TermKind::StrConcat(a, b)
                | TermKind::StrAt(a, b)
                | TermKind::StrContains(a, b)
                | TermKind::StrPrefixOf(a, b)
                | TermKind::StrSuffixOf(a, b)
                | TermKind::StrInRe(a, b)
                | TermKind::BvConcat(a, b)
                | TermKind::BvAnd(a, b)
                | TermKind::BvOr(a, b)
                | TermKind::BvXor(a, b)
                | TermKind::BvAdd(a, b)
                | TermKind::BvSub(a, b)
                | TermKind::BvMul(a, b)
                | TermKind::BvUdiv(a, b)
                | TermKind::BvSdiv(a, b)
                | TermKind::BvUrem(a, b)
                | TermKind::BvSrem(a, b)
                | TermKind::BvShl(a, b)
                | TermKind::BvLshr(a, b)
                | TermKind::BvAshr(a, b)
                | TermKind::BvUlt(a, b)
                | TermKind::BvUle(a, b)
                | TermKind::BvSlt(a, b)
                | TermKind::BvSle(a, b),
            ) => {
                self.collect_free_vars(*a, vars, visited);
                self.collect_free_vars(*b, vars, visited);
            }
            Some(
                TermKind::Ite(c, t, e)
                | TermKind::Store(c, t, e)
                | TermKind::StrSubstr(c, t, e)
                | TermKind::StrIndexOf(c, t, e)
                | TermKind::StrReplace(c, t, e)
                | TermKind::StrReplaceAll(c, t, e),
            ) => {
                self.collect_free_vars(*c, vars, visited);
                self.collect_free_vars(*t, vars, visited);
                self.collect_free_vars(*e, vars, visited);
            }
            Some(TermKind::Apply { args, .. }) => {
                for &arg in args {
                    self.collect_free_vars(arg, vars, visited);
                }
            }
            Some(TermKind::Forall { body, .. } | TermKind::Exists { body, .. }) => {
                // Note: This is simplified - we should track bound vars
                self.collect_free_vars(*body, vars, visited);
            }
            Some(TermKind::Let { bindings, body }) => {
                for (_, term) in bindings {
                    self.collect_free_vars(*term, vars, visited);
                }
                self.collect_free_vars(*body, vars, visited);
            }
            // Floating-point operations - collect vars from children
            Some(_) => {
                if let Some(term) = self.get(id) {
                    for &child in &get_children(&term.kind) {
                        self.collect_free_vars(child, vars, visited);
                    }
                }
            }
        }
    }
}
