//! Cross-`TermManager` term transplantation.
//!
//! `TermId` (and `SortId`, for non-builtin sorts) are indices into whichever
//! `TermManager`/`SortManager` instance minted them — they are not portable
//! to a different manager without translation. This module provides that
//! translation for the fragment of terms an optimization objective or
//! `assert-soft` weight actually needs: boolean structure, linear
//! arithmetic, comparisons, and uninterpreted function applications, all
//! over the BUILTIN sorts (`Bool`/`Int`/`Real`).
//!
//! ## Builtin-sort-id stability
//!
//! `SortManager::new()` always interns `Bool`, `Int`, `Real` — in that
//! order — as the very first three sorts, against a freshly-zeroed id
//! counter (see `SortManager::new()`). Every freshly constructed
//! `TermManager`/`SortManager` therefore assigns `Bool = SortId(0)`,
//! `Int = SortId(1)`, `Real = SortId(2)`, with no dependency on what a
//! caller does afterwards. This transplant still looks the destination's
//! builtin `SortId`s up via `dst.sorts.{bool,int,real}_sort` (rather than
//! reusing the source's raw numeric id) so correctness does not silently
//! depend on that coincidence — but empirically, for any two managers
//! built through `TermManager::new()`, the ids match.
//!
//! ## Scope
//!
//! Deliberately narrow: only the `TermKind` variants listed below are
//! transplanted. Anything else — arrays, bitvectors, floats, strings,
//! datatypes, quantifiers, `let`, `match` — fails cleanly with
//! [`TransplantError`] rather than silently producing a wrong `TermId` or
//! panicking, even in cases where the top-level sort happens to be
//! builtin (e.g. a `let`-bound `Int` value is still rejected: the
//! allowlist is on `TermKind`, checked in addition to the sort check).

use super::TermManager;
use crate::ast::term::{TermId, TermKind};
#[allow(unused_imports)]
use crate::prelude::*;
use crate::sort::{SortId, SortKind};
use smallvec::SmallVec;

/// Why [`transplant_term`] could not translate a term into the destination
/// manager.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TransplantError {
    /// `id` (or a reachable subterm) is not `Bool`/`Int`/`Real`-sorted —
    /// e.g. references a user-declared sort, a datatype, an array, a
    /// bitvector, etc.
    UnsupportedSort,
    /// `id` (or a reachable subterm) uses a `TermKind` this transplant does
    /// not support, regardless of its own sort (e.g. `Select`/`Store`,
    /// `Forall`/`Exists`, `Let`, `Match`, any Bv/Fp/Str/Dt construct).
    UnsupportedTermKind,
    /// `id` does not resolve to a term in `src` (a stale/foreign `TermId`).
    DanglingTermId,
}

impl core::fmt::Display for TransplantError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::UnsupportedSort => write!(
                f,
                "term references a non-builtin sort (only Bool/Int/Real are supported here)"
            ),
            Self::UnsupportedTermKind => {
                write!(f, "term uses a construct not supported in this context")
            }
            Self::DanglingTermId => write!(f, "term id does not exist in the source manager"),
        }
    }
}

impl core::error::Error for TransplantError {}

/// Translate the destination's builtin `SortId` for a source sort kind
/// already confirmed to be `Bool`/`Int`/`Real`.
fn dst_builtin_sort(dst: &TermManager, kind: &SortKind) -> SortId {
    match kind {
        SortKind::Bool => dst.sorts.bool_sort,
        SortKind::Int => dst.sorts.int_sort,
        SortKind::Real => dst.sorts.real_sort,
        // Callers only reach here after confirming `kind` is one of the
        // three arms above.
        _ => unreachable!("dst_builtin_sort called with a non-builtin SortKind"),
    }
}

/// Translate `id` (from `src`) into the equivalent `TermId` in `dst`.
///
/// Memoized via an internal worklist (`TermId` in `src` -> `TermId` in
/// `dst`) so DAG sharing in `src` is preserved in `dst` (a subterm
/// referenced twice in `src` is transplanted once and reused twice) and the
/// walk stays linear in the number of distinct subterms rather than
/// exponential.
///
/// Iterative (explicit heap-allocated worklist), not recursive: an earlier
/// version used plain recursion and stack-overflowed the process (not just
/// returned an error) on a linearly-nested term around depth ~8000-9000 on
/// the default thread stack — a realistic shape for a summed/folded
/// objective over thousands of soft terms. The worklist depth is bounded
/// only by available heap, so this has no equivalent depth ceiling.
///
/// Scope: only `Bool`/`Int`/`Real`-sorted terms built from boolean
/// structure, linear arithmetic, comparisons, and uninterpreted function
/// applications. See the module doc for the exact allowlist and rationale.
pub fn transplant_term(
    src: &TermManager,
    id: TermId,
    dst: &mut TermManager,
) -> Result<TermId, TransplantError> {
    let mut memo: FxHashMap<TermId, TermId> = FxHashMap::default();
    transplant_iter(src, id, dst, &mut memo)
}

/// One frame of the iterative worklist: `Expand` visits `id` for the first
/// time (validates it, and — for a composite kind — schedules its children
/// to be expanded before scheduling `Assemble` to run after them);
/// `Assemble` runs once every child of `id` is already in `memo`, and
/// performs the actual `dst.mk_*` reconstruction.
enum Frame {
    Expand(TermId),
    Assemble(TermId),
}

/// Fetch `id` from `src`, confirming it resolves and is `Bool`/`Int`/
/// `Real`-sorted. Returns the term's (cloned) `kind` and `SortKind`.
fn fetch_checked(
    src: &TermManager,
    id: TermId,
) -> Result<(TermKind, SortKind), TransplantError> {
    let term = src.get(id).ok_or(TransplantError::DanglingTermId)?;
    let sort_kind = src
        .sorts
        .get(term.sort)
        .ok_or(TransplantError::UnsupportedSort)?
        .kind
        .clone();
    if !matches!(sort_kind, SortKind::Bool | SortKind::Int | SortKind::Real) {
        return Err(TransplantError::UnsupportedSort);
    }
    Ok((term.kind.clone(), sort_kind))
}

/// The direct children (in `src`) of a composite `TermKind`. Empty for leaf
/// kinds (`True`/`False`/`IntConst`/`RealConst`/`Var`) and for any kind
/// outside this transplant's supported fragment (the latter is rejected by
/// `fetch_checked`'s caller before this is ever consulted for such a kind).
fn children_of(kind: &TermKind) -> SmallVec<[TermId; 4]> {
    match kind {
        TermKind::Not(a) | TermKind::Neg(a) => smallvec::smallvec![*a],
        TermKind::And(args)
        | TermKind::Or(args)
        | TermKind::Add(args)
        | TermKind::Mul(args)
        | TermKind::Distinct(args) => args.iter().copied().collect(),
        TermKind::Xor(l, r)
        | TermKind::Implies(l, r)
        | TermKind::Eq(l, r)
        | TermKind::Sub(l, r)
        | TermKind::Div(l, r)
        | TermKind::Mod(l, r)
        | TermKind::Lt(l, r)
        | TermKind::Le(l, r)
        | TermKind::Gt(l, r)
        | TermKind::Ge(l, r) => smallvec::smallvec![*l, *r],
        TermKind::Ite(c, t, e) => smallvec::smallvec![*c, *t, *e],
        TermKind::Apply { args, .. } => args.iter().copied().collect(),
        _ => SmallVec::new(),
    }
}

/// Reconstruct a LEAF kind (no children) directly in `dst`.
fn assemble_leaf(
    dst: &mut TermManager,
    src: &TermManager,
    kind: TermKind,
    sort_kind: &SortKind,
) -> TermId {
    match kind {
        TermKind::True => dst.mk_true(),
        TermKind::False => dst.mk_false(),
        TermKind::IntConst(n) => dst.mk_int(n),
        TermKind::RealConst(r) => dst.mk_real(r),
        TermKind::Var(spur) => {
            let name = src.resolve_str(spur).to_string();
            let dst_sort = dst_builtin_sort(dst, sort_kind);
            dst.mk_var(&name, dst_sort)
        }
        other => unreachable!("assemble_leaf called with non-leaf kind {other:?}"),
    }
}

/// Reconstruct a COMPOSITE kind in `dst`, looking up each child's already-
/// transplanted `TermId` from `memo` (guaranteed present: `Assemble(id)` is
/// only scheduled after every child of `id` has been fully processed).
fn assemble_composite(
    dst: &mut TermManager,
    src: &TermManager,
    kind: TermKind,
    sort_kind: &SortKind,
    memo: &FxHashMap<TermId, TermId>,
) -> TermId {
    let g = |t: TermId| -> TermId {
        *memo
            .get(&t)
            .expect("child must already be transplanted before parent assembly")
    };
    match kind {
        TermKind::Not(a) => dst.mk_not(g(a)),
        TermKind::And(args) => {
            let args2: SmallVec<[TermId; 4]> = args.iter().map(|&a| g(a)).collect();
            dst.mk_and(args2)
        }
        TermKind::Or(args) => {
            let args2: SmallVec<[TermId; 4]> = args.iter().map(|&a| g(a)).collect();
            dst.mk_or(args2)
        }
        TermKind::Xor(l, r) => dst.mk_xor(g(l), g(r)),
        TermKind::Implies(l, r) => dst.mk_implies(g(l), g(r)),
        TermKind::Ite(c, t, e) => dst.mk_ite(g(c), g(t), g(e)),
        TermKind::Eq(l, r) => dst.mk_eq(g(l), g(r)),
        TermKind::Distinct(args) => {
            let args2: SmallVec<[TermId; 4]> = args.iter().map(|&a| g(a)).collect();
            dst.mk_distinct(args2)
        }
        TermKind::Neg(a) => dst.mk_neg(g(a)),
        TermKind::Add(args) => {
            let args2: SmallVec<[TermId; 4]> = args.iter().map(|&a| g(a)).collect();
            dst.mk_add(args2)
        }
        TermKind::Sub(l, r) => dst.mk_sub(g(l), g(r)),
        TermKind::Mul(args) => {
            let args2: SmallVec<[TermId; 4]> = args.iter().map(|&a| g(a)).collect();
            dst.mk_mul(args2)
        }
        TermKind::Div(l, r) => dst.mk_div(g(l), g(r)),
        TermKind::Mod(l, r) => dst.mk_mod(g(l), g(r)),
        TermKind::Lt(l, r) => dst.mk_lt(g(l), g(r)),
        TermKind::Le(l, r) => dst.mk_le(g(l), g(r)),
        TermKind::Gt(l, r) => dst.mk_gt(g(l), g(r)),
        TermKind::Ge(l, r) => dst.mk_ge(g(l), g(r)),
        TermKind::Apply { func, args } => {
            let name = src.resolve_str(func).to_string();
            let args2: SmallVec<[TermId; 4]> = args.iter().map(|&a| g(a)).collect();
            let dst_sort = dst_builtin_sort(dst, sort_kind);
            dst.mk_apply(&name, args2, dst_sort)
        }
        other => unreachable!("assemble_composite called with unsupported kind {other:?}"),
    }
}

fn transplant_iter(
    src: &TermManager,
    root: TermId,
    dst: &mut TermManager,
    memo: &mut FxHashMap<TermId, TermId>,
) -> Result<TermId, TransplantError> {
    let mut stack: Vec<Frame> = vec![Frame::Expand(root)];

    while let Some(frame) = stack.pop() {
        match frame {
            Frame::Expand(id) => {
                if memo.contains_key(&id) {
                    continue;
                }
                let (kind, sort_kind) = fetch_checked(src, id)?;

                let is_leaf = matches!(
                    kind,
                    TermKind::True
                        | TermKind::False
                        | TermKind::IntConst(_)
                        | TermKind::RealConst(_)
                        | TermKind::Var(_)
                );
                if is_leaf {
                    let result = assemble_leaf(dst, src, kind, &sort_kind);
                    memo.insert(id, result);
                    continue;
                }

                let children = children_of(&kind);
                // Everything else (arrays, bitvectors, floats, strings,
                // datatypes, quantifiers, let, match) is out of scope for
                // this transplant even when its own sort happens to be
                // builtin — `children_of` returns empty for those too, so
                // distinguish them explicitly here rather than silently
                // "assembling" a 0-ary node for a kind that isn't actually
                // a supported leaf or a supported composite.
                if !matches!(
                    kind,
                    TermKind::Not(_)
                        | TermKind::And(_)
                        | TermKind::Or(_)
                        | TermKind::Xor(..)
                        | TermKind::Implies(..)
                        | TermKind::Ite(..)
                        | TermKind::Eq(..)
                        | TermKind::Distinct(_)
                        | TermKind::Neg(_)
                        | TermKind::Add(_)
                        | TermKind::Sub(..)
                        | TermKind::Mul(_)
                        | TermKind::Div(..)
                        | TermKind::Mod(..)
                        | TermKind::Lt(..)
                        | TermKind::Le(..)
                        | TermKind::Gt(..)
                        | TermKind::Ge(..)
                        | TermKind::Apply { .. }
                ) {
                    return Err(TransplantError::UnsupportedTermKind);
                }

                // Push `Assemble(id)` BEFORE its children's `Expand` frames
                // so it sits deeper in the stack and only runs once every
                // child (pushed on top, LIFO) has fully resolved.
                stack.push(Frame::Assemble(id));
                for &c in children.iter().rev() {
                    stack.push(Frame::Expand(c));
                }
            }
            Frame::Assemble(id) => {
                if memo.contains_key(&id) {
                    continue;
                }
                let (kind, sort_kind) = fetch_checked(src, id)?;
                let result = assemble_composite(dst, src, kind, &sort_kind, memo);
                memo.insert(id, result);
            }
        }
    }

    memo.get(&root).copied().ok_or(TransplantError::DanglingTermId)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::manager::TermManager;

    #[test]
    fn builtin_sort_ids_are_stable_across_fresh_managers() {
        // Empirical confirmation of the module-doc claim: two independently
        // constructed managers assign the same ids to Bool/Int/Real.
        let a = TermManager::new();
        let b = TermManager::new();
        assert_eq!(a.sorts.bool_sort, b.sorts.bool_sort);
        assert_eq!(a.sorts.int_sort, b.sorts.int_sort);
        assert_eq!(a.sorts.real_sort, b.sorts.real_sort);
        assert_eq!(a.sorts.bool_sort.raw(), 0);
        assert_eq!(a.sorts.int_sort.raw(), 1);
        assert_eq!(a.sorts.real_sort.raw(), 2);
    }

    #[test]
    fn transplants_int_const() {
        let mut src = TermManager::new();
        let mut dst = TermManager::new();
        let c = src.mk_int(42);
        let c2 = transplant_term(&src, c, &mut dst).expect("transplant should succeed");
        let t = dst.get(c2).expect("term should exist in dst");
        match &t.kind {
            TermKind::IntConst(n) => assert_eq!(n, &num_bigint::BigInt::from(42)),
            other => panic!("expected IntConst, got {other:?}"),
        }
        assert_eq!(t.sort, dst.sorts.int_sort);
    }

    #[test]
    fn transplants_var_preserving_name_and_sort() {
        let mut src = TermManager::new();
        let mut dst = TermManager::new();
        let x = src.mk_var("x", src.sorts.int_sort);
        let x2 = transplant_term(&src, x, &mut dst).expect("transplant should succeed");
        let t = dst.get(x2).expect("term should exist in dst");
        assert_eq!(t.sort, dst.sorts.int_sort);
        match &t.kind {
            TermKind::Var(spur) => assert_eq!(dst.resolve_str(*spur), "x"),
            other => panic!("expected Var, got {other:?}"),
        }
    }

    #[test]
    fn transplants_nested_arithmetic_and_boolean_structure() {
        let mut src = TermManager::new();
        let mut dst = TermManager::new();

        let x = src.mk_var("x", src.sorts.int_sort);
        let y = src.mk_var("y", src.sorts.int_sort);
        let sum = src.mk_add([x, y]);
        let ten = src.mk_int(10);
        let le = src.mk_le(sum, ten);
        let z = src.mk_var("z", src.sorts.bool_sort);
        let goal = src.mk_and([le, z]);

        let goal2 = transplant_term(&src, goal, &mut dst).expect("transplant should succeed");
        let t = dst.get(goal2).expect("term should exist in dst");
        assert_eq!(t.sort, dst.sorts.bool_sort);
        match &t.kind {
            TermKind::And(args) => assert_eq!(args.len(), 2),
            other => panic!("expected And, got {other:?}"),
        }
    }

    #[test]
    fn transplants_uninterpreted_function_application() {
        let mut src = TermManager::new();
        let mut dst = TermManager::new();

        let x = src.mk_var("x", src.sorts.int_sort);
        let f_x = src.mk_apply("f", [x], src.sorts.int_sort);
        let five = src.mk_int(5);
        let gt = src.mk_gt(f_x, five);

        let gt2 = transplant_term(&src, gt, &mut dst).expect("transplant should succeed");
        let t = dst.get(gt2).expect("term should exist in dst");
        match &t.kind {
            TermKind::Gt(l, _) => {
                let lt = dst.get(*l).expect("term should exist in dst");
                match &lt.kind {
                    TermKind::Apply { func, args } => {
                        assert_eq!(dst.resolve_str(*func), "f");
                        assert_eq!(args.len(), 1);
                    }
                    other => panic!("expected Apply, got {other:?}"),
                }
            }
            other => panic!("expected Gt, got {other:?}"),
        }
    }

    #[test]
    fn preserves_dag_sharing() {
        let mut src = TermManager::new();
        let mut dst = TermManager::new();

        // Build a term where a shared subexpression is used twice:
        // (and (<= (+ x y) 10) (<= (+ x y) 20))
        let x = src.mk_var("x", src.sorts.int_sort);
        let y = src.mk_var("y", src.sorts.int_sort);
        let sum = src.mk_add([x, y]);
        let ten = src.mk_int(10);
        let twenty = src.mk_int(20);
        let le1 = src.mk_le(sum, ten);
        let le2 = src.mk_le(sum, twenty);
        let both = src.mk_and([le1, le2]);
        assert_eq!(src.term_count(), src.term_count()); // sanity, no-op

        let both2 = transplant_term(&src, both, &mut dst).expect("transplant should succeed");
        let t = dst.get(both2).expect("term should exist in dst");
        let (a2, b2) = match &t.kind {
            TermKind::And(args) => (args[0], args[1]),
            other => panic!("expected And, got {other:?}"),
        };
        let extract_sum = |le: TermId| -> TermId {
            match &dst.get(le).expect("term should exist in dst").kind {
                TermKind::Le(l, _) => *l,
                other => panic!("expected Le, got {other:?}"),
            }
        };
        let sum_a = extract_sum(a2);
        let sum_b = extract_sum(b2);
        // The shared `(+ x y)` subterm must transplant to the SAME TermId
        // in dst, not two separate copies.
        assert_eq!(sum_a, sum_b);
    }

    #[test]
    fn rejects_non_builtin_sort_cleanly() {
        let mut src = TermManager::new();
        let mut dst = TermManager::new();

        // A term over an uninterpreted sort is out of scope.
        let foo = src.intern_str("Foo");
        let uninterp = src.sorts.intern(SortKind::Uninterpreted(foo));
        let x = src.mk_var("x", uninterp);
        let y = src.mk_var("y", uninterp);
        let eq = src.mk_eq(x, y);

        let result = transplant_term(&src, eq, &mut dst);
        assert_eq!(result, Err(TransplantError::UnsupportedSort));
    }

    #[test]
    fn rejects_non_builtin_sort_reachable_deep_inside_a_builtin_sorted_term() {
        let mut src = TermManager::new();
        let mut dst = TermManager::new();

        // (= (f x) 5) where f: Foo -> Int and x: Foo — the top-level term
        // is Bool-sorted (an Eq of two Ints), but a reachable subterm (x)
        // is Foo-sorted (uninterpreted), so this must still fail cleanly.
        let foo = src.intern_str("Foo");
        let uninterp = src.sorts.intern(SortKind::Uninterpreted(foo));
        let x = src.mk_var("x", uninterp);
        let f_x = src.mk_apply("f", [x], src.sorts.int_sort);
        let five = src.mk_int(5);
        let eq = src.mk_eq(f_x, five);

        let result = transplant_term(&src, eq, &mut dst);
        assert_eq!(result, Err(TransplantError::UnsupportedSort));
    }

    #[test]
    fn rejects_unsupported_term_kind_cleanly() {
        let mut src = TermManager::new();
        let mut dst = TermManager::new();

        // Array select is out of scope even though the result is Int.
        let arr_sort = src.sorts.array(src.sorts.int_sort, src.sorts.int_sort);
        let arr = src.mk_var("a", arr_sort);
        let idx = src.mk_int(0);
        let sel = src.mk_select(arr, idx);

        let result = transplant_term(&src, sel, &mut dst);
        assert_eq!(result, Err(TransplantError::UnsupportedTermKind));
    }

    #[test]
    fn deep_linear_nesting_does_not_overflow_stack() {
        // Regression test for a P1 finding (fill-the-gap/maxsat fixup
        // pass): the original plain-recursive `transplant_rec` aborted the
        // whole process (stack overflow, not a catchable error) around
        // depth ~8000-9000 on the default thread stack. 50,000 is well
        // past that on any thread stack size, and the iterative worklist
        // rebuild has no depth ceiling at all (bounded only by heap), so
        // this must succeed rather than crash or time out.
        let mut src = TermManager::new();
        let mut dst = TermManager::new();

        let mut cur = src.mk_int(0);
        let one = src.mk_int(1);
        for _ in 0..50_000 {
            cur = src.mk_add([cur, one]);
        }

        let result = transplant_term(&src, cur, &mut dst);
        assert!(result.is_ok(), "deep linear chain should transplant, got {result:?}");
    }

    #[test]
    fn dangling_term_id_fails_cleanly_not_panics() {
        let src = TermManager::new();
        let mut dst = TermManager::new();
        let bogus = TermId::new(999_999);
        let result = transplant_term(&src, bogus, &mut dst);
        assert_eq!(result, Err(TransplantError::DanglingTermId));
    }
}
