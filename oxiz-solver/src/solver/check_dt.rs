//! Datatype theory constraint checking
//!
//! # Known residual completeness boundaries (spurious-SAT direction only,
//! never spurious-unsat)
//!
//! Items 1-3 below were found by this integration pass's own 1000-seed
//! z3-differential re-verification of the already-landed #419 items (NOT
//! newly introduced by that session's own changes) and are recorded here,
//! historically, as **CLOSED by #422** — see that task's own three landed
//! fixes for the mechanism each one uses. Items 4-5 are **CLOSED by #423**
//! (item 4 narrows/closes item 1's own honest residual; item 5 is a new,
//! previously-undocumented gap). The section is kept (rather than deleted)
//! to match this file's existing convention of a permanent, append-only
//! residual log.
//!
//! 1. **CLOSED (#422) — OR-branch non-cycle conflicts.**
//!    `dt_items_force_conflict` (the `#418`/`#419` OR-branch case-split
//!    evaluator) used to check each branch's closed hypothesis for an
//!    ACYCLICITY conflict ONLY — see its own doc comment, "#422 — beyond
//!    acyclicity-only". A branch internally contradictory for a DIFFERENT
//!    reason (e.g. `x=cons(a,b) ∧ x=cons(c,b) ∧ (distinct a c)`, where
//!    constructor injectivity forces `a=c`) was invisible to it. Fixed by
//!    threading a fourth hypothesis slice, `h_diseq` (cloned by value
//!    through every recursive call, same branch-isolation discipline as
//!    `h_var`/`h_ctor`/`h_sel`), and checking `closure.
//!    forces_disequality_conflict(h_diseq)` at the leaf alongside the
//!    existing cycle check. The SAME gap also existed on the FLAT
//!    (non-OR) path whenever `config.simplify == false` (a real, reachable
//!    config via `--preset minimal`/the portfolio's `LocalSearch`
//!    strategy) — closed there too, by the identical
//!    `forces_disequality_conflict` check reusing the closure
//!    `check_dt_constraints` already computes (see that function's #422
//!    doc note). See `dt_or_case_split_regression.rs`'s `#422` test
//!    section for the original tests; its HONEST documented residual
//!    (the flat path's disequality-source collection from `Eq`'s negative
//!    arm was DT-SORT-GATED, unlike `distinct`'s unconditional push) is now
//!    **CLOSED (#423 item 1)** — see item 4 below.
//! 2. **CLOSED (#422) — `distinct` not recognized in any polarity.**
//!    `collect_dt_constraints_v2` had NO `TermKind::Distinct` arm at all —
//!    neither a positive `(distinct a b)` (a disequality) nor a negated
//!    `(not (distinct a b))` (semantically `(= a b)`) was ever recognized,
//!    so a ground conflict expressed either way was invisible to every
//!    check in this file. Fixed by a new `TermKind::Distinct(args) if
//!    args.len() == 2` arm reusing `record_dt_positive_eq_fact`/
//!    `record_dt_negative_eq_fact` (see `collect_dt_constraints_v2`'s doc
//!    comment, "`Distinct` polarity mapping", for the full soundness
//!    argument and the N-ARY GUARD — `args.len() != 2` is a genuine
//!    DISJUNCTION when negated, never collected as a single equality).
//! 3. **CLOSED (#422) — direct `C(..) = D(..)` ctor-ctor equality
//!    invisible to the closure.** `collect_dt_constraints_v2`'s `Eq` arm
//!    only recorded a var-ctor-term pair when ONE side `is_dt_variable` —
//!    an equality where BOTH sides are manifest constructor applications
//!    (no mediating variable) contributed NOTHING to
//!    `compute_dt_equality_closure`'s base equality set, even though the
//!    SAT-level simplifier (`DatatypeRewriter::rewrite_constructor_eq`,
//!    `config.simplify`-gated) already decomposes the same equality for
//!    ordinary solving. Fixed by a new `dt_ctor_ctor_eqs` out-param,
//!    populated inside `record_dt_positive_eq_fact` whenever BOTH sides
//!    are `TermKind::DtConstructor`, merged into `var_ctor_term_eqs` at
//!    every call site before the closure call (`compute_dt_equality_
//!    closure`'s own signature is unchanged — both slices were already
//!    treated identically inside it).
//! 4. **CLOSED (#423) — `Eq`'s negative arm was narrower than `distinct`.**
//!    `collect_dt_constraints_v2`'s `Eq` negative-context arm only pushed
//!    into `dt_diseq_pairs` when `both_dt_sorted(lhs, rhs, manager)` held —
//!    a plain `(not (= a c))` between two Int-sorted terms was never
//!    recorded as a disequality candidate, unlike the sibling `Distinct`
//!    positive-context arm (#422), which already pushed unconditionally.
//!    Reachable under DEFAULT config (not just `simplify: false`): the
//!    OR-branch case-split evaluator (`dt_items_force_conflict`) has no
//!    SAT-level fallback at all, so a formula like `(or (and (= x (cons a
//!    b)) (= x (cons c b)) (not (= a c))) ...)` with Int-sorted `a`/`c` read
//!    spurious `sat` under default settings even though the FLAT path was
//!    masked by `inject_dt_derived_ctor_equalities`'s `simplify`-gated
//!    fallback. Fixed by deleting the `both_dt_sorted` gate (and the
//!    now-fully-dead `both_dt_sorted` helper itself) — the identical
//!    "always safe" argument `Distinct`'s unconditional push already relies
//!    on applies verbatim to `Eq`'s negative arm. See
//!    `dt_or_case_split_regression.rs`'s `#423` test section (including the
//!    flipped `flat_injectivity_forced_noteq_intfields_simplify_false_*`
//!    test, now closed rather than a documented residual) and
//!    `dt_distinct_regression.rs`'s updated cross-reference comment.
//! 5. **CLOSED (#423) — nullary-constructor tester implied no equality.**
//!    `(is-c0 x) ∧ (is-c0 y) ∧ (distinct x y)` read spurious `sat`: a
//!    NULLARY constructor `C` (zero fields) has exactly ONE possible value,
//!    so `is-C(arg) ⟺ arg = C()` is a TRUE EQUIVALENCE — but
//!    `collect_dt_constraints_v2`'s `DtTester` arm only ever accumulated
//!    constructor-name-tag strings (`constructor_testers`/
//!    `negative_testers`), never an equality/disequality fact, regardless
//!    of arity. Fixed by a new `record_dt_nullary_tester_eq_fact` helper,
//!    called alongside the existing tag bookkeeping: on a POSITIVE nullary
//!    tester, pushes `(arg, c_term)` into `var_ctor_term_eqs`; on a
//!    NEGATIVE one, pushes `(arg, c_term)` into `dt_diseq_pairs`. `c_term`
//!    is looked up via the new `&self`-only `TermManager::
//!    find_nullary_dt_constructor_term`, and the constructor's arity via
//!    `manager.sorts.datatype_constructors_of` — comparing constructor
//!    NAMES as strings (never raw `Spur`s across the term-manager /
//!    sort-manager interner boundary, the exact cross-interner mistake
//!    that caused a real #399 bug). See
//!    `dt_nullary_tester_equality_regression.rs` for the full test suite,
//!    including composition with #419's injectivity machinery and an
//!    arity>0 control confirming non-nullary testers stay unaffected.

#[allow(unused_imports)]
use crate::prelude::*;
use oxiz_core::ast::{TermId, TermKind, TermManager};

use super::Solver;

/// #418 item 3 — pragmatic safety valve for
/// `Solver::check_dt_or_case_split_conflict`'s combinatorial case-split
/// search (never a soundness concern in either direction: exceeding the
/// budget only means "no conflict found," the always-safe answer). See that
/// function's doc comment, "Termination / blowup guard".
const DT_OR_CASE_SPLIT_BUDGET: u32 = 200_000;

/// #419 (OR-branch wiring) — the per-call step budget `compute_dt_equality_
/// closure` runs under when called from the two NON-branch-scoped call
/// sites (`check_dt_constraints`'s flat acyclicity check and
/// `collect_var_ctor_bindings`'s once-per-check-sat axiom-injection feed).
/// Each of those sites owns its OWN fresh budget of this size (mirroring the
/// closure's pre-OR-wiring behavior exactly — a once-per-check-sat call has
/// no combinatorial sibling search to share a pool with). The THIRD call
/// site — inside `dt_items_force_conflict`'s per-leaf conflict check, added
/// for #418/#419's OR-branch case-split wiring — deliberately does NOT get
/// its own fresh pool of this size; it instead threads the SAME `&mut u32`
/// counter already bounding the case-split work-list's own pop-steps
/// (`DT_OR_CASE_SPLIT_BUDGET`), so a pathological formula that visits many
/// leaves, each triggering an expensive closure computation, is still
/// bounded by ONE combined total-work budget rather than
/// `DT_OR_CASE_SPLIT_BUDGET` leaves × `DT_CLOSURE_STEP_BUDGET` closure-steps
/// each. See `dt_items_force_conflict`'s doc comment for the full argument;
/// as ever, exceeding either budget only ever means "derive/search less,"
/// never "fabricate a conflict."
const DT_CLOSURE_STEP_BUDGET: u32 = 20_000;

/// #419 — the full result of `Solver::compute_dt_equality_closure`, consumed
/// by both the acyclicity check (non-OR path) and the SAT-level
/// axiom-injection wiring in `mod.rs::check_level`. See that function's doc
/// comment for the derivation algorithm.
pub(super) struct DtEqualityClosure {
    /// Every equality pair in the converged closure (base facts plus every
    /// item-1/item-2 derivation), as generic `(TermId, TermId)` pairs — fed
    /// directly into `Solver::check_dt_acyclicity`'s union-find (in place of
    /// the old one-shot `dt_var_equalities`/`var_ctor_term_eqs` slices) so a
    /// selector-shaped equality that only becomes acyclicity-relevant once
    /// its argument resolves (#419 item 2) still participates in the cycle
    /// graph.
    pub(super) closed_eqs: Vec<(TermId, TermId)>,
    /// var -> ONE representative (arbitrarily but deterministically chosen)
    /// resolved ctor-term binding for its class. Same shape/contract the
    /// pre-#419 `collect_var_ctor_bindings` always returned and
    /// `encode.rs::resolve_dt_normal_form` still expects; now populated from
    /// the FULL iterative closure rather than a single non-iterating pass,
    /// so a binding only reachable via a chain of selector-resolutions
    /// (#419 item 2) is included too.
    pub(super) primary_bindings: FxHashMap<TermId, TermId>,
    /// #419 item 1 — for every equivalence class with 2+ DISTINCT
    /// same-constructor ctor-term bindings: the list of every DT VARIABLE in
    /// that class (so a selector/tester applied to ANY synonym is covered),
    /// paired with the list of every EXTRA (non-primary) same-constructor
    /// ctor term for that class. Consumed by
    /// `encode.rs::add_dt_multi_binding_selector_reduction_axioms`, which
    /// re-runs the audited selector-reduction walk once per extra binding
    /// (with that one class's entries in the resolution map overridden to
    /// the extra value) so EVERY distinct resolved field value gets its own
    /// ground fact injected — the actual mechanism that closes the
    /// injectivity-transitivity repro (see that function's doc comment for
    /// why the ctor=ctor equality below is not, by itself, sufficient).
    pub(super) extra_by_class: Vec<(Vec<TermId>, Vec<TermId>)>,
    /// #419 item 1 — the ground `binding1 = binding2` equality axiom for
    /// every DISTINCT pair of same-constructor ctor-term bindings found
    /// within one class. Always a SOUND consequence (ordinary equality
    /// transitivity through the shared class) — injected as a SAT-level
    /// ground unit clause by `encode.rs::inject_dt_derived_ctor_equalities`
    /// so other equality-consuming machinery (cover-axiom exclusivity,
    /// `distinct` reasoning, etc.) sees it directly too, not just the
    /// selector-reduction consumers `extra_by_class` targets.
    pub(super) derived_ctor_eqs: Vec<(TermId, TermId)>,
}

impl Solver {
    pub(super) fn check_dt_constraints(&self, manager: &TermManager) -> bool {
        // Collect positive constructor tester constraints: ((_ is Constructor) x)
        let mut constructor_testers: FxHashMap<TermId, Vec<String>> = FxHashMap::default();
        // Collect negative constructor tester constraints: (not ((_ is Constructor) x))
        let mut negative_testers: FxHashMap<TermId, Vec<String>> = FxHashMap::default();
        // Collect constructor equalities: x = Constructor(...)
        let mut constructor_equalities: FxHashMap<TermId, Vec<String>> = FxHashMap::default();
        // Collect NEGATIVE constructor equalities: (not (= x Constructor)) — the
        // ctor must be NULLARY for the diseq to exclude the whole constructor
        // class (x ≠ cons(a,b) only excludes ONE instance), which the collector
        // enforces (#399 — the nullary-ctor exhaustiveness check below).
        let mut negative_ctor_equalities: FxHashMap<TermId, Vec<String>> = FxHashMap::default();
        // Collect DT variable equalities: x = y where both are DT variables
        let mut dt_var_equalities: Vec<(TermId, TermId)> = Vec::new();
        // #406 — DT variable = manifest constructor-TERM equalities (the same
        // shape `constructor_equalities` records by CTOR NAME, but here we
        // also keep the actual constructor TERM id so the acyclicity check
        // below can union the variable into that term's argument graph). One
        // entry per positively-asserted `x = C(args…)` / `C(args…) = x`.
        let mut var_ctor_term_eqs: Vec<(TermId, TermId)> = Vec::new();
        // #419 item 2 — raw `sel(t) = t2` facts feeding
        // `compute_dt_equality_closure`'s iterative selector-resolution step.
        let mut sel_eqs: Vec<(TermId, TermId)> = Vec::new();
        // #422 item 3 — direct `C(..) = D(..)` ctor-ctor equalities (no
        // mediating variable), merged into `var_ctor_term_eqs` before the
        // closure call below (`compute_dt_equality_closure` itself treats
        // both slices identically, so no signature change is needed there).
        let mut dt_ctor_ctor_eqs: Vec<(TermId, TermId)> = Vec::new();
        // #422 items 1+2 — disequality-source pairs (from a negative
        // DT-sorted `Eq`, or a positive 2-ary `distinct`) feeding
        // `DtEqualityClosure::forces_disequality_conflict` below.
        let mut dt_diseq_pairs: Vec<(TermId, TermId)> = Vec::new();

        for &assertion in &self.assertions {
            self.collect_dt_constraints_v2(
                assertion,
                manager,
                &mut constructor_testers,
                &mut negative_testers,
                &mut constructor_equalities,
                &mut negative_ctor_equalities,
                &mut dt_var_equalities,
                &mut var_ctor_term_eqs,
                &mut sel_eqs,
                &mut dt_ctor_ctor_eqs,
                &mut dt_diseq_pairs,
                true,
            );
        }
        var_ctor_term_eqs.extend(dt_ctor_ctor_eqs);

        // Check: If a variable has multiple different constructor testers, it's UNSAT
        for (_var, testers) in &constructor_testers {
            if testers.len() > 1 {
                // Multiple different constructors asserted for the same variable
                // Check if they're actually different
                let first = &testers[0];
                for tester in testers.iter().skip(1) {
                    if tester != first {
                        return true; // Conflict: x is Constructor1 AND x is Constructor2
                    }
                }
            }
        }

        // Check: If a variable has a positive and negative tester for the same constructor
        for (var, pos_testers) in &constructor_testers {
            if let Some(neg_testers) = negative_testers.get(var) {
                for pos in pos_testers {
                    for neg in neg_testers {
                        if pos == neg {
                            return true; // Conflict: (is Cons x) AND (not (is Cons x))
                        }
                    }
                }
            }
        }

        // Check: If a variable has different constructor equalities, it's UNSAT
        for (_var, constructors) in &constructor_equalities {
            if constructors.len() > 1 {
                let first = &constructors[0];
                for cons in constructors.iter().skip(1) {
                    if cons != first {
                        return true; // Conflict: x = Constructor1 AND x = Constructor2
                    }
                }
            }
        }

        // Check: If a variable has a constructor tester that conflicts with its equality
        for (var, testers) in &constructor_testers {
            if let Some(equalities) = constructor_equalities.get(var) {
                for tester in testers {
                    for eq_cons in equalities {
                        if tester != eq_cons {
                            return true; // Conflict: (is Cons1 x) AND x = Cons2(...)
                        }
                    }
                }
            }
        }

        // Check: If a variable has a negative tester that conflicts with its equality
        for (var, neg_testers) in &negative_testers {
            if let Some(equalities) = constructor_equalities.get(var) {
                for neg in neg_testers {
                    for eq_cons in equalities {
                        if neg == eq_cons {
                            return true; // Conflict: (not (is Cons x)) AND x = Cons(...)
                        }
                    }
                }
            }
        }

        // Check cross-variable constraints through equality
        // If l1 = l2 and they have conflicting tester constraints, it's UNSAT
        for &(var1, var2) in &dt_var_equalities {
            // Case 1: var1 has positive tester, var2 has negative tester for same constructor
            if let Some(pos1) = constructor_testers.get(&var1) {
                if let Some(neg2) = negative_testers.get(&var2) {
                    for p in pos1 {
                        for n in neg2 {
                            if p == n {
                                // l1 = l2, (is Cons l1), (not (is Cons l2)) => UNSAT
                                return true;
                            }
                        }
                    }
                }
            }
            // Case 2: var2 has positive tester, var1 has negative tester for same constructor
            if let Some(pos2) = constructor_testers.get(&var2) {
                if let Some(neg1) = negative_testers.get(&var1) {
                    for p in pos2 {
                        for n in neg1 {
                            if p == n {
                                // l1 = l2, (is Cons l2), (not (is Cons l1)) => UNSAT
                                return true;
                            }
                        }
                    }
                }
            }

            // Case 3: var1 has different positive tester than var2
            if let Some(pos1) = constructor_testers.get(&var1) {
                if let Some(pos2) = constructor_testers.get(&var2) {
                    for p1 in pos1 {
                        for p2 in pos2 {
                            if p1 != p2 {
                                // l1 = l2, (is Cons1 l1), (is Cons2 l2) where Cons1 != Cons2 => UNSAT
                                return true;
                            }
                        }
                    }
                }
            }

            // Case 4: var1 has constructor equality, var2 has conflicting negative tester
            if let Some(eq1) = constructor_equalities.get(&var1) {
                if let Some(neg2) = negative_testers.get(&var2) {
                    for e in eq1 {
                        for n in neg2 {
                            if e == n {
                                // l1 = l2, l1 = Cons(...), (not (is Cons l2)) => UNSAT
                                return true;
                            }
                        }
                    }
                }
            }
            // Case 5: var2 has constructor equality, var1 has conflicting negative tester
            if let Some(eq2) = constructor_equalities.get(&var2) {
                if let Some(neg1) = negative_testers.get(&var1) {
                    for e in eq2 {
                        for n in neg1 {
                            if e == n {
                                // l1 = l2, l2 = Cons(...), (not (is Cons l1)) => UNSAT
                                return true;
                            }
                        }
                    }
                }
            }

            // Case 6: var1 has constructor equality, var2 has conflicting positive tester
            if let Some(eq1) = constructor_equalities.get(&var1) {
                if let Some(pos2) = constructor_testers.get(&var2) {
                    for e in eq1 {
                        for p in pos2 {
                            if e != p {
                                // l1 = l2, l1 = Cons1(...), (is Cons2 l2) where Cons1 != Cons2 => UNSAT
                                return true;
                            }
                        }
                    }
                }
            }
            // Case 7: var2 has constructor equality, var1 has conflicting positive tester
            if let Some(eq2) = constructor_equalities.get(&var2) {
                if let Some(pos1) = constructor_testers.get(&var1) {
                    for e in eq2 {
                        for p in pos1 {
                            if e != p {
                                // l1 = l2, l2 = Cons1(...), (is Cons2 l1) where Cons1 != Cons2 => UNSAT
                                return true;
                            }
                        }
                    }
                }
            }

            // Case 8: Both have different constructor equalities
            if let Some(eq1) = constructor_equalities.get(&var1) {
                if let Some(eq2) = constructor_equalities.get(&var2) {
                    for e1 in eq1 {
                        for e2 in eq2 {
                            if e1 != e2 {
                                // l1 = l2, l1 = Cons1(...), l2 = Cons2(...) where Cons1 != Cons2 => UNSAT
                                return true;
                            }
                        }
                    }
                }
            }
        }

        // #399 — nullary-ctor EXHAUSTIVENESS: every datatype value is built by
        // some constructor, so a variable excluded from EVERY constructor of
        // its (nonempty) datatype is a ground conflict. An exclusion is a
        // negative TESTER (any ctor) or a negative equality to a NULLARY ctor
        // (the collector only records those — `x ≠ cons(a,b)` excludes one
        // instance, not the class). Pre-fix `¬(k=c00 ∨ k=c01)` over a 2-ctor
        // enum read `sat` (z3+cvc5: unsat).
        for var in negative_testers.keys().chain(negative_ctor_equalities.keys()) {
            let Some(var_term) = manager.get(*var) else {
                continue;
            };
            let Some(ctors) = manager.sorts.datatype_constructors_of(var_term.sort) else {
                continue;
            };
            if ctors.is_empty() {
                continue;
            }
            let neg_t = negative_testers.get(var);
            let neg_e = negative_ctor_equalities.get(var);
            let all_excluded = ctors.iter().all(|(name, arity)| {
                neg_t.is_some_and(|v| v.iter().any(|n| n == name))
                    || (*arity == 0 && neg_e.is_some_and(|v| v.iter().any(|n| n == name)))
            });
            if all_excluded {
                return true; // Conflict: x is none of its datatype's constructors
            }
        }

        // #406 — ground acyclicity: SMT-LIB datatypes denote the free
        // (well-founded) algebra, so no ground term may equal a proper
        // constructor-subterm of itself (e.g. `y = cons(x, y)` is UNSAT — no
        // finite list equals its own tail-extension). See
        // `check_dt_acyclicity`'s doc comment for the full soundness
        // argument; it only trusts the two equality collections above
        // (`dt_var_equalities`, `var_ctor_term_eqs`), which are already
        // filtered to genuinely-asserted-POSITIVE facts by
        // `collect_dt_constraints_v2`'s existing And/Or/Not polarity
        // handling.
        //
        // #419 item 2 — feed the ITERATIVE CLOSURE's fully-derived equality
        // set (`compute_dt_equality_closure`), not the raw, one-shot
        // `dt_var_equalities`/`var_ctor_term_eqs` collections directly: a
        // selector application equated to something (`(= (tl z) z)`) only
        // contributes an acyclicity-relevant equality once its OWN argument
        // has been resolved to a manifest constructor application (possibly
        // via another equality asserted elsewhere), which the raw collectors
        // never attempt. The closure starts from exactly these same two
        // (already-audited, polarity-gated) collections, so the soundness
        // argument above still applies unchanged to everything it contains;
        // see that function's doc comment for why every additional pair it
        // derives is itself a sound logical consequence of the base facts.
        let mut closure_budget = DT_CLOSURE_STEP_BUDGET;
        let closure = self.compute_dt_equality_closure(
            &dt_var_equalities,
            &var_ctor_term_eqs,
            &sel_eqs,
            manager,
            &mut closure_budget,
        );
        if self.check_dt_acyclicity(manager, &closure.closed_eqs, &[]) {
            return true;
        }

        // #422 STEP 6 — close the flat-path non-cycle-conflict gap, reusing
        // the closure just computed above (no new closure computation
        // needed): a branch/assertion set can be internally contradictory
        // for a reason OTHER than acyclicity — e.g. `x=cons(a,b)`,
        // `x=cons(c,b)`, `(distinct a c)`, where injectivity forces `a=c`
        // (folded into `closure.closed_eqs` by step (b2)'s field
        // decomposition) while `a≠c` is also asserted. This check is
        // UNCONDITIONAL (not gated on `config.simplify`) — unlike the
        // SAT-level route (`inject_dt_derived_ctor_equalities`, which only
        // decomposes an injected ctor=ctor equality through the simplifier
        // when `config.simplify == true`), `compute_dt_equality_closure`'s
        // result is simplify-independent by construction, so this closes the
        // gap even under `--preset minimal` / `simplify=false` configs. See
        // `DtEqualityClosure::forces_disequality_conflict`'s doc comment.
        if closure.forces_disequality_conflict(&dt_diseq_pairs) {
            return true;
        }

        // #418 item 3 — OR-branch cyclic disjunction case-split: even when
        // NO single equality is unconditionally (flatly) true, every WAY of
        // satisfying the assertion set might still force a cycle (e.g. every
        // disjunct of an `or` independently forces one). See
        // `check_dt_or_case_split_conflict`'s doc comment for the full
        // design; this is a pure generalization of the check just above (it
        // reduces to exactly the same answer when there is no case-split
        // structure to consider).
        if self.check_dt_or_case_split_conflict(manager) {
            return true;
        }

        false
    }

    /// #406 — ground datatype acyclicity check.
    ///
    /// Standard technique (as used in CVC4/Z3's datatype theory): build a
    /// directed graph over EQUIVALENCE CLASSES of ground datatype-sorted
    /// terms. An edge `class(t) -> class(a)` exists whenever some member of
    /// `class(t)` is a manifest constructor application `C(…, a, …)` and `a`
    /// is itself datatype-sorted (only a datatype-sorted field can
    /// participate in a well-foundedness cycle — an `Int`/`Bool` field
    /// can't). A CYCLE in this graph is a genuine ground conflict: it means
    /// some class is asserted to properly contain itself as a constructor
    /// argument, which is impossible in the free/well-founded algebra SMT-LIB
    /// datatypes denote.
    ///
    /// # Soundness
    ///
    /// Two things must each be sound for the whole check to be sound:
    ///
    /// 1. **Which terms get UNIONED into the same class.** This function
    ///    does NO polarity reasoning itself — it only unions pairs it is
    ///    handed (`dt_var_equalities` for `x = y` between two DT variables,
    ///    `var_ctor_term_eqs` for `x = C(args…)`), and BOTH of those are
    ///    collected by `collect_dt_constraints_v2`, which already threads the
    ///    `in_positive_context` flag correctly through `And`/`Or`/`Not` (the
    ///    same collector `constructor_equalities`/`constructor_testers` rely
    ///    on elsewhere in this file). Two datatype-sorted variables that
    ///    merely SHARE A SORT but have no asserted equality are never handed
    ///    to `union`, so they are never conflated — they simply never appear
    ///    together in either input slice.
    /// 2. **Which edges get added.** A constructor application's OWN shape
    ///    (`C`'s name and argument list) is a fact about the TERM itself —
    ///    `cons(x, y)` denotes "cons applied to x and y" regardless of what
    ///    logical context that term sits in (a term is not a proposition), so
    ///    the unconditional structural walk below (no polarity gating) that
    ///    records `ctor_shape` is safe: it never claims anything is asserted,
    ///    only that a certain term, IF it ever matters, has that shape. The
    ///    walk stops at `Forall`/`Exists` bodies (ground-only scope, matching
    ///    the rest of this file and `encode.rs`'s `add_dt_cover_axioms`
    ///    worklist).
    ///
    /// Combining the two: an edge `class(t) -> class(a)` only ever exists
    /// when `t`'s class contains a term that is LITERALLY `C(…, a, …)` in the
    /// term graph, and `t`'s class is exactly what genuinely-asserted
    /// equalities put there. No edge is ever added from a merely-possible or
    /// currently-inactive relationship (e.g. an unevaluated `ite` branch
    /// contributes no equality to either collection, so it contributes no
    /// union and no edge).
    ///
    /// # Termination
    ///
    /// The structural walk is a bounded DFS over the (finite) term DAG,
    /// deduplicated via `seen`. The graph has at most one node per distinct
    /// `TermId` and at most `arity` edges per constructor application, both
    /// bounded by formula size. Cycle detection is a standard iterative
    /// (explicit-stack, no recursion) white/gray/black DFS, `O(V + E)`.
    fn check_dt_acyclicity(
        &self,
        manager: &TermManager,
        dt_var_equalities: &[(TermId, TermId)],
        var_ctor_term_eqs: &[(TermId, TermId)],
    ) -> bool {
        let ctor_terms = self.build_dt_ctor_terms(manager);
        self.cycle_exists_given(dt_var_equalities, var_ctor_term_eqs, &ctor_terms, manager)
    }

    /// Unconditional structural walk: record every manifest `DtConstructor`
    /// application's own (term-id, args) shape, over the WHOLE current
    /// assertion set. Ground-only: skips quantifier bodies (see
    /// `check_dt_acyclicity`'s doc comment, point 2, for why this needs no
    /// polarity gating — a term's shape is a fact about the term, not a
    /// proposition). Extracted out of `check_dt_acyclicity` so `#418` item
    /// 3's case-split evaluator (`check_dt_or_case_split_conflict`) can reuse
    /// it as a subroutine: this structural shape NEVER depends on which
    /// branch of an Or/And is chosen, so it is always safe/correct to compute
    /// it exactly ONCE and share it across every hypothesis-set variant the
    /// case-split evaluator tries.
    fn build_dt_ctor_terms(&self, manager: &TermManager) -> Vec<(TermId, Vec<TermId>)> {
        let mut ctor_terms: Vec<(TermId, Vec<TermId>)> = Vec::new();
        let mut stack: Vec<TermId> = self.assertions.clone();
        let mut seen: FxHashSet<TermId> = FxHashSet::default();
        while let Some(t) = stack.pop() {
            if !seen.insert(t) {
                continue;
            }
            let Some(td) = manager.get(t) else { continue };
            if matches!(td.kind, TermKind::Forall { .. } | TermKind::Exists { .. }) {
                continue;
            }
            for c in oxiz_core::ast::get_children(&td.kind) {
                stack.push(c);
            }
            if let TermKind::DtConstructor { args, .. } = &td.kind {
                ctor_terms.push((t, args.iter().copied().collect()));
            }
        }
        ctor_terms
    }

    /// Union-Find + directed-containment-graph + DFS cycle detector,
    /// PARAMETERIZED by an arbitrary equality set (`dt_var_equalities`,
    /// `var_ctor_term_eqs`) and the precomputed `ctor_terms` structural walk
    /// (see `build_dt_ctor_terms`). This is the exact same algorithm
    /// `check_dt_acyclicity` always used, extracted so `#418` item 3's
    /// recursive per-branch evaluator can reuse it as a subroutine — feeding
    /// it the union of the global background equalities and whatever
    /// branch-local hypothesis the case split is currently exploring,
    /// exactly as the task's design calls for ("Reuse
    /// `check_dt_acyclicity`'s existing union-find + DFS cycle-detection
    /// machinery as a subroutine").
    fn cycle_exists_given(
        &self,
        dt_var_equalities: &[(TermId, TermId)],
        var_ctor_term_eqs: &[(TermId, TermId)],
        ctor_terms: &[(TermId, Vec<TermId>)],
        manager: &TermManager,
    ) -> bool {
        // --- Union-Find over TermId (path compression; inputs are tiny, no
        // union-by-rank needed). ---
        fn find(parent: &mut FxHashMap<TermId, TermId>, x: TermId) -> TermId {
            let p = *parent.entry(x).or_insert(x);
            if p == x {
                x
            } else {
                let root = find(parent, p);
                parent.insert(x, root);
                root
            }
        }
        fn union(parent: &mut FxHashMap<TermId, TermId>, a: TermId, b: TermId) {
            let ra = find(parent, a);
            let rb = find(parent, b);
            if ra != rb {
                parent.insert(ra, rb);
            }
        }

        let mut parent: FxHashMap<TermId, TermId> = FxHashMap::default();
        for &(a, b) in dt_var_equalities {
            union(&mut parent, a, b);
        }
        for &(v, c) in var_ctor_term_eqs {
            union(&mut parent, v, c);
        }

        // --- Directed containment graph over equivalence-class roots. ---
        let mut adj: FxHashMap<TermId, Vec<TermId>> = FxHashMap::default();
        for (t, args) in ctor_terms {
            let src = find(&mut parent, *t);
            for &a in args {
                let Some(a_sort) = manager.get(a).map(|d| d.sort) else {
                    continue;
                };
                if !manager.sorts.is_datatype(a_sort) {
                    // Only a datatype-sorted argument can carry a
                    // well-foundedness cycle (an Int/Bool/etc. field is not
                    // itself a datatype value).
                    continue;
                }
                let dst = find(&mut parent, a);
                adj.entry(src).or_default().push(dst);
            }
        }

        // --- Cycle detection: iterative white/gray/black DFS. A GRAY node
        // reached again (a back-edge to a node still on the current path) is
        // exactly a directed cycle. ---
        #[derive(Clone, Copy, PartialEq, Eq)]
        enum Color {
            White,
            Gray,
            Black,
        }
        let mut color: FxHashMap<TermId, Color> = FxHashMap::default();
        let starts: Vec<TermId> = adj.keys().copied().collect();
        for start in starts {
            if color.get(&start).copied().unwrap_or(Color::White) != Color::White {
                continue;
            }
            let mut path: Vec<(TermId, usize)> = vec![(start, 0)];
            color.insert(start, Color::Gray);
            while let Some(&(node, idx)) = path.last() {
                let next_child = adj.get(&node).and_then(|c| c.get(idx)).copied();
                match next_child {
                    Some(child) => {
                        path.last_mut().unwrap().1 += 1;
                        match color.get(&child).copied().unwrap_or(Color::White) {
                            Color::White => {
                                color.insert(child, Color::Gray);
                                path.push((child, 0));
                            }
                            Color::Gray => {
                                // Back-edge to an ancestor on the current
                                // path => a real cycle through asserted
                                // constructor-argument containment.
                                return true;
                            }
                            Color::Black => {
                                // Already fully explored via another path —
                                // not a cycle by itself.
                            }
                        }
                    }
                    None => {
                        color.insert(node, Color::Black);
                        path.pop();
                    }
                }
            }
        }

        false
    }

    /// #418 item 3 — OR-branch cyclic disjunction case-split detection.
    ///
    /// Generalizes the flat, globally-unconditional equality check above
    /// (`check_dt_acyclicity`) into a genuine recursive per-branch
    /// entailment evaluator: the current assertion set can force a datatype
    /// acyclicity conflict even when NO single equality is unconditionally
    /// true, as long as EVERY way of making the assertions true (i.e. every
    /// combination of disjunct choices across every `Or`/negated-`And` case
    /// split) independently forces a cycle. Minimal motivating example:
    /// `(assert (or (= y (cons x y)) (and (= y (cons x z)) (= z (cons x
    /// y)))))` — neither disjunct is unconditionally true, but BOTH force a
    /// cycle through `y`, so the whole assertion does too.
    ///
    /// # Design
    ///
    /// The current assertion set is implicitly one big conjunction, so this
    /// drives a single work-list evaluator (`dt_items_force_conflict`) over
    /// `self.assertions` (each assertion starts at `ctx = true`, i.e.
    /// "asserted true"). The evaluator processes a work-list of `(TermId,
    /// bool)` pairs — `(term, "is this term currently required to be true
    /// (true) or false (false)")` — one item at a time, POPPING the front
    /// and, depending on the popped term's shape, either splicing replacement
    /// items back onto the (still-to-process) rest of the list, extending
    /// the accumulated hypothesis, or (for a genuine case split) branching:
    ///
    /// - `Not(inner)` at `(t, ctx)`: replace with `(inner, !ctx)` — flip and
    ///   continue (no hypothesis change), mirroring
    ///   `collect_dt_constraints_v2`'s existing `Not` handling exactly.
    /// - `And(children)` at `ctx == true`, or `Or(children)` at `ctx ==
    ///   false` (a **conjunctive** node — De Morgan makes `¬(A∨B) ≡
    ///   ¬A∧¬B`, exactly `collect_dt_constraints_v2`'s existing recursion
    ///   rule): splice `children` (each at the SAME `ctx`) in place of this
    ///   item and continue with the combined list. This is the "extend the
    ///   hypothesis set and recurse" half of the task's spec, expressed
    ///   incrementally: rather than eagerly flattening first, the work-list
    ///   just keeps walking, so the hypothesis grows lazily as each leaf
    ///   equality is reached — an equivalent result to eager flattening, via
    ///   the exact same recursion the existing flat collector already
    ///   trusts.
    /// - `Or(children)` at `ctx == true`, or `And(children)` at `ctx ==
    ///   false` (a genuinely **disjunctive** node — the NEW case;
    ///   `collect_dt_constraints_v2` deliberately contributes nothing here):
    ///   a real case split. The whole remaining conjunction (this node plus
    ///   everything still left on the work-list) is conflict-forced only if
    ///   EVERY branch `b` of `children`, substituted for this item (at the
    ///   SAME `ctx` — `Or`/true picks a disjunct that is true, `And`/false
    ///   picks a disjunct that is false, so recursion continues under the
    ///   identical polarity), independently forces a conflict. Because each
    ///   branch simply CONTINUES processing the same rest-of-work-list under
    ///   its own extended hypothesis, sibling/nested disjunctions naturally
    ///   compose via full cross-product recursion — e.g. an `And` of two
    ///   `Or`s recurses into the SECOND `Or`'s own branching once inside
    ///   each branch of the FIRST, requiring all 2×2 combinations to
    ///   conflict — with no special-casing needed.
    /// - Anything else (a leaf w.r.t. the Boolean skeleton — `Eq`,
    ///   `DtTester`, or any other term kind): delegate straight to
    ///   `collect_dt_constraints_v2` on just this ONE node (which, being a
    ///   non-recursing kind from that function's point of view, does exactly
    ///   one thing: record whatever `dt_var_equalities`/`var_ctor_term_eqs`/
    ///   `sel_eqs` (#419 — see below) contribution this single node makes at
    ///   this `ctx`, if any) to extend the hypothesis, then continue with
    ///   the rest of the work-list. (`collect_dt_constraints_v2`'s other
    ///   outputs, e.g. `constructor_testers`, are collected into throwaway
    ///   maps — out of scope here, see below.)
    ///
    /// # #419 — equality closure wiring
    ///
    /// The three per-branch hypothesis slices (`h_var`, `h_ctor`, and now
    /// `h_sel` — the raw `sel(t) = t2` facts `collect_dt_constraints_v2`
    /// contributes per leaf, previously discarded here) are CLOSED via
    /// `compute_dt_equality_closure` exactly once, at the SAME point the
    /// (pre-#419) code already called `cycle_exists_given` — i.e. only when
    /// the work-list is fully exhausted for THIS particular combination of
    /// branch choices, never at every intermediate And/Or/Not node. This
    /// mirrors the existing "check only at the leaf" discipline and means
    /// the (non-trivial) closure fixpoint runs at most once per LEAF of the
    /// case-split search tree, not once per node visited while walking down
    /// to it.
    ///
    /// This closes both #419 items for the OR-branch path too: a branch
    /// whose hypothesis needs an item-1 (injectivity-transitivity) or item-2
    /// (selector-resolution-derived) fact to complete its own cycle is now
    /// detected, exactly as the flat (non-OR) acyclicity check in
    /// `check_dt_constraints` already was after that phase's landing.
    ///
    /// **Branch isolation.** `h_var`/`h_ctor`/`h_sel` are threaded by VALUE
    /// (cloned, never a shared mutable reference) through the recursion —
    /// the same discipline #418's own adversarial-verification report
    /// confirmed for `h_var`/`h_ctor` ("clones h_var/h_ctor per branch with
    /// no cross-contamination") continues to hold for `h_sel` and,
    /// therefore, for the CLOSURE computed FROM them: `compute_dt_equality_
    /// closure` is a pure function of whatever hypothesis slice a given leaf
    /// call happens to hold, so two sibling branches (or a branch and its
    /// unrelated sibling under an enclosing `And`) can never see each
    /// other's derived facts — each leaf gets its own from-scratch closure
    /// over only ITS OWN accumulated hypothesis.
    ///
    /// **Budget.** The closure computation is NOT given its own fresh
    /// `DT_CLOSURE_STEP_BUDGET`-sized pool here — it is handed the SAME
    /// `&mut u32 budget` already threading through every `dt_items_force_conflict`
    /// call (the one bounding work-list pop-steps at
    /// `DT_OR_CASE_SPLIT_BUDGET` total), so closure-fixpoint rounds run at
    /// EVERY leaf draw from that one shared pool alongside the pop-steps.
    /// This is what keeps the OVERALL search bounded even though a
    /// combinatorial case-split can reach many leaves, each now doing
    /// nontrivial extra work: the total of (pops + all closures' fixpoint
    /// rounds, across every leaf visited) can never exceed
    /// `DT_OR_CASE_SPLIT_BUDGET`, rather than that budget applying only to
    /// pops while closures separately got `DT_CLOSURE_STEP_BUDGET` EACH
    /// (which could multiply the two budgets together in the worst case).
    /// Exceeding the shared budget mid-closure has the identical safe
    /// semantics as everywhere else in this file: the search (or, here, one
    /// leaf's closure) simply stops early, which can only make the overall
    /// check MISS a conflict, never fabricate one.
    /// - An empty work-list means every conjunct has been walked: first
    ///   close the FULLY accumulated branch-local hypothesis
    ///   (`h_var`/`h_ctor`/`h_sel`) via `compute_dt_equality_closure` — see
    ///   "#419 — equality closure wiring" below — then check the CLOSED
    ///   result for a cycle via `cycle_exists_given` (the exact same
    ///   union-find+DFS subroutine `check_dt_acyclicity` uses), parameterized
    ///   by the SAME unconditional `ctor_terms` structural walk (computed
    ///   ONCE up front, since it never depends on which branch is chosen —
    ///   see `build_dt_ctor_terms`'s doc comment).
    ///
    /// # Scope: acyclicity + disequality (#422 — no longer acyclicity-only)
    ///
    /// Originally (through `#419`) this generalized ONLY the acyclicity
    /// conflict signal (a manifest cycle through constructor-argument
    /// containment). `#422` item 1 extended the leaf check to ALSO fire on
    /// a forced-disequality conflict (`closure.
    /// forces_disequality_conflict(h_diseq)` — see "#422 — beyond
    /// acyclicity-only" above), since a branch can be internally
    /// contradictory via constructor injectivity forcing an equality that
    /// contradicts an asserted `distinct`/`(not (= ..))` in the SAME
    /// branch, a DIFFERENT conflict family than acyclicity. This still does
    /// NOT additionally case-split-check the constructor-tester /
    /// constructor-equality conflict families checked earlier in
    /// `check_dt_constraints` (e.g. "does every branch force a `(is C1 x)`
    /// vs. `(is C2 x)` clash") — `#418` explicitly called extending that far
    /// a bonus, not the required minimum, and `#422` did not revisit that
    /// boundary either. Combining tester/equality conflicts with this same
    /// case-split machinery remains a documented, not-attempted boundary.
    ///
    /// # Scope: cross-theory case splits
    ///
    /// Only a Boolean-skeleton `Or`/`And`/`Not` is treated as case-split
    /// structure. An arithmetic disjunction that only INDIRECTLY implies a
    /// datatype equality (e.g. two arithmetic branches that each happen to
    /// pin down a shared integer-sorted selector value in a way that, when
    /// combined with OTHER asserted facts, would force a datatype equality)
    /// is out of scope — per `#418`'s own text, that needs live
    /// SAT-trail-integrated theory propagation, a fundamentally bigger
    /// change than this one-shot, once-per-check-sat structural evaluator.
    ///
    /// # Termination / blowup guard
    ///
    /// The work-list only ever splices in already-existing subterms
    /// (bounded by the assertion set's own finite AST size for the
    /// conjunctive/leaf cases), but disjunctive case-splits multiply
    /// combinatorially when several independent `Or`s are effectively ANDed
    /// together (the cross-product behavior above is intentional — it is
    /// exactly what makes the "AND of two ORs" case work). As a pragmatic
    /// safety valve against a pathological/adversarial input — NEVER a
    /// soundness concern either way, since exceeding the budget just returns
    /// `false` ("no conflict found," always the safe direction) — a bounded
    /// step counter aborts the search past `DT_OR_CASE_SPLIT_BUDGET` total
    /// work-list-pop steps.
    pub(super) fn check_dt_or_case_split_conflict(&self, manager: &TermManager) -> bool {
        let ctor_terms = self.build_dt_ctor_terms(manager);
        let items: Vec<(TermId, bool)> = self.assertions.iter().map(|&a| (a, true)).collect();
        let mut budget: u32 = DT_OR_CASE_SPLIT_BUDGET;
        self.dt_items_force_conflict(
            &items, &[], &[], &[], &[], manager, &ctor_terms, &mut budget,
        )
    }

    /// Work-list step of the `#418` item 3 evaluator — see
    /// `check_dt_or_case_split_conflict`'s doc comment for the full design,
    /// including "#419 — equality closure wiring" for `h_sel` and the
    /// leaf-time `compute_dt_equality_closure` call.
    ///
    /// # #422 — beyond acyclicity-only
    ///
    /// Previously this evaluator's leaf ONLY checked the closed hypothesis
    /// for an acyclicity conflict (`cycle_exists_given`) — a branch
    /// internally contradictory for a DIFFERENT reason (e.g. constructor
    /// injectivity forcing `a=c` while `a≠c` is also asserted in the SAME
    /// branch) was invisible to it. `h_diseq` (the NEW fourth hypothesis
    /// slice, threaded by VALUE through every recursive call exactly like
    /// `h_var`/`h_ctor`/`h_sel` — same branch-isolation discipline, cloned
    /// per branch, never a shared mutable reference) accumulates every
    /// disequality-source pair (`dt_diseq_pairs`) each leaf contributes; the
    /// leaf now also checks `closure.forces_disequality_conflict(h_diseq)`.
    fn dt_items_force_conflict(
        &self,
        items: &[(TermId, bool)],
        h_var: &[(TermId, TermId)],
        h_ctor: &[(TermId, TermId)],
        h_sel: &[(TermId, TermId)],
        h_diseq: &[(TermId, TermId)],
        manager: &TermManager,
        ctor_terms: &[(TermId, Vec<TermId>)],
        budget: &mut u32,
    ) -> bool {
        if *budget == 0 {
            // Safety valve only — never claims a conflict past this point,
            // so exceeding the budget can only make us MISS a conflict
            // (stay sat/unknown), never fabricate one.
            return false;
        }
        *budget -= 1;

        let Some((&(t, ctx), rest)) = items.split_first() else {
            // Fully assembled hypothesis for this combination of branch
            // choices — #419: close it (item 1 same-constructor-binding
            // ctor=ctor derivations + item 2 selector-resolution
            // derivations) before checking for a cycle, so a branch whose
            // conflict only becomes visible after closing its OWN hypothesis
            // is detected too. `budget` is deliberately reused (not a fresh
            // `DT_CLOSURE_STEP_BUDGET` pool) so pop-steps and closure-fixpoint
            // steps draw from the SAME shared total-work bound — see the
            // "#419 — equality closure wiring" doc section above.
            let closure = self.compute_dt_equality_closure(h_var, h_ctor, h_sel, manager, budget);
            // #422 — acyclicity OR a forced disequality conflict, whichever
            // this branch's closed hypothesis exhibits (see this function's
            // "#422 — beyond acyclicity-only" doc section above).
            return self.cycle_exists_given(&closure.closed_eqs, &[], ctor_terms, manager)
                || closure.forces_disequality_conflict(h_diseq);
        };

        let Some(td) = manager.get(t) else {
            return self.dt_items_force_conflict(
                rest, h_var, h_ctor, h_sel, h_diseq, manager, ctor_terms, budget,
            );
        };

        match &td.kind {
            TermKind::Not(inner) => {
                let mut new_items = Vec::with_capacity(rest.len() + 1);
                new_items.push((*inner, !ctx));
                new_items.extend_from_slice(rest);
                self.dt_items_force_conflict(
                    &new_items, h_var, h_ctor, h_sel, h_diseq, manager, ctor_terms, budget,
                )
            }
            TermKind::And(children) if ctx => {
                // Conjunctive: all children are asserted true too.
                let mut new_items = Vec::with_capacity(rest.len() + children.len());
                new_items.extend(children.iter().map(|&c| (c, true)));
                new_items.extend_from_slice(rest);
                self.dt_items_force_conflict(
                    &new_items, h_var, h_ctor, h_sel, h_diseq, manager, ctor_terms, budget,
                )
            }
            TermKind::Or(children) if !ctx => {
                // Conjunctive (De Morgan): all children are asserted false too.
                let mut new_items = Vec::with_capacity(rest.len() + children.len());
                new_items.extend(children.iter().map(|&c| (c, false)));
                new_items.extend_from_slice(rest);
                self.dt_items_force_conflict(
                    &new_items, h_var, h_ctor, h_sel, h_diseq, manager, ctor_terms, budget,
                )
            }
            TermKind::Or(children) if ctx => {
                // Disjunctive case split: EVERY branch must independently
                // force a conflict (combined with the unchanged rest of the
                // work-list) for the whole thing to be conflict-forced.
                children.iter().all(|&b| {
                    let mut new_items = Vec::with_capacity(rest.len() + 1);
                    new_items.push((b, true));
                    new_items.extend_from_slice(rest);
                    self.dt_items_force_conflict(
                        &new_items, h_var, h_ctor, h_sel, h_diseq, manager, ctor_terms, budget,
                    )
                })
            }
            TermKind::And(children) if !ctx => {
                // Disjunctive case split (De Morgan — ¬(A∧B) ≡ ¬A∨¬B): EVERY
                // branch (negated) must independently force a conflict.
                children.iter().all(|&b| {
                    let mut new_items = Vec::with_capacity(rest.len() + 1);
                    new_items.push((b, false));
                    new_items.extend_from_slice(rest);
                    self.dt_items_force_conflict(
                        &new_items, h_var, h_ctor, h_sel, h_diseq, manager, ctor_terms, budget,
                    )
                })
            }
            _ => {
                // A leaf w.r.t. the Boolean skeleton (`Eq`, `DtTester`, or
                // anything else): delegate to the audited single-node
                // extraction already in `collect_dt_constraints_v2` — it
                // does not recurse into further Boolean structure for these
                // kinds, so calling it on just `t` extracts exactly this
                // node's own contribution (if any) and nothing more.
                let mut throwaway_pos_testers: FxHashMap<TermId, Vec<String>> =
                    FxHashMap::default();
                let mut throwaway_neg_testers: FxHashMap<TermId, Vec<String>> =
                    FxHashMap::default();
                let mut throwaway_ctor_eqs: FxHashMap<TermId, Vec<String>> = FxHashMap::default();
                let mut throwaway_neg_ctor_eqs: FxHashMap<TermId, Vec<String>> =
                    FxHashMap::default();
                let mut new_var_eqs: Vec<(TermId, TermId)> = Vec::new();
                let mut new_ctor_eqs: Vec<(TermId, TermId)> = Vec::new();
                // #419 item 2 — this leaf's own raw `sel(t) = t2` fact
                // contribution (if any), now THREADED into `h_sel` (no
                // longer discarded) so the leaf-time closure call above can
                // resolve it once the rest of this branch's hypothesis is
                // known.
                let mut new_sel_eqs: Vec<(TermId, TermId)> = Vec::new();
                // #422 item 3 — this leaf's own `C(..) = D(..)` ctor-ctor
                // contribution (if any); folded into `h_ctor2` below (the
                // SAME accumulator `var_ctor_term_eqs`-shaped facts use — no
                // separate persistent thread needed, mirroring the flat-path
                // call sites' `.extend()` merge).
                let mut new_ctor_ctor_eqs: Vec<(TermId, TermId)> = Vec::new();
                // #422 items 1+2 — this leaf's own disequality-source
                // contribution (if any); THIS one DOES need its own
                // persistent thread (`h_diseq`), since it is not folded into
                // `var_ctor_term_eqs`/`compute_dt_equality_closure` at all —
                // it is consumed separately by `forces_disequality_conflict`.
                let mut new_diseq_pairs: Vec<(TermId, TermId)> = Vec::new();
                self.collect_dt_constraints_v2(
                    t,
                    manager,
                    &mut throwaway_pos_testers,
                    &mut throwaway_neg_testers,
                    &mut throwaway_ctor_eqs,
                    &mut throwaway_neg_ctor_eqs,
                    &mut new_var_eqs,
                    &mut new_ctor_eqs,
                    &mut new_sel_eqs,
                    &mut new_ctor_ctor_eqs,
                    &mut new_diseq_pairs,
                    ctx,
                );
                // #422 — extend the early-return emptiness check to ALSO
                // cover the two new lists: a leaf whose ONLY contribution is
                // a disequality/ctor-ctor fact (no var/ctor/sel fact at all)
                // must still extend the hypothesis, not be silently dropped.
                if new_var_eqs.is_empty()
                    && new_ctor_eqs.is_empty()
                    && new_sel_eqs.is_empty()
                    && new_ctor_ctor_eqs.is_empty()
                    && new_diseq_pairs.is_empty()
                {
                    self.dt_items_force_conflict(
                        rest, h_var, h_ctor, h_sel, h_diseq, manager, ctor_terms, budget,
                    )
                } else {
                    let mut h_var2 = h_var.to_vec();
                    h_var2.extend(new_var_eqs);
                    let mut h_ctor2 = h_ctor.to_vec();
                    h_ctor2.extend(new_ctor_eqs);
                    // #422 item 3 — fold this leaf's ctor-ctor facts into the
                    // SAME `var_ctor_term_eqs`-shaped accumulator
                    // `compute_dt_equality_closure` consumes as `h_ctor`.
                    h_ctor2.extend(new_ctor_ctor_eqs);
                    let mut h_sel2 = h_sel.to_vec();
                    h_sel2.extend(new_sel_eqs);
                    let mut h_diseq2 = h_diseq.to_vec();
                    h_diseq2.extend(new_diseq_pairs);
                    self.dt_items_force_conflict(
                        rest, &h_var2, &h_ctor2, &h_sel2, &h_diseq2, manager, ctor_terms, budget,
                    )
                }
            }
        }
    }

    /// #418 item 2 — build a TRANSITIVELY-CLOSED variable→constructor-
    /// application binding map for the CURRENT check-sat's assertion set, for
    /// use by `encode.rs::resolve_dt_normal_form` (via
    /// `Solver::add_dt_indirect_var_reduction_axioms`, called once per
    /// check-sat from `mod.rs::check_level`).
    ///
    /// Reuses the exact same `collect_dt_constraints_v2` collector (and
    /// hence the exact same positive/negative polarity gating already
    /// proven correct by the acyclicity check in this file, `#406`) to
    /// gather:
    ///   - `dt_var_equalities`: pairs of DATATYPE VARIABLES asserted equal
    ///     (`x = y`), unconditionally/globally positive (Or-branch-local
    ///     equalities are NEVER collected here — see the collector's own
    ///     doc comments for the And/Or/Not polarity threading that
    ///     guarantees this);
    ///   - `var_ctor_term_eqs`: a DATATYPE VARIABLE asserted equal to a
    ///     manifest `DtConstructor` application (`x = C(args…)`), same
    ///     polarity gating.
    ///
    /// Then closes `dt_var_equalities` under union-find (so a chain `w = z,
    /// z = C(...)` binds `w` too, transitively, no matter how many plain
    /// variable-to-variable hops away — this is what lets
    /// `resolve_dt_normal_form` handle the "chain of plain equalities"
    /// soundness-control case from #418's verification plan) and, for every
    /// union-find class that contains at least one `var_ctor_term_eqs`
    /// binding, maps EVERY variable in that class to that binding's
    /// constructor term. (If a class somehow has more than one distinct
    /// binding — e.g. `x = C(a,b)` and `x = C(c,d)` where `a≠c` as terms —
    /// picking either is sound: this map is only a HINT for reduction, not a
    /// source of truth, and the two bindings are already provably equal via
    /// constructor injectivity/EUF congruence handled elsewhere; conflicting
    /// DIFFERENTLY-NAMED constructors for the same class are already caught
    /// as a ground conflict by `check_dt_constraints` itself, which always
    /// runs before this map is even consulted.)
    ///
    /// Rebuilt from scratch every call (idempotent, no incremental state of
    /// its own to desync) — callers key their own trail-undo on the SAT
    /// clauses THEY inject from this map (see
    /// `add_dt_indirect_var_reduction_axioms`'s doc comment), never on this
    /// map's contents, which is why rebuilding it fresh every check-sat is
    /// always safe regardless of push/pop history.
    ///
    /// #419 — now RETURNS the full [`DtEqualityClosure`] (not just the
    /// picked-one-per-class map its name still describes): the closure
    /// subsumes the old first-wins union-find exactly (a class with a single
    /// distinct ctor binding degenerates to the same `primary_bindings`
    /// entry this function always produced), while ALSO exposing the
    /// injectivity-transitivity (item 1) and selector-chase-derived (item 2)
    /// facts the old version silently dropped. See
    /// `compute_dt_equality_closure`'s doc comment for the algorithm.
    pub(super) fn collect_var_ctor_bindings(&self, manager: &TermManager) -> DtEqualityClosure {
        let mut constructor_testers: FxHashMap<TermId, Vec<String>> = FxHashMap::default();
        let mut negative_testers: FxHashMap<TermId, Vec<String>> = FxHashMap::default();
        let mut constructor_equalities: FxHashMap<TermId, Vec<String>> = FxHashMap::default();
        let mut negative_ctor_equalities: FxHashMap<TermId, Vec<String>> = FxHashMap::default();
        let mut dt_var_equalities: Vec<(TermId, TermId)> = Vec::new();
        let mut var_ctor_term_eqs: Vec<(TermId, TermId)> = Vec::new();
        let mut sel_eqs: Vec<(TermId, TermId)> = Vec::new();
        // #422 item 3 — merged into `var_ctor_term_eqs` below before the
        // closure call (see `check_dt_constraints`'s analogous merge for the
        // full rationale).
        let mut dt_ctor_ctor_eqs: Vec<(TermId, TermId)> = Vec::new();
        // #422 items 1+2 — this call site (SAT-level axiom-injection feed,
        // not a conflict check) has no use for the disequality-source pairs;
        // collected only because `collect_dt_constraints_v2` requires the
        // out-param, then discarded.
        let mut dt_diseq_pairs: Vec<(TermId, TermId)> = Vec::new();

        for &assertion in &self.assertions {
            self.collect_dt_constraints_v2(
                assertion,
                manager,
                &mut constructor_testers,
                &mut negative_testers,
                &mut constructor_equalities,
                &mut negative_ctor_equalities,
                &mut dt_var_equalities,
                &mut var_ctor_term_eqs,
                &mut sel_eqs,
                &mut dt_ctor_ctor_eqs,
                &mut dt_diseq_pairs,
                true,
            );
        }
        var_ctor_term_eqs.extend(dt_ctor_ctor_eqs);

        let mut closure_budget = DT_CLOSURE_STEP_BUDGET;
        self.compute_dt_equality_closure(
            &dt_var_equalities,
            &var_ctor_term_eqs,
            &sel_eqs,
            manager,
            &mut closure_budget,
        )
    }

    /// #419 items 1 & 2 — the shared iterative equality/binding closure that
    /// underlies both the injectivity-transitivity fix (item 1) and the
    /// acyclicity/`resolve_dt_normal_form` composition fix (item 2).
    ///
    /// # Inputs
    ///
    /// All three inputs are the SAME collections `check_dt_constraints`'s
    /// acyclicity check and the old `collect_var_ctor_bindings` already
    /// trusted, unmodified: `base_var_eqs` (`dt_var_equalities`, DT
    /// variable-to-variable equalities), `base_ctor_bindings`
    /// (`var_ctor_term_eqs`, DT variable-to-manifest-constructor-application
    /// equalities), and `base_sel_eqs` (raw `sel(t) = t2` facts, #419 item
    /// 2's new collection). All three are already filtered to
    /// genuinely-asserted-POSITIVE facts by `collect_dt_constraints_v2`'s
    /// existing And/Or/Not polarity threading — the closure below does NO
    /// polarity reasoning of its own, it only ever combines/derives from
    /// facts already known to hold unconditionally.
    ///
    /// #422 item 3 — every call site now merges `dt_ctor_ctor_eqs` (direct
    /// `C(..) = D(..)` equalities with NO mediating variable at all) into
    /// `base_ctor_bindings` via `.extend()` BEFORE calling this function.
    /// This function's OWN signature is deliberately UNCHANGED: both
    /// `base_var_eqs` and `base_ctor_bindings` were already treated
    /// IDENTICALLY inside it (`eqs.extend_from_slice(...)` for both, see
    /// the loop below) — a "variable-to-ctor" binding is just one more
    /// generic `(TermId, TermId)` equality pair to this closure, so folding
    /// in a ctor-to-ctor pair the exact same way is exact, not an
    /// approximation, and needs no new parameter.
    ///
    /// #422 items 1+2's `dt_diseq_pairs` (disequality-source facts from a
    /// negative `Eq` between two datatype-sorted terms, or a positive 2-ary
    /// `distinct`) are DELIBERATELY NOT an input here — they are consumed
    /// separately, downstream of this closure's OUTPUT, by
    /// `DtEqualityClosure::forces_disequality_conflict`. This closure's own
    /// job remains exactly what it always was: derive every SOUND
    /// consequence of the base equalities. Whether any of those derived
    /// equalities happens to CONTRADICT a separately-asserted disequality is
    /// a different question, answered by the caller after this function
    /// returns.
    ///
    /// # Algorithm (iterative fixpoint)
    ///
    /// Maintains one growing list `eqs` of generic `(TermId, TermId)` pairs,
    /// seeded with `base_var_eqs ++ base_ctor_bindings` (a "ctor binding"
    /// `(v, c)` IS itself just an equality `v = c`, so folding both into one
    /// list is exact, not an approximation). Each round:
    ///
    ///   a. Union-find over the CURRENT `eqs` (freshly rebuilt every round,
    ///      so a fact derived THIS round is visible to steps (b)/(c) starting
    ///      NEXT round — a fixpoint over "one rule-application pass" is
    ///      equivalent to eagerly propagating within a round, just possibly a
    ///      few extra (bounded) iterations, which is fine given the
    ///      step-budget below).
    ///   b. **Item 1**: group every term with kind `DtConstructor` appearing
    ///      anywhere in `eqs` by its class root. For any two DISTINCT such
    ///      terms in the SAME class sharing the SAME constructor NAME (a
    ///      class can easily hold 2+ once several separate assertions each
    ///      bind the same variable — or two variables later found equal — to
    ///      their OWN ctor application), add the equality `c1 = c2` between
    ///      the ctor terms THEMSELVES. This is always a SOUND consequence:
    ///      `v = c1 ∧ v = c2 ⊢ c1 = c2` by ordinary equality transitivity,
    ///      true regardless of what `c1`/`c2` even denote. Two bindings to
    ///      DIFFERENT constructor names are deliberately NOT unioned or
    ///      otherwise acted on here — that is a direct ground conflict
    ///      already caught elsewhere (the name-keyed cross-checks earlier in
    ///      `check_dt_constraints`), not this closure's job to duplicate.
    ///      `encode.rs::add_dt_multi_binding_selector_reduction_axioms`
    ///      SEPARATELY re-runs the audited selector-reduction walk per extra
    ///      binding to produce ACTUAL SAT-level ground facts for a formula
    ///      that mentions a selector — this closure's OWN copy of the same
    ///      derivation (step (b2) below) exists for a different consumer:
    ///      the STATIC pre-solving acyclicity check (`check_dt_acyclicity`
    ///      via `check_dt_constraints`, and `dt_items_force_conflict`'s
    ///      per-branch cycle check), which never reaches the SAT solver at
    ///      all when it fires, so it cannot rely on that separate,
    ///      SAT-clause-level mechanism.
    ///   b2. **Item 1 follow-up — constructor injectivity, field-decomposed**
    ///      (found by this integration pass's own 1000-seed z3-differential
    ///      re-verification of the already-landed items above, NOT part of
    ///      the original #419 task text): for the SAME `(c1, c2)` pair step
    ///      (b) just confirmed share a constructor — whether the whole-term
    ///      pair was freshly derived THIS round or came straight from
    ///      `base_ctor_bindings` in an EARLIER round — zip their argument
    ///      lists and add `args1[i] = args2[i]` for every field `i` where
    ///      the two differ. Without this, a same-constructor pair only ever
    ///      contributed an OPAQUE whole-term fact to `eqs`: invisible to
    ///      `cycle_exists_given`'s class-based edges (which key cycles off
    ///      which term-ARGUMENTS' classes coincide, not off opaque
    ///      container-level equalities) and invisible to a LATER round's own
    ///      step (c) (which needs a genuine per-field equality to chase a
    ///      selector through). E.g. `x = C(a, ...)` and `x = C(b, ...,
    ///      C(c, ..., a))` derives, on decomposition, `a = C(c, ..., a)` — a
    ///      direct well-foundedness cycle only reachable by first performing
    ///      THIS decomposition. Sound for the same reason step (b) itself is
    ///      (`C(x1..xn) = C(y1..yn)` denoting the SAME free-algebra value
    ///      forces `xi = yi` for every field — ordinary constructor
    ///      injectivity, the identical consequence
    ///      `DatatypeRewriter::rewrite_constructor_eq` already draws when a
    ///      ctor=ctor equality reaches the simplifier, drawn here too,
    ///      directly inside this closure's own abstract equality set).
    ///   c. **Item 2**: for each raw `(sel_term, other)` pair in
    ///      `base_sel_eqs` (destructuring `sel_term` as `DtSelector {
    ///      selector, arg }`), attempt `resolve_dt_normal_form(arg,
    ///      hint_map)` using a `hint_map` built from THIS round's classes (one
    ///      arbitrary — "primary" — ctor-term binding per class, mirroring
    ///      exactly what `resolve_dt_normal_form`'s contract expects). If
    ///      `arg` resolves to a manifest `C(args…)` and `selector` names one
    ///      of `C`'s own fields at index `i`, add the equality `args[i] =
    ///      other`. Sound for the identical reason `resolve_dt_normal_form`
    ///      itself is sound (a chain of congruence + the standard selector-
    ///      of-its-own-constructor axiom + transitivity with the raw fact) —
    ///      see that function's doc comment.
    ///
    /// Repeats a–c (through b2) until a round adds nothing new. Termination: `eqs` only
    /// ever grows by pairs drawn from a FINITE universe (`TermId` pairs
    /// bounded by the term arena's size), each added at most once (`seen_pairs`
    /// dedup), so the loop is bounded by the arena's size regardless of the
    /// budget below; the budget is a pure defensive safety valve (mirroring
    /// `DT_OR_CASE_SPLIT_BUDGET`'s spirit) against pathological/adversarial
    /// input, and exceeding it can only mean "stop deriving more" (an
    /// incomplete but always-safe outcome — the returned closure is simply a
    /// SUBSET of the true full closure, never a superset, so nothing
    /// spuriously conflicts).
    ///
    /// # Budget
    ///
    /// `budget` is an EXTERNALLY-owned step counter (see
    /// `DT_CLOSURE_STEP_BUDGET`'s doc comment for why this is a caller-
    /// supplied `&mut u32` rather than an internal constant): the two
    /// flat/once-per-check-sat call sites each pass a dedicated fresh
    /// `DT_CLOSURE_STEP_BUDGET`-sized counter, while the OR-branch
    /// case-split call site threads its OWN already-in-flight
    /// `DT_OR_CASE_SPLIT_BUDGET` work-list counter through instead, so
    /// closure-fixpoint rounds and case-split work-list pops draw from one
    /// shared total-work pool there. Either way, running out of budget mid-
    /// fixpoint just stops the loop early — same safe-subset guarantee as
    /// above.
    ///
    /// # Outputs
    ///
    /// See [`DtEqualityClosure`]'s field docs.
    pub(super) fn compute_dt_equality_closure(
        &self,
        base_var_eqs: &[(TermId, TermId)],
        base_ctor_bindings: &[(TermId, TermId)],
        base_sel_eqs: &[(TermId, TermId)],
        manager: &TermManager,
        budget: &mut u32,
    ) -> DtEqualityClosure {
        fn find(parent: &mut FxHashMap<TermId, TermId>, x: TermId) -> TermId {
            let p = *parent.entry(x).or_insert(x);
            if p == x {
                x
            } else {
                let root = find(parent, p);
                parent.insert(x, root);
                root
            }
        }
        fn union(parent: &mut FxHashMap<TermId, TermId>, a: TermId, b: TermId) {
            let ra = find(parent, a);
            let rb = find(parent, b);
            if ra != rb {
                parent.insert(ra, rb);
            }
        }
        fn canon(a: TermId, b: TermId) -> (TermId, TermId) {
            if a.raw() <= b.raw() {
                (a, b)
            } else {
                (b, a)
            }
        }
        fn ctor_name(manager: &TermManager, t: TermId) -> Option<String> {
            match manager.get(t).map(|d| &d.kind) {
                Some(TermKind::DtConstructor { constructor, .. }) => {
                    Some(manager.resolve_str(*constructor).to_string())
                }
                _ => None,
            }
        }
        // Post-landing follow-up (found by this session's own differential
        // re-verification, NOT part of the original #419 task text — see
        // `compute_dt_equality_closure`'s doc comment, "Step (b2)", for the
        // full story): extract a manifest `DtConstructor` application's own
        // argument list, owned (not borrowed), so step (b2) below can zip two
        // same-constructor terms' fields without fighting the borrow checker
        // over `manager.get(..)`'s temporary `Ref`.
        fn ctor_args(manager: &TermManager, t: TermId) -> Option<Vec<TermId>> {
            match manager.get(t).map(|d| &d.kind) {
                Some(TermKind::DtConstructor { args, .. }) => {
                    Some(args.iter().copied().collect())
                }
                _ => None,
            }
        }

        let mut eqs: Vec<(TermId, TermId)> =
            Vec::with_capacity(base_var_eqs.len() + base_ctor_bindings.len());
        eqs.extend_from_slice(base_var_eqs);
        eqs.extend_from_slice(base_ctor_bindings);

        let mut seen_pairs: FxHashSet<(TermId, TermId)> =
            eqs.iter().map(|&(a, b)| canon(a, b)).collect();
        let mut derived_ctor_eqs: Vec<(TermId, TermId)> = Vec::new();

        loop {
            if *budget == 0 {
                break;
            }
            *budget -= 1;
            let mut changed = false;

            let mut parent: FxHashMap<TermId, TermId> = FxHashMap::default();
            for &(a, b) in &eqs {
                union(&mut parent, a, b);
            }

            let mut terms_in_play: FxHashSet<TermId> = FxHashSet::default();
            for &(a, b) in &eqs {
                terms_in_play.insert(a);
                terms_in_play.insert(b);
            }

            // Group manifest ctor-application members by class root.
            let mut root_ctors: FxHashMap<TermId, Vec<TermId>> = FxHashMap::default();
            for &t in &terms_in_play {
                if matches!(
                    manager.get(t).map(|d| &d.kind),
                    Some(TermKind::DtConstructor { .. })
                ) {
                    let r = find(&mut parent, t);
                    let bucket = root_ctors.entry(r).or_default();
                    if !bucket.contains(&t) {
                        bucket.push(t);
                    }
                }
            }

            // --- Step (b): item 1 — same-constructor-name pairwise
            // equalities within one class. ---
            for terms in root_ctors.values() {
                if terms.len() < 2 {
                    continue;
                }
                for i in 0..terms.len() {
                    for j in (i + 1)..terms.len() {
                        let (c1, c2) = (terms[i], terms[j]);
                        let n1 = ctor_name(manager, c1);
                        if n1.is_none() || n1 != ctor_name(manager, c2) {
                            continue;
                        }
                        let key = canon(c1, c2);
                        if seen_pairs.insert(key) {
                            eqs.push(key);
                            derived_ctor_eqs.push(key);
                            changed = true;
                        }
                        // --- Step (b2), post-landing follow-up: constructor
                        // INJECTIVITY field decomposition. `c1`/`c2` are two
                        // manifest applications of the SAME constructor
                        // (`n1 == ctor_name(c2)` just above) found in one
                        // class, so `c1 = c2` (whether that whole-term pair
                        // was already known or is the one just pushed above)
                        // entails, field-by-field, `args1[k] = args2[k]` for
                        // every field `k` — ordinary constructor injectivity,
                        // exactly the same sound consequence
                        // `DatatypeRewriter::rewrite_constructor_eq` already
                        // draws when a ctor=ctor equality reaches the
                        // simplifier (see `inject_dt_derived_ctor_equalities`'s
                        // doc comment) — but drawn HERE too, directly inside
                        // the abstract equality set this closure computes,
                        // unconditionally (not gated behind `seen_pairs.
                        // insert(key)` above): a same-class pair from an
                        // EARLIER round (e.g. straight from `base_ctor_
                        // bindings`, already recorded before this closure
                        // ever ran) must still get its fields decomposed the
                        // FIRST time this loop is reached, not only when the
                        // whole-term pair itself is freshly discovered.
                        // Without this step, a derived/base same-constructor
                        // binding pair contributes only an OPAQUE whole-term
                        // fact to `eqs` — invisible to `cycle_exists_given`'s
                        // graph, which keys cycles off which term-arguments'
                        // classes coincide, and invisible to a LATER round's
                        // own selector-resolution step (c), both of which
                        // need the per-field equality itself, not just the
                        // container equality. (Confirmed load-bearing by a
                        // 1000-seed z3-differential re-run turning up exactly
                        // this composition gap post-landing — a 2-binding
                        // `x=C(a,...); x=C(b,...,C(c,...,x-again-shaped))`
                        // minimized repro whose forced field-level cycle was
                        // invisible without this step; see
                        // `dt_equality_closure_field_decomp_regression.rs`.)
                        if let (Some(a1), Some(a2)) = (ctor_args(manager, c1), ctor_args(manager, c2))
                        {
                            for (&fa, &fb) in a1.iter().zip(a2.iter()) {
                                if fa == fb {
                                    continue;
                                }
                                let fkey = canon(fa, fb);
                                if seen_pairs.insert(fkey) {
                                    eqs.push(fkey);
                                    changed = true;
                                }
                            }
                        }
                    }
                }
            }

            // --- Step (c): item 2 — selector-shaped equality resolution,
            // using ONE arbitrary ("primary") binding per class as this
            // round's resolution hint. ---
            let mut hint_map: FxHashMap<TermId, TermId> = FxHashMap::default();
            for (&root, terms) in &root_ctors {
                if let Some(&primary) = terms.first() {
                    for &t in &terms_in_play {
                        if t != primary && find(&mut parent, t) == root {
                            hint_map.insert(t, primary);
                        }
                    }
                }
            }

            let mut memo: FxHashMap<TermId, Option<TermId>> = FxHashMap::default();
            let mut in_progress: FxHashSet<TermId> = FxHashSet::default();
            for &(sel_term, other) in base_sel_eqs {
                let Some(td) = manager.get(sel_term) else {
                    continue;
                };
                let TermKind::DtSelector { selector, arg } = &td.kind else {
                    continue;
                };
                let selector = *selector;
                let arg = *arg;
                let Some(resolved_arg) = Solver::resolve_dt_normal_form(
                    arg,
                    &hint_map,
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
                    TermKind::DtConstructor { constructor, args } => {
                        (argd.sort, *constructor, args)
                    }
                    _ => continue,
                };
                let Some(layouts) = manager.sorts.datatype_ctor_layouts(dt_sort) else {
                    continue;
                };
                let cname = manager.resolve_str(constructor).to_string();
                let sname = manager.resolve_str(selector).to_string();
                let Some((_, fields)) = layouts.iter().find(|(c, _)| *c == cname) else {
                    continue;
                };
                let Some(idx) = fields.iter().position(|(s, _)| *s == sname) else {
                    continue;
                };
                let Some(&field_term) = ctor_args.get(idx) else {
                    continue;
                };
                if field_term == other {
                    continue;
                }
                let key = canon(field_term, other);
                if seen_pairs.insert(key) {
                    eqs.push(key);
                    changed = true;
                }
            }

            if !changed {
                break;
            }
        }

        // Final pass: derive `primary_bindings` (var -> one representative
        // ctor term per class, the same shape/contract the pre-#419 code
        // always returned) and `extra_by_class` (#419 item 1's wiring input
        // — every OTHER same-constructor binding beyond the primary one,
        // paired with every DT VARIABLE in that class so a selector/tester
        // applied to ANY synonym is covered).
        let mut parent: FxHashMap<TermId, TermId> = FxHashMap::default();
        for &(a, b) in &eqs {
            union(&mut parent, a, b);
        }
        let mut terms_in_play: FxHashSet<TermId> = FxHashSet::default();
        for &(a, b) in &eqs {
            terms_in_play.insert(a);
            terms_in_play.insert(b);
        }
        let mut root_ctors: FxHashMap<TermId, Vec<TermId>> = FxHashMap::default();
        for &t in &terms_in_play {
            if matches!(
                manager.get(t).map(|d| &d.kind),
                Some(TermKind::DtConstructor { .. })
            ) {
                let r = find(&mut parent, t);
                let bucket = root_ctors.entry(r).or_default();
                if !bucket.contains(&t) {
                    bucket.push(t);
                }
            }
        }

        let mut primary_bindings: FxHashMap<TermId, TermId> = FxHashMap::default();
        let mut extra_by_class: Vec<(Vec<TermId>, Vec<TermId>)> = Vec::new();
        for (&root, terms) in &root_ctors {
            // Deterministic ordering (by raw TermId) so which binding is
            // "primary" doesn't depend on FxHashMap iteration order —
            // doesn't affect soundness (any true binding is as good as any
            // other as a resolution hint), only reproducibility.
            let mut sorted_terms = terms.clone();
            sorted_terms.sort_by_key(|t| t.raw());
            let primary = sorted_terms[0];

            let mut class_vars: Vec<TermId> = Vec::new();
            for &t in &terms_in_play {
                if find(&mut parent, t) == root
                    && t != primary
                    && matches!(manager.get(t).map(|d| &d.kind), Some(TermKind::Var(_)))
                {
                    primary_bindings.insert(t, primary);
                    class_vars.push(t);
                }
            }

            if sorted_terms.len() > 1 && !class_vars.is_empty() {
                let extras: Vec<TermId> = sorted_terms[1..].to_vec();
                extra_by_class.push((class_vars, extras));
            }
        }

        DtEqualityClosure {
            closed_eqs: eqs,
            primary_bindings,
            extra_by_class,
            derived_ctor_eqs,
        }
    }
}

impl DtEqualityClosure {
    /// #422 STEP 5 — does this closure's fully-derived equality set force ANY
    /// of `diseq_pairs` to be equal? Consumed by `check_dt_constraints`'s
    /// flat pre-pass (STEP 6) and `dt_items_force_conflict`'s per-branch leaf
    /// check (items 1+2's non-cycle conflict signal).
    ///
    /// Builds ONE union-find over `self.closed_eqs` (the SAME find/union
    /// pattern `cycle_exists_given`/`compute_dt_equality_closure` already use,
    /// for consistency), then checks whether any `(a, b)` pair in
    /// `diseq_pairs` shares a root — i.e. whether the closure's OWN sound
    /// derivations entail `a = b` despite `a`/`b` having been asserted (or,
    /// for a positive `distinct`, implied) unequal. A pair that never
    /// appears in `closed_eqs` at all gets its own singleton root (via the
    /// union-find's `or_insert` default), so it can only ever report a
    /// conflict when the two sides are LITERALLY the same `TermId` or were
    /// genuinely unioned by a real, already-audited derivation — never a
    /// false positive.
    pub(super) fn forces_disequality_conflict(&self, diseq_pairs: &[(TermId, TermId)]) -> bool {
        fn find(parent: &mut FxHashMap<TermId, TermId>, x: TermId) -> TermId {
            let p = *parent.entry(x).or_insert(x);
            if p == x {
                x
            } else {
                let root = find(parent, p);
                parent.insert(x, root);
                root
            }
        }
        fn union(parent: &mut FxHashMap<TermId, TermId>, a: TermId, b: TermId) {
            let ra = find(parent, a);
            let rb = find(parent, b);
            if ra != rb {
                parent.insert(ra, rb);
            }
        }

        let mut parent: FxHashMap<TermId, TermId> = FxHashMap::default();
        for &(a, b) in &self.closed_eqs {
            union(&mut parent, a, b);
        }
        diseq_pairs
            .iter()
            .any(|&(a, b)| find(&mut parent, a) == find(&mut parent, b))
    }
}

impl Solver {
    /// #422 STEP 1 (pure refactor, no behavior change) — the positive body of
    /// the `Eq` arm below, extracted so #422's item 2 (`(not (distinct a b))`
    /// recognized as an equality) and item 3 (`dt_ctor_ctor_eqs`) can reuse
    /// the EXACT SAME polarity-correct logic instead of hand-duplicating it.
    ///
    /// Populates, for a POSITIVELY-asserted `lhs = rhs`:
    ///   - `constructor_equalities` / `var_ctor_term_eqs`: when exactly one
    ///     side is a manifest `DtConstructor` application and the other is a
    ///     DT variable.
    ///   - `dt_var_equalities`: when BOTH sides are DT variables.
    ///   - `sel_eqs`: when either side is a `DtSelector` application (#419
    ///     item 2 — no `is_dt_variable` gating on the other side, since the
    ///     point is to feed `compute_dt_equality_closure`'s iterative
    ///     resolution).
    ///   - `dt_ctor_ctor_eqs` (#422 item 3): when BOTH sides are manifest
    ///     `DtConstructor` applications (`C(..) = D(..)` with no mediating
    ///     variable) — previously invisible to every collection above,
    ///     since none of them fire unless at least one side is a variable.
    #[allow(clippy::too_many_arguments)]
    fn record_dt_positive_eq_fact(
        &self,
        lhs: TermId,
        rhs: TermId,
        manager: &TermManager,
        constructor_equalities: &mut FxHashMap<TermId, Vec<String>>,
        dt_var_equalities: &mut Vec<(TermId, TermId)>,
        var_ctor_term_eqs: &mut Vec<(TermId, TermId)>,
        sel_eqs: &mut Vec<(TermId, TermId)>,
        dt_ctor_ctor_eqs: &mut Vec<(TermId, TermId)>,
    ) {
        // Check for x = Constructor(...)
        if let Some(rhs_data) = manager.get(rhs) {
            if let TermKind::DtConstructor { constructor, .. } = &rhs_data.kind {
                if self.is_dt_variable(lhs, manager) {
                    constructor_equalities
                        .entry(lhs)
                        .or_default()
                        .push(manager.resolve_str(*constructor).to_string());
                    // #406 — also keep the actual constructor TERM
                    // id (not just its name) so the acyclicity
                    // check can union `lhs` into `rhs`'s
                    // argument graph.
                    var_ctor_term_eqs.push((lhs, rhs));
                }
            }
        }
        if let Some(lhs_data) = manager.get(lhs) {
            if let TermKind::DtConstructor { constructor, .. } = &lhs_data.kind {
                if self.is_dt_variable(rhs, manager) {
                    constructor_equalities
                        .entry(rhs)
                        .or_default()
                        .push(manager.resolve_str(*constructor).to_string());
                    var_ctor_term_eqs.push((rhs, lhs));
                }
            }
        }

        // Check for DT variable equality: x = y where both are DT variables
        if self.is_dt_variable(lhs, manager) && self.is_dt_variable(rhs, manager) {
            dt_var_equalities.push((lhs, rhs));
        }

        // #419 item 2 — also record a raw `sel(t) = t2` /
        // `t2 = sel(t)` fact whenever one operand is a
        // `DtSelector` application, with NO `is_dt_variable`
        // gating on the other side (unlike `var_ctor_term_eqs`
        // above): `compute_dt_equality_closure` is what decides,
        // iteratively, whether `t` (the selector's own argument)
        // ever becomes resolvable to a manifest constructor
        // application — that may only happen once OTHER derived
        // bindings have already landed, so this collector must
        // hand over the raw fact unconditionally and let the
        // closure do the (repeated) resolution attempts.
        if manager
            .get(lhs)
            .is_some_and(|d| matches!(d.kind, TermKind::DtSelector { .. }))
        {
            sel_eqs.push((lhs, rhs));
        }
        if manager
            .get(rhs)
            .is_some_and(|d| matches!(d.kind, TermKind::DtSelector { .. }))
        {
            sel_eqs.push((rhs, lhs));
        }

        // #422 item 3 — a direct `C(..) = D(..)` equality between two
        // NON-VARIABLE constructor applications (no mediating variable at
        // all) was previously invisible to every collection above. Always a
        // SOUND fact regardless of what `C`/`D` even denote (it's just the
        // literal asserted equality between the two terms themselves);
        // `compute_dt_equality_closure` decides what, if anything, follows
        // from it (same-constructor injectivity decomposition, or a direct
        // ground conflict if `C != D` — already caught elsewhere).
        if let (Some(lhs_data), Some(rhs_data)) = (manager.get(lhs), manager.get(rhs)) {
            if matches!(lhs_data.kind, TermKind::DtConstructor { .. })
                && matches!(rhs_data.kind, TermKind::DtConstructor { .. })
            {
                dt_ctor_ctor_eqs.push((lhs, rhs));
            }
        }
    }

    /// #422 STEP 1 (pure refactor, no behavior change) — the negative body of
    /// the `Eq` arm below (`#399`/`#404 phase 2`'s nullary-ctor-exclusion /
    /// tester-shape recognizer), extracted so #422's item 2 (`(distinct a
    /// b)`, a real disequality) can reuse the EXACT SAME polarity-correct
    /// logic instead of hand-duplicating it.
    ///
    /// A NEGATED equality `v ≠ c` (or, after #422, a positively-asserted
    /// `(distinct v c)`) to a NULLARY constructor excludes that whole
    /// constructor class (the nullary ctor's value is unique). A generic
    /// field-bearing ctor diseq excludes only one instance, so it is
    /// deliberately NOT collected — with ONE exception (#404 phase 2): the
    /// TESTER SHAPE `v ≠ C(sel_{C,0}(v), …, sel_{C,k}(v))` is exactly
    /// `¬is-C(v)` for ANY arity (rebuilding `v` from its own C-fields equals
    /// `v` iff `v` is C-shaped; a non-C `v` differs by constructor
    /// distinctness) — this is the very form the parser's recognizer
    /// desugar and the verus decreases-check guards emit. Record it as a
    /// negative TESTER, feeding the same injectivity + exhaustiveness
    /// reasoning; excluding ALL ctors this way is a ground conflict (z3
    /// parity).
    fn record_dt_negative_eq_fact(
        &self,
        v: TermId,
        c: TermId,
        manager: &TermManager,
        negative_ctor_equalities: &mut FxHashMap<TermId, Vec<String>>,
        negative_testers: &mut FxHashMap<TermId, Vec<String>>,
    ) {
        if !self.is_dt_variable(v, manager) {
            return;
        }
        let Some(cd) = manager.get(c) else { return };
        let TermKind::DtConstructor { constructor, args } = &cd.kind else {
            return;
        };
        let cons_name = manager.resolve_str(*constructor).to_string();
        if args.is_empty() {
            negative_ctor_equalities.entry(v).or_default().push(cons_name);
            return;
        }
        // Positional selector match: every argᵢ must be
        // `(sel_{C,i} v)` — the selector names come from the
        // SORT manager (datatype spurs live in ITS interner,
        // the #399 cross-interner lesson), the node spurs
        // from the term manager; compare resolved strings.
        let Some(vsort) = manager.get(v).map(|t| t.sort) else { return };
        let Some(sel_names) = manager.sorts.datatype_ctor_selectors(vsort, &cons_name) else {
            return;
        };
        if sel_names.len() != args.len() {
            return;
        }
        // A selector application reaches us either as the
        // dedicated `DtSelector` node or as a plain `Apply` of
        // the selector's (namespace-unique) function symbol —
        // the parser emits the latter for user-written
        // `(sel v)`. `datatype_ctor_selectors` already proved
        // `want` IS this ctor's selector for v's sort, so a
        // same-named unary Apply on exactly `v` is that
        // selector application.
        let tester_shape = args.iter().zip(sel_names.iter()).all(|(&a, want)| {
            manager.get(a).is_some_and(|ad| match &ad.kind {
                TermKind::DtSelector { selector, arg } => {
                    *arg == v && manager.resolve_str(*selector) == *want
                }
                TermKind::Apply { func, args } => {
                    args.len() == 1 && args[0] == v && manager.resolve_str(*func) == *want
                }
                _ => false,
            })
        });
        if tester_shape {
            negative_testers.entry(v).or_default().push(cons_name);
        }
    }

    /// #423 item 2 — nullary-constructor tester ⟺ equality derivation.
    ///
    /// `collect_dt_constraints_v2`'s `DtTester` arm previously ONLY
    /// accumulated constructor-name-tag strings into `constructor_testers`/
    /// `negative_testers` (used elsewhere for pairwise-tester-conflict and
    /// `#399`'s exhaustiveness checks) — it never derived an equality/
    /// disequality fact from a tester, regardless of arity. Called
    /// ALONGSIDE that existing bookkeeping (not in place of it).
    ///
    /// # Soundness
    ///
    /// A NULLARY constructor `C` (zero fields) has exactly ONE possible
    /// value, so `is-C(arg) ⟺ arg = C()` is a TRUE EQUIVALENCE, not merely
    /// an implication — `C()` is the unique value of shape `C`, and
    /// constructor injectivity/distinctness (already pervasively trusted by
    /// this file's `#419`/`#422` machinery) makes "not C-shaped" exactly
    /// "not equal to `C()`". This does NOT depend on exhaustiveness or any
    /// assumption beyond what `compute_dt_equality_closure` already trusts:
    ///   - POSITIVE `is-C(arg)` known true ⟹ `arg = C()` — an equality fact,
    ///     pushed into `var_ctor_term_eqs` (the SAME pipeline #422 item 3
    ///     already built for direct ctor=ctor equalities).
    ///   - NEGATIVE `¬is-C(arg)` known true ⟹ `arg ≠ C()` — a disequality
    ///     fact, pushed into `dt_diseq_pairs`.
    ///
    /// A non-nullary tester contributes NOTHING here (arity is checked
    /// below) — `is-C(arg)` for a field-bearing `C` does not pin `arg` to
    /// any single ground value, so no equality/disequality follows.
    ///
    /// # Cross-interner discipline
    ///
    /// `constructor` is a `Spur` from the TERM MANAGER's interner (the same
    /// interner `find_nullary_dt_constructor_term`'s cache lookup uses — see
    /// that method's doc comment), so reusing it directly there is correct.
    /// `manager.sorts.datatype_constructors_of` returns constructor names as
    /// already-resolved `String`s from the SORT manager's OWN (different)
    /// interner — comparing those two Spur spaces directly would be the
    /// exact cross-interner mistake that caused a real `#399` bug, so the
    /// arity lookup below compares constructor NAMES as strings, never raw
    /// `Spur`s across the two interners.
    ///
    /// # Safety on miss
    ///
    /// Any lookup miss — unresolved sort, non-nullary arity, or a
    /// `find_nullary_dt_constructor_term` cache miss (the nullary
    /// constructor term was never actually interned) — silently skips the
    /// derivation. A missed derivation is always safe (at worst, a
    /// completeness gap); nothing here can fabricate a fact.
    #[allow(clippy::too_many_arguments)]
    fn record_dt_nullary_tester_eq_fact(
        &self,
        constructor: oxiz_core::interner::Spur,
        arg: TermId,
        manager: &TermManager,
        in_positive_context: bool,
        var_ctor_term_eqs: &mut Vec<(TermId, TermId)>,
        dt_diseq_pairs: &mut Vec<(TermId, TermId)>,
    ) {
        let Some(arg_sort) = manager.get(arg).map(|d| d.sort) else {
            return;
        };
        let Some(ctors) = manager.sorts.datatype_constructors_of(arg_sort) else {
            return;
        };
        let cons_name = manager.resolve_str(constructor);
        let Some(&(_, arity)) = ctors.iter().find(|(name, _)| name == cons_name) else {
            return;
        };
        if arity != 0 {
            // Non-nullary tester: `is-C(arg)` does not pin `arg` to a single
            // ground value — no equality/disequality follows. Safe to skip.
            return;
        }
        let Some(c_term) = manager.find_nullary_dt_constructor_term(constructor) else {
            // The nullary constructor term was never interned — no fact to
            // derive from (safe: a missed derivation, never fabricated).
            return;
        };
        if in_positive_context {
            var_ctor_term_eqs.push((arg, c_term));
        } else {
            dt_diseq_pairs.push((arg, c_term));
        }
    }

    /// Collect datatype constraints from a term (version 2 with negative testers and var equalities)
    ///
    /// # #422 — `Distinct` polarity mapping (soundness note)
    ///
    /// A 2-ary `(distinct a b)` is a real, non-desugared `TermKind::Distinct`
    /// AST node (never rewritten to `Not(Eq(a,b))` at parse/build time — only
    /// arity ≤ 1 collapses to `true`). Semantically `(distinct a b) ≡ ¬(a =
    /// b)`, so its polarity mapping is the EXACT MIRROR of `Eq`'s:
    ///
    ///   - POSITIVE `(distinct a b)` is a disequality — handled by the SAME
    ///     `record_dt_negative_eq_fact` helper `Eq`'s negative arm uses (a
    ///     positive `distinct` and a negative `=` are the same fact), called
    ///     BOTH ways (`(a,b)` then `(b,a)`) exactly like `Eq`'s existing
    ///     dual-call, plus a `dt_diseq_pairs` entry for
    ///     `forces_disequality_conflict` (see that method's doc comment).
    ///   - NEGATIVE `(not (distinct a b))` is an EQUALITY — handled by the
    ///     SAME `record_dt_positive_eq_fact` helper `Eq`'s positive arm uses.
    ///     This is item 2's actual target: `(not (distinct a b))` was
    ///     PREVIOUSLY invisible to every collection in this function (no
    ///     `Distinct` arm existed at all), so a ground conflict expressed
    ///     that way (rather than as a direct `=`) went undetected.
    ///
    /// **N-ARY GUARD — the single most important soundness guard in this
    /// function.** The arm below is guarded `if args.len() == 2`. An N-ARY
    /// `distinct` (3+ args) negated is a genuine DISJUNCTION (`¬distinct(a,b,c)
    /// ≡ a=b ∨ a=c ∨ b=c`), NOT a single equality — collecting it as one
    /// equality via `record_dt_positive_eq_fact` would be UNSOUND (it would
    /// assert something strictly stronger than what is actually entailed,
    /// risking a spurious conflict elsewhere). `args.len() != 2` therefore
    /// falls through to the `_ => {}` catch-all below, collecting NOTHING —
    /// safe (if incomplete) in both polarities, mirroring every other
    /// deliberately-uncollected shape in this function. A POSITIVE N-ARY
    /// `distinct` (all pairwise different) IS in principle decomposable into
    /// `C(n,2)` pairwise disequalities, but that generalization is left for a
    /// separate, distinctly-scoped follow-up (not needed by any of #422's
    /// three items) to keep this diff small and independently re-verifiable.
    ///
    /// Neither `Distinct` arm recurses into its own operands, mirroring the
    /// existing `Eq` arm's discipline (`#392` — a Bool-sorted `=`/`distinct`
    /// is an iff/negated-iff; a tester nested inside an operand has
    /// undetermined polarity until the WHOLE equality/distinct's own truth
    /// value is fixed, which this collector never assumes beyond the direct
    /// `a`/`b` shape it explicitly handles above).
    #[allow(clippy::too_many_arguments)]
    fn collect_dt_constraints_v2(
        &self,
        term: TermId,
        manager: &TermManager,
        constructor_testers: &mut FxHashMap<TermId, Vec<String>>,
        negative_testers: &mut FxHashMap<TermId, Vec<String>>,
        constructor_equalities: &mut FxHashMap<TermId, Vec<String>>,
        negative_ctor_equalities: &mut FxHashMap<TermId, Vec<String>>,
        dt_var_equalities: &mut Vec<(TermId, TermId)>,
        var_ctor_term_eqs: &mut Vec<(TermId, TermId)>,
        // #419 item 2 — raw, positively-asserted `sel(t) = t2` / `t2 = sel(t)`
        // facts (a `DtSelector` application equated to ANYTHING, no
        // `is_dt_variable` gating on the other side — unlike
        // `var_ctor_term_eqs`, the "variable" here isn't required, since the
        // point is to feed `compute_dt_equality_closure`'s iterative
        // selector-resolution step, which may only become resolvable once
        // OTHER derived bindings arrive). One entry per selector-shaped
        // operand; a doubly-selector-shaped equality contributes both.
        sel_eqs: &mut Vec<(TermId, TermId)>,
        // #422 item 3 — direct `C(..) = D(..)` ctor-ctor equalities (no
        // mediating variable); see `record_dt_positive_eq_fact`'s doc
        // comment.
        dt_ctor_ctor_eqs: &mut Vec<(TermId, TermId)>,
        // #422 items 1+2 — disequality-source pairs feeding
        // `DtEqualityClosure::forces_disequality_conflict`: populated from a
        // NEGATIVE `Eq` whose two sides are BOTH datatype-sorted (item 1 —
        // the gate keys off the equality's own resolved `.sort`, not a
        // heuristic like `is_dt_variable`, so it fires for `x ≠ y` between
        // two DT variables AND for `C(..) ≠ D(..)` between two manifest
        // constructor applications alike) and, UNCONDITIONALLY (no sort
        // gate — see the `Distinct` arm's own doc note above), from a
        // POSITIVE 2-ary `distinct` (item 2).
        dt_diseq_pairs: &mut Vec<(TermId, TermId)>,
        in_positive_context: bool,
    ) {
        let Some(term_data) = manager.get(term) else {
            return;
        };

        match &term_data.kind {
            TermKind::DtTester { constructor, arg } => {
                let cons_name = manager.resolve_str(*constructor).to_string();
                if in_positive_context {
                    // Positive: ((_ is Constructor) var)
                    constructor_testers.entry(*arg).or_default().push(cons_name);
                } else {
                    // Negative: (not ((_ is Constructor) var))
                    negative_testers.entry(*arg).or_default().push(cons_name);
                }
                // #423 item 2 — independent derivation ALONGSIDE the
                // name-tag bookkeeping above (does not replace it): a
                // NULLARY constructor's tester is an equality/disequality
                // in its own right, not just a name tag. See
                // `record_dt_nullary_tester_eq_fact`'s doc comment for the
                // full soundness argument.
                self.record_dt_nullary_tester_eq_fact(
                    *constructor,
                    *arg,
                    manager,
                    in_positive_context,
                    var_ctor_term_eqs,
                    dt_diseq_pairs,
                );
            }
            TermKind::Eq(lhs, rhs) => {
                if in_positive_context {
                    self.record_dt_positive_eq_fact(
                        *lhs,
                        *rhs,
                        manager,
                        constructor_equalities,
                        dt_var_equalities,
                        var_ctor_term_eqs,
                        sel_eqs,
                        dt_ctor_ctor_eqs,
                    );
                } else {
                    self.record_dt_negative_eq_fact(
                        *lhs,
                        *rhs,
                        manager,
                        negative_ctor_equalities,
                        negative_testers,
                    );
                    self.record_dt_negative_eq_fact(
                        *rhs,
                        *lhs,
                        manager,
                        negative_ctor_equalities,
                        negative_testers,
                    );
                    // #422 item 1 / #423 item 1 — a NEGATIVE equality
                    // between two terms is a genuine disequality source for
                    // `forces_disequality_conflict`, regardless of whether
                    // either side is a plain variable (unlike
                    // `record_dt_negative_eq_fact` above, which only ever
                    // fires for a variable-vs-manifest-ctor shape): a direct
                    // `C(..) ≠ D(..)` between two constructor applications,
                    // or `x ≠ y` between two DT variables, both belong here.
                    //
                    // Unconditional (no DT-sort gate — #423 removed the
                    // `both_dt_sorted` gate this arm used to have): `(not (=
                    // lhs rhs))` is ALWAYS a genuine disequality between
                    // exactly these two terms regardless of their sort —
                    // `forces_disequality_conflict`'s union-find only ever
                    // fires if `lhs`/`rhs` are ACTUALLY unioned via a
                    // genuinely-derived `closed_eqs` pair (itself always
                    // sound), so recording every negative `Eq` here can only
                    // ever help completeness, never fabricate a conflict —
                    // the EXACT SAME argument the sibling `Distinct` arm's
                    // unconditional push already relies on (see that arm's
                    // doc comment below), now identical for both arms.
                    dt_diseq_pairs.push((*lhs, *rhs));
                }

                // Do NOT recurse into the equality's operands: they are not
                // asserted facts. A Bool-sorted `=` is an iff — a tester inside
                // either operand has UNDETERMINED polarity (`(= b ((_ is C) x))`
                // with `(not b)` asserts the tester FALSE), and collecting it as
                // if asserted produced a spurious unsat (#392 differential,
                // minR shape). Non-Bool operands are first-order terms with no
                // asserted sub-facts. The direct `x = Ctor(..)` / `x = y`
                // collections above are the equality's whole contribution.
            }
            TermKind::Distinct(args) if args.len() == 2 => {
                // #422 item 2 — see this function's own doc comment,
                // "`Distinct` polarity mapping", for the full soundness
                // argument (including the N-ARY GUARD above this arm).
                let (a, b) = (args[0], args[1]);
                if in_positive_context {
                    // POSITIVE `(distinct a b)` ≡ a disequality — same
                    // shape `Eq`'s negative arm handles, same dual-call.
                    self.record_dt_negative_eq_fact(
                        a,
                        b,
                        manager,
                        negative_ctor_equalities,
                        negative_testers,
                    );
                    self.record_dt_negative_eq_fact(
                        b,
                        a,
                        manager,
                        negative_ctor_equalities,
                        negative_testers,
                    );
                    // Unconditional (no DT-sort gate): `(distinct a b)` is
                    // ALWAYS a genuine disequality between exactly these two
                    // terms regardless of their sort — `forces_disequality_
                    // conflict`'s union-find only ever fires if `a`/`b` are
                    // ACTUALLY unioned via a genuinely-derived `closed_eqs`
                    // pair (itself always sound), so recording every 2-ary
                    // `distinct` here can only ever help completeness, never
                    // fabricate a conflict.
                    dt_diseq_pairs.push((a, b));
                } else {
                    // NEGATIVE `(not (distinct a b))` ≡ `(= a b)` — same
                    // shape `Eq`'s positive arm handles.
                    self.record_dt_positive_eq_fact(
                        a,
                        b,
                        manager,
                        constructor_equalities,
                        dt_var_equalities,
                        var_ctor_term_eqs,
                        sel_eqs,
                        dt_ctor_ctor_eqs,
                    );
                }
                // Do NOT recurse into the operands — mirrors `Eq`'s
                // discipline above (same `#392` iff-polarity argument
                // applies identically to a Bool-sorted `distinct`... though
                // `distinct` is never itself Bool-ARGUMENT-sorted the way an
                // `=` between two Bools can be an iff, the operands here are
                // still not independently-asserted facts).
            }
            TermKind::And(args) => {
                // A conjunction contributes its children only when the And
                // itself is asserted POSITIVELY. Under a negative context
                // `(not (and X Y))` is a DISJUNCTION (≡ ¬X ∨ ¬Y) — collecting
                // both children as joint facts falsely conflicted
                // `(not (and (not (= k c00)) (not (= k c01))))` (≡ k=c00 ∨
                // k=c01) with 2-ctor exhaustiveness (#392 differential, minB).
                if in_positive_context {
                    for &arg in args {
                        self.collect_dt_constraints_v2(
                            arg,
                            manager,
                            constructor_testers,
                            negative_testers,
                            constructor_equalities,
                            negative_ctor_equalities,
                            dt_var_equalities,
                            var_ctor_term_eqs,
                            sel_eqs,
                            dt_ctor_ctor_eqs,
                            dt_diseq_pairs,
                            in_positive_context,
                        );
                    }
                }
            }
            TermKind::Or(args) => {
                // Don't collect from OR branches - they represent disjunctions, not conjunctions
                // If we collected from both branches of (or (= x A) (= x B)), we'd falsely detect a conflict
                //
                // ...but a NEGATED Or is a conjunction (¬(X ∨ Y) ≡ ¬X ∧ ¬Y):
                // each child is genuinely asserted at the (negative) context,
                // so collect them — the dual of the And rule above.
                if !in_positive_context {
                    for &arg in args {
                        self.collect_dt_constraints_v2(
                            arg,
                            manager,
                            constructor_testers,
                            negative_testers,
                            constructor_equalities,
                            negative_ctor_equalities,
                            dt_var_equalities,
                            var_ctor_term_eqs,
                            sel_eqs,
                            dt_ctor_ctor_eqs,
                            dt_diseq_pairs,
                            in_positive_context,
                        );
                    }
                }
            }
            TermKind::Not(inner) => {
                // Flip context when entering Not
                self.collect_dt_constraints_v2(
                    *inner,
                    manager,
                    constructor_testers,
                    negative_testers,
                    constructor_equalities,
                    negative_ctor_equalities,
                    dt_var_equalities,
                    var_ctor_term_eqs,
                    sel_eqs,
                    dt_ctor_ctor_eqs,
                    dt_diseq_pairs,
                    !in_positive_context,
                );
            }
            _ => {}
        }
    }

    /// Collect datatype constraints from a term
    #[allow(dead_code)]
    fn collect_dt_constraints(
        &self,
        term: TermId,
        manager: &TermManager,
        constructor_testers: &mut FxHashMap<TermId, Vec<String>>,
        constructor_equalities: &mut FxHashMap<TermId, Vec<String>>,
    ) {
        self.collect_dt_constraints_inner(
            term,
            manager,
            constructor_testers,
            constructor_equalities,
            true,
        );
    }

    #[allow(dead_code)]
    fn collect_dt_constraints_inner(
        &self,
        term: TermId,
        manager: &TermManager,
        constructor_testers: &mut FxHashMap<TermId, Vec<String>>,
        constructor_equalities: &mut FxHashMap<TermId, Vec<String>>,
        in_positive_context: bool,
    ) {
        let Some(term_data) = manager.get(term) else {
            return;
        };

        match &term_data.kind {
            TermKind::DtTester { constructor, arg } if in_positive_context => {
                // ((_ is Constructor) var) - only collect when in positive context
                constructor_testers
                    .entry(*arg)
                    .or_default()
                    .push(manager.resolve_str(*constructor).to_string());
            }
            TermKind::Eq(lhs, rhs) => {
                // Check for x = Constructor(...) - only collect when in positive context
                if in_positive_context {
                    if let Some(rhs_data) = manager.get(*rhs) {
                        if let TermKind::DtConstructor { constructor, .. } = &rhs_data.kind {
                            if self.is_dt_variable(*lhs, manager) {
                                constructor_equalities
                                    .entry(*lhs)
                                    .or_default()
                                    .push(manager.resolve_str(*constructor).to_string());
                            }
                        }
                    }
                    if let Some(lhs_data) = manager.get(*lhs) {
                        if let TermKind::DtConstructor { constructor, .. } = &lhs_data.kind {
                            if self.is_dt_variable(*rhs, manager) {
                                constructor_equalities
                                    .entry(*rhs)
                                    .or_default()
                                    .push(manager.resolve_str(*constructor).to_string());
                            }
                        }
                    }
                }

                // No operand recursion — see collect_dt_constraints_v2: equality
                // operands are not asserted facts (Bool `=` is an iff).
            }
            TermKind::And(args) => {
                // Positive context only — a negated And is a disjunction
                // (see collect_dt_constraints_v2).
                if in_positive_context {
                    for &arg in args {
                        self.collect_dt_constraints_inner(
                            arg,
                            manager,
                            constructor_testers,
                            constructor_equalities,
                            in_positive_context,
                        );
                    }
                }
            }
            TermKind::Or(args) => {
                // Don't collect from OR branches - they represent disjunctions, not conjunctions
                // If we collected from both branches of (or (= x A) (= x B)), we'd falsely detect a conflict
                //
                // ...but a NEGATED Or is a conjunction — collect its children
                // (see collect_dt_constraints_v2).
                if !in_positive_context {
                    for &arg in args {
                        self.collect_dt_constraints_inner(
                            arg,
                            manager,
                            constructor_testers,
                            constructor_equalities,
                            in_positive_context,
                        );
                    }
                }
            }
            TermKind::Not(inner) => {
                // Flip context when entering Not
                self.collect_dt_constraints_inner(
                    *inner,
                    manager,
                    constructor_testers,
                    constructor_equalities,
                    !in_positive_context,
                );
            }
            _ => {}
        }
    }

    /// Check if a term is a datatype variable
    fn is_dt_variable(&self, term: TermId, manager: &TermManager) -> bool {
        let Some(term_data) = manager.get(term) else {
            return false;
        };
        matches!(term_data.kind, TermKind::Var(_))
    }
}
