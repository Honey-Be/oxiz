//! Datatype theory constraint checking

#[allow(unused_imports)]
use crate::prelude::*;
use oxiz_core::ast::{TermId, TermKind, TermManager};

use super::Solver;

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
                true,
            );
        }

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
        if self.check_dt_acyclicity(manager, &dt_var_equalities, &var_ctor_term_eqs) {
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

        // --- Unconditional structural walk: record every manifest
        // `DtConstructor` application's own (term-id, args) shape. Ground-
        // only: skip quantifier bodies (see doc comment). ---
        let mut ctor_terms: Vec<(TermId, Vec<TermId>)> = Vec::new();
        {
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
        }

        // --- Directed containment graph over equivalence-class roots. ---
        let mut adj: FxHashMap<TermId, Vec<TermId>> = FxHashMap::default();
        for (t, args) in &ctor_terms {
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

    /// Collect datatype constraints from a term (version 2 with negative testers and var equalities)
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
            }
            TermKind::Eq(lhs, rhs) => {
                if in_positive_context {
                    // Check for x = Constructor(...)
                    if let Some(rhs_data) = manager.get(*rhs) {
                        if let TermKind::DtConstructor { constructor, .. } = &rhs_data.kind {
                            if self.is_dt_variable(*lhs, manager) {
                                constructor_equalities
                                    .entry(*lhs)
                                    .or_default()
                                    .push(manager.resolve_str(*constructor).to_string());
                                // #406 — also keep the actual constructor TERM
                                // id (not just its name) so the acyclicity
                                // check can union `lhs` into `rhs`'s
                                // argument graph.
                                var_ctor_term_eqs.push((*lhs, *rhs));
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
                                var_ctor_term_eqs.push((*rhs, *lhs));
                            }
                        }
                    }

                    // Check for DT variable equality: x = y where both are DT variables
                    if self.is_dt_variable(*lhs, manager) && self.is_dt_variable(*rhs, manager) {
                        dt_var_equalities.push((*lhs, *rhs));
                    }
                } else {
                    // #399 — a NEGATED equality to a NULLARY constructor excludes
                    // that whole constructor class (the nullary ctor's value is
                    // unique). A generic field-bearing ctor diseq excludes only
                    // one instance, so it is deliberately NOT collected — with
                    // ONE exception (#404 phase 2): the TESTER SHAPE
                    // `v ≠ C(sel_{C,0}(v), …, sel_{C,k}(v))` is exactly
                    // `¬is-C(v)` for ANY arity (rebuilding `v` from its own
                    // C-fields equals `v` iff `v` is C-shaped; a non-C `v`
                    // differs by constructor distinctness) — this is the very
                    // form the parser's recognizer desugar and the verus
                    // decreases-check guards emit. Record it as a negative
                    // TESTER, feeding the same injectivity + exhaustiveness
                    // reasoning; excluding ALL ctors this way is a ground
                    // conflict (z3 parity — was a spurious `sat`).
                    let mut record = |v: TermId, c: TermId| {
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
                        let Some(sel_names) =
                            manager.sorts.datatype_ctor_selectors(vsort, &cons_name)
                        else {
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
                                    args.len() == 1
                                        && args[0] == v
                                        && manager.resolve_str(*func) == *want
                                }
                                _ => false,
                            })
                        });
                        if tester_shape {
                            negative_testers.entry(v).or_default().push(cons_name);
                        }
                    };
                    record(*lhs, *rhs);
                    record(*rhs, *lhs);
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
