//! CCFV — E-ground (dis)unification, the unified instantiation core (design
//! `CCFV_UNIFIED_INSTANTIATION.md` §2, Phase **P1**).
//!
//! This is the **matching-modulo-congruence** half: given a trigger pattern `p`
//! (a term whose holes are the quantifier's bound variables) and the ground
//! congruence `E` (read through the [`Congruence`] oracle, P0), find every
//! substitution `σ` grounding the holes such that `E ⊨ pσ ≃ g` for a ground
//! candidate `g`. It is the inference a purely *syntactic* matcher cannot make
//! — two terms in one congruence class but syntactically distinct now match.
//! CCFV is now the engine's SOLE matcher: with a real congruence oracle it
//! matches modulo `E`; with the trivial [`NoCong`](crate::congruence::NoCong) it
//! degenerates to exactly syntactic matching (the old `trigger` module).
//!
//! It is the executable refinement of the verus-pre-verified abstract model
//! (`ccfv-verification`): the **ASSIGN** rule is binding a hole to a ground term
//! (grounding invariant (ii) — bindings are always real ground terms, never
//! fabricated); **DECOMPOSE** is recursing `f(p̄) ≃ f(t̄)` into the arguments
//! (the variable-depth measure strictly decreases, so the search terminates,
//! invariant (iii)); **SPLIT** is the branch over a congruence class's members; a
//! complete unification is a **YIELD** — and it is sound because every leaf
//! comparison goes through the congruence `equal`, so `pσ` is genuinely congruent
//! to `g` (invariant (i)).
//!
//! **Behaviour-isolated (P1):** seed enumeration (which ground terms to match the
//! top pattern against) is the *caller's* job — `match_trigger` takes the seeds —
//! so this core has no host-symbol ↔ EUF-func-id concern and no engine wiring yet
//! (that is P2, re-expressing trigger e-matching through CCFV). It produces only
//! candidate substitutions; the engine's `instantiate`/`emit` gate stays the
//! soundness firewall, unchanged.
use crate::congruence::Congruence;
use crate::term::{Sig, TermLang, TermView};

/// A substitution from bound-variable holes to ground terms. The ASSIGN rule
/// extends it; a complete match returns it. Every range term is ground (drawn
/// from the congruence), so a returned `Subst` always passes the engine's
/// ground-term `instantiate` gate (verus invariant (ii)).
pub type Subst<S> = Vec<(<S as Sig>::VarName, <S as Sig>::Term)>;

fn is_hole<S: Sig>(holes: &[S::VarName], name: S::VarName) -> bool {
    holes.iter().any(|&h| h == name)
}

fn subst_get<S: Sig>(s: &Subst<S>, name: S::VarName) -> Option<S::Term> {
    s.iter().find(|(n, _)| *n == name).map(|(_, t)| *t)
}

/// Match trigger pattern `pat` (holes = `holes`) against each ground candidate in
/// `seeds`, modulo the congruence `cong`. Returns every substitution `σ` with
/// `E ⊨ pat·σ ≃ g` for some `g ∈ seeds`. (For trigger e-matching the seeds are
/// the ground applications sharing `pat`'s head — supplied by the caller, P2.)
pub fn match_trigger<S, C, L>(
    cong: &C,
    host: &L,
    pat: S::Term,
    holes: &[S::VarName],
    seeds: &[S::Term],
) -> Vec<Subst<S>>
where
    S: Sig,
    C: Congruence<S>,
    L: TermLang<Sig = S>,
{
    let mut out = Vec::new();
    for &g in seeds {
        out.extend(unify(cong, host, pat, g, holes, Subst::<S>::new()));
    }
    out
}

/// Match a **multi-pattern** trigger group: every pattern in `patterns` must
/// match under ONE consistent substitution, modulo the congruence. `seeds[i]`
/// are the ground candidates for `patterns[i]` (the ground applications sharing
/// `patterns[i]`'s head — supplied by the caller, like [`match_trigger`]).
///
/// The join threads the accumulated substitution through each pattern in turn:
/// a hole shared between patterns is bound once (ASSIGN) and re-checked for
/// congruence by every later pattern (the consistency case of ASSIGN). A
/// returned `σ` therefore satisfies `E ⊨ patternsᵢ·σ ≃ gᵢ` simultaneously for a
/// `gᵢ ∈ seeds[i]` per pattern. Each yield is still a vector of ground bindings
/// (the engine's `instantiate`/`emit` gate filters to full, sound instances).
///
/// Unlike the prior syntactic `trigger::match_multi`, the seed of the join does
/// NOT require the first pattern to bind every variable — partial bindings are
/// threaded forward and completed by the remaining patterns — so a genuine
/// multi-pattern `((f x) (g y))` that no single pattern fully covers now matches.
pub fn match_trigger_multi<S, C, L>(
    cong: &C,
    host: &L,
    patterns: &[S::Term],
    holes: &[S::VarName],
    seeds: &[Vec<S::Term>],
) -> Vec<Subst<S>>
where
    S: Sig,
    C: Congruence<S>,
    L: TermLang<Sig = S>,
{
    if patterns.is_empty() {
        return Vec::new();
    }
    // Seed with the first pattern's matches (each a fresh accumulator).
    let mut accs: Vec<Subst<S>> = Vec::new();
    for &g in seeds.first().map(Vec::as_slice).unwrap_or(&[]) {
        accs.extend(unify(cong, host, patterns[0], g, holes, Subst::<S>::new()));
    }
    // Filter-extend by each remaining pattern, threading the substitution.
    for (i, &p) in patterns.iter().enumerate().skip(1) {
        let mut next = Vec::new();
        for acc in &accs {
            for &g in seeds.get(i).map(Vec::as_slice).unwrap_or(&[]) {
                next.extend(unify(cong, host, p, g, holes, acc.clone()));
            }
        }
        accs = next;
        if accs.is_empty() {
            break;
        }
    }
    accs
}

/// Unify pattern `pat` against ground term `g` modulo `E`, extending `acc`.
/// Returns every consistent extension (∅ on failure). Recursion is bounded by the
/// pattern's variable-depth (DECOMPOSE strictly shrinks it — verus invariant
/// (iii)).
fn unify<S, C, L>(
    cong: &C,
    host: &L,
    pat: S::Term,
    g: S::Term,
    holes: &[S::VarName],
    acc: Subst<S>,
) -> Vec<Subst<S>>
where
    S: Sig,
    C: Congruence<S>,
    L: TermLang<Sig = S>,
{
    match host.view(pat) {
        // A bound-variable hole: ASSIGN (bind to a ground rep) or check.
        TermView::Var { name } if is_hole::<S>(holes, name) => match subst_get::<S>(&acc, name) {
            // Already bound: the binding must be congruent to `g` (consistency —
            // handles non-linear patterns like `f(x, x)`).
            Some(t) => {
                if cong.equal(t, g) {
                    vec![acc]
                } else {
                    Vec::new()
                }
            }
            // Unbound: ASSIGN x ↦ rep(g). `rep(g)` is a ground class member, so
            // the binding is ground (invariant (ii)).
            None => {
                let mut s = acc;
                s.push((name, cong.rep(g)));
                vec![s]
            }
        },
        // A non-hole leaf (declared constant / opaque literal): match modulo
        // congruence — the leaf is itself a ground term.
        TermView::Var { .. } | TermView::Opaque => {
            if cong.equal(pat, g) {
                vec![acc]
            } else {
                Vec::new()
            }
        }
        // An application `f(p̄)`: `g`'s congruence class must contain an
        // `f`-application `f(t̄)` of the same arity; DECOMPOSE into the arguments.
        // Iterating the class members that match the head is the SPLIT branch.
        TermView::App { sym } => {
            let p_args = host.children(pat);
            let mut results = Vec::new();
            for m in cong.class(g) {
                if let TermView::App { sym: m_sym } = host.view(m) {
                    if m_sym == sym {
                        let m_args = host.children(m);
                        if m_args.len() == p_args.len() {
                            results.extend(unify_args(cong, host, &p_args, &m_args, holes, acc.clone()));
                        }
                    }
                }
            }
            results
        }
        // A quantifier is never a ground match target.
        TermView::Quant { .. } => Vec::new(),
    }
}

/// DECOMPOSE: unify the pattern args `ps` against the ground args `gs`
/// position-by-position, threading the substitution (the product of per-argument
/// extensions). Each pattern arg is strictly shallower than the enclosing
/// application, so the recursion is well-founded.
fn unify_args<S, C, L>(
    cong: &C,
    host: &L,
    ps: &[S::Term],
    gs: &[S::Term],
    holes: &[S::VarName],
    acc: Subst<S>,
) -> Vec<Subst<S>>
where
    S: Sig,
    C: Congruence<S>,
    L: TermLang<Sig = S>,
{
    let mut accs = vec![acc];
    for (&p, &g) in ps.iter().zip(gs.iter()) {
        let mut next = Vec::new();
        for a in accs {
            next.extend(unify(cong, host, p, g, holes, a));
        }
        accs = next;
        if accs.is_empty() {
            break;
        }
    }
    accs
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::congruence::FuncApp;
    use crate::toy::{Toy, ToySig};
    use rustc_hash::FxHashMap;

    /// A toy congruence over explicit equivalence classes — lets the matcher
    /// tests control `equal`/`class`/`rep` directly (the live oracle is the EUF).
    struct ToyCong {
        classes: Vec<Vec<u32>>,
        of: FxHashMap<u32, usize>,
    }
    impl ToyCong {
        fn new(classes: Vec<Vec<u32>>) -> Self {
            let mut of = FxHashMap::default();
            for (i, c) in classes.iter().enumerate() {
                for &t in c {
                    of.insert(t, i);
                }
            }
            ToyCong { classes, of }
        }
    }
    impl Congruence<ToySig> for ToyCong {
        fn rep(&self, t: u32) -> u32 {
            self.of.get(&t).map(|&i| self.classes[i][0]).unwrap_or(t)
        }
        fn equal(&self, a: u32, b: u32) -> bool {
            a == b || matches!((self.of.get(&a), self.of.get(&b)), (Some(i), Some(j)) if i == j)
        }
        fn class(&self, t: u32) -> Vec<u32> {
            self.of.get(&t).map(|&i| self.classes[i].clone()).unwrap_or_else(|| vec![t])
        }
        fn apps_like(&self, _app: u32) -> Vec<FuncApp<ToySig>> {
            Vec::new() // unused — the matcher takes seeds directly
        }
    }

    const S: u32 = 0; // the only sort
    const X: u32 = 100; // a hole name

    #[test]
    fn assign_and_decompose_no_congruence() {
        // pattern f(x), seed f(a) ⟹ x ↦ a   (DECOMPOSE then ASSIGN)
        let mut h = Toy::new();
        let a = h.konst(1, S);
        let x = h.var(X, S);
        let fa = h.app(10, &[a], S);
        let fx = h.app(10, &[x], S);

        let cong = ToyCong::new(vec![]); // trivial congruence
        let res = match_trigger::<ToySig, _, _>(&cong, &h, fx, &[X], &[fa]);
        assert_eq!(res.len(), 1);
        assert_eq!(subst_get::<ToySig>(&res[0], X), Some(a));
    }

    #[test]
    fn matches_modulo_congruence_the_syntactic_matcher_cannot() {
        // pattern f(g(x)), seed f(c), with c = g(a) in the congruence.
        // Syntactic matching fails (c is a constant, not g(_)); CCFV succeeds via
        // the class of c, binding x ↦ a.
        let mut h = Toy::new();
        let a = h.konst(1, S);
        let c = h.konst(2, S);
        let x = h.var(X, S);
        let ga = h.app(20, &[a], S); // g(a)
        let gx = h.app(20, &[x], S); // g(x)
        let fc = h.app(10, &[c], S); // f(c)
        let fgx = h.app(10, &[gx], S); // f(g(x))

        // c ≡ g(a)
        let cong = ToyCong::new(vec![vec![c, ga]]);
        let res = match_trigger::<ToySig, _, _>(&cong, &h, fgx, &[X], &[fc]);
        assert_eq!(res.len(), 1, "congruence match should find x ↦ a");
        assert_eq!(subst_get::<ToySig>(&res[0], X), Some(a));

        // control: without the congruence (c alone) the same match fails.
        let cong0 = ToyCong::new(vec![]);
        assert!(match_trigger::<ToySig, _, _>(&cong0, &h, fgx, &[X], &[fc]).is_empty());
    }

    #[test]
    fn nonlinear_pattern_enforces_consistency() {
        // pattern f(x, x): matches f(a, b) iff a ≡ b.
        let mut h = Toy::new();
        let a = h.konst(1, S);
        let b = h.konst(2, S);
        let d = h.konst(3, S);
        let x = h.var(X, S);
        let fxx = h.app(10, &[x, x], S);
        let fab = h.app(10, &[a, b], S);
        let fad = h.app(10, &[a, d], S);

        // a ≡ b, but d apart.
        let cong = ToyCong::new(vec![vec![a, b]]);
        let r1 = match_trigger::<ToySig, _, _>(&cong, &h, fxx, &[X], &[fab]);
        assert_eq!(r1.len(), 1, "f(x,x) ~ f(a,b) with a≡b");
        assert_eq!(subst_get::<ToySig>(&r1[0], X), Some(a));

        let r2 = match_trigger::<ToySig, _, _>(&cong, &h, fxx, &[X], &[fad]);
        assert!(r2.is_empty(), "f(x,x) ≁ f(a,d) with a≢d");
    }

    #[test]
    fn split_over_class_yields_multiple_substitutions() {
        // pattern f(x), seed s, where s's class holds two f-applications
        // f(a) and f(b) ⟹ two substitutions x↦a and x↦b.
        let mut h = Toy::new();
        let a = h.konst(1, S);
        let b = h.konst(2, S);
        let x = h.var(X, S);
        let fa = h.app(10, &[a], S);
        let fb = h.app(10, &[b], S);
        let fx = h.app(10, &[x], S);

        // f(a) ≡ f(b) (one class); match the pattern against that class.
        let cong = ToyCong::new(vec![vec![fa, fb]]);
        let res = match_trigger::<ToySig, _, _>(&cong, &h, fx, &[X], &[fa]);
        let binds: Vec<u32> = res.iter().filter_map(|s| subst_get::<ToySig>(s, X)).collect();
        assert_eq!(res.len(), 2, "SPLIT over the two class members");
        assert!(binds.contains(&a) && binds.contains(&b));
    }

    #[test]
    fn head_mismatch_does_not_match() {
        // pattern f(x), seed h(a): different head ⟹ no match.
        let mut h = Toy::new();
        let a = h.konst(1, S);
        let x = h.var(X, S);
        let ha = h.app(99, &[a], S);
        let fx = h.app(10, &[x], S);
        let cong = ToyCong::new(vec![]);
        assert!(match_trigger::<ToySig, _, _>(&cong, &h, fx, &[X], &[ha]).is_empty());
    }

    const Y: u32 = 101; // a second hole name

    #[test]
    fn multi_pattern_joins_partial_bindings_no_single_covers() {
        // A genuine multi-pattern `((f x) (g y))` over `∀x y`: neither pattern
        // covers both holes. CCFV threads x from `(f x)`~f(a) and y from
        // `(g y)`~g(b) into one substitution {x↦a, y↦b} — the match the prior
        // syntactic `match_multi` dropped (its seed required the FIRST pattern
        // to bind every var).
        let mut h = Toy::new();
        let a = h.konst(1, S);
        let b = h.konst(2, S);
        let x = h.var(X, S);
        let y = h.var(Y, S);
        let fa = h.app(10, &[a], S);
        let gb = h.app(20, &[b], S);
        let fx = h.app(10, &[x], S);
        let gy = h.app(20, &[y], S);

        let cong = ToyCong::new(vec![]); // syntactic (NoCong-equivalent)
        let res =
            match_trigger_multi::<ToySig, _, _>(&cong, &h, &[fx, gy], &[X, Y], &[vec![fa], vec![gb]]);
        assert_eq!(res.len(), 1, "the two patterns join into one substitution");
        assert_eq!(subst_get::<ToySig>(&res[0], X), Some(a));
        assert_eq!(subst_get::<ToySig>(&res[0], Y), Some(b));
    }

    #[test]
    fn multi_pattern_shared_hole_enforces_consistency() {
        // `((f x) (g x))` shares the hole x: it matches f(a)+g(c) only when the
        // two bindings for x agree modulo congruence. With a≡c the join holds
        // (x↦a); with a≢c it is dropped.
        let mut h = Toy::new();
        let a = h.konst(1, S);
        let c = h.konst(3, S);
        let x = h.var(X, S);
        let fa = h.app(10, &[a], S);
        let gc = h.app(20, &[c], S);
        let fx = h.app(10, &[x], S);
        let gx = h.app(20, &[x], S);

        // a ≡ c ⟹ consistent, one match x↦a (rep of the class).
        let cong = ToyCong::new(vec![vec![a, c]]);
        let r1 =
            match_trigger_multi::<ToySig, _, _>(&cong, &h, &[fx, gx], &[X], &[vec![fa], vec![gc]]);
        assert_eq!(r1.len(), 1, "shared hole consistent under a≡c");
        assert_eq!(subst_get::<ToySig>(&r1[0], X), Some(a));

        // a ≢ c ⟹ no consistent binding for the shared hole.
        let cong0 = ToyCong::new(vec![]);
        let r2 =
            match_trigger_multi::<ToySig, _, _>(&cong0, &h, &[fx, gx], &[X], &[vec![fa], vec![gc]]);
        assert!(r2.is_empty(), "shared hole inconsistent under a≢c");
    }

    #[test]
    fn multi_pattern_empty_seed_for_one_pattern_yields_nothing() {
        // If any pattern has no ground candidate, the whole group cannot match.
        let mut h = Toy::new();
        let a = h.konst(1, S);
        let x = h.var(X, S);
        let y = h.var(Y, S);
        let fa = h.app(10, &[a], S);
        let fx = h.app(10, &[x], S);
        let gy = h.app(20, &[y], S);
        let cong = ToyCong::new(vec![]);
        assert!(
            match_trigger_multi::<ToySig, _, _>(&cong, &h, &[fx, gy], &[X, Y], &[vec![fa], vec![]])
                .is_empty()
        );
    }
}
