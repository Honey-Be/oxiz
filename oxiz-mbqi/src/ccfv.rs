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
///
/// **Budget/abort contract (SOUNDNESS-CRITICAL for the caller):** the search is
/// bounded by an optional wall-clock `deadline` and a `max_substs` cap on the
/// result set, polled every 1024 seed iterations (one iteration = one top-level
/// `unify` call, measured mean 1.4–7.5 µs, max < 3 ms — so the poll blind spot
/// is ~10 ms and the poll overhead is ≪ 1 %). The returned bool is the **abort
/// signal**: `true` means the result is PARTIAL (the deadline passed or the
/// result was truncated to `max_substs`). A partial match set means "e-matching
/// added nothing" can no longer be read as saturation — the engine MUST route
/// an abort into `budget_hit` → `Verdict::BudgetExhausted` → `Unknown`, never
/// `Saturated`/`Sat`. Pass `(None, usize::MAX)` for the exact unbounded
/// behaviour (always `false`). Every returned substitution is a genuine match
/// (truncation only DROPS matches, it never fabricates one), so using the
/// partial set for instantiation stays sound.
pub fn match_trigger<S, C, L>(
    cong: &C,
    host: &L,
    pat: S::Term,
    holes: &[S::VarName],
    seeds: &[S::Term],
    deadline: Option<std::time::Instant>,
    max_substs: usize,
) -> (Vec<Subst<S>>, bool)
where
    S: Sig,
    C: Congruence<S>,
    L: TermLang<Sig = S>,
{
    let mut out = Vec::new();
    let mut aborted = false;
    for (i, &g) in seeds.iter().enumerate() {
        if i & 0x3FF == 0
            && (out.len() >= max_substs
                || deadline.is_some_and(|d| std::time::Instant::now() >= d))
        {
            aborted = true;
            break;
        }
        out.extend(unify(cong, host, pat, g, holes, Subst::<S>::new()));
    }
    // Enforce the cap between polls too: a truncated result MUST carry the
    // abort signal (dropping matches silently would let the engine read a
    // partial e-match as saturation — the spurious-Sat risk this exists for).
    if out.len() > max_substs {
        out.truncate(max_substs);
        aborted = true;
    }
    (out, aborted)
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
///
/// **Budget/abort contract:** same as [`match_trigger`] — `deadline` and
/// `max_substs` are polled every 1024 iterations (one iteration = one `unify`
/// call, counted across the seeding loop AND the acc × seeds join loop, whose
/// product is where the corpus blow-ups live). The returned bool is the abort
/// signal; on abort the result is PARTIAL: substitutions from an interrupted
/// join level satisfy only the patterns joined so far. That is still SOUND to
/// instantiate with (any ground tuple is a sound instance of a universal —
/// triggers are relevance heuristics, and the fullness filter in the engine
/// drops under-bound substitutions anyway), but it is NOT the full match set,
/// so the caller MUST route the abort into `budget_hit`, never `Saturated`.
/// Pass `(None, usize::MAX)` for the exact unbounded behaviour.
pub fn match_trigger_multi<S, C, L>(
    cong: &C,
    host: &L,
    patterns: &[S::Term],
    holes: &[S::VarName],
    seeds: &[Vec<S::Term>],
    deadline: Option<std::time::Instant>,
    max_substs: usize,
) -> (Vec<Subst<S>>, bool)
where
    S: Sig,
    C: Congruence<S>,
    L: TermLang<Sig = S>,
{
    if patterns.is_empty() {
        return (Vec::new(), false);
    }
    let mut iters = 0usize;
    let mut aborted = false;
    // One poll per 1024 unify calls, shared across the seeding and join loops.
    macro_rules! poll {
        ($len:expr) => {
            iters & 0x3FF == 0
                && ($len >= max_substs
                    || deadline.is_some_and(|d| std::time::Instant::now() >= d))
        };
    }
    // Seed with the first pattern's matches (each a fresh accumulator).
    let mut accs: Vec<Subst<S>> = Vec::new();
    for &g in seeds.first().map(Vec::as_slice).unwrap_or(&[]) {
        if poll!(accs.len()) {
            aborted = true;
            break;
        }
        iters += 1;
        accs.extend(unify(cong, host, patterns[0], g, holes, Subst::<S>::new()));
    }
    // Filter-extend by each remaining pattern, threading the substitution.
    if !aborted {
        for (i, &p) in patterns.iter().enumerate().skip(1) {
            let mut next = Vec::new();
            'join: for acc in &accs {
                for &g in seeds.get(i).map(Vec::as_slice).unwrap_or(&[]) {
                    if poll!(next.len()) {
                        aborted = true;
                        break 'join;
                    }
                    iters += 1;
                    next.extend(unify(cong, host, p, g, holes, acc.clone()));
                }
            }
            accs = next;
            if aborted || accs.is_empty() {
                break;
            }
        }
    }
    // Enforce the cap between polls too (see `match_trigger`): a truncated
    // result MUST carry the abort signal.
    if accs.len() > max_substs {
        accs.truncate(max_substs);
        aborted = true;
    }
    (accs, aborted)
}

// ─────────────────────────────────────────────────────────────────────────────
// The complete E-ground (dis)unification core — `solve` (design §2, the P4
// keystone). `match_trigger` above is the equality-matching half; `solve` is the
// COMPLETE conflict search the model-completion verdict-flip needs: given a
// constraint `C` (a DNF of Eq/Diseq literals over the bound-var holes) and the
// congruence `E`, it enumerates every σ for which `E ⊨ Cσ` MIGHT hold — a
// SUPERSET of the genuine conflicts (an undecidable literal is kept, never
// dropped). So an EMPTY result soundly means "no conflict exists over the witness
// domain" — exactly what the flip reads to conclude `Sat`. This is the verus-
// verified model (`ccfv-verification/src/complete.rs` `no_conflict_when_empty`):
// BRUTE-FORCE over the finite witness domain (each hole ranges over
// `cong.class_reps_of_sort(sort)`), so completeness holds by construction (no
// pruning to prove sound — that is the deferred P5 `R_*`/FAIL optimization). The
// per-σ literal check reuses the verified `unify` (applied terms matched modulo
// congruence). SOUNDNESS PRECONDITION: the disequality gate `cong.disequal` is a
// genuine `≄` only on a TOTAL view (E_TOT) where distinct class reps are
// disequal by construction — the flip MUST pass a `TotalView`, never the bare
// ground congruence (whose `disequal` is the conservative asserted-only query).
// ─────────────────────────────────────────────────────────────────────────────

/// One (dis)equality literal over terms that may contain bound-var holes.
pub enum Lit<S: Sig> {
    /// `lhs ≃ rhs`.
    Eq(S::Term, S::Term),
    /// `lhs ≄ rhs`.
    Diseq(S::Term, S::Term),
}

/// A DNF cube — a conjunction of literals.
pub type Conj<S> = Vec<Lit<S>>;

/// A constraint in disjunctive normal form (⋁ of cubes, each a ⋀ of literals) —
/// the lowered `¬ψ` for the conflict search. The host builds it (only its term
/// language knows the connective symbols).
pub struct Constraint<S: Sig> {
    /// The disjuncts; `E ⊨ Cσ` iff SOME cube's literals are all entailed.
    pub cubes: Vec<Conj<S>>,
}

/// Solve `c` against `cong`: return every σ (grounding `holes` to class reps of
/// their sorts) that MIGHT satisfy some cube — a SUPERSET of the conflicts. Empty
/// ⇒ no conflict over the witness domain (the flip's soundness). `holes` carries
/// each bound var's sort (the enumeration domain). SPLIT over cubes (union),
/// bounded by `max_tuples` per cube (a budget — hitting it yields a partial set,
/// still a superset, so still sound for the empty-means-no-conflict read… as long
/// as the budget is not hit, which the caller must ensure for a decisive `Sat`).
pub fn solve<S, C, L>(
    cong: &C,
    host: &L,
    c: &Constraint<S>,
    holes: &[(S::VarName, S::Sort)],
    max_tuples: usize,
) -> Vec<Subst<S>>
where
    S: Sig,
    C: Congruence<S>,
    L: TermLang<Sig = S>,
{
    let mut out = Vec::new();
    for cube in &c.cubes {
        solve_cube(cong, host, cube, holes, max_tuples, &mut out);
    }
    out
}

/// Brute-force a single cube: enumerate every hole→class-rep tuple and keep those
/// for which NO literal is decidably FALSE (every literal is `Some(true)` or
/// undecidable `None`). Keeping the undecidable ones is what makes an empty result
/// mean "no conflict" rather than the weaker "no DECIDED conflict".
fn solve_cube<S, C, L>(
    cong: &C,
    host: &L,
    cube: &Conj<S>,
    holes: &[(S::VarName, S::Sort)],
    max_tuples: usize,
    out: &mut Vec<Subst<S>>,
) where
    S: Sig,
    C: Congruence<S>,
    L: TermLang<Sig = S>,
{
    let names: Vec<S::VarName> = holes.iter().map(|(n, _)| *n).collect();
    let domains: Vec<Vec<S::Term>> =
        holes.iter().map(|(_, s)| cong.class_reps_of_sort(*s)).collect();
    // A hole with no witness ⇒ no grounding ⇒ this cube contributes nothing.
    if domains.iter().any(|d| d.is_empty()) {
        return;
    }
    let k = domains.len();
    let mut idx = vec![0usize; k];
    let mut tuples = 0usize;
    loop {
        if tuples >= max_tuples {
            break;
        }
        tuples += 1;
        let subst: Subst<S> = names
            .iter()
            .copied()
            .zip((0..k).map(|i| domains[i][idx[i]]))
            .collect();
        if cube
            .iter()
            .all(|lit| lit_eval(cong, host, lit, &subst, &names) != Some(false))
        {
            out.push(subst);
        }
        let mut carry = true;
        for i in 0..k {
            if carry {
                idx[i] += 1;
                if idx[i] >= domains[i].len() {
                    idx[i] = 0;
                } else {
                    carry = false;
                }
            }
        }
        if carry {
            break;
        }
    }
}

/// Evaluate one literal under a fully-bound σ. `Some(true)` = it holds (so σ is a
/// conflict for `¬ψ`), `Some(false)` = decidably violated, `None` = undecidable
/// (handled conservatively by the caller — never read as `false`).
fn lit_eval<S, C, L>(
    cong: &C,
    host: &L,
    lit: &Lit<S>,
    subst: &Subst<S>,
    holes: &[S::VarName],
) -> Option<bool>
where
    S: Sig,
    C: Congruence<S>,
    L: TermLang<Sig = S>,
{
    let (u, v, is_eq) = match lit {
        Lit::Eq(u, v) => (*u, *v, true),
        Lit::Diseq(u, v) => (*u, *v, false),
    };
    let congruent = terms_congruent(cong, host, u, v, subst, holes)?;
    Some(if is_eq { congruent } else { !congruent })
}

/// Whether `uσ ≃ vσ` in `E`, when decidable. Reuses the verified `unify` so
/// applied terms are matched modulo congruence: if one side grounds under σ (a
/// hole's binding or a hole-free term), the other is matched against it as a
/// pattern. `None` when neither side grounds (both applied with holes — the
/// `U_GEN` shared-class join, conservatively undecidable here).
fn terms_congruent<S, C, L>(
    cong: &C,
    host: &L,
    u: S::Term,
    v: S::Term,
    subst: &Subst<S>,
    holes: &[S::VarName],
) -> Option<bool>
where
    S: Sig,
    C: Congruence<S>,
    L: TermLang<Sig = S>,
{
    match (
        ground_after_subst(host, u, subst, holes),
        ground_after_subst(host, v, subst, holes),
    ) {
        (Some(ug), Some(vg)) => Some(cong.equal(ug, vg)),
        (Some(ug), None) => Some(!unify(cong, host, v, ug, holes, subst.clone()).is_empty()),
        (None, Some(vg)) => Some(!unify(cong, host, u, vg, holes, subst.clone()).is_empty()),
        (None, None) => None,
    }
}

/// The single ground term `term` becomes under σ, if it grounds: a hole → its
/// binding; a hole-free term (already interned, incl. ground applications) →
/// itself. `None` for a term still containing a hole (a pattern — matched by
/// `unify` against the other, ground, side).
fn ground_after_subst<S, L>(
    host: &L,
    term: S::Term,
    subst: &Subst<S>,
    holes: &[S::VarName],
) -> Option<S::Term>
where
    S: Sig,
    L: TermLang<Sig = S>,
{
    if let TermView::Var { name } = host.view(term) {
        if is_hole::<S>(holes, name) {
            return subst_get::<S>(subst, name);
        }
    }
    if !contains_hole(host, term, holes) {
        return Some(term);
    }
    None
}

/// Whether `term` mentions any hole. Bounded by term depth.
fn contains_hole<S, L>(host: &L, term: S::Term, holes: &[S::VarName]) -> bool
where
    S: Sig,
    L: TermLang<Sig = S>,
{
    match host.view(term) {
        TermView::Var { name } => is_hole::<S>(holes, name),
        TermView::App { .. } => host
            .children(term)
            .iter()
            .any(|&c| contains_hole(host, c, holes)),
        TermView::Opaque | TermView::Quant { .. } => false,
    }
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
        // (Future throughput optimization, deliberately NOT part of the
        // deadline/max_substs budget fix: `cong.class(g)` allocates a fresh
        // member Vec per call — caching class members per (class-rep,
        // congruence-generation) would cut the dominant allocation in hot
        // e-match loops. Excluded from the minimal viable fix on purpose.)
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
        /// The ground witness universe (for `class_reps_of_sort` — `solve`'s
        /// enumeration domain). Empty by default (the matching-half tests don't
        /// use it).
        universe: Vec<u32>,
    }
    impl ToyCong {
        fn new(classes: Vec<Vec<u32>>) -> Self {
            let mut of = FxHashMap::default();
            for (i, c) in classes.iter().enumerate() {
                for &t in c {
                    of.insert(t, i);
                }
            }
            ToyCong { classes, of, universe: Vec::new() }
        }
        fn with_universe(mut self, u: Vec<u32>) -> Self {
            self.universe = u;
            self
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
        /// Total-view semantics (the `solve`/flip precondition): distinct classes
        /// are disequal by construction.
        fn disequal(&self, a: u32, b: u32) -> bool {
            !self.equal(a, b)
        }
        /// One representative ground term per class over the universe.
        fn class_reps_of_sort(&self, _s: u32) -> Vec<u32> {
            let mut seen: FxHashMap<u32, ()> = FxHashMap::default();
            let mut out = Vec::new();
            for &t in &self.universe {
                let r = self.rep(t);
                if seen.insert(r, ()).is_none() {
                    out.push(r);
                }
            }
            out
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
        let res = match_trigger::<ToySig, _, _>(&cong, &h, fx, &[X], &[fa], None, usize::MAX).0;
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
        let res = match_trigger::<ToySig, _, _>(&cong, &h, fgx, &[X], &[fc], None, usize::MAX).0;
        assert_eq!(res.len(), 1, "congruence match should find x ↦ a");
        assert_eq!(subst_get::<ToySig>(&res[0], X), Some(a));

        // control: without the congruence (c alone) the same match fails.
        let cong0 = ToyCong::new(vec![]);
        assert!(match_trigger::<ToySig, _, _>(&cong0, &h, fgx, &[X], &[fc], None, usize::MAX).0.is_empty());
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
        let r1 = match_trigger::<ToySig, _, _>(&cong, &h, fxx, &[X], &[fab], None, usize::MAX).0;
        assert_eq!(r1.len(), 1, "f(x,x) ~ f(a,b) with a≡b");
        assert_eq!(subst_get::<ToySig>(&r1[0], X), Some(a));

        let r2 = match_trigger::<ToySig, _, _>(&cong, &h, fxx, &[X], &[fad], None, usize::MAX).0;
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
        let res = match_trigger::<ToySig, _, _>(&cong, &h, fx, &[X], &[fa], None, usize::MAX).0;
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
        assert!(match_trigger::<ToySig, _, _>(&cong, &h, fx, &[X], &[ha], None, usize::MAX).0.is_empty());
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
            match_trigger_multi::<ToySig, _, _>(&cong, &h, &[fx, gy], &[X, Y], &[vec![fa], vec![gb]], None, usize::MAX).0;
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
            match_trigger_multi::<ToySig, _, _>(&cong, &h, &[fx, gx], &[X], &[vec![fa], vec![gc]], None, usize::MAX).0;
        assert_eq!(r1.len(), 1, "shared hole consistent under a≡c");
        assert_eq!(subst_get::<ToySig>(&r1[0], X), Some(a));

        // a ≢ c ⟹ no consistent binding for the shared hole.
        let cong0 = ToyCong::new(vec![]);
        let r2 =
            match_trigger_multi::<ToySig, _, _>(&cong0, &h, &[fx, gx], &[X], &[vec![fa], vec![gc]], None, usize::MAX).0;
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
            match_trigger_multi::<ToySig, _, _>(&cong, &h, &[fx, gy], &[X, Y], &[vec![fa], vec![]], None, usize::MAX).0
                .is_empty()
        );
    }

    // ── the complete `solve` (Phase 2: the brute-force E-ground (dis)unification
    //    conflict search the P4 model-completion verdict-flip reads) ────────────

    #[test]
    fn solve_finds_an_equality_conflict() {
        // C = [[x ≃ a]] over the universe {a, b} (a, b apart). x↦a is a conflict
        // (a ≃ a); x↦b is not. So solve enumerates exactly {x↦a} — non-empty, so
        // the flip would NOT (wrongly) conclude no-conflict.
        let mut h = Toy::new();
        let a = h.konst(1, S);
        let b = h.konst(2, S);
        let x = h.var(X, S);
        let cong = ToyCong::new(vec![]).with_universe(vec![a, b]);
        let c = Constraint { cubes: vec![vec![Lit::Eq(x, a)]] };
        let res = solve::<ToySig, _, _>(&cong, &h, &c, &[(X, S)], 64);
        assert_eq!(res.len(), 1, "exactly x↦a is a conflict");
        assert_eq!(subst_get::<ToySig>(&res[0], X), Some(a));
    }

    #[test]
    fn solve_empty_means_no_conflict_the_flip_keystone() {
        // C = [[x ≄ x]] — a reflexive disequality, NEVER satisfiable. solve returns
        // ∅, which is EXACTLY what the model-completion flip reads to conclude
        // `Sat` (verus `complete::no_conflict_when_empty`).
        let mut h = Toy::new();
        let a = h.konst(1, S);
        let b = h.konst(2, S);
        let x = h.var(X, S);
        let cong = ToyCong::new(vec![]).with_universe(vec![a, b]);
        let c = Constraint { cubes: vec![vec![Lit::Diseq(x, x)]] };
        let res = solve::<ToySig, _, _>(&cong, &h, &c, &[(X, S)], 64);
        assert!(res.is_empty(), "x ≄ x is unsatisfiable ⇒ no conflict ⇒ empty");
    }

    #[test]
    fn solve_disequality_uses_the_total_view_separation() {
        // C = [[x ≃ a ∧ x ≄ b]] over {a, b} apart. x↦a: a≃a ∧ a≄b (distinct
        // classes ⇒ disequal on the total view) → conflict. x↦b: b≃a is false →
        // dropped. So exactly {x↦a}.
        let mut h = Toy::new();
        let a = h.konst(1, S);
        let b = h.konst(2, S);
        let x = h.var(X, S);
        let cong = ToyCong::new(vec![]).with_universe(vec![a, b]);
        let c = Constraint { cubes: vec![vec![Lit::Eq(x, a), Lit::Diseq(x, b)]] };
        let res = solve::<ToySig, _, _>(&cong, &h, &c, &[(X, S)], 64);
        assert_eq!(res.len(), 1);
        assert_eq!(subst_get::<ToySig>(&res[0], X), Some(a));
    }

    #[test]
    fn solve_applied_term_reuses_unify_modulo_congruence() {
        // C = [[f(x) ≃ c]] with f(a) ≡ c in the congruence, universe {a, b}.
        // x↦a: f(x) is a pattern (has a hole) vs ground c ⇒ the per-σ check reuses
        // `unify(f(x), c, {x↦a})`, which matches f(a) in c's class ⇒ conflict.
        // x↦b: f(b) ∉ c's class ⇒ no match ⇒ dropped. So exactly {x↦a}.
        let mut h = Toy::new();
        let a = h.konst(1, S);
        let b = h.konst(2, S);
        let c = h.konst(3, S);
        let x = h.var(X, S);
        let fa = h.app(10, &[a], S); // f(a)
        let fx = h.app(10, &[x], S); // f(x)
        // f(a) ≡ c
        let cong = ToyCong::new(vec![vec![fa, c]]).with_universe(vec![a, b]);
        let constraint = Constraint { cubes: vec![vec![Lit::Eq(fx, c)]] };
        let res = solve::<ToySig, _, _>(&cong, &h, &constraint, &[(X, S)], 64);
        assert_eq!(res.len(), 1, "f(a)≡c ⇒ only x↦a is a conflict");
        assert_eq!(subst_get::<ToySig>(&res[0], X), Some(a));
    }

    #[test]
    fn solve_keeps_an_undecidable_literal_conservatively() {
        // Both sides applied-with-holes (no side grounds) ⇒ the per-σ check is
        // undecidable (`None`) ⇒ σ is KEPT (a superset), so the empty-means-
        // no-conflict read stays sound (the flip declines rather than wrongly
        // firing). C = [[f(x) ≃ g(x)]].
        let mut h = Toy::new();
        let a = h.konst(1, S);
        let x = h.var(X, S);
        let fx = h.app(10, &[x], S);
        let gx = h.app(20, &[x], S);
        let cong = ToyCong::new(vec![]).with_universe(vec![a]);
        let c = Constraint { cubes: vec![vec![Lit::Eq(fx, gx)]] };
        let res = solve::<ToySig, _, _>(&cong, &h, &c, &[(X, S)], 64);
        assert_eq!(res.len(), 1, "an undecidable literal is kept (superset), not dropped");
    }

    // ── deadline / max_substs budget-abort contract ─────────────────────────
    // THE soundness-critical property: an interrupted match MUST come back
    // with `aborted == true` so the engine can route it into `budget_hit` →
    // `BudgetExhausted` → the host's `Unknown` (a silently-partial result
    // would be read as "e-matching added nothing" ⇒ spurious `Saturated`/Sat).

    /// The SPLIT scenario (two matches) with an ALREADY-EXPIRED deadline: the
    /// iteration-0 poll fires before any unify runs ⇒ empty partial result +
    /// the mandatory abort signal.
    #[test]
    fn expired_deadline_aborts_match_trigger_with_abort_signal() {
        let mut h = Toy::new();
        let a = h.konst(1, S);
        let b = h.konst(2, S);
        let x = h.var(X, S);
        let fa = h.app(10, &[a], S);
        let fb = h.app(10, &[b], S);
        let fx = h.app(10, &[x], S);
        let cong = ToyCong::new(vec![vec![fa, fb]]);
        let expired = std::time::Instant::now() - std::time::Duration::from_millis(1);
        let (res, aborted) =
            match_trigger::<ToySig, _, _>(&cong, &h, fx, &[X], &[fa], Some(expired), usize::MAX);
        assert!(aborted, "expired deadline MUST raise the abort signal");
        assert!(res.is_empty(), "aborted at iteration 0 ⇒ empty partial result");
    }

    /// Same scenario with `max_substs = 1` (< the 2 genuine matches): the
    /// result is truncated to EXACTLY `max_substs` and the abort signal is
    /// raised — truncation must never be silent.
    #[test]
    fn max_substs_truncates_to_exactly_the_cap_and_aborts() {
        let mut h = Toy::new();
        let a = h.konst(1, S);
        let b = h.konst(2, S);
        let x = h.var(X, S);
        let fa = h.app(10, &[a], S);
        let fb = h.app(10, &[b], S);
        let fx = h.app(10, &[x], S);
        let cong = ToyCong::new(vec![vec![fa, fb]]);
        let (res, aborted) =
            match_trigger::<ToySig, _, _>(&cong, &h, fx, &[X], &[fa], None, 1);
        assert!(aborted, "truncation MUST raise the abort signal");
        assert_eq!(res.len(), 1, "truncated to exactly max_substs");
        // The one kept substitution is still a genuine match (a or b).
        let bind = subst_get::<ToySig>(&res[0], X);
        assert!(bind == Some(a) || bind == Some(b));
    }

    /// The 1024-iteration poll cadence, not just the iteration-0 poll: 1300
    /// seeds each yielding one substitution with `max_substs = 100` aborts at
    /// the i = 1024 poll and truncates to exactly 100.
    #[test]
    fn max_substs_poll_fires_at_the_1024_cadence() {
        let mut h = Toy::new();
        let x = h.var(X, S);
        let fx = h.app(10, &[x], S);
        let seeds: Vec<u32> = (0..1300u32)
            .map(|i| {
                let c = h.konst(1000 + i, S);
                h.app(10, &[c], S)
            })
            .collect();
        let cong = ToyCong::new(vec![]);
        let (res, aborted) =
            match_trigger::<ToySig, _, _>(&cong, &h, fx, &[X], &seeds, None, 100);
        assert!(aborted, "cap exceeded at the 1024-iteration poll ⇒ abort");
        assert_eq!(res.len(), 100, "truncated to exactly max_substs");
    }

    /// `(None, usize::MAX)` is the exact pre-fix behaviour: the SPLIT scenario
    /// yields EXACTLY the pinned substitution set {x↦a, x↦b}, never aborted.
    #[test]
    fn unbounded_control_is_identical_to_pre_fix_pinned_set() {
        let mut h = Toy::new();
        let a = h.konst(1, S);
        let b = h.konst(2, S);
        let x = h.var(X, S);
        let fa = h.app(10, &[a], S);
        let fb = h.app(10, &[b], S);
        let fx = h.app(10, &[x], S);
        let cong = ToyCong::new(vec![vec![fa, fb]]);
        let (res, aborted) =
            match_trigger::<ToySig, _, _>(&cong, &h, fx, &[X], &[fa], None, usize::MAX);
        assert!(!aborted, "(None, usize::MAX) never aborts");
        let binds: Vec<u32> = res.iter().filter_map(|s| subst_get::<ToySig>(s, X)).collect();
        assert_eq!(res.len(), 2, "the pinned pre-fix result: both SPLIT matches");
        assert!(binds.contains(&a) && binds.contains(&b), "pinned set {{x↦a, x↦b}}");
    }

    /// Multi-pattern: expired deadline aborts the join with the signal set.
    #[test]
    fn expired_deadline_aborts_match_trigger_multi() {
        let mut h = Toy::new();
        let a = h.konst(1, S);
        let b = h.konst(2, S);
        let x = h.var(X, S);
        let y = h.var(Y, S);
        let fa = h.app(10, &[a], S);
        let gb = h.app(20, &[b], S);
        let fx = h.app(10, &[x], S);
        let gy = h.app(20, &[y], S);
        let cong = ToyCong::new(vec![]);
        let expired = std::time::Instant::now() - std::time::Duration::from_millis(1);
        let (res, aborted) = match_trigger_multi::<ToySig, _, _>(
            &cong,
            &h,
            &[fx, gy],
            &[X, Y],
            &[vec![fa], vec![gb]],
            Some(expired),
            usize::MAX,
        );
        assert!(aborted, "expired deadline MUST raise the abort signal (multi)");
        assert!(res.is_empty(), "aborted at iteration 0 ⇒ empty partial result");
    }

    /// Multi-pattern: `max_substs` truncates the joined result to exactly the
    /// cap and aborts. `((f x) (g y))` over 2×2 seeds yields 4 joined
    /// substitutions unbounded; capped at 2 it returns exactly 2 + aborted.
    #[test]
    fn max_substs_truncates_match_trigger_multi_and_aborts() {
        let mut h = Toy::new();
        let a = h.konst(1, S);
        let b = h.konst(2, S);
        let c = h.konst(3, S);
        let d = h.konst(4, S);
        let x = h.var(X, S);
        let y = h.var(Y, S);
        let fa = h.app(10, &[a], S);
        let fb = h.app(10, &[b], S);
        let gc = h.app(20, &[c], S);
        let gd = h.app(20, &[d], S);
        let fx = h.app(10, &[x], S);
        let gy = h.app(20, &[y], S);
        let cong = ToyCong::new(vec![]);
        // Control: unbounded yields the full 2×2 join.
        let (all, ab0) = match_trigger_multi::<ToySig, _, _>(
            &cong,
            &h,
            &[fx, gy],
            &[X, Y],
            &[vec![fa, fb], vec![gc, gd]],
            None,
            usize::MAX,
        );
        assert!(!ab0);
        assert_eq!(all.len(), 4, "pinned pre-fix join: 2×2 substitutions");
        // Capped: exactly max_substs survive, with the abort signal.
        let (res, aborted) = match_trigger_multi::<ToySig, _, _>(
            &cong,
            &h,
            &[fx, gy],
            &[X, Y],
            &[vec![fa, fb], vec![gc, gd]],
            None,
            2,
        );
        assert!(aborted, "truncation MUST raise the abort signal (multi)");
        assert_eq!(res.len(), 2, "truncated to exactly max_substs");
    }
}
