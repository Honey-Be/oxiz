//! E-matching: match `:pattern` triggers against the ground-term index.
//!
//! A trigger is a term containing the quantifier's bound variables as holes,
//! e.g. `(f x (g y))`. E-matching finds ground terms it unifies with and
//! reads off the substitution `{x↦…, y↦…}`.
//!
//! **Why this is sound by construction.** Candidates come only from the
//! ground index, and the ground index never holds a quantifier-body subterm
//! (it does not descend into `Quant`). So a trigger can NEVER match its own
//! body (OxiZ bug B: identity `{i↦i}`) or a sibling's body (bug E:
//! `{i↦x_sibling}`) — those terms simply are not candidates. Every match
//! binds the trigger's variables to subterms of a real ground term, which
//! are themselves ground. The B/E bug class is unrepresentable here.

use crate::ground::GroundIndex;
use crate::term::{Sig, TermLang, TermView};
use rustc_hash::FxHashMap;

/// A substitution under construction: bound-var name → ground term.
type Subst<S> = FxHashMap<<S as Sig>::VarName, <S as Sig>::Term>;

/// Match a single trigger `pattern` (whose holes are `bound`) against the
/// given `candidates` (ground terms sharing the pattern's top symbol — the
/// caller frontier-filters them), returning all consistent substitutions.
/// Each returned substitution binds **every** bound variable (partial matches
/// are dropped — an instance must be fully ground).
pub fn match_single<S, L>(
    lang: &L,
    candidates: &[S::Term],
    pattern: S::Term,
    bound: &[(S::VarName, S::Sort)],
) -> Vec<Vec<(S::VarName, S::Term)>>
where
    S: Sig,
    L: TermLang<Sig = S>,
{
    let mut out = Vec::new();
    for &cand in candidates {
        let mut subst: Subst<S> = FxHashMap::default();
        if match_term(lang, pattern, cand, bound, &mut subst)
            && bound.iter().all(|(n, _)| subst.contains_key(n))
        {
            out.push(bound.iter().map(|(n, _)| (*n, subst[n])).collect());
        }
    }
    out
}

/// Match several trigger patterns simultaneously with one consistent
/// substitution (a multi-pattern `:pattern (p1 p2 …)`). All must match.
pub fn match_multi<S, L>(
    lang: &L,
    ground: &GroundIndex<S>,
    patterns: &[S::Term],
    bound: &[(S::VarName, S::Sort)],
) -> Vec<Vec<(S::VarName, S::Term)>>
where
    S: Sig,
    L: TermLang<Sig = S>,
{
    if patterns.is_empty() {
        return Vec::new();
    }
    let head0 = match lang.view(patterns[0]) {
        TermView::App { sym, .. } => sym,
        _ => return Vec::new(),
    };
    // Seed with the first pattern's matches, then filter-extend by the rest.
    let mut partial: Vec<Subst<S>> = match_single(lang, ground.with_head(head0), patterns[0], bound)
        .into_iter()
        .map(|b| b.into_iter().collect())
        .collect();
    for &p in &patterns[1..] {
        let head = match lang.view(p) {
            TermView::App { sym, .. } => sym,
            _ => return Vec::new(),
        };
        let mut next = Vec::new();
        for s in &partial {
            for &cand in ground.with_head(head) {
                let mut s2 = s.clone();
                if match_term(lang, p, cand, bound, &mut s2) {
                    next.push(s2);
                }
            }
        }
        partial = next;
    }
    partial
        .into_iter()
        .filter(|s| bound.iter().all(|(n, _)| s.contains_key(n)))
        .map(|s| bound.iter().map(|(n, _)| (*n, s[n])).collect())
        .collect()
}

/// Unify `pattern` (holes = `bound`) against ground term `g`, extending
/// `subst`. Returns false on structural mismatch or inconsistent binding.
fn match_term<S, L>(
    lang: &L,
    pattern: S::Term,
    g: S::Term,
    bound: &[(S::VarName, S::Sort)],
    subst: &mut Subst<S>,
) -> bool
where
    S: Sig,
    L: TermLang<Sig = S>,
{
    match lang.view(pattern) {
        TermView::Var { name } if bound.iter().any(|(n, _)| *n == name) => {
            // A hole. Bind it to `g` (which is ground), or check consistency.
            match subst.get(&name) {
                Some(&prev) => prev == g,
                None => {
                    subst.insert(name, g);
                    true
                }
            }
        }
        TermView::Var { .. } => {
            // A free variable in the pattern (not a hole): must match identically.
            pattern == g
        }
        TermView::App { sym: psym } => {
            let pargs = lang.children(pattern);
            match lang.view(g) {
                TermView::App { sym: gsym } if gsym == psym => {
                    let gargs = lang.children(g);
                    gargs.len() == pargs.len()
                        && pargs
                            .iter()
                            .zip(gargs.iter())
                            .all(|(&p, &q)| match_term(lang, p, q, bound, subst))
                }
                _ => false,
            }
        }
        // Opaque / quantifier patterns: only an identical ground term matches.
        TermView::Opaque | TermView::Quant { .. } => pattern == g,
    }
}
