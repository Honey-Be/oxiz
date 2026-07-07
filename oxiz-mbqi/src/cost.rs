//! The cost function, fuel-depth reader, generativity classifier, and content
//! sort-key — the scheduler's INPUTS (design `FUEL_AWARE_COST_SCHEDULER.md`
//! §3/§4/§5.2), P1.
//!
//! Pure functions over the host term language ([`TermLang`]) + the E1/E2/E3
//! accessors: they compute what the [`crate::cost_scheduler::CostScheduler`]
//! prices and orders on. Consumed by the engine's scheduled discover⇄drain
//! fixpoint ([`crate::engine::Engine`], behind the `cost_schedule` flag): P3c
//! wired [`classify_static`] + the Δfuel discount into `collect_candidate`. With
//! the **default `CostParams` (`k_fuel = 0`, `gen_class_delta = 0`) the classifier
//! is COMPUTED but INERT** — `cost = weight + generation` (Z3 parity) — so a
//! flag-on run with defaults is byte-identical in *ordering effect* to P2; the
//! corpus sweep raises the knobs.

use crate::cost_scheduler::CAP;
use crate::term::{FuelRole, Sig, TermLang, TermView};

// ---- fuel depth (E2) -------------------------------------------------------

/// The `succ`-nesting of `t` **if `t` is itself a fuel-constructor term**
/// (`succ(succ(…zero))`), else `None`. `zero` is 0; `succ(u)` is `1 + depth(u)`;
/// anything else (including `succ` applied to a bound fuel variable, whose depth
/// is not statically known) is `None`.
pub fn fuel_succ_depth<L: TermLang>(lang: &L, t: <L::Sig as Sig>::Term) -> Option<u32> {
    match lang.view(t) {
        TermView::App { sym } => match lang.fuel_role(sym) {
            Some(FuelRole::Zero) => Some(0),
            Some(FuelRole::Succ) => lang
                .children(t)
                .first()
                .and_then(|c| fuel_succ_depth(lang, *c))
                .map(|d| d + 1),
            None => None,
        },
        _ => None,
    }
}

/// The fuel level of a recursive-function application `t = f(fuel_chain, …)`: the
/// `succ`-depth of `t`'s first fuel-sorted (ground `succ`/`zero`) argument, or
/// `None` if `t` carries no ground fuel argument (a non-fuel application, or one
/// whose fuel argument is a bound variable). This is what a `Δfuel` gradient is
/// measured against.
pub fn fuel_arg_depth<L: TermLang>(lang: &L, t: <L::Sig as Sig>::Term) -> Option<u32> {
    if let TermView::App { .. } = lang.view(t) {
        for c in lang.children(t) {
            if let Some(d) = fuel_succ_depth(lang, c) {
                return Some(d);
            }
        }
    }
    None
}

/// `(v, k)` if `t` is a **pure fuel chain over a bound variable** — `succ^k(v)`
/// with `v ∈ vars` (`k = 0` ⇒ `t` is the bare bound var, `k ≥ 1` ⇒ wrapped in
/// that many `succ`s) — else `None`. Unlike [`fuel_succ_depth`] (which bottoms out
/// at the ground `zero`), this bottoms out at a BOUND var: it reads the fuel level
/// a recursive-definition trigger/body binds *symbolically*.
fn fuel_chain_var<L: TermLang>(
    lang: &L,
    t: <L::Sig as Sig>::Term,
    vars: &[<L::Sig as Sig>::VarName],
) -> Option<(<L::Sig as Sig>::VarName, u32)> {
    match lang.view(t) {
        TermView::Var { name } if vars.contains(&name) => Some((name, 0)),
        TermView::App { sym } if lang.fuel_role(sym) == Some(FuelRole::Succ) => lang
            .children(t)
            .first()
            .and_then(|c| fuel_chain_var(lang, *c, vars))
            .map(|(v, k)| (v, k + 1)),
        _ => None,
    }
}

/// Collect every `(bound_var, succ_depth)` fuel occurrence in `t`: each maximal
/// `succ^k(v)` chain (v ∈ `vars`) contributes ONE pair — the whole chain is a
/// single fuel argument at depth `k`, so the inner `succ`s are NOT double-counted
/// as shallower occurrences (which would spoof a peel). When `only` is `Some`, an
/// occurrence is kept only if its var is in that set (used to restrict the body
/// scan to the identified fuel vars, excluding non-fuel bound args like the `a` in
/// `f(succ(F), a)`).
fn collect_fuel_occ<L: TermLang>(
    lang: &L,
    t: <L::Sig as Sig>::Term,
    vars: &[<L::Sig as Sig>::VarName],
    only: Option<&[<L::Sig as Sig>::VarName]>,
    out: &mut Vec<(<L::Sig as Sig>::VarName, u32)>,
) {
    if let Some((v, k)) = fuel_chain_var(lang, t, vars) {
        if only.is_none_or(|s| s.contains(&v)) {
            out.push((v, k));
        }
        return; // the whole `succ`-chain is one occurrence — don't recurse into it
    }
    for c in lang.children(t) {
        collect_fuel_occ(lang, c, vars, only, out);
    }
}

/// **Static generativity class (design §4), computed at trigger-fix from the E2
/// fuel structure.** Two passes: (1) identify the quantifier's *fuel* variables —
/// the bound vars a trigger wraps in ≥ 1 `succ` (`trig_depth` = their max trigger
/// `succ`-depth); (2) scan the body for how deep those same vars are re-committed.
///
/// - **`Decreasing`** iff `trig_depth ≥ 1`, the body never wraps a fuel var
///   *deeper* than `trig_depth` (no growth), AND the body uses one *shallower* than
///   `trig_depth` (a real `succ`-peel: `f(succ(F),a) = …f(F,a)…`). The
///   self-bounding cascade the deep closers need — run it uncapped/discounted.
/// - **`Unknown`** otherwise: a non-fuel quantifier (`trig_depth = 0`), a fuel-flat
///   one (body echoes only the trigger depth), or a fuel-*growing* one. §4 makes
///   the static analysis authoritative ONLY for `Decreasing`, so growth is left for
///   the live `g_out` corroborator to escalate toward `Ascending` — a mis-inferred
///   trigger can then only under-discount a real peel, never wrongly throttle it.
///
/// The body-scan restricts to the identified fuel vars, so a non-fuel bound arg
/// (bare, depth 0) never counterfeits a peel. Pure + read-only.
pub fn classify_static<L: TermLang>(
    lang: &L,
    vars: &[<L::Sig as Sig>::VarName],
    triggers: &[Vec<<L::Sig as Sig>::Term>],
    body: <L::Sig as Sig>::Term,
) -> GenClass {
    // Pass 1 — the fuel vars are those a trigger wraps in ≥ 1 `succ`.
    let mut trig_occ = Vec::new();
    for &t in triggers.iter().flatten() {
        collect_fuel_occ(lang, t, vars, None, &mut trig_occ);
    }
    let mut fuel_vars: Vec<<L::Sig as Sig>::VarName> = Vec::new();
    let mut trig_depth = 0u32;
    for &(v, k) in &trig_occ {
        if k >= 1 {
            trig_depth = trig_depth.max(k);
            if !fuel_vars.contains(&v) {
                fuel_vars.push(v);
            }
        }
    }
    if fuel_vars.is_empty() {
        return GenClass::Unknown; // no bound fuel var under succ in any trigger
    }
    // Pass 2 — how deep does the body re-commit those fuel vars?
    let mut body_occ = Vec::new();
    collect_fuel_occ(lang, body, vars, Some(&fuel_vars), &mut body_occ);
    let grows = body_occ.iter().any(|&(_, k)| k > trig_depth);
    let peels = body_occ.iter().any(|&(_, k)| k < trig_depth);
    if !grows && peels {
        GenClass::Decreasing
    } else {
        GenClass::Unknown // fuel-flat / growing → live signal governs
    }
}

// ---- content sort-key (E3) -------------------------------------------------

const FNV_OFFSET: u64 = 0xcbf2_9ce4_8422_2325;
const FNV_PRIME: u64 = 0x0000_0100_0000_01b3;
#[inline]
fn mix(h: u64, x: u64) -> u64 {
    let mut h = h ^ x;
    h = h.wrapping_mul(FNV_PRIME);
    h
}

/// A stable, content-derived structural hash of a term — the raw material for the
/// scheduler's R7 shuffle-invariant tie-break (design §5.2). Application heads are
/// folded through the host's E3 [`content_key`](TermLang::content_key) (name-stable,
/// not interner-order), so the hash is invariant under an assertion shuffle;
/// structural shape (arity, nesting) is folded in positionally. Leaf variables and
/// opaque literals fold a fixed tag — full leaf discrimination (const names, literal
/// values, which this trait surface does not expose) is composed by the caller as a
/// `(content_key, term_id)` pair (§5.2); this primitive supplies the content half.
pub fn term_content_key<L: TermLang>(lang: &L, t: <L::Sig as Sig>::Term) -> u64 {
    fn go<L: TermLang>(lang: &L, t: <L::Sig as Sig>::Term, h: u64) -> u64 {
        match lang.view(t) {
            TermView::App { sym } => {
                let mut h = mix(h, lang.content_key(sym).unwrap_or(0xA9)); // head content
                h = mix(h, 0x28); // '(' — open
                for c in lang.children(t) {
                    h = go(lang, c, h);
                }
                mix(h, 0x29) // ')' — close
            }
            TermView::Var { .. } => mix(h, 0x56),    // 'V'
            TermView::Opaque => mix(h, 0x4C),        // 'L' (literal)
            TermView::Quant { .. } => mix(h, 0x51),  // 'Q'
        }
    }
    go(lang, t, FNV_OFFSET)
}

// ---- generativity class (§4) + the cost combiner (§3) ----------------------

/// Generativity class of a quantifier (design §4). `Decreasing` = provably
/// loop-free (fuel-peeling / non-generative) ⇒ run uncapped; `Ascending` =
/// generative / fuel-flat ⇒ throttle; `Unknown` = not statically decided ⇒ base
/// cost (the live `g_out` may only escalate it toward `Ascending`, never override
/// a static `Decreasing` — M3).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum GenClass {
    Decreasing,
    Ascending,
    Unknown,
}

/// Reconcile the static class with the live `g_out` signal (M3 direction): a
/// static `Decreasing` is FINAL; `g_out > 0` escalates only an `Unknown` toward
/// `Ascending`. `g_out` (a generation-delta) is a weak corroborator, never the
/// discriminator.
pub fn reconcile(static_class: GenClass, g_out: u32) -> GenClass {
    match static_class {
        GenClass::Decreasing => GenClass::Decreasing,
        GenClass::Ascending => GenClass::Ascending,
        GenClass::Unknown => {
            if g_out > 0 {
                GenClass::Ascending
            } else {
                GenClass::Unknown
            }
        }
    }
}

/// Tunable cost parameters (design §3). `Default` is **Z3 parity**: `k_fuel = 0`,
/// `gen_class_delta = 0` ⇒ `cost = weight + generation`. The corpus sweep (P3)
/// raises `k_fuel` (the fuel discount/penalty magnitude) and `gen_class_delta`
/// (the ascending penalty) from there.
#[derive(Clone, Copy, Debug)]
pub struct CostParams {
    /// Fuel-gradient weight: `fuel_penalty = k_fuel * Δfuel`. A fuel-*decreasing*
    /// edge (Δfuel < 0, the `succ`-peel) becomes a discount; fuel-flat/ascending
    /// (Δfuel ≥ 0) a penalty.
    pub k_fuel: i32,
    /// The extra cost an `Ascending` quantifier's instances carry, so they cross
    /// the eager→lazy thresholds sooner.
    pub gen_class_delta: u16,
}

impl Default for CostParams {
    fn default() -> Self {
        CostParams { k_fuel: 0, gen_class_delta: 0 } // Z3 parity: cost = weight + generation
    }
}

/// The instance cost (design §3): `clamp_0_CAP(weight + generation + k_fuel·Δfuel
/// + [Ascending ? gen_class_delta : 0])`. `Δfuel` is `fuel_arg_depth(minted) −
/// fuel_arg_depth(matched trigger term)` (negative for a `succ`-peel). Saturates
/// into the `CAP` overflow bucket — DEFER, never a hard gate.
pub fn cost_of(
    p: &CostParams,
    weight: u16,
    generation: u32,
    delta_fuel: i32,
    class: GenClass,
) -> u16 {
    let base = weight as i64 + generation as i64;
    let fuel = p.k_fuel as i64 * delta_fuel as i64;
    let class_pen = if class == GenClass::Ascending {
        p.gen_class_delta as i64
    } else {
        0
    };
    (base + fuel + class_pen).clamp(0, CAP as i64) as u16
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::toy::Toy;

    const INT: u32 = 2;
    const FUEL: u32 = 3;
    // Toy fuel constructors: the toy host does not resolve names, so we exercise
    // the numeric/structural primitives on a toy that overrides fuel_role via a
    // wrapper. For fuel-shape tests we use the real host elsewhere (oxiz-solver);
    // here we test the arithmetic + content-key primitives that need no fuel.

    #[test]
    fn cost_default_is_z3_parity() {
        let p = CostParams::default();
        // cost = weight + generation; fuel/class terms vanish.
        assert_eq!(cost_of(&p, 0, 0, 0, GenClass::Unknown), 0);
        assert_eq!(cost_of(&p, 3, 5, -9, GenClass::Ascending), 8, "k_fuel=delta=0 ⇒ weight+gen only");
    }

    #[test]
    fn cost_monotonic_in_generation() {
        let p = CostParams::default();
        let a = cost_of(&p, 0, 2, 0, GenClass::Unknown);
        let b = cost_of(&p, 0, 7, 0, GenClass::Unknown);
        assert!(b >= a, "cost non-decreasing in generation (holding others)");
    }

    #[test]
    fn cost_fuel_discount_and_ascending_penalty() {
        let p = CostParams { k_fuel: 3, gen_class_delta: 10 };
        // Decreasing succ-peel: Δfuel = -1 ⇒ discount of 3.
        let dec = cost_of(&p, 0, 5, -1, GenClass::Decreasing);
        assert_eq!(dec, 2, "5 + 3*(-1) = 2 (fuel discount)");
        // Ascending fuel-flat: Δfuel = 0, +gen_class_delta.
        let asc = cost_of(&p, 0, 5, 0, GenClass::Ascending);
        assert_eq!(asc, 15, "5 + 0 + 10 ascending penalty");
        assert!(dec < asc, "a decreasing succ-peel is cheaper than an ascending sibling");
    }

    #[test]
    fn cost_saturates_into_overflow() {
        let p = CostParams { k_fuel: 0, gen_class_delta: 0 };
        assert_eq!(cost_of(&p, 0, 100_000, 0, GenClass::Unknown), CAP, "over-CAP ⇒ DEFER bucket");
        // Never negative even with a large discount.
        let p2 = CostParams { k_fuel: 100, gen_class_delta: 0 };
        assert_eq!(cost_of(&p2, 0, 1, -50, GenClass::Decreasing), 0, "clamped at 0, not negative");
    }

    #[test]
    fn reconcile_is_static_authoritative_live_only_escalates_unknown() {
        // M3: a static Decreasing is final regardless of the live signal.
        assert_eq!(reconcile(GenClass::Decreasing, 5), GenClass::Decreasing);
        assert_eq!(reconcile(GenClass::Ascending, 0), GenClass::Ascending);
        // Unknown escalates to Ascending only when g_out > 0.
        assert_eq!(reconcile(GenClass::Unknown, 3), GenClass::Ascending);
        assert_eq!(reconcile(GenClass::Unknown, 0), GenClass::Unknown);
    }

    #[test]
    fn content_key_is_deterministic_and_structural() {
        let mut t = Toy::new();
        let a = t.konst(100, INT);
        let fa = t.app(40, &[a], INT);
        let fa2 = t.app(40, &[a], INT); // hash-consed → same id
        let ffa = t.app(40, &[fa], INT); // deeper nesting

        // Deterministic: the same term always hashes the same.
        assert_eq!(term_content_key(&t, fa), term_content_key(&t, fa));
        assert_eq!(term_content_key(&t, fa), term_content_key(&t, fa2));
        // Structural: different nesting depth → different key.
        assert_ne!(term_content_key(&t, fa), term_content_key(&t, ffa));
        // On the toy (content_key = None) application HEADS are folded through the
        // 0xA9 fallback, so same-shape/different-head terms are NOT discriminated —
        // the graceful non-content degrade. Real head/leaf discrimination via the
        // E3 content_key is exercised on the OxiZ host in oxiz-solver.
    }

    #[test]
    fn classify_static_degrades_to_unknown_without_fuel_ctors() {
        // The toy host has no fuel constructors (fuel_role = None), so no trigger
        // can bind a fuel var under a `succ` ⇒ every quantifier is `Unknown` (the
        // Z3-parity degrade). Real `Decreasing` detection is exercised on the OxiZ
        // host (oxiz-solver `classify_static_detects_fuel_peel_on_real_host`).
        let mut t = Toy::new();
        let x = t.var(700, INT);
        let px = t.app(40, &[x], INT);
        assert_eq!(
            classify_static(&t, &[700], &[vec![px]], px),
            GenClass::Unknown,
            "no fuel ctors ⇒ Unknown regardless of shape"
        );
    }

    #[test]
    fn fuel_depth_none_without_fuel_ctors() {
        // The toy host returns fuel_role = None for every sym, so fuel readers are
        // None (the graceful non-fuel degrade). Real succ/zero recognition is
        // tested on the OxiZ host in oxiz-solver.
        let mut t = Toy::new();
        let z = t.konst(FUEL, FUEL);
        let s = t.app(50, &[z], FUEL);
        assert_eq!(fuel_succ_depth(&t, z), None);
        assert_eq!(fuel_succ_depth(&t, s), None);
        assert_eq!(fuel_arg_depth(&t, s), None);
    }
}
