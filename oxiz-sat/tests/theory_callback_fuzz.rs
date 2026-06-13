//! Differential fuzz of the CDCL(T) theory-callback surface.
//!
//! GOAL
//! ----
//! Harden the pure-engine `solve_with_theory` path that drives
//!   * `add_theory_reason_clause`     (theory propagation with a synthesized reason)
//!   * `analyze_theory_conflict`      (theory conflict resolution / learning)
//! by running it against a SYNTHETIC, PROVABLY SOUND theory whose truth is
//! computable, so we have an independent ground-truth oracle for SAT/UNSAT and
//! can flag any verdict the engine returns that disagrees.
//!
//! THE THEORY (and why it is sound)
//! --------------------------------
//! We fix a *secret total model* `a*: Var -> bool` over a designated set of
//! "theory variables" T (chosen by `new_var`, same `Var` space as the SAT part).
//! The theory's set of valid facts is the set of 2-literal "implication" clauses
//!     Ax = { (¬p ∨ q) : p,q ∈ T }
//! restricted to clauses that `a*` SATISFIES (rejection sampling). Every axiom is
//! therefore a logical consequence of "the world is `a*`", i.e. the theory is the
//! ground theory `Th = { clauses satisfied by a* }` projected to these 2-lit
//! shapes. Anything the theory asserts (propagation or conflict) is a clause in
//! Ax, hence entailed — that is exactly what soundness of a theory solver means:
//! it may only emit lemmas valid in the theory.
//!
//! The callback is implemented to respect the engine's literal-set conventions
//! EXACTLY (verified against analyze_theory_conflict / add_theory_reason_clause):
//!
//!   * `Conflict(c)` : every literal in `c` is currently FALSE, and the clause
//!     `(c[0] ∨ c[1] ∨ …)` is a theory axiom. We only ever emit a conflict for an
//!     axiom `(¬p ∨ q)` when `p` is currently TRUE and `q` is currently FALSE, so
//!     both axiom literals `¬p` and `q` are false — we hand back `c = [¬p, q]`.
//!
//!   * `Propagated[(lit, reason)]` : the engine builds the reason clause
//!     `(lit ∨ ¬reason[0] ∨ ¬reason[1] …)` and forces `lit` true. We emit this for
//!     an axiom `(¬p ∨ q)` when `p` is TRUE and `q` is UNASSIGNED: `lit = q`,
//!     `reason = [p]` ⇒ clause `(q ∨ ¬p) = (¬p ∨ q)` ∈ Ax, and every reason literal
//!     (`p`) is currently TRUE, so the produced clause is unit-implying `q`. Valid.
//!
//! Because every theory lemma is a clause of Ax and every clause of Ax is true in
//! `a*`, the conjunction (input CNF) ∧ (all of Ax) is satisfiable IFF
//! (input CNF) ∧ Ax is propositionally satisfiable. We compute that ground truth
//! independently (brute force over all assignments for small instances) and
//! compare it to `solve_with_theory`'s verdict. A SAT verdict is additionally
//! *model-checked*: the returned model must satisfy every input clause AND every
//! axiom (so a "lucky" unsound SAT cannot slip through even if the brute-force
//! oracle had a bug).
//!
//! Separately, `analyze_theory_conflict` is INSTRUMENTED (see
//! `solve_with_theory_probe`, which re-implements the public driver but routes
//! conflict analysis through an instrumented copy) to detect whether the
//! `p == None` / `Lit::from_code(0)` placeholder at conflict.rs:342 can ever leak
//! into a learned clause.
//!
//! Run with:  cargo test -p oxiz-sat --test theory_callback_fuzz -- --ignored --nocapture

#![allow(clippy::needless_range_loop)]

use oxiz_sat::{Lit, Solver, SolverResult, TheoryCallback, TheoryCheckResult, Var};
use smallvec::SmallVec;

// ---------------------------------------------------------------------------
// xorshift64* PRNG — deterministic, no external dev-dep needed.
// ---------------------------------------------------------------------------
struct Rng(u64);
impl Rng {
    fn new(seed: u64) -> Self {
        Rng(seed ^ 0x9E37_79B9_7F4A_7C15)
    }
    fn next_u64(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x >> 12;
        x ^= x << 25;
        x ^= x >> 27;
        self.0 = x;
        x.wrapping_mul(0x2545_F491_4F6C_DD1D)
    }
    fn below(&mut self, n: usize) -> usize {
        (self.next_u64() % (n as u64)) as usize
    }
    fn bool(&mut self) -> bool {
        self.next_u64() & 1 == 1
    }
}

// ---------------------------------------------------------------------------
// Instance description (so we can build a fresh solver per run + brute-force it).
// ---------------------------------------------------------------------------
struct Instance {
    num_vars: usize,
    /// Propositional input clauses (DIMACS-style, 1-based, signed). Var i -> i+1.
    sat_clauses: Vec<Vec<i32>>,
    /// Theory axiom clauses, the SAME (¬p ∨ q) the theory may emit. DIMACS form.
    /// These are entailed by `a_star` (rejection sampled), so adding them is sound.
    axioms: Vec<[i32; 2]>,
    /// Secret model over all vars (only theory vars are constrained by axioms,
    /// but a_star is total so we can check axiom satisfaction trivially).
    a_star: Vec<bool>,
    /// Which variables are "theory" variables (axioms only reference these).
    theory_vars: Vec<usize>,
}

fn dimacs_to_lit(d: i32) -> Lit {
    Lit::from_dimacs(d)
}
fn lit_sat_by(d: i32, assign: &[bool]) -> bool {
    let v = (d.unsigned_abs() - 1) as usize;
    if d > 0 {
        assign[v]
    } else {
        !assign[v]
    }
}

fn gen_instance(rng: &mut Rng) -> Instance {
    // Small enough that brute force (2^num_vars) is cheap, but big enough to
    // create real decision/propagation/backtrack interplay.
    let num_vars = 4 + rng.below(7); // 4..=10
    let a_star: Vec<bool> = (0..num_vars).map(|_| rng.bool()).collect();

    // Pick a subset of variables to be theory variables (at least 2).
    let mut theory_vars: Vec<usize> = Vec::new();
    for v in 0..num_vars {
        if rng.bool() {
            theory_vars.push(v);
        }
    }
    while theory_vars.len() < 2 {
        let v = rng.below(num_vars);
        if !theory_vars.contains(&v) {
            theory_vars.push(v);
        }
    }

    // Theory axioms: random (¬p ∨ q) over theory vars that a_star satisfies.
    let n_ax = rng.below(2 * num_vars + 1); // 0..=2N
    let mut axioms: Vec<[i32; 2]> = Vec::new();
    let mut attempts = 0;
    while axioms.len() < n_ax && attempts < 50 * (n_ax + 1) {
        attempts += 1;
        let p = theory_vars[rng.below(theory_vars.len())];
        let q = theory_vars[rng.below(theory_vars.len())];
        if p == q {
            continue;
        }
        // Random polarity for each side, then keep only a_star-satisfied clauses.
        let lp = if rng.bool() { p as i32 + 1 } else { -(p as i32 + 1) };
        let lq = if rng.bool() { q as i32 + 1 } else { -(q as i32 + 1) };
        // Axiom clause is (lp ∨ lq); keep iff satisfied by a_star (=> entailed).
        if lit_sat_by(lp, &a_star) || lit_sat_by(lq, &a_star) {
            axioms.push([lp, lq]);
        }
    }

    // Propositional input clauses (1..=3 literals), unconstrained — these are the
    // ones that can make the instance UNSAT against the theory.
    let n_clauses = rng.below(3 * num_vars + 2);
    let mut sat_clauses: Vec<Vec<i32>> = Vec::new();
    for _ in 0..n_clauses {
        let k = 1 + rng.below(3);
        let mut cl: Vec<i32> = Vec::new();
        for _ in 0..k {
            let v = rng.below(num_vars) as i32 + 1;
            let l = if rng.bool() { v } else { -v };
            if !cl.contains(&l) && !cl.contains(&-l) {
                cl.push(l);
            }
        }
        if !cl.is_empty() {
            sat_clauses.push(cl);
        }
    }

    Instance {
        num_vars,
        sat_clauses,
        axioms,
        a_star,
        theory_vars,
    }
}

impl Instance {
    /// Ground truth: is (sat_clauses ∧ axioms) propositionally satisfiable?
    /// Brute force over all 2^num_vars assignments.
    fn ground_truth_sat(&self) -> bool {
        let n = self.num_vars;
        assert!(n <= 24, "brute force guard");
        for mask in 0u32..(1u32 << n) {
            let assign: Vec<bool> = (0..n).map(|i| (mask >> i) & 1 == 1).collect();
            if self.assignment_ok(&assign) {
                return true;
            }
        }
        false
    }

    fn assignment_ok(&self, assign: &[bool]) -> bool {
        for cl in &self.sat_clauses {
            if !cl.iter().any(|&d| lit_sat_by(d, assign)) {
                return false;
            }
        }
        for ax in &self.axioms {
            if !ax.iter().any(|&d| lit_sat_by(d, assign)) {
                return false;
            }
        }
        true
    }

    fn build_solver(&self) -> Solver {
        let mut s = Solver::new();
        s.ensure_vars(self.num_vars);
        for cl in &self.sat_clauses {
            s.add_clause(cl.iter().map(|&d| dimacs_to_lit(d)));
        }
        s
    }
}

// ---------------------------------------------------------------------------
// The sound theory callback.
// ---------------------------------------------------------------------------
struct GroundTheory<'a> {
    inst: &'a Instance,
    /// value[v] : Some(true/false) if theory var v currently assigned, else None.
    value: Vec<Option<bool>>,
    /// level[v] : the decision level at which value[v] was last set (for undo).
    level_of: Vec<u32>,
    current_level: u32,
    /// For instrumentation / sanity: number of conflicts & propagations emitted.
    conflicts: usize,
    propagations: usize,
}

impl<'a> GroundTheory<'a> {
    fn new(inst: &'a Instance) -> Self {
        GroundTheory {
            inst,
            value: vec![None; inst.num_vars],
            level_of: vec![0; inst.num_vars],
            current_level: 0,
            conflicts: 0,
            propagations: 0,
        }
    }

    fn is_theory_var(&self, v: usize) -> bool {
        self.inst.theory_vars.contains(&v)
    }

    /// lit value under current partial theory assignment, if known.
    fn lit_val(&self, dimacs: i32) -> Option<bool> {
        let v = (dimacs.unsigned_abs() - 1) as usize;
        self.value[v].map(|b| if dimacs > 0 { b } else { !b })
    }

    fn record(&mut self, lit: Lit) {
        let v = lit.var().index();
        if v >= self.value.len() || !self.is_theory_var(v) {
            return;
        }
        // The engine's on_assignment is AUTHORITATIVE for this literal right now.
        // Always overwrite (a var may be reassigned across backtracks/restarts) and
        // stamp the current decision level so on_backtrack can undo it precisely.
        // (The earlier "only set when None" tracking could desync from the trail
        // after a reassignment and let final_check pass on a stale value.)
        self.value[v] = Some(lit.is_pos());
        self.level_of[v] = self.current_level;
    }

    /// After recording a fresh assignment, scan axioms for a conflict/propagation.
    /// Returns at most ONE result per call (engine re-queries until Sat).
    fn check_axioms(&mut self) -> TheoryCheckResult {
        // First pass: look for an outright conflict (both axiom lits false).
        for ax in &self.inst.axioms {
            let a = self.lit_val(ax[0]);
            let b = self.lit_val(ax[1]);
            if a == Some(false) && b == Some(false) {
                // clause (ax0 ∨ ax1) is fully falsified -> conflict literals are
                // exactly the (currently-false) clause literals.
                self.conflicts += 1;
                let mut c: SmallVec<[Lit; 8]> = SmallVec::new();
                c.push(dimacs_to_lit(ax[0]));
                c.push(dimacs_to_lit(ax[1]));
                return TheoryCheckResult::Conflict(c);
            }
        }
        // Second pass: unit propagation. axiom (l0 ∨ l1): if one lit is false and
        // the other unassigned, force the unassigned one true. reason = the
        // currently-TRUE literals whose negation appears in the clause, i.e. the
        // negation of the false literal.
        let mut props: Vec<(Lit, SmallVec<[Lit; 8]>)> = Vec::new();
        for ax in &self.inst.axioms {
            let a = self.lit_val(ax[0]);
            let b = self.lit_val(ax[1]);
            let (force, other) = if a == Some(false) && b.is_none() {
                (ax[1], ax[0]) // force ax[1] true; ax[0] is false
            } else if b == Some(false) && a.is_none() {
                (ax[0], ax[1]) // force ax[0] true; ax[1] is false
            } else {
                continue;
            };
            // reason clause must be (force ∨ ¬reason[0]). The axiom clause is
            // (force ∨ other) with `other` false. So ¬reason[0] = other, i.e.
            // reason[0] = ¬other, which is currently TRUE. Sound unit reason.
            let force_lit = dimacs_to_lit(force);
            let reason_lit = dimacs_to_lit(-other); // negation of the false lit
            debug_assert_eq!(self.lit_val(-other), Some(true));
            let mut reason: SmallVec<[Lit; 8]> = SmallVec::new();
            reason.push(reason_lit);
            props.push((force_lit, reason));
        }
        if props.is_empty() {
            TheoryCheckResult::Sat
        } else {
            self.propagations += props.len();
            TheoryCheckResult::Propagated(props)
        }
    }
}

impl<'a> TheoryCallback for GroundTheory<'a> {
    fn on_assignment(&mut self, lit: Lit) -> TheoryCheckResult {
        self.record(lit);
        self.check_axioms()
    }

    fn final_check(&mut self) -> TheoryCheckResult {
        // All SAT vars assigned; ensure every axiom holds (it must, since the
        // theory vars are now fully assigned and every conflict/prop was handled,
        // but re-scan defensively — a stale axiom violation would be a bug).
        self.check_axioms()
    }

    fn on_new_level(&mut self, level: u32) {
        self.current_level = level;
    }

    fn on_backtrack(&mut self, level: u32) {
        self.current_level = level;
        // Unassign every theory var whose recorded level is strictly above the
        // backtrack level. Scanning all vars (vs a stack) is O(num_vars) but
        // bulletproof against any level desync — the differential oracle must not
        // itself be the source of a false soundness signal.
        for v in 0..self.value.len() {
            if self.value[v].is_some() && self.level_of[v] > level {
                self.value[v] = None;
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Model-check a SAT verdict from the engine.
// ---------------------------------------------------------------------------
fn engine_model_ok(inst: &Instance, s: &Solver) -> bool {
    use oxiz_sat::LBool;
    let assign: Vec<bool> = (0..inst.num_vars)
        .map(|i| match s.model_value(Var::new(i as u32)) {
            LBool::True => true,
            LBool::False => false,
            // Unassigned in model: pick a_star to give it best chance; any
            // completion that satisfies is fine, but engine should assign all.
            LBool::Undef => inst.a_star[i],
        })
        .collect();
    inst.assignment_ok(&assign)
}

/// Replay a SINGLE seed (THEORY_FUZZ_SEED) and dump the instance + verdict, plus
/// the (clauses ∧ axioms) CNF in DIMACS so it can be cross-checked with z3/cadical.
/// Used to minimize / root-cause a flagged unsound seed.
#[test]
#[ignore = "single-seed repro; set THEORY_FUZZ_SEED"]
fn theory_callback_single_seed_repro() {
    let seed: Option<u64> = std::env::var("THEORY_FUZZ_SEED")
        .ok()
        .and_then(|s| {
            let s = s.trim();
            if let Some(h) = s.strip_prefix("0x").or_else(|| s.strip_prefix("0X")) {
                u64::from_str_radix(h, 16).ok()
            } else {
                s.parse().ok()
            }
        });
    let Some(seed) = seed else {
        eprintln!("THEORY_FUZZ_SEED not set; nothing to replay (this test is a manual repro tool)");
        return;
    };

    let mut rng = Rng::new(seed);
    let inst = gen_instance(&mut rng);
    let truth = inst.ground_truth_sat();
    let mut solver = inst.build_solver();
    let mut theory = GroundTheory::new(&inst);
    let res = solver.solve_with_theory(&mut theory);
    let engine_sat = matches!(res, SolverResult::Sat);
    let model_ok = engine_sat && engine_model_ok(&inst, &solver);

    eprintln!("seed={seed:#018x}");
    eprintln!("num_vars={}", inst.num_vars);
    eprintln!("theory_vars={:?}", inst.theory_vars);
    eprintln!("sat_clauses={:?}", inst.sat_clauses);
    eprintln!("axioms={:?}", inst.axioms);
    eprintln!("a_star={:?}", inst.a_star);
    eprintln!("ground_truth_sat={truth} engine={res:?} model_ok={model_ok}");
    if engine_sat {
        use oxiz_sat::LBool;
        let m: Vec<i32> = (0..inst.num_vars)
            .map(|i| match solver.model_value(Var::new(i as u32)) {
                LBool::True => i as i32 + 1,
                _ => -(i as i32 + 1),
            })
            .collect();
        eprintln!("engine_model={m:?}");
    }

    // DIMACS dump of (clauses ∧ axioms) for external cross-check.
    let total = inst.sat_clauses.len() + inst.axioms.len();
    eprintln!("---DIMACS---");
    eprintln!("p cnf {} {}", inst.num_vars, total);
    for cl in &inst.sat_clauses {
        eprintln!("{} 0", cl.iter().map(|d| d.to_string()).collect::<Vec<_>>().join(" "));
    }
    for ax in &inst.axioms {
        eprintln!("{} {} 0", ax[0], ax[1]);
    }
    eprintln!("---END---");
}

// ---------------------------------------------------------------------------
// MAIN DIFFERENTIAL FUZZ
// ---------------------------------------------------------------------------
#[test]
#[ignore = "heavy differential fuzz; run with --ignored"]
fn theory_callback_differential_fuzz() {
    let iters: u64 = std::env::var("THEORY_FUZZ_ITERS")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(20_000);
    let base_seed: u64 = std::env::var("THEORY_FUZZ_SEED")
        .ok()
        .and_then(|s| {
            let s = s.trim();
            if let Some(hex) = s.strip_prefix("0x").or_else(|| s.strip_prefix("0X")) {
                u64::from_str_radix(hex, 16).ok()
            } else {
                s.parse().ok()
            }
        })
        .unwrap_or(0xC0FF_EE00_1234_5678);

    let mut unsound: Vec<u64> = Vec::new();
    let mut n_sat = 0u64;
    let mut n_unsat = 0u64;
    let mut n_exercised_conflict = 0u64;
    let mut n_exercised_prop = 0u64;

    for i in 0..iters {
        let seed = base_seed.wrapping_add(i.wrapping_mul(0x9E37_79B9_7F4A_7C15));
        let mut rng = Rng::new(seed);
        let inst = gen_instance(&mut rng);

        let truth = inst.ground_truth_sat();

        let mut solver = inst.build_solver();
        let mut theory = GroundTheory::new(&inst);
        let res = solver.solve_with_theory(&mut theory);

        if theory.conflicts > 0 {
            n_exercised_conflict += 1;
        }
        if theory.propagations > 0 {
            n_exercised_prop += 1;
        }

        let engine_sat = match res {
            SolverResult::Sat => true,
            SolverResult::Unsat => false,
            SolverResult::Unknown => {
                // Unknown is never unsound, but we don't expect it here.
                continue;
            }
        };

        // Disagreement with ground truth => potential soundness/completeness bug.
        let mut bad = engine_sat != truth;
        // A SAT verdict whose model fails to satisfy the instance is DEFINITELY
        // unsound (independent of the brute-force oracle).
        if engine_sat && !engine_model_ok(&inst, &solver) {
            bad = true;
        }

        if engine_sat {
            n_sat += 1;
        } else {
            n_unsat += 1;
        }

        if bad {
            unsound.push(seed);
            if unsound.len() <= 5 {
                eprintln!(
                    "UNSOUND seed={seed:#018x} engine_sat={engine_sat} truth={truth} \
                     nv={} sat_clauses={} axioms={} theory_vars={:?} model_ok={}",
                    inst.num_vars,
                    inst.sat_clauses.len(),
                    inst.axioms.len(),
                    inst.theory_vars,
                    engine_sat && engine_model_ok(&inst, &solver),
                );
                eprintln!("  sat_clauses = {:?}", inst.sat_clauses);
                eprintln!("  axioms      = {:?}", inst.axioms);
                eprintln!("  a_star      = {:?}", inst.a_star);
            }
        }
    }

    eprintln!(
        "theory fuzz: iters={iters} sat={n_sat} unsat={n_unsat} \
         exercised_conflict={n_exercised_conflict} exercised_prop={n_exercised_prop} \
         unsound={}",
        unsound.len()
    );
    assert!(
        n_exercised_conflict > 0,
        "fuzz never triggered a theory conflict (analyze_theory_conflict not exercised)"
    );
    assert!(
        n_exercised_prop > 0,
        "fuzz never triggered a theory propagation (add_theory_reason_clause not exercised)"
    );
    assert!(
        unsound.is_empty(),
        "{} unsound verdicts; first seeds = {:?}",
        unsound.len(),
        &unsound[..unsound.len().min(10)]
    );
}

// ===========================================================================
// PLACEHOLDER-LEAK PROBE (feature `theory-probe`)
// ===========================================================================
// These tests require `--features theory-probe`, which instruments
// analyze_theory_conflict to count how often the `p == None` /
// `Lit::from_code(0)` placeholder survives into the learned clause. Without the
// feature the bodies degrade to a no-op so the file still compiles.

/// Re-run the SAME differential corpus while counting placeholder leaks.
/// Reports the exact count; does NOT (yet) assert on it, since whether the leak
/// is reachable is the question under investigation.
#[test]
#[ignore = "requires --features theory-probe; run with --ignored"]
fn theory_conflict_placeholder_leak_survey() {
    #[cfg(not(feature = "theory-probe"))]
    {
        eprintln!(
            "theory-probe feature OFF; rebuild with \
             `--features theory-probe` to run this survey"
        );
    }
    #[cfg(feature = "theory-probe")]
    {
        use oxiz_sat::theory_probe;
        let iters: u64 = std::env::var("THEORY_FUZZ_ITERS")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(50_000);
        let base_seed: u64 = 0xC0FF_EE00_1234_5678;

        theory_probe::reset();
        let mut total_conflicts = 0u64;
        for i in 0..iters {
            let seed = base_seed.wrapping_add(i.wrapping_mul(0x9E37_79B9_7F4A_7C15));
            let mut rng = Rng::new(seed);
            let inst = gen_instance(&mut rng);
            let mut solver = inst.build_solver();
            let mut theory = GroundTheory::new(&inst);
            let _ = solver.solve_with_theory(&mut theory);
            total_conflicts += theory.conflicts as u64;
        }
        let snap = theory_probe::snapshot();
        eprintln!(
            "placeholder-leak survey: iters={iters} theory_conflicts_emitted={total_conflicts} \
             analyze_theory_conflict_calls={} no_uip={} placeholder_in_clause={} \
             zero_counter_nonroot={}",
            snap.calls, snap.no_uip, snap.placeholder_in_clause, snap.zero_counter_nonroot
        );
        // A leak (placeholder_in_clause) must NEVER be observed in the FIXED engine.
        assert_eq!(
            snap.placeholder_in_clause, 0,
            "placeholder leaked into a learned clause during the random survey"
        );
    }
}

/// Construct the EXACT structural trigger for the placeholder leak by hand:
/// a theory conflict whose literals live at a decision level strictly between 0
/// and the current level, with NO conflict literal at the current level. In that
/// case `analyze_theory_conflict` takes neither the all-level-0 early return nor
/// enters the UIP loop (counter stays 0), so `p` stays `None` and `learnt[0]`
/// keeps the `Lit::from_code(0)` placeholder.
///
/// This uses a bespoke theory that fires a conflict only at the moment described.
#[test]
#[ignore = "requires --features theory-probe; run with --ignored"]
fn theory_conflict_placeholder_leak_targeted() {
    #[cfg(not(feature = "theory-probe"))]
    {
        eprintln!("theory-probe feature OFF; rebuild with `--features theory-probe`");
    }
    #[cfg(feature = "theory-probe")]
    {
        use oxiz_sat::{theory_probe, LBool};

        // A theory engineered to produce a conflict whose literals all live at a
        // decision level STRICTLY between 0 and the current level, with NONE at the
        // current level — the exact precondition for analyze_theory_conflict to skip
        // both the all-level-0 early return AND the UIP loop, leaving learnt[0] as
        // the Lit::from_code(0) placeholder.
        //
        // Mechanism:
        //   * When the brancher decides v_anchor (var 3) TRUE at level 1, the theory
        //     PROPAGATES v_target (var 0) FALSE with a valid reason clause
        //     (¬v0 ∨ ¬v3) [a declared theory lemma]. v0 is now FALSE at level 1.
        //   * The theory then reports Sat, letting the brancher make a fresh
        //     decision (var 1) at level 2.
        //   * On that level-2 assignment the theory fires a ONE-LITERAL conflict
        //     [Lit::pos(v0)] — v0 is false (so the literal is false, satisfying the
        //     "all conflict lits false" contract), and it sits at level 1 < 2.
        //
        // analyze_theory_conflict then: pushes v0 to learnt (level 1 ≠ current 2),
        // counter stays 0, not-all-level-0 ⇒ UIP loop skipped ⇒ p == None ⇒
        // learnt[0] is the placeholder. LEAK.
        struct CrossLevelConflict {
            anchor: Var,  // v3: when decided true, triggers the propagation
            target: Var,  // v0: propagated false at level 1, then used as conflict
            propagated: bool,
            level: u32,
            target_level_at_prop: u32,
        }
        impl TheoryCallback for CrossLevelConflict {
            fn on_assignment(&mut self, lit: Lit) -> TheoryCheckResult {
                // Step 1: anchor assigned at level >= 1 -> propagate target false.
                if !self.propagated && lit.var() == self.anchor && self.level >= 1 {
                    self.propagated = true;
                    self.target_level_at_prop = self.level;
                    // reason = [the anchor literal that is currently TRUE] -> clause
                    // (¬target ∨ ¬anchor_lit). A theory lemma we hereby declare.
                    let mut reason: SmallVec<[Lit; 8]> = SmallVec::new();
                    reason.push(lit); // the just-assigned (currently TRUE) anchor lit
                    let mut props = Vec::new();
                    props.push((Lit::neg(self.target), reason));
                    return TheoryCheckResult::Propagated(props);
                }
                // Step 2: at a strictly higher level, fire a conflict on the target,
                // which is FALSE and sits below the current level.
                if self.propagated && self.level > self.target_level_at_prop {
                    let mut c: SmallVec<[Lit; 8]> = SmallVec::new();
                    c.push(Lit::pos(self.target)); // currently FALSE (target=false)
                    return TheoryCheckResult::Conflict(c);
                }
                TheoryCheckResult::Sat
            }
            fn final_check(&mut self) -> TheoryCheckResult {
                if self.propagated && self.level > self.target_level_at_prop {
                    let mut c: SmallVec<[Lit; 8]> = SmallVec::new();
                    c.push(Lit::pos(self.target));
                    return TheoryCheckResult::Conflict(c);
                }
                TheoryCheckResult::Sat
            }
            fn on_new_level(&mut self, level: u32) {
                self.level = level;
            }
            fn on_backtrack(&mut self, level: u32) {
                self.level = level;
                if level < self.target_level_at_prop {
                    self.propagated = false;
                }
            }
        }

        // 6 free vars, only loosely constrained so the brancher makes several
        // decisions (giving us a level-2 decision on top of the level-1 propagation).
        let mut s = Solver::new();
        s.ensure_vars(6);
        // A few clauses to keep multiple vars live without forcing everything at
        // level 0 (avoid units). Each clause has >= 2 literals.
        s.add_clause([Lit::pos(Var::new(1)), Lit::pos(Var::new(2))]);
        s.add_clause([Lit::pos(Var::new(2)), Lit::neg(Var::new(4))]);
        s.add_clause([Lit::pos(Var::new(4)), Lit::pos(Var::new(5))]);
        s.add_clause([Lit::neg(Var::new(1)), Lit::pos(Var::new(5))]);

        // The default brancher decides v0 first (level 1). Use it as the anchor;
        // the target is a var that will otherwise be decided later (v3) — we steal
        // it by propagating it false at level 1, then fire the conflict on it once a
        // level-2 decision lands on top.
        let mut theory = CrossLevelConflict {
            anchor: Var::new(0),
            target: Var::new(3),
            propagated: false,
            level: 0,
            target_level_at_prop: 0,
        };
        theory_probe::reset();
        let res = s.solve_with_theory(&mut theory);
        let snap = theory_probe::snapshot();
        eprintln!(
            "targeted leak attempt: result={res:?} \
             analyze_theory_conflict_calls={} no_uip={} zero_counter_nonroot={} \
             placeholder_in_clause={} var0={:?}",
            snap.calls,
            snap.no_uip,
            snap.zero_counter_nonroot,
            snap.placeholder_in_clause,
            s.model_value(Var::new(0))
        );
        let _ = LBool::Undef;

        // The scenario MUST reach the leak precondition (no-UIP / zero-counter
        // branch); that proves the latent path is reachable.
        assert!(
            snap.no_uip > 0 && snap.zero_counter_nonroot > 0,
            "targeted scenario failed to reach the analyze_theory_conflict no-UIP branch \
             (the leak precondition)"
        );
        assert!(snap.calls > 0, "analyze_theory_conflict was never called");

        // EXPECTATION on the FIXED engine: even though the no-UIP branch is taken,
        // the var-0 placeholder Lit::from_code(0) is NEVER returned in a learned
        // clause. On the UNFIXED engine this would be > 0 (and would also assign the
        // bogus var-0 literal as a propagation + thrash the search).
        assert_eq!(
            snap.placeholder_in_clause, 0,
            "placeholder leaked into the learned clause (engine NOT fixed)"
        );
    }
}

// ===========================================================================
// SOUNDNESS IMPACT of the placeholder leak: differential vs ground truth.
// ===========================================================================
// We build a CLEAN, FIXED-CLAUSE theory (so SAT(input ∧ lemmas) is a well-defined
// oracle) whose conflict is reported LAZILY — only after a decision is taken above
// the level at which the conflict literal was falsified — which is exactly the
// shape that drives analyze_theory_conflict into the placeholder-leak branch. We
// then check the engine's verdict against the brute-force oracle. A disagreement,
// or a SAT model violating a clause/lemma, is an unsoundness directly attributable
// to the leak.
#[test]
#[ignore = "soundness witness for the placeholder leak; run with --ignored"]
fn theory_conflict_placeholder_leak_soundness() {
    // Fixed theory lemmas (as DIMACS clauses), all 2-literal:
    //   L1 = (¬x0 ∨ ¬x3)   "if x0 then not x3"   [drives the propagation x3:=false]
    //   L2 = (x3 ∨ x0)      "x3 or x0"            [the lazily-reported conflict clause]
    // Note L1 ∧ L2 is satisfiable (e.g. x0=true,x3=false), so the lemmas are
    // mutually consistent and represent a genuine sound theory.
    let lemmas: [[i32; 2]; 2] = [[-1, -4], [4, 1]];
    // Input clauses: keep several vars live so the brancher makes >= 2 decisions.
    let input: Vec<Vec<i32>> = vec![
        vec![2, 3],
        vec![3, -5],
        vec![5, 6],
        vec![-2, 6],
    ];
    let num_vars = 6;

    // ---- ground truth: SAT(input ∧ lemmas)? brute force ----
    let lit_ok = |d: i32, a: &[bool]| -> bool {
        let v = (d.unsigned_abs() - 1) as usize;
        if d > 0 {
            a[v]
        } else {
            !a[v]
        }
    };
    let assignment_ok = |a: &[bool]| -> bool {
        input
            .iter()
            .all(|cl| cl.iter().any(|&d| lit_ok(d, a)))
            && lemmas.iter().all(|cl| cl.iter().any(|&d| lit_ok(d, a)))
    };
    let mut truth = false;
    for mask in 0u32..(1u32 << num_vars) {
        let a: Vec<bool> = (0..num_vars).map(|i| (mask >> i) & 1 == 1).collect();
        if assignment_ok(&a) {
            truth = true;
            break;
        }
    }

    // ---- a sound, fixed-clause theory with LAZY conflict reporting ----
    // It tracks assignments to x0,x3. When x0 becomes true it propagates x3 false
    // (reason = [x0], clause (¬x3 ∨ ¬x0) = L1). It reports the L2 conflict (x3 ∨ x0)
    // only once BOTH are false AND a strictly higher decision level has been
    // entered (lazy), producing the cross-level structure.
    struct LazyTheory {
        val: [Option<bool>; 6],
        lvl: [u32; 6],
        level: u32,
        x3_propagated: bool,
        x3_prop_level: u32,
    }
    impl LazyTheory {
        fn set(&mut self, lit: Lit) {
            let v = lit.var().index();
            if v < 6 && self.val[v].is_none() {
                self.val[v] = Some(lit.is_pos());
                self.lvl[v] = self.level;
            }
        }
    }
    impl TheoryCallback for LazyTheory {
        fn on_assignment(&mut self, lit: Lit) -> TheoryCheckResult {
            self.set(lit);
            // Propagate x3 := false when x0 := true (lemma L1 = (¬x0 ∨ ¬x3)).
            if self.val[0] == Some(true) && self.val[3].is_none() {
                self.x3_propagated = true;
                self.x3_prop_level = self.level;
                let mut reason: SmallVec<[Lit; 8]> = SmallVec::new();
                reason.push(Lit::pos(Var::new(0))); // x0 currently true
                let mut props = Vec::new();
                props.push((Lit::neg(Var::new(3)), reason));
                return TheoryCheckResult::Propagated(props);
            }
            // LAZY conflict on L2 = (x3 ∨ x0): both false, reported only after a
            // higher decision level exists than where x3 was falsified.
            if self.val[3] == Some(false)
                && self.val[0] == Some(false)
                && self.x3_propagated
                && self.level > self.x3_prop_level
            {
                let mut c: SmallVec<[Lit; 8]> = SmallVec::new();
                c.push(Lit::pos(Var::new(3))); // false
                c.push(Lit::pos(Var::new(0))); // false
                return TheoryCheckResult::Conflict(c);
            }
            TheoryCheckResult::Sat
        }
        fn final_check(&mut self) -> TheoryCheckResult {
            // Enforce all lemmas at a full assignment (defensive completeness).
            let lemmas: [[i32; 2]; 2] = [[-1, -4], [4, 1]];
            for cl in &lemmas {
                let falsified = cl.iter().all(|&d| {
                    let v = (d.unsigned_abs() - 1) as usize;
                    match self.val[v] {
                        Some(b) => (d > 0) != b, // literal is false
                        None => false,
                    }
                });
                if falsified {
                    let mut c: SmallVec<[Lit; 8]> = SmallVec::new();
                    for &d in cl {
                        c.push(Lit::from_dimacs(d));
                    }
                    return TheoryCheckResult::Conflict(c);
                }
            }
            TheoryCheckResult::Sat
        }
        fn on_new_level(&mut self, level: u32) {
            self.level = level;
        }
        fn on_backtrack(&mut self, level: u32) {
            self.level = level;
            for v in 0..6 {
                if self.val[v].is_some() && self.lvl[v] > level {
                    self.val[v] = None;
                }
            }
            if level < self.x3_prop_level {
                self.x3_propagated = false;
            }
        }
    }

    let mut s = Solver::new();
    s.ensure_vars(num_vars);
    for cl in &input {
        s.add_clause(cl.iter().map(|&d| Lit::from_dimacs(d)));
    }
    let mut theory = LazyTheory {
        val: [None; 6],
        lvl: [0; 6],
        level: 0,
        x3_propagated: false,
        x3_prop_level: 0,
    };
    let res = s.solve_with_theory(&mut theory);

    let engine_sat = match res {
        SolverResult::Sat => true,
        SolverResult::Unsat => false,
        SolverResult::Unknown => {
            eprintln!("soundness witness: engine returned Unknown (no verdict)");
            return;
        }
    };

    // Independent model check on a SAT verdict.
    let mut model_ok = true;
    if engine_sat {
        use oxiz_sat::LBool;
        let a: Vec<bool> = (0..num_vars)
            .map(|i| matches!(s.model_value(Var::new(i as u32)), LBool::True))
            .collect();
        model_ok = assignment_ok(&a);
        eprintln!("soundness witness: engine SAT model = {a:?} model_ok={model_ok}");
    }

    eprintln!(
        "soundness witness: ground_truth_sat={truth} engine_sat={engine_sat} model_ok={model_ok}"
    );
    assert_eq!(
        engine_sat, truth,
        "VERDICT MISMATCH (placeholder-leak soundness bug): engine_sat={engine_sat} \
         ground_truth={truth}"
    );
    assert!(
        model_ok,
        "engine returned SAT with a model that violates an input clause or theory lemma"
    );
}

// ===========================================================================
// DETERMINISTIC SOUNDNESS REGRESSION TESTS
// ===========================================================================
// Each is a minimized instance found by the differential fuzz that exposed a
// real ENGINE soundness defect (cross-checked UNSAT/SAT with z3 + cadical +
// cryptominisat5). They run without env vars and assert the correct verdict.
//
// The theory here is the same SOUND ground theory as the fuzz: a fixed set of
// 2-literal axiom clauses, all entailed; it propagates a unit when one side is
// false and the other unassigned, and reports a conflict when both sides are
// false. (clauses ∧ axioms) is checked by brute force as the oracle.

struct FixedAxiomTheory {
    axioms: Vec<[i32; 2]>,
    val: Vec<Option<bool>>,
    level_of: Vec<u32>,
    level: u32,
}
impl FixedAxiomTheory {
    fn new(num_vars: usize, axioms: Vec<[i32; 2]>) -> Self {
        FixedAxiomTheory {
            axioms,
            val: vec![None; num_vars],
            level_of: vec![0; num_vars],
            level: 0,
        }
    }
    fn lv(&self, d: i32) -> Option<bool> {
        let v = (d.unsigned_abs() - 1) as usize;
        self.val[v].map(|b| if d > 0 { b } else { !b })
    }
    fn check(&mut self) -> TheoryCheckResult {
        for ax in &self.axioms {
            if self.lv(ax[0]) == Some(false) && self.lv(ax[1]) == Some(false) {
                let mut c: SmallVec<[Lit; 8]> = SmallVec::new();
                c.push(Lit::from_dimacs(ax[0]));
                c.push(Lit::from_dimacs(ax[1]));
                return TheoryCheckResult::Conflict(c);
            }
        }
        let mut props = Vec::new();
        for ax in &self.axioms {
            let a = self.lv(ax[0]);
            let b = self.lv(ax[1]);
            let (f, o) = if a == Some(false) && b.is_none() {
                (ax[1], ax[0])
            } else if b == Some(false) && a.is_none() {
                (ax[0], ax[1])
            } else {
                continue;
            };
            let mut r: SmallVec<[Lit; 8]> = SmallVec::new();
            r.push(Lit::from_dimacs(-o)); // currently true
            props.push((Lit::from_dimacs(f), r));
        }
        if props.is_empty() {
            TheoryCheckResult::Sat
        } else {
            TheoryCheckResult::Propagated(props)
        }
    }
}
impl TheoryCallback for FixedAxiomTheory {
    fn on_assignment(&mut self, lit: Lit) -> TheoryCheckResult {
        let v = lit.var().index();
        if v < self.val.len() {
            self.val[v] = Some(lit.is_pos());
            self.level_of[v] = self.level;
        }
        self.check()
    }
    fn final_check(&mut self) -> TheoryCheckResult {
        self.check()
    }
    fn on_new_level(&mut self, level: u32) {
        self.level = level;
    }
    fn on_backtrack(&mut self, level: u32) {
        self.level = level;
        for v in 0..self.val.len() {
            if self.val[v].is_some() && self.level_of[v] > level {
                self.val[v] = None;
            }
        }
    }
}

fn run_fixed(
    num_vars: usize,
    clauses: &[&[i32]],
    axioms: Vec<[i32; 2]>,
) -> (SolverResult, bool) {
    let mut s = Solver::new();
    s.ensure_vars(num_vars);
    for cl in clauses {
        s.add_clause(cl.iter().map(|&d| Lit::from_dimacs(d)));
    }
    let mut theory = FixedAxiomTheory::new(num_vars, axioms.clone());
    let res = s.solve_with_theory(&mut theory);
    let mut model_ok = true;
    if matches!(res, SolverResult::Sat) {
        use oxiz_sat::LBool;
        let a: Vec<bool> = (0..num_vars)
            .map(|i| matches!(s.model_value(Var::new(i as u32)), LBool::True))
            .collect();
        let ok = |d: i32| {
            let v = (d.unsigned_abs() - 1) as usize;
            if d > 0 { a[v] } else { !a[v] }
        };
        model_ok = clauses.iter().all(|cl| cl.iter().any(|&d| ok(d)))
            && axioms.iter().all(|ax| ax.iter().any(|&d| ok(d)));
    }
    (res, model_ok)
}

/// BUG 1 (analyze_theory_conflict reason-clause positional assumption): the
/// reason clause's implied literal is no longer at lits[0] after watch
/// reordering, so the UIP walk learns the wrong unit and over-commits.
/// z3/cadical/cryptominisat: SAT. Pre-fix engine returned UNSAT.
#[test]
fn regress_theory_conflict_reason_position_unsat() {
    let (res, ok) = run_fixed(
        7,
        &[&[-1, 3], &[-1, -4]],
        vec![[6, 4], [4, -3], [4, -6], [3, -4]],
    );
    assert_eq!(res, SolverResult::Sat, "spurious UNSAT (reason-position bug)");
    assert!(ok);
}

/// BUG 2 (regular analyze: all-level-0 conflict + reason positional assumption):
/// theory-learned level-0 units make an original clause all-false at level 0
/// while at a higher level; analyze fabricated a unit `(¬x6)` contradicting the
/// level-0 unit `(x6)`. z3/cadical: UNSAT. Pre-fix engine returned SAT.
#[test]
fn regress_bool_analyze_all_level0_sat() {
    let (res, ok) = run_fixed(
        7,
        &[&[-1, 7], &[7, 1], &[-5, -7], &[6], &[-7, -4]],
        vec![[-1, 7], [3, 5], [-3, -5], [-7, -1], [-7, 3], [-3, -7], [-7, -3]],
    );
    assert_eq!(res, SolverResult::Unsat, "spurious SAT (all-level-0 bug)");
    let _ = ok;
}

/// BUG 3 (no Boolean propagation after a theory-conflict unit is learned at
/// level 0): a level-0 contradiction created by the learned unit went
/// undetected and the engine decided over it, terminating SAT with a model
/// violating an input clause. z3/cadical: UNSAT. Pre-fix engine returned SAT.
#[test]
fn regress_post_theory_conflict_propagation_sat() {
    let (res, ok) = run_fixed(
        5,
        &[&[-1, -2], &[-5, -3], &[1, -5]],
        vec![[5, 3], [-1, -5], [-4, 3], [-1, 5], [-1, -3], [-1, 5], [-3, 5]],
    );
    assert_eq!(res, SolverResult::Unsat, "spurious SAT (post-conflict propagation bug)");
    let _ = ok;
}

/// Pure-SAT sanity: the `analyze` changes (identity-based reason resolution +
/// degenerate-conflict guard) must NOT affect the pure CDCL path. Differentially
/// check `solve()` (no theory) against brute force on thousands of random CNFs.
#[test]
#[ignore = "heavy; run with --ignored"]
fn pure_sat_unaffected_by_analyze_changes() {
    let iters: u64 = std::env::var("PURE_SAT_ITERS")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(20_000);
    let mut bad = 0u64;
    for i in 0..iters {
        let seed = 0x5EED_u64.wrapping_mul(i + 1).wrapping_add(0x1234_5678);
        let mut rng = Rng::new(seed);
        let nv = 3 + rng.below(7);
        let nc = rng.below(4 * nv + 1);
        let mut clauses: Vec<Vec<i32>> = Vec::new();
        for _ in 0..nc {
            let k = 1 + rng.below(3);
            let mut cl: Vec<i32> = Vec::new();
            for _ in 0..k {
                let v = rng.below(nv) as i32 + 1;
                let l = if rng.bool() { v } else { -v };
                if !cl.contains(&l) && !cl.contains(&-l) {
                    cl.push(l);
                }
            }
            if !cl.is_empty() {
                clauses.push(cl);
            }
        }
        // brute force
        let lit_ok = |d: i32, a: &[bool]| {
            let v = (d.unsigned_abs() - 1) as usize;
            if d > 0 { a[v] } else { !a[v] }
        };
        let mut truth = false;
        for mask in 0u32..(1u32 << nv) {
            let a: Vec<bool> = (0..nv).map(|j| (mask >> j) & 1 == 1).collect();
            if clauses.iter().all(|c| c.iter().any(|&d| lit_ok(d, &a))) {
                truth = true;
                break;
            }
        }
        let mut s = Solver::new();
        s.ensure_vars(nv);
        for c in &clauses {
            s.add_clause(c.iter().map(|&d| Lit::from_dimacs(d)));
        }
        let engine_sat = matches!(s.solve(), SolverResult::Sat);
        if engine_sat != truth {
            bad += 1;
            if bad <= 5 {
                eprintln!("PURE-SAT MISMATCH seed={seed:#x} engine={engine_sat} truth={truth} clauses={clauses:?}");
            }
        }
    }
    eprintln!("pure-sat sanity: iters={iters} mismatches={bad}");
    assert_eq!(bad, 0, "pure-SAT path regressed");
}
