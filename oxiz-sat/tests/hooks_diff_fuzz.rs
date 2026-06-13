//! Differential fuzz of the §4 redesign driver `solve_with_hooks` + `ToyImplTheory`
//! against an exhaustive brute-force oracle.
//!
//! For each random instance we build a small CNF plus a set of binary implication
//! axioms `premise ⇒ conclusion` (each equivalent to the clause
//! `[premise.negate(), conclusion]`). The ground truth — is `CNF ∧ axiom-clauses`
//! satisfiable? — is computed by brute force over all assignments. We then run
//! `solve_with_hooks` with `ToyImplTheory(axioms)` and require:
//!   * the SAT/UNSAT verdict matches the oracle, AND
//!   * on SAT, the returned model genuinely satisfies CNF ∧ axiom-clauses
//!     (so a "lucky" spurious SAT cannot pass).
//!
//! This targets the NEW driver loop (propagation/conflict routing, termination,
//! the trail-driven hooks) — the high-risk Phase-1 integration.

use oxiz_sat::{Lit, Solver, SolverResult, ToyImplTheory, Var};

/// Tiny deterministic LCG so the fuzz is reproducible with no external deps.
struct Rng(u64);
impl Rng {
    fn next_u64(&mut self) -> u64 {
        // SplitMix64.
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }
    fn below(&mut self, n: u64) -> u64 {
        self.next_u64() % n
    }
    fn coin(&mut self) -> bool {
        self.next_u64() & 1 == 0
    }
}

/// A literal as (var index, positive?).
#[derive(Clone, Copy, Debug)]
struct L {
    v: usize,
    pos: bool,
}

fn lit_sat(assign: u32, l: L) -> bool {
    let val = (assign >> l.v) & 1 == 1;
    val == l.pos
}

/// Brute-force satisfiability of CNF clauses + implication-axiom clauses.
fn brute_sat(nv: usize, clauses: &[Vec<L>], axioms: &[(L, L)]) -> bool {
    for assign in 0u32..(1u32 << nv) {
        let cnf_ok = clauses
            .iter()
            .all(|c| c.iter().any(|&l| lit_sat(assign, l)));
        if !cnf_ok {
            continue;
        }
        // axiom premise ⇒ conclusion  ≡  clause (¬premise ∨ conclusion)
        let ax_ok = axioms.iter().all(|&(p, c)| {
            let prem_neg = L { v: p.v, pos: !p.pos };
            lit_sat(assign, prem_neg) || lit_sat(assign, c)
        });
        if cnf_ok && ax_ok {
            return true;
        }
    }
    false
}

fn to_lit(l: L) -> Lit {
    if l.pos {
        Lit::pos(Var::new(l.v as u32))
    } else {
        Lit::neg(Var::new(l.v as u32))
    }
}

fn run_campaign(seed: u64, iters: usize) -> (usize, usize) {
    let mut rng = Rng(seed);
    let mut checked = 0usize;
    let mut unsound = 0usize;

    for _ in 0..iters {
        let nv = 3 + rng.below(4) as usize; // 3..=6 vars
        let nc = rng.below(8) as usize; // 0..=7 clauses
        let na = rng.below(4) as usize; // 0..=3 axioms

        let rand_lit = |rng: &mut Rng| -> L {
            L {
                v: rng.below(nv as u64) as usize,
                pos: rng.coin(),
            }
        };

        let mut clauses: Vec<Vec<L>> = Vec::new();
        for _ in 0..nc {
            let k = 1 + rng.below(3) as usize; // 1..=3 literals
            let mut c = Vec::new();
            for _ in 0..k {
                c.push(rand_lit(&mut rng));
            }
            clauses.push(c);
        }
        let mut axioms: Vec<(L, L)> = Vec::new();
        for _ in 0..na {
            axioms.push((rand_lit(&mut rng), rand_lit(&mut rng)));
        }

        let truth = brute_sat(nv, &clauses, &axioms);

        // Build the solver instance.
        let mut solver = Solver::new();
        for _ in 0..nv {
            solver.new_var();
        }
        for c in &clauses {
            solver.add_clause(c.iter().map(|&l| to_lit(l)));
        }
        let theory = ToyImplTheory::new(
            axioms.iter().map(|&(p, c)| (to_lit(p), to_lit(c))).collect(),
        );
        let (result, _t) = solver.solve_with_hooks(theory);

        checked += 1;
        match result {
            SolverResult::Sat => {
                if !truth {
                    unsound += 1; // SPURIOUS SAT (truth = UNSAT)
                    eprintln!("[hooks-fuzz] spurious SAT: nv={nv} clauses={clauses:?} axioms exist");
                    continue;
                }
                // Independently validate the returned model satisfies CNF ∧ axioms.
                let mut assign = 0u32;
                for v in 0..nv {
                    if solver.model_value(Var::new(v as u32)).is_true() {
                        assign |= 1 << v;
                    }
                }
                let cnf_ok = clauses
                    .iter()
                    .all(|c| c.iter().any(|&l| lit_sat(assign, l)));
                let ax_ok = axioms.iter().all(|&(p, c)| {
                    let pn = L { v: p.v, pos: !p.pos };
                    lit_sat(assign, pn) || lit_sat(assign, c)
                });
                if !(cnf_ok && ax_ok) {
                    unsound += 1; // model does not actually satisfy the constraints
                    eprintln!("[hooks-fuzz] SAT model invalid: nv={nv}");
                }
            }
            SolverResult::Unsat => {
                if truth {
                    unsound += 1; // SPURIOUS UNSAT (truth = SAT) — the dangerous one
                    eprintln!("[hooks-fuzz] SPURIOUS UNSAT: nv={nv} clauses={clauses:?} axioms={axioms:?}");
                }
            }
            SolverResult::Unknown => {}
        }
    }
    (checked, unsound)
}

#[test]
fn hooks_driver_vs_bruteforce() {
    // A few thousand instances across several seeds; fast (small instances).
    let mut total_checked = 0;
    let mut total_unsound = 0;
    for &seed in &[
        0x1u64, 0xBEEF, 0xC0FFEE, 0x9E3779B9, 0xDEAD, 0x42, 0x7777, 0xABCDEF, 0x12345, 0xFEED,
    ] {
        let (c, u) = run_campaign(seed, 3000);
        total_checked += c;
        total_unsound += u;
    }
    println!("[hooks-fuzz] checked={total_checked} unsound={total_unsound}");
    assert_eq!(total_unsound, 0, "solve_with_hooks disagreed with brute force");
}
