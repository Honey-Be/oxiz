//! Black-box GROUND soundness audit: differential fuzzing of OxiZ's
//! quantifier-FREE EUF+LIA solving against z3.
//!
//! Motivation: the clean quantifier engine (`oxiz-mbqi`) is sound *given a
//! sound host ground core*. The M4e-3 corpus run surfaced a spurious `unsat`
//! whose root is OxiZ's GROUND solver mishandling a deep EUF+LIA instance set
//! (`UFLIA/injective.smt2`). This harness generates random ground QF_UFLIA
//! problems, solves each with OxiZ (clean off — pure ground) and with z3, and
//! flags every UNSOUND disagreement:
//!   * spurious UNSAT — OxiZ `unsat`, z3 `sat`   (the dangerous one)
//!   * spurious SAT   — OxiZ `sat`,   z3 `unsat`
//! On the first unsound case it delta-debugs the assertion list to a minimal
//! reproducer and prints it as SMT-LIB.
//!
//! Heavy + needs `z3` on PATH → `#[ignore]`. Run:
//!   cargo test -p oxiz-solver --test ground_soundness_fuzz -- --ignored --nocapture
//! Tune with OXIZ_FUZZ_N (cases, default 1500) and OXIZ_FUZZ_SEED.

use oxiz_solver::Context;
use std::io::Write;
use std::process::{Command, Stdio};

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum V {
    Sat,
    Unsat,
    Unknown,
}

fn parse_v(s: &str) -> Option<V> {
    s.lines().rev().find_map(|l| match l.trim() {
        "sat" => Some(V::Sat),
        "unsat" => Some(V::Unsat),
        "unknown" => Some(V::Unknown),
        _ => None,
    })
}

fn solve_z3(script: &str) -> Option<V> {
    let mut child = Command::new("z3")
        .args(["-in", "-T:5"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .spawn()
        .ok()?;
    child.stdin.take()?.write_all(script.as_bytes()).ok()?;
    let out = child.wait_with_output().ok()?;
    parse_v(&String::from_utf8_lossy(&out.stdout))
}

fn solve_oxiz(script: &str) -> V {
    // Pure ground: clean_mbqi stays OFF (default); the scripts have no
    // quantifiers, so neither engine instantiates.
    let mut ctx = Context::new();
    ctx.set_timeout_ms(4000);
    match ctx.execute_script(script) {
        Ok(out) => out
            .iter()
            .rev()
            .find_map(|l| parse_v(l))
            .unwrap_or(V::Unknown),
        Err(_) => V::Unknown,
    }
}

// ---- deterministic PRNG -----------------------------------------------------
struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.0 >> 33
    }
    fn upto(&mut self, n: usize) -> usize {
        (self.next() as usize) % n.max(1)
    }
    fn chance(&mut self, num: usize, den: usize) -> bool {
        self.upto(den) < num
    }
}

// ---- random ground QF_UFLIA generator --------------------------------------
/// Build a random ground problem. Returns (full_script, assertion_lines) so the
/// minimizer can drop assertions independently.
fn gen_problem(rng: &mut Rng) -> (String, Vec<String>) {
    // term pool of ground Int terms
    let consts = ["a", "b", "c", "d"];
    let ints = ["0", "1", "2", "3", "5", "10", "20"];
    let mut pool: Vec<String> = Vec::new();
    for c in consts {
        pool.push(c.to_string());
    }
    for i in ints {
        pool.push(i.to_string());
    }
    // grow with nested f/g applications (this is what stresses EUF×LIA: a
    // function value that is also an integer used as an argument, e.g. f(10)
    // where f(1)=10 — the injective.smt2 shape)
    let depth = 2 + rng.upto(2);
    for _ in 0..depth {
        let extra = 3 + rng.upto(4);
        for _ in 0..extra {
            let func = if rng.chance(1, 2) { "f" } else { "g" };
            let arg = pool[rng.upto(pool.len())].clone();
            pool.push(format!("({} {})", func, arg));
        }
    }

    let term = |rng: &mut Rng, pool: &[String]| pool[rng.upto(pool.len())].clone();
    let n_asserts = 4 + rng.upto(14);
    let mut asserts: Vec<String> = Vec::new();
    for _ in 0..n_asserts {
        let k = rng.upto(6);
        let a = match k {
            0 => format!("(= {} {})", term(rng, &pool), term(rng, &pool)),
            1 => format!("(not (= {} {}))", term(rng, &pool), term(rng, &pool)),
            2 => format!("(<= {} {})", term(rng, &pool), ints[rng.upto(ints.len())]),
            3 => format!("(>= {} {})", term(rng, &pool), ints[rng.upto(ints.len())]),
            4 => format!(
                "(distinct {} {} {})",
                term(rng, &pool),
                term(rng, &pool),
                term(rng, &pool)
            ),
            // injective-style implication instance (ground)
            _ => format!(
                "(=> (= ({0} {1}) ({0} {2})) (= {1} {2}))",
                if rng.chance(1, 2) { "f" } else { "g" },
                term(rng, &pool),
                term(rng, &pool)
            ),
        };
        asserts.push(a);
    }

    (build(&asserts), asserts)
}

fn build(asserts: &[String]) -> String {
    let mut s = String::from(
        "(set-logic QF_UFLIA)\n(declare-fun f (Int) Int)\n(declare-fun g (Int) Int)\n",
    );
    for c in ["a", "b", "c", "d"] {
        s.push_str(&format!("(declare-fun {} () Int)\n", c));
    }
    for a in asserts {
        s.push_str(&format!("(assert {})\n", a));
    }
    s.push_str("(check-sat)\n");
    s
}

/// Is this an UNSOUND disagreement (one side proves what the other refutes)?
fn unsound(oxiz: V, z3: V) -> Option<&'static str> {
    match (oxiz, z3) {
        (V::Unsat, V::Sat) => Some("SPURIOUS UNSAT (oxiz=unsat, z3=sat)"),
        (V::Sat, V::Unsat) => Some("SPURIOUS SAT (oxiz=sat, z3=unsat)"),
        _ => None,
    }
}

/// Delta-debug: drop assertions while the unsound disagreement persists.
fn minimize(mut asserts: Vec<String>) -> Vec<String> {
    let mut changed = true;
    while changed && asserts.len() > 1 {
        changed = false;
        for i in 0..asserts.len() {
            let mut cand = asserts.clone();
            cand.remove(i);
            let script = build(&cand);
            let (ox, z) = (solve_oxiz(&script), solve_z3(&script));
            if z.is_some_and(|z| unsound(ox, z).is_some()) {
                asserts = cand;
                changed = true;
                break;
            }
        }
    }
    asserts
}

#[test]
#[ignore = "differential fuzz vs z3; run with --ignored"]
fn ground_euf_lia_vs_z3() {
    let n: usize = std::env::var("OXIZ_FUZZ_N")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(1500);
    let seed: u64 = std::env::var("OXIZ_FUZZ_SEED")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(0x9E3779B97F4A7C15);

    // z3 must be present; otherwise this audit cannot run.
    assert!(
        solve_z3("(check-sat)").is_some(),
        "z3 not on PATH — cannot run the ground soundness audit"
    );

    let mut rng = Rng(seed);
    let (mut checked, mut agree, mut z3_unknown, mut oxiz_unknown) = (0usize, 0, 0, 0);
    let mut unsound_cases: Vec<(String, Vec<String>, V, V, &'static str)> = Vec::new();

    for _ in 0..n {
        let (script, asserts) = gen_problem(&mut rng);
        let z3 = match solve_z3(&script) {
            Some(v) => v,
            None => continue,
        };
        if z3 == V::Unknown {
            z3_unknown += 1;
            continue;
        }
        let oxiz = solve_oxiz(&script);
        checked += 1;
        if oxiz == V::Unknown {
            oxiz_unknown += 1;
            continue;
        }
        if let Some(kind) = unsound(oxiz, z3) {
            unsound_cases.push((script, asserts, oxiz, z3, kind));
            if unsound_cases.len() >= 5 {
                break;
            }
        } else if oxiz == z3 {
            agree += 1;
        }
    }

    eprintln!(
        "[ground-audit] checked={checked} agree={agree} oxiz_unknown={oxiz_unknown} z3_unknown={z3_unknown} unsound={}",
        unsound_cases.len()
    );

    if let Some((_, asserts, oxiz, z3, kind)) = unsound_cases.first().cloned() {
        eprintln!("[ground-audit] {kind}: oxiz={oxiz:?} z3={z3:?}");
        eprintln!("[ground-audit] minimizing {} assertions…", asserts.len());
        let min = minimize(asserts);
        eprintln!(
            "[ground-audit] MINIMAL REPRO ({} assertions):\n{}",
            min.len(),
            build(&min)
        );
    }

    assert!(
        unsound_cases.is_empty(),
        "{} unsound ground verdict(s) vs z3 — see minimized repro above",
        unsound_cases.len()
    );
}
