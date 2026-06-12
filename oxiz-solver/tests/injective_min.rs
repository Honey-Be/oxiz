//! Bug (b) reconstruction: the bounded-injectivity GROUND instantiation that
//! the clean engine drives OxiZ into a spurious `unsat` on (UFLIA/injective).
//! Build the ground instances, confirm OxiZ unsat vs z3 sat, delta-debug to a
//! minimal reproducer. GROUND only (clean off) — this is a host-core bug.

use oxiz_solver::Context;
use std::io::Write;
use std::process::{Command, Stdio};

fn parse(s: &str) -> Option<&'static str> {
    s.lines().rev().find_map(|l| match l.trim() {
        "sat" => Some("sat"),
        "unsat" => Some("unsat"),
        "unknown" => Some("unknown"),
        _ => None,
    })
}

fn z3(script: &str) -> Option<&'static str> {
    let mut c = Command::new("z3")
        .args(["-in", "-T:5"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .spawn()
        .ok()?;
    c.stdin.take()?.write_all(script.as_bytes()).ok()?;
    let o = c.wait_with_output().ok()?;
    parse(&String::from_utf8_lossy(&o.stdout))
}

fn oxiz(script: &str) -> &'static str {
    let mut ctx = Context::new();
    ctx.set_timeout_ms(5000);
    match ctx.execute_script(script) {
        Ok(out) => out.iter().rev().find_map(|l| parse(l)).unwrap_or("unknown"),
        Err(_) => "unknown",
    }
}

fn build(asserts: &[String]) -> String {
    let mut s = String::from("(set-logic QF_UFLIA)\n(declare-fun f (Int) Int)\n");
    for a in asserts {
        s.push_str(&format!("(assert {})\n", a));
    }
    s.push_str("(check-sat)\n");
    s
}

/// spurious unsat: OxiZ unsat where z3 is sat.
fn spurious(asserts: &[String]) -> bool {
    let sc = build(asserts);
    oxiz(&sc) == "unsat" && z3(&sc) == Some("sat")
}

fn minimize(mut a: Vec<String>) -> Vec<String> {
    let mut changed = true;
    while changed && a.len() > 1 {
        changed = false;
        for i in 0..a.len() {
            let mut cand = a.clone();
            cand.remove(i);
            if spurious(&cand) {
                a = cand;
                changed = true;
                break;
            }
        }
    }
    a
}

#[test]
#[ignore = "needs z3; run with --ignored"]
fn injective_bounded_ground() {
    assert!(z3("(check-sat)").is_some(), "z3 not on PATH");

    // Ground term pool the clean engine reaches: the args 1,2,3, the values
    // 10,20,30, and the function applications (incl. nested via the chain).
    let pool = [
        "1", "2", "3", "10", "20", "30", "(f 1)", "(f 2)", "(f 3)", "(f 10)", "(f 20)", "(f 30)",
    ];
    let mut asserts = vec![
        "(= (f 1) 10)".to_string(),
        "(= (f 2) 20)".to_string(),
        "(= (f 3) 30)".to_string(),
    ];
    // bounded injectivity instances over all ordered pairs
    for &a in &pool {
        for &b in &pool {
            if a == b {
                continue;
            }
            asserts.push(format!(
                "(=> (and (>= {a} 0) (<= {a} 10) (>= {b} 0) (<= {b} 10) (= (f {a}) (f {b}))) (= {a} {b}))"
            ));
        }
    }

    let sc = build(&asserts);
    let (ox, z) = (oxiz(&sc), z3(&sc));
    eprintln!("[inj] full: oxiz={ox} z3={z:?} ({} assertions)", asserts.len());
    assert_eq!(z, Some("sat"), "z3 oracle must be sat");

    if ox == "unsat" {
        eprintln!("[inj] reproduced spurious unsat — minimizing…");
        let min = minimize(asserts);
        eprintln!("[inj] MINIMAL REPRO ({} assertions):\n{}", min.len(), build(&min));
        panic!("spurious unsat reproduced; minimal repro printed");
    } else {
        eprintln!("[inj] NOT reproduced at this pool (oxiz={ox}); widen the pool/depth");
    }
}
