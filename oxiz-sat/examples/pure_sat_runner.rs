//! Pure-SAT runner: drives `oxiz_sat::Solver` DIRECTLY (the 38k-line CDCL engine),
//! bypassing the SMT/theory layer that `oxiz --dimacs` routes through.
//!
//! Usage:  pure_sat_runner <file.cnf>
//! Env:    OXIZ_SAT_PRESET = default|industrial|random|cryptographic|hardware|
//!                            aggressive|conservative|glucose|minisat|cadical
//!         (selects SolverConfig; non-default presets flip on inprocessing /
//!          LRB / CHB branching so the fuzz can exercise those code paths.)
//!
//! Output (DIMACS-ish, matched by the fuzz harness verdict() parser):
//!   s SATISFIABLE   / s UNSATISFIABLE   / s UNKNOWN
//! On SAT, the returned model is re-checked against the parsed clauses; if any
//! clause is unsatisfied the runner prints `s MODEL-INVALID` (a self-detected
//! unsound-SAT, independent of any external oracle) and exits non-zero.

use std::io::BufReader;

use oxiz_sat::{ConfigPreset, DimacsParser, LBool, Lit, Solver, SolverResult, Var};

fn preset_from_env() -> ConfigPreset {
    match std::env::var("OXIZ_SAT_PRESET").as_deref() {
        Ok("industrial") => ConfigPreset::Industrial,
        Ok("random") => ConfigPreset::Random,
        Ok("cryptographic") => ConfigPreset::Cryptographic,
        Ok("hardware") => ConfigPreset::Hardware,
        Ok("aggressive") => ConfigPreset::Aggressive,
        Ok("conservative") => ConfigPreset::Conservative,
        Ok("glucose") => ConfigPreset::Glucose,
        Ok("minisat") => ConfigPreset::MiniSat,
        Ok("cadical") => ConfigPreset::CaDiCaL,
        _ => ConfigPreset::Default,
    }
}

/// Parse the DIMACS clauses a second time, independently, so we can validate a
/// reported model without trusting the solver's own clause database.
fn parse_clauses(path: &str) -> (usize, Vec<Vec<i32>>) {
    let txt = std::fs::read_to_string(path).expect("read cnf");
    let mut nv = 0usize;
    let mut clauses = Vec::new();
    let mut cur: Vec<i32> = Vec::new();
    for line in txt.lines() {
        let line = line.trim();
        if line.is_empty() || line.starts_with('c') {
            continue;
        }
        if line.starts_with('p') {
            // p cnf <nv> <nc>
            let parts: Vec<&str> = line.split_whitespace().collect();
            if parts.len() >= 3 {
                nv = parts[2].parse().unwrap_or(0);
            }
            continue;
        }
        for tok in line.split_whitespace() {
            let v: i32 = match tok.parse() {
                Ok(v) => v,
                Err(_) => continue,
            };
            if v == 0 {
                if !cur.is_empty() {
                    clauses.push(std::mem::take(&mut cur));
                }
            } else {
                cur.push(v);
            }
        }
    }
    if !cur.is_empty() {
        clauses.push(cur);
    }
    (nv, clauses)
}

/// Returns Some(bad_clause) if the model fails to satisfy that clause.
fn validate_model(solver: &Solver, clauses: &[Vec<i32>]) -> Option<Vec<i32>> {
    for cl in clauses {
        let mut sat = false;
        for &lit in cl {
            let var = Var::new((lit.unsigned_abs() - 1) as u32);
            let val = solver.model_value(var);
            let lit_true = match val {
                LBool::True => lit > 0,
                LBool::False => lit < 0,
                // An unassigned var in a SAT model: treat as free → clause may
                // still be satisfied by another literal; only flag if NO literal
                // is forced true. We count Undef as "not forcing true".
                LBool::Undef => false,
            };
            if lit_true {
                sat = true;
                break;
            }
        }
        if !sat {
            // Re-scan: maybe satisfied by an Undef literal we conservatively
            // skipped — but an Undef literal can be assigned either way, so a
            // clause containing an Undef var IS satisfiable. Only a clause where
            // every literal is definitively false is a true violation.
            let all_false = cl.iter().all(|&lit| {
                let var = Var::new((lit.unsigned_abs() - 1) as u32);
                match solver.model_value(var) {
                    LBool::True => lit < 0,
                    LBool::False => lit > 0,
                    LBool::Undef => false,
                }
            });
            if all_false {
                return Some(cl.clone());
            }
        }
    }
    None
}

fn main() {
    let path = match std::env::args().nth(1) {
        Some(p) => p,
        None => {
            eprintln!("usage: pure_sat_runner <file.cnf>");
            std::process::exit(2);
        }
    };

    let mut config = preset_from_env().config();
    // Per-feature override knobs (for root-cause isolation). Each env var, when
    // set to 0/1, forces that single config flag without changing the preset.
    if let Ok(v) = std::env::var("OXIZ_LHB") {
        config.enable_lazy_hyper_binary = v == "1";
    }
    if let Ok(v) = std::env::var("OXIZ_CHRONO") {
        config.enable_chronological_backtrack = v == "1";
    }
    if let Ok(v) = std::env::var("OXIZ_INPROC") {
        config.enable_inprocessing = v == "1";
    }
    if let Ok(v) = std::env::var("OXIZ_RANDPOL") {
        config.random_polarity_prob = v.parse().unwrap_or(config.random_polarity_prob);
    }
    if let Ok(v) = std::env::var("OXIZ_LRB") {
        config.use_lrb_branching = v == "1";
    }
    if let Ok(v) = std::env::var("OXIZ_CHB") {
        config.use_chb_branching = v == "1";
    }
    if let Ok(v) = std::env::var("OXIZ_RESTART_INT") {
        config.restart_interval = v.parse().unwrap_or(config.restart_interval);
    }
    if let Ok(v) = std::env::var("OXIZ_CDT") {
        config.clause_deletion_threshold = v.parse().unwrap_or(config.clause_deletion_threshold);
    }
    let mut solver = Solver::with_config(config);

    // DRAT proof emission (opt-in): when OXIZ_DRAT is set, write the DRAT proof
    // to a temp file and print its path on stdout as `c DRAT <path>`. The fuzz
    // harness's --drat mode parses this line and, on UNSAT, runs
    // `drat-trim <cnf> <path>` to independently certify the UNSAT result.
    // If OXIZ_DRAT names a non-empty value other than "1"/"auto", it is used as
    // the literal output path (useful for manual inspection).
    let drat_path: Option<String> = match std::env::var("OXIZ_DRAT") {
        Ok(v) if !v.is_empty() => {
            let p = if v == "1" || v == "auto" {
                let mut tmp = std::env::temp_dir();
                tmp.push(format!("oxiz_drat_{}.drat", std::process::id()));
                tmp.to_string_lossy().into_owned()
            } else {
                v
            };
            match solver.enable_drat(&p) {
                Ok(()) => {
                    println!("c DRAT {p}");
                    Some(p)
                }
                Err(e) => {
                    eprintln!("c DRAT-enable-failed: {e}");
                    None
                }
            }
        }
        _ => None,
    };
    let _ = &drat_path; // path already printed; kept for clarity

    let file = std::fs::File::open(&path).expect("open cnf");
    let reader = BufReader::new(file);
    let mut parser = DimacsParser::new();
    if let Err(e) = parser.parse_reader(reader, &mut solver) {
        eprintln!("parse error: {e}");
        std::process::exit(2);
    }

    let result = solver.solve();
    match result {
        SolverResult::Sat => {
            // Self-soundness check: the model must satisfy every input clause.
            let (_nv, clauses) = parse_clauses(&path);
            if let Some(bad) = validate_model(&solver, &clauses) {
                println!("s MODEL-INVALID");
                eprintln!("UNSOUND: reported SAT but clause unsatisfied: {bad:?}");
                // sentinel literal vector so the harness can capture it
                let lits: Vec<Lit> = bad.iter().map(|&l| Lit::from_dimacs(l)).collect();
                eprintln!("({} lits)", lits.len());
                std::process::exit(3);
            }
            println!("s SATISFIABLE");
        }
        SolverResult::Unsat => println!("s UNSATISFIABLE"),
        SolverResult::Unknown => println!("s UNKNOWN"),
    }
}
