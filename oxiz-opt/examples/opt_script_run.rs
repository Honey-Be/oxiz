//! Minimal MaxSMT/OMT SMT-LIB2 script runner CLI.
//!
//! `cargo run --release -p oxiz-opt --example opt_script_run -- <script.smt2>`
//!
//! Reads an SMT-LIB2 script (from a file argument, or stdin if `-`/no
//! argument is given) and runs it through [`oxiz_opt::OptScriptRunner`],
//! printing one output line per command that produces output — exactly the
//! contract `oxiz_solver::Context::execute_script` has, extended to
//! understand `minimize`/`maximize`/`assert-soft`/`get-objectives`.
//!
//! This exists as the P1 slice's differential-testing entry point (see
//! `.claude/jobs/5ec69da0/tmp/maxsat_cli_diff.py`): a small, low-risk way to
//! drive `OptScriptRunner` from a subprocess without touching `oxiz-cli`'s
//! `main.rs`, whose primary `execute_and_format` path still uses plain
//! `oxiz_solver::Context` (see the P1 report for why full CLI integration
//! was scoped out — the short version: this wiring was discovered mid-slice
//! to require living in `oxiz-opt`, not `oxiz-solver`, to avoid a cyclic
//! crate dependency, and retrofitting every `oxiz-cli` call site that
//! threads a `&mut Context` through portfolio/auto-tune/unsat-core/etc. was
//! out of scope for this slice).

use oxiz_opt::OptScriptRunner;
use std::io::Read;

fn main() {
    let path = std::env::args().nth(1);
    let script = match path.as_deref() {
        None | Some("-") => {
            let mut s = String::new();
            std::io::stdin()
                .read_to_string(&mut s)
                .expect("failed to read script from stdin");
            s
        }
        Some(p) => std::fs::read_to_string(p).unwrap_or_else(|e| {
            eprintln!("error: failed to read {p}: {e}");
            std::process::exit(1);
        }),
    };

    let mut runner = OptScriptRunner::new();
    match runner.execute_script(&script) {
        Ok(output) => {
            for line in output {
                println!("{line}");
            }
        }
        Err(e) => {
            eprintln!("error: {e}");
            std::process::exit(1);
        }
    }
}
