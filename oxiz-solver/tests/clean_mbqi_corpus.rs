//! M4e-3 corpus regression: drive the 168-case z3-parity corpus through the
//! FULL OxiZ SMT-LIB pipeline with `clean_mbqi = true`, enforcing the
//! soundness gate against the z3 oracle.
//!
//! The oracle is z3 (the `z3_verdict` column of `manifest.tsv`), NEVER OxiZ —
//! OxiZ's own MBQI verdict on the verus prelude was unsound, which is exactly
//! why the clean engine exists. The gate PANICS on any spurious verdict:
//!   * spurious `unsat` — z3 says Sat/Unknown, OxiZ says Unsat (the regression
//!     the whole rewrite prevents);
//!   * spurious `sat`   — z3 says Unsat, OxiZ says Sat.
//! `Unknown` from OxiZ is always acceptable (sound; the clean engine is less
//! complete than the legacy path on non-LIA+UF problems).
//!
//! Heavy (168 full solves) → `#[ignore]` by default. Run on demand with:
//!   cargo test -p oxiz-solver --test clean_mbqi_corpus -- --ignored --nocapture
//! The corpus is vendored under `tests/corpus/z3_parity`.

use oxiz_solver::Context;
use std::path::{Path, PathBuf};

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Verdict {
    Sat,
    Unsat,
    Unknown,
}

impl Verdict {
    fn parse(s: &str) -> Option<Verdict> {
        match s.trim().to_ascii_lowercase().as_str() {
            "sat" => Some(Verdict::Sat),
            "unsat" => Some(Verdict::Unsat),
            "unknown" => Some(Verdict::Unknown),
            _ => None,
        }
    }
}

fn corpus_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/corpus/z3_parity")
}

struct Case {
    relpath: String,
    z3: Verdict,
}

fn load_manifest() -> Vec<Case> {
    let text = std::fs::read_to_string(corpus_root().join("manifest.tsv"))
        .expect("vendored manifest.tsv present");
    text.lines()
        .filter(|l| !l.starts_with('#') && !l.trim().is_empty())
        .map(|l| {
            let mut it = l.split('\t');
            let relpath = it.next().unwrap().to_string();
            let _logic = it.next().unwrap_or("?");
            let z3 = Verdict::parse(it.next().unwrap_or("?")).expect("valid z3 verdict");
            Case { relpath, z3 }
        })
        .collect()
}

/// Solve one benchmark through the full SMT-LIB pipeline with the clean engine.
/// Returns `Unknown` on any parse/feature error (an unsupported command is not
/// a soundness violation — the clean engine simply did not get to run).
fn solve_clean(path: &Path) -> Verdict {
    let script = match std::fs::read_to_string(path) {
        Ok(s) => s,
        Err(_) => return Verdict::Unknown,
    };
    let mut ctx = Context::new();
    ctx.set_clean_mbqi(true);
    // Cap per-case wall-clock so the WHOLE corpus completes in CI-time. The
    // SOUNDNESS gate is unaffected — a spurious `unsat` is a wrong conclusion
    // reached fast, not a non-termination, so a short deadline cannot hide it;
    // it only turns slow-but-correct cases into the sound `Unknown` sooner.
    // Override with OXIZ_PARITY_TIMEOUT_MS (e.g. 3000) for a completeness run.
    let ms: u64 = std::env::var("OXIZ_PARITY_TIMEOUT_MS")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(1000);
    ctx.set_timeout_ms(ms);
    match ctx.execute_script(&script) {
        Ok(out) => out
            .iter()
            .rev()
            .find_map(|line| Verdict::parse(line))
            .unwrap_or(Verdict::Unknown),
        Err(_) => Verdict::Unknown,
    }
}

#[test]
#[ignore = "heavy: 168 full solves; run with --ignored"]
fn clean_engine_corpus_no_spurious_verdict() {
    let cases = load_manifest();
    assert!(cases.len() >= 150, "expected the full z3-parity corpus");

    // Solve the cases in PARALLEL: each `solve_clean` builds its own `Context`
    // (fresh `TermManager`, hence its own interner — the interner is a manager
    // FIELD, not a global) and shares no mutable state with any other case, so
    // the solves are independent. OxiZ's only process globals are thread-safe
    // (atomic profiling counters, a read-only `OnceLock` tactic registry, a
    // per-thread `thread_local!` conflict scratch — reused across cases on one
    // worker exactly as the old single-thread loop reused it across all cases).
    // The soundness gate is unaffected: under CPU contention a case may hit its
    // wall-clock deadline and report the sound `Unknown` instead of a decisive
    // verdict, but a spurious sat/unsat is a wrong conclusion reached FAST, which
    // contention cannot manufacture. rayon work-steals, which matters here
    // because per-case solve time is highly skewed (instant ↔ the 1 s cap).
    use rayon::prelude::*;
    // BOUND the parallelism. Each prelude-scale case holds a large hash-consed
    // term DAG (the corpus solve is ~75% term construction / hash-consing, and
    // the per-case wall-clock cap bounds only the SOLVE loop, not parsing), so
    // all-core parallelism exhausts RAM → OOM SIGKILL. Only `jobs` Contexts are
    // ever alive at once (each is dropped when its closure returns), so a small
    // pool bounds peak memory. Default conservative; override with
    // OXIZ_PARITY_JOBS (RAYON_NUM_THREADS does NOT apply — we build our own pool).
    let jobs = std::env::var("OXIZ_PARITY_JOBS")
        .ok()
        .and_then(|v| v.parse::<usize>().ok())
        .filter(|&n| n > 0)
        .unwrap_or_else(|| {
            std::thread::available_parallelism()
                .map(|n| n.get().min(4))
                .unwrap_or(2)
        });
    let pool = rayon::ThreadPoolBuilder::new()
        .num_threads(jobs)
        .build()
        .expect("build rayon pool");
    let results: Vec<(&str, Verdict, Verdict)> = pool.install(|| {
        cases
            .par_iter()
            .map(|c| {
                let got = solve_clean(&corpus_root().join("benchmarks").join(&c.relpath));
                eprintln!("[clean-corpus] {} z3={:?} oxiz={:?}", c.relpath, c.z3, got);
                (c.relpath.as_str(), c.z3, got)
            })
            .collect()
    });

    // Classify serially (cheap; keeps the accumulation race-free).
    let (mut agree, mut weaker, mut stronger, mut unknown) = (0usize, 0usize, 0usize, 0usize);
    let mut spurious: Vec<String> = Vec::new();
    for (relpath, z3, got) in results {
        match (z3, got) {
            // SOUNDNESS VIOLATIONS — the gate.
            (Verdict::Sat, Verdict::Unsat) | (Verdict::Unknown, Verdict::Unsat) => {
                spurious.push(format!("SPURIOUS UNSAT: {relpath} (z3={z3:?})"));
            }
            (Verdict::Unsat, Verdict::Sat) => {
                spurious.push(format!("SPURIOUS SAT: {relpath} (z3=Unsat)"));
            }
            // Sound outcomes.
            (_, Verdict::Unknown) => unknown += 1,
            (z, g) if z == g => agree += 1,
            (Verdict::Unknown, _) => stronger += 1, // OxiZ decided where z3 could not
            _ => weaker += 1,                       // disagreement that is not a spurious verdict
        }
    }

    eprintln!(
        "[clean-corpus] {} cases: {} agree, {} unknown (sound-incomplete), {} stronger-than-z3, {} other",
        cases.len(),
        agree,
        unknown,
        stronger,
        weaker
    );

    assert!(
        spurious.is_empty(),
        "clean engine produced {} spurious verdict(s):\n{}",
        spurious.len(),
        spurious.join("\n")
    );
}
