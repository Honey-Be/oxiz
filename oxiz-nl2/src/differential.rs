//! The z3-differential gate — the day-1 regression spine (DESIGN.md §8).
//!
//! This is the harness that *found* the original P0 (a 13/13 unit battery
//! looked safe; a randomized z3-differential found 119/600 false-unsats — see
//! the `feedback-z3-differential-for-unsat-trust` memory). It is the soundness
//! wall every milestone runs against:
//!
//! * **`FALSE_UNSAT = 0`** — `oxiz-nl2 = Unsat` while `z3 = Sat`. The
//!   verus-DANGEROUS direction (a false proof). A hard gate.
//! * **`FALSE_SAT = 0`** — `oxiz-nl2 = Sat` while `z3 = Unsat`. Verus-safe but
//!   still wrong; gated too. Every `Sat` must also carry a model that passes
//!   G-SAT (enforced by the solver, not here).
//! * `Unknown` against any z3 verdict is always allowed (completeness, tracked
//!   as telemetry, never gating).
//!
//! At M0 the solver returns `Unknown` for everything, so the gate is trivially
//! green and the Unknown-rate is 100%; the harness wiring is what M0 ships.

use std::process::Command;

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed};

use crate::atom::{PolyAtom, VarSort};
use crate::verdict::Verdict;

/// A third-party solver's verdict (z3 / cvc5), parsed from `(check-sat)`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum OracleVerdict {
    Sat,
    Unsat,
    Unknown,
}

/// One classified differential outcome.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Class {
    /// Both decided the same way.
    Agree,
    /// oxiz=Unknown — completeness gap, sound. Telemetry only.
    OursUnknown,
    /// z3=Unknown — oracle gave up; nothing to check against.
    OracleUnknown,
    /// **oxiz=Unsat ∧ z3=Sat. The catastrophic direction. MUST be 0.**
    FalseUnsat,
    /// oxiz=Sat ∧ z3=Unsat. Wrong but verus-safe. Gated to 0.
    FalseSat,
}

/// Classify an `oxiz-nl2` verdict against an oracle verdict.
#[must_use]
pub fn classify(ours: &Verdict, oracle: OracleVerdict) -> Class {
    match (ours, oracle) {
        (Verdict::Unknown(_), _) => Class::OursUnknown,
        (_, OracleVerdict::Unknown) => Class::OracleUnknown,
        (Verdict::Unsat(_), OracleVerdict::Sat) => Class::FalseUnsat,
        (Verdict::Sat(_), OracleVerdict::Unsat) => Class::FalseSat,
        (Verdict::Sat(_), OracleVerdict::Sat) => Class::Agree,
        (Verdict::Unsat(_), OracleVerdict::Unsat) => Class::Agree,
    }
}

/// Aggregate counts over a corpus run. The gate asserts `false_unsat == 0 &&
/// false_sat == 0`; `ours_unknown` is the completeness telemetry.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Tally {
    pub agree: usize,
    pub ours_unknown: usize,
    pub oracle_unknown: usize,
    pub false_unsat: usize,
    pub false_sat: usize,
}

impl Tally {
    pub fn record(&mut self, class: Class) {
        match class {
            Class::Agree => self.agree += 1,
            Class::OursUnknown => self.ours_unknown += 1,
            Class::OracleUnknown => self.oracle_unknown += 1,
            Class::FalseUnsat => self.false_unsat += 1,
            Class::FalseSat => self.false_sat += 1,
        }
    }

    /// The hard soundness invariant. Both directions must be zero.
    #[must_use]
    pub fn is_sound(&self) -> bool {
        self.false_unsat == 0 && self.false_sat == 0
    }

    #[must_use]
    pub fn total(&self) -> usize {
        self.agree + self.ours_unknown + self.oracle_unknown + self.false_unsat + self.false_sat
    }
}

// ── SMT-LIB serialisation ────────────────────────────────────────────────

fn var_name(v: u32) -> String {
    format!("x{v}")
}

fn int_to_smtlib(n: &BigInt) -> String {
    if n.is_negative() {
        format!("(- {})", n.magnitude())
    } else {
        n.to_string()
    }
}

fn rational_to_smtlib(r: &BigRational, sort: VarSort) -> String {
    if r.denom().is_one() {
        return int_to_smtlib(r.numer());
    }
    // Non-integer coefficient: only meaningful for Real. (Generators keep
    // integer coefficients for QF_NIA.)
    debug_assert_eq!(sort, VarSort::Real, "non-integer coeff in an integer problem");
    format!("(/ {} {})", int_to_smtlib(r.numer()), int_to_smtlib(r.denom()))
}

/// Serialise one polynomial atom to an SMT-LIB assertion `(op poly 0)`.
fn atom_to_smtlib(atom: &PolyAtom) -> String {
    let poly_expr = poly_to_smtlib(atom, atom.sort);
    format!("(assert ({} {} 0))", atom.op.smtlib_op(), poly_expr)
}

fn poly_to_smtlib(atom: &PolyAtom, sort: VarSort) -> String {
    let terms = atom.poly.terms();
    if terms.is_empty() {
        return "0".to_string();
    }
    let parts: Vec<String> = terms.iter().map(|t| term_to_smtlib(t, sort)).collect();
    if parts.len() == 1 {
        parts.into_iter().next().unwrap()
    } else {
        format!("(+ {})", parts.join(" "))
    }
}

fn term_to_smtlib(term: &oxiz_math::polynomial::Term, sort: VarSort) -> String {
    // Expand x^k into k repeated factors (QF_NRA/NIA have no `^`).
    let mut factors: Vec<String> = Vec::new();
    for vp in term.monomial.vars() {
        for _ in 0..vp.power {
            factors.push(var_name(vp.var));
        }
    }
    let coeff_is_one = term.coeff.is_one();
    if factors.is_empty() {
        return rational_to_smtlib(&term.coeff, sort);
    }
    if coeff_is_one {
        return if factors.len() == 1 {
            factors.into_iter().next().unwrap()
        } else {
            format!("(* {})", factors.join(" "))
        };
    }
    format!("(* {} {})", rational_to_smtlib(&term.coeff, sort), factors.join(" "))
}

/// Build a complete SMT-LIB script for a conjunction of atoms.
#[must_use]
pub fn to_smtlib(atoms: &[PolyAtom], sort: VarSort) -> String {
    let mut vars: Vec<u32> = atoms.iter().flat_map(|a| a.poly.vars()).collect();
    vars.sort_unstable();
    vars.dedup();
    let sort_kw = match sort {
        VarSort::Real => "Real",
        VarSort::Integer => "Int",
    };
    let logic = match sort {
        VarSort::Real => "QF_NRA",
        VarSort::Integer => "QF_NIA",
    };
    let mut s = format!("(set-logic {logic})\n");
    for v in vars {
        s.push_str(&format!("(declare-const {} {sort_kw})\n", var_name(v)));
    }
    for a in atoms {
        s.push_str(&atom_to_smtlib(a));
        s.push('\n');
    }
    s.push_str("(check-sat)\n");
    s
}

// ── Oracle invocation ────────────────────────────────────────────────────

/// Run an external solver (`z3 -in`, `cvc5`) on an SMT-LIB script and parse the
/// `(check-sat)` answer. Returns `None` if the binary is missing or errored.
#[must_use]
pub fn run_oracle(binary: &str, args: &[&str], script: &str) -> Option<OracleVerdict> {
    use std::io::Write;
    let mut child = Command::new(binary)
        .args(args)
        .stdin(std::process::Stdio::piped())
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::null())
        .spawn()
        .ok()?;
    child.stdin.take()?.write_all(script.as_bytes()).ok()?;
    let out = child.wait_with_output().ok()?;
    let text = String::from_utf8_lossy(&out.stdout);
    for line in text.lines() {
        match line.trim() {
            "sat" => return Some(OracleVerdict::Sat),
            "unsat" => return Some(OracleVerdict::Unsat),
            "unknown" => return Some(OracleVerdict::Unknown),
            _ => {}
        }
    }
    None
}

/// Convenience: z3 over stdin with a short per-query timeout.
#[must_use]
pub fn run_z3(script: &str) -> Option<OracleVerdict> {
    run_oracle("z3", &["-in", "-T:5"], script)
}

/// Is a z3 binary callable? Lets tests skip gracefully in a sandbox.
#[must_use]
pub fn z3_available() -> bool {
    run_z3("(set-logic QF_NRA)(check-sat)\n").is_some()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::atom::{AtomCmp, OriginId, Polynomial};

    fn atom(coeffs: &[(i64, &[(u32, u32)])], op: AtomCmp, sort: VarSort) -> PolyAtom {
        PolyAtom::new(Polynomial::from_coeffs_int(coeffs), op, sort, OriginId(0))
    }

    #[test]
    fn serialises_quadratic_atom() {
        // 3*x^2 - 5 < 0
        let a = atom(&[(3, &[(0, 2)]), (-5, &[])], AtomCmp::Lt, VarSort::Real);
        let s = to_smtlib(std::slice::from_ref(&a), VarSort::Real);
        assert!(s.contains("(set-logic QF_NRA)"));
        assert!(s.contains("(declare-const x0 Real)"));
        assert!(s.contains("(* 3 x0 x0)"));
        assert!(s.contains("(check-sat)"));
    }

    #[test]
    fn serialises_bilinear_atom() {
        // x*y - 5 > 0  (the documented sat case)
        let a = atom(&[(1, &[(0, 1), (1, 1)]), (-5, &[])], AtomCmp::Gt, VarSort::Real);
        let s = to_smtlib(std::slice::from_ref(&a), VarSort::Real);
        assert!(s.contains("(* x0 x1)"), "got: {s}");
    }

    #[test]
    fn classify_directions() {
        use crate::verdict::{Cause, UnsatReason};
        let unsat = Verdict::Unsat(UnsatReason::default());
        let unknown = Verdict::Unknown(Cause::NotImplemented);
        assert_eq!(classify(&unsat, OracleVerdict::Sat), Class::FalseUnsat);
        assert_eq!(classify(&unsat, OracleVerdict::Unsat), Class::Agree);
        assert_eq!(classify(&unknown, OracleVerdict::Sat), Class::OursUnknown);
    }
}
