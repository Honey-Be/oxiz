//! Randomized **ground-truth differential** for `fd_core` — the soundness gate
//! ([[feedback_z3_differential_for_unsat_trust]]: a unit battery hides false
//! verdicts; a randomized differential against an independent oracle does not).
//!
//! Construction: every generated problem bounds EVERY variable with a small random
//! box, so a brute-force enumeration of the box is the **exact** ground truth
//! (sat ⟺ some in-box integer point satisfies every atom). We then assert
//! `fd_core::decide` never contradicts it:
//!   * brute = SAT  ⇒ decide ∈ {Sat, Open}, NEVER Unsat   (FALSE_UNSAT = 0)
//!   * brute = UNSAT ⇒ decide ∈ {Unsat, Open}, NEVER Sat   (FALSE_SAT  = 0)
//! and whenever decide returns `Sat(model)` the model is re-checked exactly.
//!
//! Polynomials are nonlinear (degree up to 3 over up to 3 vars) — exactly the
//! fragment the legacy `NiaSolver` was unsound on and `fd_core` now backs in the
//! live dispatch.

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::Zero;
use oxiz_math::polynomial::{Polynomial, Var};
use oxiz_theories::fd_core::{self, FdCmp, FdDecision};
use rustc_hash::FxHashMap;

/// A deterministic LCG (no `rand`, no `Math.random` — reproducible failures).
struct Rng(u64);
impl Rng {
    fn new(seed: u64) -> Self {
        Rng(seed.wrapping_mul(0x9E37_79B9_7F4A_7C15).wrapping_add(1))
    }
    fn next_u64(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.0 >> 33
    }
    /// Inclusive integer in `[lo, hi]`.
    fn range(&mut self, lo: i64, hi: i64) -> i64 {
        lo + (self.next_u64() % ((hi - lo + 1) as u64)) as i64
    }
}

const ALL_CMP: [FdCmp; 6] =
    [FdCmp::Lt, FdCmp::Le, FdCmp::Gt, FdCmp::Ge, FdCmp::Eq, FdCmp::Ne];

/// A random nonlinear polynomial over vars `0..nvars`: a sum of 1..=3 monomials
/// (each a product of up to 2 distinct variable powers, power 1..=2) plus a small
/// constant, all with coefficients in `[-3, 3]`.
fn rand_poly(rng: &mut Rng, nvars: u32) -> Polynomial {
    let nterms = rng.range(1, 3);
    // build a coeff spec for `from_coeffs_int`
    let mut owned: Vec<(i64, Vec<(Var, u32)>)> = Vec::new();
    for _ in 0..nterms {
        let coeff = rng.range(-3, 3);
        if coeff == 0 {
            continue;
        }
        let nfac = rng.range(0, 2); // 0 ⇒ constant term
        let mut mono: Vec<(Var, u32)> = Vec::new();
        for _ in 0..nfac {
            let v = rng.range(0, (nvars - 1) as i64) as Var;
            let p = rng.range(1, 2) as u32;
            mono.push((v, p));
        }
        owned.push((coeff, mono));
    }
    if owned.is_empty() {
        owned.push((rng.range(-3, 3), Vec::new()));
    }
    let spec: Vec<(i64, &[(Var, u32)])> = owned.iter().map(|(c, m)| (*c, m.as_slice())).collect();
    Polynomial::from_coeffs_int(&spec)
}

fn sign_of(r: &BigRational) -> i32 {
    use num_traits::Signed;
    if r.is_zero() {
        0
    } else if r.is_negative() {
        -1
    } else {
        1
    }
}

/// Brute-force ground truth: is there an integer point in the (all-bounded) box
/// satisfying every atom? Enumerates the product of `[lo, hi]` per var.
fn brute_sat(atoms: &[(Polynomial, FdCmp)], bounds: &[(Var, i64, i64)]) -> bool {
    let dims: Vec<(Var, i64, i64)> = bounds.to_vec();
    let mut idx = vec![0i64; dims.len()];
    // initialise to the lo of each dim
    for (i, &(_, lo, _)) in dims.iter().enumerate() {
        idx[i] = lo;
    }
    loop {
        // assemble the point
        let mut model: FxHashMap<Var, BigRational> = FxHashMap::default();
        for (i, &(v, _, _)) in dims.iter().enumerate() {
            model.insert(v, BigRational::from(BigInt::from(idx[i])));
        }
        let ok = atoms
            .iter()
            .all(|(p, op)| op.holds_for_sign(sign_of(&p.eval(&model))));
        if ok {
            return true;
        }
        // odometer increment
        let mut carry = 0;
        loop {
            if carry == dims.len() {
                return false; // exhausted the whole box, none satisfied
            }
            idx[carry] += 1;
            if idx[carry] <= dims[carry].2 {
                break;
            }
            idx[carry] = dims[carry].1;
            carry += 1;
        }
    }
}

#[test]
fn fd_core_ground_truth_differential() {
    let mut false_unsat = 0u32;
    let mut false_sat = 0u32;
    let mut decided_unsat = 0u32;
    let mut decided_sat = 0u32;
    let mut open = 0u32;
    let mut first_failure: Option<String> = None;

    for seed in [
        1u64, 2, 3, 5, 7, 11, 42, 99, 0xBEEF, 0xC0FFEE, 0xD00D, 0x1234_5678, 0xACE,
        0xFACE, 0xBAD, 0xF00D,
    ] {
        let mut rng = Rng::new(seed);
        for _ in 0..1500 {
            let nvars = rng.range(1, 3) as u32;
            // bound EVERY variable so the brute force is exact ground truth.
            let mut bounds: Vec<(Var, i64, i64)> = Vec::new();
            let mut atoms: Vec<(Polynomial, FdCmp)> = Vec::new();
            for v in 0..nvars {
                let lo = rng.range(-4, 2);
                let hi = lo + rng.range(0, 7);
                bounds.push((v as Var, lo, hi));
                // encode the box as atoms: (x - lo) >= 0  and  (hi - x) >= 0
                atoms.push((
                    Polynomial::from_coeffs_int(&[(1, &[(v as Var, 1)]), (-lo, &[])]),
                    FdCmp::Ge,
                ));
                atoms.push((
                    Polynomial::from_coeffs_int(&[(-1, &[(v as Var, 1)]), (hi, &[])]),
                    FdCmp::Ge,
                ));
            }
            // add 1..=4 random nonlinear atoms with random comparisons.
            let natoms = rng.range(1, 4);
            for _ in 0..natoms {
                let p = rand_poly(&mut rng, nvars);
                let op = ALL_CMP[(rng.next_u64() % 6) as usize];
                atoms.push((p, op));
            }

            let truth = brute_sat(&atoms, &bounds);
            match fd_core::decide(&atoms) {
                FdDecision::Unsat => {
                    decided_unsat += 1;
                    if truth {
                        false_unsat += 1;
                        first_failure.get_or_insert_with(|| {
                            format!("FALSE_UNSAT seed={seed}: brute=SAT but decide=Unsat; atoms={atoms:?}")
                        });
                    }
                }
                FdDecision::Sat(model) => {
                    decided_sat += 1;
                    // re-check the returned model exactly
                    let model_ok = atoms
                        .iter()
                        .all(|(p, op)| op.holds_for_sign(sign_of(&p.eval(&model))));
                    if !model_ok || !truth {
                        false_sat += 1;
                        first_failure.get_or_insert_with(|| {
                            format!("FALSE_SAT seed={seed}: brute={truth} model_ok={model_ok}; atoms={atoms:?}")
                        });
                    }
                }
                FdDecision::Open => {
                    open += 1;
                }
            }
        }
    }

    eprintln!(
        "fd_core differential: unsat={decided_unsat} sat={decided_sat} open={open} \
         | FALSE_UNSAT={false_unsat} FALSE_SAT={false_sat}"
    );
    assert_eq!(false_unsat, 0, "FALSE_UNSAT must be 0: {first_failure:?}");
    assert_eq!(false_sat, 0, "FALSE_SAT must be 0: {first_failure:?}");
    // Sanity: the corpus must actually exercise both definitive verdicts (else the
    // gate proves nothing). With all-bounded boxes most problems are decided.
    assert!(decided_unsat > 100, "differential should decide many UNSAT ({decided_unsat})");
    assert!(decided_sat > 100, "differential should decide many SAT ({decided_sat})");
}
