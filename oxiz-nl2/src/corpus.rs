//! The differential corpus: the documented failing shapes (seeded) plus a
//! **deterministic** bounded-random polynomial generator (DESIGN.md §8).
//!
//! Determinism matters: a flaky corpus makes the soundness gate useless, so the
//! generator is a fixed-seed LCG — the same seed always yields the same
//! problems, and a regression is reproducible from its seed alone.

use num_bigint::BigInt;
use num_rational::BigRational;

use crate::atom::{AtomCmp, OriginId, PolyAtom, Polynomial, Var, VarSort};

/// A named differential problem: a conjunction of atoms over one sort.
#[derive(Clone, Debug)]
pub struct Problem {
    pub name: String,
    pub atoms: Vec<PolyAtom>,
    pub sort: VarSort,
}

fn poly(coeffs: &[(i64, &[(Var, u32)])]) -> Polynomial {
    Polynomial::from_coeffs_int(coeffs)
}

fn atom(coeffs: &[(i64, &[(Var, u32)])], op: AtomCmp, sort: VarSort) -> PolyAtom {
    PolyAtom::new(poly(coeffs), op, sort, OriginId(0))
}

/// The shapes the z3-differential first exposed as false-unsat / the documented
/// boundary cases. Every one of these must end up **decided correctly** (or
/// `Unknown`) — never spurious. They are the M1 acceptance set.
#[must_use]
pub fn seeded_shapes() -> Vec<Problem> {
    use AtomCmp::*;
    use VarSort::*;
    let r = Real;
    vec![
        // 3x² < 5  — sat (x small); was spurious unsat
        Problem { name: "3x2_lt_5".into(), atoms: vec![atom(&[(3, &[(0, 2)]), (-5, &[])], Lt, r)], sort: r },
        // x⁴ > 4  — sat; was spurious unsat
        Problem { name: "x4_gt_4".into(), atoms: vec![atom(&[(1, &[(0, 4)]), (-4, &[])], Gt, r)], sort: r },
        // x·y > 5 — sat; documented sat-side case
        Problem { name: "xy_gt_5".into(), atoms: vec![atom(&[(1, &[(0, 1), (1, 1)]), (-5, &[])], Gt, r)], sort: r },
        // 3x² ≥ 25 — sat (|x| ≥ 5/√3); was spurious unsat
        Problem { name: "3x2_ge_25".into(), atoms: vec![atom(&[(3, &[(0, 2)]), (-25, &[])], Ge, r)], sort: r },
        // x² = 3 — sat over ℝ (x = ±√3); over ℤ unsat (not a perfect square)
        Problem { name: "x2_eq_3_real".into(), atoms: vec![atom(&[(1, &[(0, 2)]), (-3, &[])], Eq, r)], sort: r },
        Problem { name: "x2_eq_3_int".into(), atoms: vec![atom(&[(1, &[(0, 2)]), (-3, &[])], Eq, Integer)], sort: Integer },
        // x² < 0 — unsat (definite sign, §G)
        Problem { name: "x2_lt_0".into(), atoms: vec![atom(&[(1, &[(0, 2)])], Lt, r)], sort: r },
        // x² - 2x + 1 ≥ 0 — valid, i.e. ¬ is unsat: the perfect-square §G case
        Problem { name: "perfect_square_ge_0".into(), atoms: vec![atom(&[(1, &[(0, 2)]), (-2, &[(0, 1)]), (1, &[])], Lt, r)], sort: r },
        // (x-y)² < 0 — unsat (multivariate SOS, §G-SOS): x²-2xy+y² < 0
        Problem { name: "sos_xy_lt_0".into(), atoms: vec![atom(&[(1, &[(0, 2)]), (-2, &[(0, 1), (1, 1)]), (1, &[(1, 2)])], Lt, r)], sort: r },
        // x² = 4 ∧ 1 < y < 2 — sat (opaque): regression for over-eager Sat→Unknown
        Problem {
            name: "x2_eq_4_and_y_in_1_2".into(),
            atoms: vec![
                atom(&[(1, &[(0, 2)]), (-4, &[])], Eq, r),
                atom(&[(1, &[(1, 1)]), (-1, &[])], Gt, r),
                atom(&[(1, &[(1, 1)]), (-2, &[])], Lt, r),
            ],
            sort: r,
        },
    ]
}

/// A small deterministic LCG (Numerical Recipes constants). Reproducible — the
/// gate's whole value depends on this not being `Math.random`.
struct Lcg(u64);
impl Lcg {
    fn next_u32(&mut self) -> u32 {
        self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        (self.0 >> 32) as u32
    }
    fn below(&mut self, n: u32) -> u32 {
        self.next_u32() % n
    }
    /// nonzero coefficient in [-range, range]
    fn coeff(&mut self, range: i64) -> i64 {
        let span = (2 * range + 1) as u32;
        let v = self.below(span) as i64 - range;
        if v == 0 { range } else { v }
    }
}

/// Generate `count` bounded-random problems from `seed`. Bounds: ≤ `max_vars`
/// variables, total degree ≤ `max_degree`, ≤ `max_terms` terms, ≤ 3 conjuncts,
/// integer coefficients in [-5, 5]. Half real, half integer.
#[must_use]
pub fn random_problems(seed: u64, count: usize) -> Vec<Problem> {
    const MAX_VARS: u32 = 3;
    const MAX_DEGREE: u32 = 4;
    const MAX_TERMS: u32 = 4;
    const MAX_CONJ: u32 = 3;
    let ops = [AtomCmp::Lt, AtomCmp::Le, AtomCmp::Gt, AtomCmp::Ge, AtomCmp::Eq, AtomCmp::Ne];

    let mut rng = Lcg(seed.wrapping_add(0x9E37_79B9_7F4A_7C15));
    let mut out = Vec::with_capacity(count);
    for i in 0..count {
        let sort = if i % 2 == 0 { VarSort::Real } else { VarSort::Integer };
        let nvars = 1 + rng.below(MAX_VARS);
        let nconj = 1 + rng.below(MAX_CONJ);
        let mut atoms = Vec::new();
        for _ in 0..nconj {
            let nterms = 1 + rng.below(MAX_TERMS);
            let mut terms: Vec<(BigRational, Vec<(Var, u32)>)> = Vec::new();
            for _ in 0..nterms {
                // build a monomial with total degree ≤ MAX_DEGREE
                let mut powers: Vec<(Var, u32)> = Vec::new();
                let mut deg_left = MAX_DEGREE;
                for v in 0..nvars {
                    if deg_left == 0 {
                        break;
                    }
                    let p = rng.below(deg_left + 1);
                    if p > 0 {
                        powers.push((v, p));
                        deg_left -= p;
                    }
                }
                let c = BigRational::from(BigInt::from(rng.coeff(5)));
                terms.push((c, powers));
            }
            let p = build_poly(&terms);
            let op = ops[rng.below(ops.len() as u32) as usize];
            atoms.push(PolyAtom::new(p, op, sort, OriginId(0)));
        }
        out.push(Problem { name: format!("rand_{seed}_{i}"), atoms, sort });
    }
    out
}

/// Assemble a polynomial from (coeff, powers) terms via the int constructor.
fn build_poly(terms: &[(BigRational, Vec<(Var, u32)>)]) -> Polynomial {
    // from_coeffs_int wants i64 coeffs + &[(Var,u32)]; our coeffs are small ints.
    let mut acc = Polynomial::zero();
    for (c, powers) in terms {
        let ci: i64 = c.numer().try_into().unwrap_or(0);
        let term = Polynomial::from_coeffs_int(&[(ci, powers.as_slice())]);
        acc = &acc + &term;
    }
    acc
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn seeded_shapes_are_nonempty_and_named() {
        let shapes = seeded_shapes();
        assert!(shapes.len() >= 10);
        for p in &shapes {
            assert!(!p.atoms.is_empty(), "{} has no atoms", p.name);
        }
    }

    #[test]
    fn random_is_deterministic() {
        let a = random_problems(42, 20);
        let b = random_problems(42, 20);
        assert_eq!(a.len(), 20);
        assert_eq!(b.len(), 20);
        // same seed ⇒ same names + same atom counts (structural determinism)
        for (x, y) in a.iter().zip(b.iter()) {
            assert_eq!(x.name, y.name);
            assert_eq!(x.atoms.len(), y.atoms.len());
        }
    }

    #[test]
    fn random_respects_degree_bound() {
        for p in random_problems(7, 50) {
            for a in &p.atoms {
                assert!(a.total_degree() <= 4, "{} exceeded degree", p.name);
            }
        }
    }
}
