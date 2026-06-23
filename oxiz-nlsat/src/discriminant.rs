//! Discriminant analysis for polynomial root counting.
//!
//! This module provides efficient discriminant computation and analysis
//! for polynomial root counting in CAD. The discriminant helps determine
//! the number of distinct roots without full root isolation.
//!
//! Key features:
//! - **Discriminant Computation**: Efficient computation of polynomial discriminants
//! - **Root Count Estimation**: Estimate the number of distinct real roots
//! - **Sign Analysis**: Analyze discriminant signs to prune impossible cases
//! - **Caching**: Cache discriminant results for repeated queries
//!
//! Reference: Z3's CAD implementation and classical algebraic geometry

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};
use oxiz_math::polynomial::Polynomial;
use rustc_hash::FxHashMap;
use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};

/// Result of discriminant analysis.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DiscriminantSign {
    /// Discriminant is positive (all roots distinct or special cases).
    Positive,
    /// Discriminant is zero (polynomial has repeated roots).
    Zero,
    /// Discriminant is negative (complex roots for degree 2, other cases for higher degree).
    Negative,
}

/// Information about polynomial roots based on discriminant.
#[derive(Debug, Clone)]
pub struct RootInfo {
    /// Minimum possible number of distinct real roots.
    pub min_roots: usize,
    /// Maximum possible number of distinct real roots.
    pub max_roots: usize,
    /// Whether the polynomial has repeated roots.
    pub has_repeated_roots: bool,
    /// Sign of the discriminant.
    pub discriminant_sign: DiscriminantSign,
}

/// Statistics for discriminant analysis.
#[derive(Debug, Clone, Default)]
pub struct DiscriminantStats {
    /// Number of discriminant computations.
    pub num_computations: u64,
    /// Number of cache hits.
    pub num_cache_hits: u64,
    /// Number of root count estimations.
    pub num_estimations: u64,
}

/// Discriminant analyzer for polynomials.
pub struct DiscriminantAnalyzer {
    /// Cache: polynomial hash -> discriminant value.
    discriminant_cache: FxHashMap<u64, BigRational>,
    /// Cache: polynomial hash -> root info.
    root_info_cache: FxHashMap<u64, RootInfo>,
    /// Statistics.
    stats: DiscriminantStats,
}

impl DiscriminantAnalyzer {
    /// Create a new discriminant analyzer.
    pub fn new() -> Self {
        Self {
            discriminant_cache: FxHashMap::default(),
            root_info_cache: FxHashMap::default(),
            stats: DiscriminantStats::default(),
        }
    }

    /// Compute the discriminant of a polynomial.
    ///
    /// The discriminant is a polynomial invariant that determines
    /// whether the polynomial has repeated roots.
    pub fn compute_discriminant(&mut self, poly: &Polynomial) -> BigRational {
        let hash = Self::hash_polynomial(poly);

        // Check cache
        if let Some(disc) = self.discriminant_cache.get(&hash) {
            self.stats.num_cache_hits += 1;
            return disc.clone();
        }

        self.stats.num_computations += 1;

        // For univariate polynomials, use the standard formula
        let discriminant = self.compute_discriminant_direct(poly);

        // Cache the result
        self.discriminant_cache.insert(hash, discriminant.clone());

        discriminant
    }

    /// Compute discriminant directly (not from cache).
    fn compute_discriminant_direct(&self, poly: &Polynomial) -> BigRational {
        let degree = poly.total_degree() as usize;

        if degree == 0 {
            // Constant polynomial has discriminant 1 (by convention)
            return BigRational::from_integer(1.into());
        }

        if degree == 1 {
            // Linear polynomial ax + b has discriminant 1 (no repeated roots)
            return BigRational::from_integer(1.into());
        }

        if degree == 2 {
            // Quadratic polynomial ax² + bx + c
            // Discriminant = b² - 4ac
            return self.discriminant_quadratic(poly);
        }

        if degree == 3 {
            // Cubic polynomial
            return self.discriminant_cubic(poly);
        }

        // For higher degrees use resultant-based formula via Sylvester matrix:
        // disc(p) = (-1)^(n*(n-1)/2) * (1/lc(p)) * res(p, p')
        self.discriminant_via_sylvester(poly)
    }

    /// Compute discriminant for degree ≥ 4 via the Sylvester matrix resultant.
    ///
    /// disc(p) = (-1)^(n*(n-1)/2) * (1/lc(p)) * det(Syl(p, p'))
    fn discriminant_via_sylvester(&self, poly: &Polynomial) -> BigRational {
        let var = poly.max_var();
        let n = poly.degree(var) as usize;
        if n == 0 {
            return BigRational::one();
        }

        let dp = poly.derivative(var);
        let m = dp.degree(var) as usize;

        // Collect coefficients: poly_coeffs[i] = coeff of x^i in poly (BigRational)
        let poly_coeffs: Vec<BigRational> =
            (0..=n).map(|k| poly.univ_coeff(var, k as u32)).collect();
        let dp_coeffs: Vec<BigRational> = (0..=m).map(|k| dp.univ_coeff(var, k as u32)).collect();

        // Sylvester matrix is (n + m) x (n + m)
        let size = n + m;
        let mut mat = vec![vec![BigRational::zero(); size]; size];

        // Top m rows: coefficients of poly shifted right 0..m-1 positions
        // Row i: poly coefficients in columns i..(i+n+1), high degree first
        for i in 0..m {
            for j in 0..=n {
                mat[i][i + j] = poly_coeffs[n - j].clone();
            }
        }

        // Bottom n rows: coefficients of dp shifted right 0..n-1 positions
        // Row (m+i): dp coefficients in columns i..(i+m+1), high degree first
        for i in 0..n {
            for j in 0..=m {
                mat[m + i][i + j] = dp_coeffs[m - j].clone();
            }
        }

        let resultant = gaussian_elimination_det(mat);

        let lc = poly_coeffs[n].clone();
        if lc.is_zero() {
            return BigRational::zero();
        }

        let sign: i64 = if (n * (n - 1) / 2).is_multiple_of(2) {
            1
        } else {
            -1
        };
        resultant / lc * BigRational::new(BigInt::from(sign), BigInt::one())
    }

    /// Compute discriminant for quadratic polynomial.
    fn discriminant_quadratic(&self, poly: &Polynomial) -> BigRational {
        // For ax² + bx + c, disc = b² - 4ac
        let coeffs = self.extract_univariate_coeffs(poly);
        if coeffs.len() < 3 {
            return BigRational::from_integer(1.into());
        }

        let a = &coeffs[2];
        let b = &coeffs[1];
        let c = &coeffs[0];

        b * b - BigRational::from_integer(4.into()) * a * c
    }

    /// Compute discriminant for cubic polynomial.
    fn discriminant_cubic(&self, poly: &Polynomial) -> BigRational {
        // For ax³ + bx² + cx + d
        // disc = 18abcd - 4b³d + b²c² - 4ac³ - 27a²d²
        let coeffs = self.extract_univariate_coeffs(poly);
        if coeffs.len() < 4 {
            return BigRational::from_integer(1.into());
        }

        let a = &coeffs[3];
        let b = &coeffs[2];
        let c = &coeffs[1];
        let d = &coeffs[0];

        let term1 = BigRational::from_integer(18.into()) * a * b * c * d;
        let term2 = BigRational::from_integer(4.into()) * b * b * b * d;
        let term3 = b * b * c * c;
        let term4 = BigRational::from_integer(4.into()) * a * c * c * c;
        let term5 = BigRational::from_integer(27.into()) * a * a * d * d;

        term1 - term2 + term3 - term4 - term5
    }

    /// Extract univariate polynomial coefficients (assumes univariate in its max_var).
    ///
    /// Returns a vector where `result[i]` is the coefficient of `x^i`.
    fn extract_univariate_coeffs(&self, poly: &Polynomial) -> Vec<BigRational> {
        let var = poly.max_var();
        let degree = poly.degree(var) as usize;
        (0..=degree)
            .map(|k| poly.univ_coeff(var, k as u32))
            .collect()
    }

    /// Analyze root information based on discriminant.
    pub fn analyze_roots(&mut self, poly: &Polynomial) -> RootInfo {
        let hash = Self::hash_polynomial(poly);

        // Check cache
        if let Some(info) = self.root_info_cache.get(&hash) {
            return info.clone();
        }

        self.stats.num_estimations += 1;

        let discriminant = self.compute_discriminant(poly);
        let discriminant_sign = if discriminant.is_zero() {
            DiscriminantSign::Zero
        } else if discriminant.is_positive() {
            DiscriminantSign::Positive
        } else {
            DiscriminantSign::Negative
        };

        let degree = poly.total_degree() as usize;
        let has_repeated_roots = discriminant.is_zero();

        // Estimate root bounds
        let (min_roots, max_roots) = self.estimate_root_bounds(degree, &discriminant_sign);

        let info = RootInfo {
            min_roots,
            max_roots,
            has_repeated_roots,
            discriminant_sign,
        };

        // Cache the result
        self.root_info_cache.insert(hash, info.clone());

        info
    }

    /// Estimate the possible range of real roots based on degree and discriminant.
    fn estimate_root_bounds(&self, degree: usize, disc_sign: &DiscriminantSign) -> (usize, usize) {
        match degree {
            0 => (0, 0),
            1 => (1, 1),
            2 => match disc_sign {
                DiscriminantSign::Positive => (2, 2), // Two distinct real roots
                DiscriminantSign::Zero => (1, 1),     // One repeated root
                DiscriminantSign::Negative => (0, 0), // No real roots
            },
            3 => match disc_sign {
                DiscriminantSign::Positive => (3, 3), // Three distinct real roots
                DiscriminantSign::Zero => (1, 2),     // At least one repeated root
                DiscriminantSign::Negative => (1, 1), // One real root, two complex
            },
            _ => {
                // For higher degrees, use Descartes' rule of signs bounds
                (0, degree)
            }
        }
    }

    /// Hash a polynomial for caching.
    fn hash_polynomial(poly: &Polynomial) -> u64 {
        let mut hasher = DefaultHasher::new();
        format!("{:?}", poly).hash(&mut hasher);
        hasher.finish()
    }

    /// Clear all caches.
    pub fn clear(&mut self) {
        self.discriminant_cache.clear();
        self.root_info_cache.clear();
    }

    /// Get statistics.
    pub fn stats(&self) -> &DiscriminantStats {
        &self.stats
    }

    /// Get cache hit rate.
    pub fn cache_hit_rate(&self) -> f64 {
        let total = self.stats.num_computations + self.stats.num_cache_hits;
        if total == 0 {
            0.0
        } else {
            self.stats.num_cache_hits as f64 / total as f64
        }
    }
}

/// Classification of a degree-2 bivariate "conic" equality (catalog §A3).
///
/// A conic GENERALISES the circle: circle ⊂ ellipse ⊂ conic. The shape is decided
/// by the discriminant `B² − 4AC` of `A·x² + B·xy + C·y² + D·x + E·y + F = 0`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ConicKind {
    /// `B² − 4AC < 0` — ellipse (the circle `A=C, B=0` is the `a=b` instance).
    Ellipse,
    /// `B² − 4AC = 0` — parabola.
    Parabola,
    /// `B² − 4AC > 0` — hyperbola.
    Hyperbola,
}

/// The six coefficients of a degree-2 bivariate equality, plus the two variables.
///
/// `A·x² + B·xy + C·y² + D·x + E·y + F = 0`, with `x = var_x`, `y = var_y`.
#[derive(Debug, Clone)]
pub struct ConicForm {
    /// First variable (the `x` of the normal form).
    pub var_x: oxiz_math::polynomial::Var,
    /// Second variable (the `y` of the normal form).
    pub var_y: oxiz_math::polynomial::Var,
    /// Coefficient of `x²`.
    pub a: BigRational,
    /// Coefficient of `xy`.
    pub b: BigRational,
    /// Coefficient of `y²`.
    pub c: BigRational,
    /// Coefficient of `x`.
    pub d: BigRational,
    /// Coefficient of `y`.
    pub e: BigRational,
    /// Constant term.
    pub f: BigRational,
}

impl ConicForm {
    /// The conic discriminant `B² − 4AC`.
    pub fn discriminant(&self) -> BigRational {
        &self.b * &self.b - BigRational::from_integer(4.into()) * &self.a * &self.c
    }

    /// Classify the conic by the sign of `B² − 4AC`.
    pub fn classify(&self) -> ConicKind {
        let disc = self.discriminant();
        if disc.is_zero() {
            ConicKind::Parabola
        } else if disc.is_negative() {
            ConicKind::Ellipse
        } else {
            ConicKind::Hyperbola
        }
    }

    /// Is this the special *circle* case (`A = C ≠ 0`, `B = 0`)?
    ///
    /// The circle is the `a = b` specialisation of the ellipse; the classifier
    /// recovers it automatically (it is reported as [`ConicKind::Ellipse`]). This
    /// helper is for diagnostics only — there is no separate "circle" rule.
    pub fn is_circle(&self) -> bool {
        self.b.is_zero() && !self.a.is_zero() && self.a == self.c
    }
}

/// Recognise a polynomial as a degree-2 bivariate conic `A x² + B xy + C y² +
/// D x + E y + F = 0` (catalog §A3).
///
/// Returns `Some(ConicForm)` iff the polynomial mentions exactly two variables,
/// has total degree exactly 2, and every monomial is one of `{x², xy, y², x, y,
/// 1}` (so the normal form is exact and the discriminant classifier applies).
/// Returns `None` otherwise (e.g. a line — degree 1, or a higher-degree / >2-var
/// polynomial) so the caller routes it elsewhere.
///
/// This is a pure *recogniser/normaliser*: it does no solving. For a pure-
/// polynomial conic∩conic or conic∩line system the actual solving is done by the
/// algebraic reduction KB's exact Level-0 linear elimination / Level-1 resultant
/// path; the classifier only identifies the shape and supplies the normalised
/// coefficients. The transcendental trig parameterisation
/// `x = a·c·cos(t), y = b·c·sin(t)` of catalog §A3 needs transcendental equation
/// solving (beyond Sturm) and is the Level-1+ frontier — it is documented (and
/// tied to `oxiz-solver/src/calculus.rs`'s sin/cos KB), NOT implemented here, so
/// no unsound trig solver is introduced.
pub fn recognize_conic(poly: &Polynomial) -> Option<ConicForm> {
    let vars = poly.vars();
    if vars.len() != 2 {
        return None;
    }
    if poly.total_degree() != 2 {
        return None;
    }
    let var_x = vars[0];
    let var_y = vars[1];

    let mut a = BigRational::zero();
    let mut b = BigRational::zero();
    let mut c = BigRational::zero();
    let mut d = BigRational::zero();
    let mut e = BigRational::zero();
    let mut f = BigRational::zero();

    for term in poly.terms() {
        let dx = term.monomial.degree(var_x);
        let dy = term.monomial.degree(var_y);
        match (dx, dy) {
            (2, 0) => a = term.coeff.clone(),
            (1, 1) => b = term.coeff.clone(),
            (0, 2) => c = term.coeff.clone(),
            (1, 0) => d = term.coeff.clone(),
            (0, 1) => e = term.coeff.clone(),
            (0, 0) => f = term.coeff.clone(),
            // Any other monomial (degree > 2 in one var, or a third variable
            // sneaking in) means this is not a clean bivariate conic.
            _ => return None,
        }
    }

    Some(ConicForm {
        var_x,
        var_y,
        a,
        b,
        c,
        d,
        e,
        f,
    })
}

// ─────────────────────────────────────────────────────────────────────────────
// §G — Univariate-quadratic definite-sign by discriminant (catalog §G)
// ─────────────────────────────────────────────────────────────────────────────

/// A recognised UNIVARIATE quadratic `f(x) = a·x² + b·x + c` with `a ≠ 0`.
///
/// The coefficients are EXACT rationals. `var` is the single variable the
/// quadratic is in. The discriminant `D = b² − 4ac` and the sign of `a` together
/// decide the definite sign of `f` over ALL real `x` — the whole point of §G is to
/// settle these by ONE rational `b² − 4ac` (no Sturm/CAD root isolation).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UnivariateQuadratic {
    /// The single variable.
    pub var: oxiz_math::polynomial::Var,
    /// Coefficient of `x²` (guaranteed non-zero).
    pub a: BigRational,
    /// Coefficient of `x`.
    pub b: BigRational,
    /// Constant term.
    pub c: BigRational,
}

impl UnivariateQuadratic {
    /// The discriminant `D = b² − 4ac` (exact rational).
    pub fn discriminant(&self) -> BigRational {
        &self.b * &self.b - BigRational::from_integer(4.into()) * &self.a * &self.c
    }
}

/// The definite sign of a univariate quadratic over ALL real `x` (catalog §G).
///
/// The classification is a THEOREM (the standard sign analysis of a parabola):
/// with `D = b² − 4ac`,
/// - `D < 0, a > 0` ⇒ `f(x) > 0` for all `x`            ([`AllPositive`]);
/// - `D < 0, a < 0` ⇒ `f(x) < 0` for all `x`            ([`AllNegative`]);
/// - `D = 0, a > 0` ⇒ `f(x) ≥ 0` for all `x` (`=0` at the double root, the
///   PERFECT-SQUARE case `(x−r)²`)                       ([`AllNonNegative`]);
/// - `D = 0, a < 0` ⇒ `f(x) ≤ 0` for all `x`            ([`AllNonPositive`]);
/// - `D > 0`        ⇒ `f` changes sign (two real roots) ([`Indefinite`]).
///
/// [`AllPositive`]: DefiniteSign::AllPositive
/// [`AllNegative`]: DefiniteSign::AllNegative
/// [`AllNonNegative`]: DefiniteSign::AllNonNegative
/// [`AllNonPositive`]: DefiniteSign::AllNonPositive
/// [`Indefinite`]: DefiniteSign::Indefinite
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DefiniteSign {
    /// `f(x) > 0` for all real `x` (`D < 0, a > 0`).
    AllPositive,
    /// `f(x) < 0` for all real `x` (`D < 0, a < 0`).
    AllNegative,
    /// `f(x) ≥ 0` for all real `x` (`D = 0, a > 0` — perfect square).
    AllNonNegative,
    /// `f(x) ≤ 0` for all real `x` (`D = 0, a < 0`).
    AllNonPositive,
    /// `f` changes sign — `D > 0`. Two distinct real roots; NOT decidable here.
    Indefinite,
}

impl UnivariateQuadratic {
    /// Classify the definite sign of this quadratic over ALL real `x`.
    ///
    /// Pure function of `(sign a, sign D)`; see [`DefiniteSign`] for the theorem.
    pub fn definite_sign(&self) -> DefiniteSign {
        let d = self.discriminant();
        let a_pos = self.a.is_positive();
        // `a ≠ 0` is an invariant of construction, so `!a_pos` ⇒ `a < 0`.
        if d.is_negative() {
            if a_pos {
                DefiniteSign::AllPositive
            } else {
                DefiniteSign::AllNegative
            }
        } else if d.is_zero() {
            if a_pos {
                DefiniteSign::AllNonNegative
            } else {
                DefiniteSign::AllNonPositive
            }
        } else {
            DefiniteSign::Indefinite
        }
    }
}

/// Recognise a polynomial as a UNIVARIATE quadratic `a·x² + b·x + c` with `a ≠ 0`
/// (catalog §G).
///
/// Returns `Some(UnivariateQuadratic)` iff the polynomial:
/// - mentions EXACTLY ONE variable (it is genuinely univariate — a quadratic with
///   a second variable present is NOT univariate and must fall through), and
/// - has total degree EXACTLY 2 (the `x²` coefficient `a` is non-zero).
///
/// Returns `None` otherwise (constant, linear, multivariate, or degree ≠ 2). The
/// coefficients are read EXACTLY via [`Polynomial::univ_coeff`]; no float.
pub fn recognize_univariate_quadratic(poly: &Polynomial) -> Option<UnivariateQuadratic> {
    let vars = poly.vars();
    if vars.len() != 1 {
        // Constant (0 vars) or genuinely multivariate (≥2 vars): not a
        // *univariate* quadratic ⇒ fall through.
        return None;
    }
    let var = vars[0];
    // `total_degree == 2` over a single-variable polynomial means the leading term
    // is `x²` with a non-zero coefficient — exactly the `a ≠ 0` quadratic shape.
    // (`degree(var)` would coincide here, but `total_degree` also rejects a stray
    // mixed monomial were one ever present.)
    if poly.total_degree() != 2 || poly.degree(var) != 2 {
        return None;
    }

    let a = poly.univ_coeff(var, 2);
    let b = poly.univ_coeff(var, 1);
    let c = poly.univ_coeff(var, 0);

    // Defensive: `total_degree == 2` already guarantees `a ≠ 0`, but never apply
    // the rule with a zero leading coefficient (it would be linear, not quadratic).
    if a.is_zero() {
        return None;
    }

    Some(UnivariateQuadratic { var, a, b, c })
}

/// Decide whether a single sign-constraint atom `q OP 0` on a UNIVARIATE quadratic
/// `q` is UNSATISFIABLE over the reals, by the definite-sign discriminant rule
/// (catalog §G).
///
/// `op` is the comparison the atom asserts on `q` (the polynomial in canonical
/// `q OP 0` form). Returns `true` ONLY when `q OP 0` can NEVER hold for any real
/// `x` — a SOUND `UNSAT` witness for the whole conjunction (one unsatisfiable
/// conjunct ⇒ the conjunction is UNSAT). Returns `false` (decline) when `q` is not
/// a univariate quadratic, when `D > 0` (indefinite), or when the atom IS
/// satisfiable. NEVER asserts satisfiability — this is a one-sided UNSAT
/// recogniser.
///
/// Soundness rests on two facts: (1) the [`DefiniteSign`] classification is exact
/// over ℝ; (2) "for all real `x`" ⟹ "for all integer `x`", so a real-domain
/// `UNSAT` is a fortiori an integer-domain `UNSAT` — the rule is sound for BOTH
/// QF_NRA and QF_NIA atoms.
pub fn quadratic_atom_is_unsat(poly: &Polynomial, op: AtomCmp) -> bool {
    let Some(q) = recognize_univariate_quadratic(poly) else {
        return false;
    };
    match q.definite_sign() {
        // q > 0 everywhere ⇒ `q < 0`, `q ≤ 0`, `q = 0` are all impossible.
        DefiniteSign::AllPositive => {
            matches!(op, AtomCmp::Lt | AtomCmp::Le | AtomCmp::Eq)
        }
        // q < 0 everywhere ⇒ `q > 0`, `q ≥ 0`, `q = 0` are all impossible.
        DefiniteSign::AllNegative => {
            matches!(op, AtomCmp::Gt | AtomCmp::Ge | AtomCmp::Eq)
        }
        // q ≥ 0 everywhere (=0 at the double root) ⇒ ONLY `q < 0` is impossible.
        // `q ≤ 0`, `q = 0`, `q ≥ 0`, `q > 0` are all SATISFIABLE (some at the
        // root, some away from it) ⇒ must NOT be reported UNSAT.
        DefiniteSign::AllNonNegative => matches!(op, AtomCmp::Lt),
        // q ≤ 0 everywhere ⇒ ONLY `q > 0` is impossible.
        DefiniteSign::AllNonPositive => matches!(op, AtomCmp::Gt),
        // D > 0: q changes sign ⇒ every single inequality is satisfiable
        // somewhere ⇒ decline (fall through to the existing nlsat/CAD path).
        DefiniteSign::Indefinite => false,
    }
}

/// The comparison a polynomial atom asserts on its (canonical `q OP 0`) polynomial.
///
/// This mirrors the atom shape the nlsat dispatch builds; it is the input to
/// [`quadratic_atom_is_unsat`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AtomCmp {
    /// `q < 0`.
    Lt,
    /// `q ≤ 0`.
    Le,
    /// `q > 0`.
    Gt,
    /// `q ≥ 0`.
    Ge,
    /// `q = 0`.
    Eq,
}

// ─────────────────────────────────────────────────────────────────────────────
// §G-SOS — definite sign of a MULTIVARIATE quadratic form (PSD recogniser)
// ─────────────────────────────────────────────────────────────────────────────

/// Max number of distinct variables we build a Gram matrix for. The PSD test
/// enumerates every principal minor (`2^(n+1)` of them), so we cap the dimension
/// to keep it cheap; a larger form DECLINES (sound — just not decided here).
const MAX_FORM_VARS: usize = 6;

/// The symmetric Gram (bordered) matrix of a multivariate quadratic
/// `f(x) = xᵀ A x + bᵀ x + c`:
/// ```text
///   M = [ A        b/2 ]      f(x) = [x; 1]ᵀ M [x; 1]
///       [ (b/2)ᵀ    c  ]
/// ```
/// `n` distinct variables ⇒ `M` is `(n+1)×(n+1)`. The last row/column is the
/// affine border (linear part `b/2`, constant `c`); the homogenising coordinate is
/// always `1`, so `[x; 1]` is never the zero vector.
pub struct QuadraticForm {
    /// The `(n+1)×(n+1)` symmetric Gram matrix.
    matrix: Vec<Vec<BigRational>>,
}

/// Recognise a polynomial as a multivariate quadratic form `xᵀ A x + bᵀ x + c`
/// and build its symmetric Gram matrix `M` (catalog §G-SOS).
///
/// Returns `Some` iff total degree is EXACTLY 2 and the variable count is in
/// `1..=MAX_FORM_VARS`. The cross-term `xᵢxⱼ` coefficient `k` is split symmetrically
/// (`M[i][j] = M[j][i] = k/2`) so `M` is symmetric and `[x;1]ᵀ M [x;1]` reproduces
/// `f` exactly. Coefficients are read EXACTLY (BigRational); no float. Returns
/// `None` for a constant/linear poly (total degree ≠ 2), a too-wide form, or any
/// monomial that is not `1`, `xᵢ`, `xᵢ²`, or `xᵢxⱼ`.
pub fn recognize_quadratic_form(poly: &Polynomial) -> Option<QuadraticForm> {
    if poly.total_degree() != 2 {
        return None;
    }
    let vars = poly.vars();
    let n = vars.len();
    if n == 0 || n > MAX_FORM_VARS {
        return None;
    }
    let dim = n + 1;
    let half = BigRational::new(BigInt::from(1), BigInt::from(2));
    let mut m = vec![vec![BigRational::zero(); dim]; dim];

    for term in poly.terms() {
        // Degree of this monomial in each of our variables (only the non-zero ones).
        let degs: Vec<(usize, u32)> = vars
            .iter()
            .enumerate()
            .filter_map(|(i, &v)| {
                let d = term.monomial.degree(v);
                if d > 0 { Some((i, d)) } else { None }
            })
            .collect();
        // Guard: the degrees we collected must account for the whole monomial — a
        // variable outside `poly.vars()` cannot exist, but never trust silently.
        let collected: u32 = degs.iter().map(|&(_, d)| d).sum();
        if collected != term.monomial.total_degree() {
            return None;
        }
        match degs.as_slice() {
            // constant c → border diagonal M[n][n]
            [] => m[n][n] += term.coeff.clone(),
            // linear bᵢ·xᵢ → border M[i][n] = M[n][i] = bᵢ/2
            [(i, 1)] => {
                let h = &term.coeff * &half;
                m[*i][n] += h.clone();
                m[n][*i] += h;
            }
            // xᵢ² → diagonal M[i][i]
            [(i, 2)] => m[*i][*i] += term.coeff.clone(),
            // xᵢ·xⱼ → off-diagonal M[i][j] = M[j][i] = k/2
            [(i, 1), (j, 1)] => {
                let h = &term.coeff * &half;
                m[*i][*j] += h.clone();
                m[*j][*i] += h;
            }
            // degree > 2 in one var, a 3-factor monomial, etc. — not a clean
            // quadratic form (cannot occur at total_degree 2, but decline defensively).
            _ => return None,
        }
    }

    Some(QuadraticForm { matrix: m })
}

/// A symmetric `m` is POSITIVE DEFINITE ⟺ ALL its leading principal minors are
/// strictly positive (Sylvester's criterion — exact over the rationals).
fn matrix_is_pd(m: &[Vec<BigRational>]) -> bool {
    let dim = m.len();
    for k in 1..=dim {
        let sub: Vec<Vec<BigRational>> = (0..k).map(|r| m[r][0..k].to_vec()).collect();
        if !gaussian_elimination_det(sub).is_positive() {
            return false;
        }
    }
    true
}

/// A symmetric `m` is POSITIVE SEMIDEFINITE ⟺ EVERY principal minor (every index
/// subset, not just the leading ones) is ≥ 0. Leading-minors-≥0 is NOT sufficient
/// for PSD (e.g. `diag(0,−1)`), so we enumerate all `2^dim − 1` non-empty subsets.
/// `dim = n+1 ≤ MAX_FORM_VARS+1`, so this is a small bounded enumeration.
fn matrix_is_psd(m: &[Vec<BigRational>]) -> bool {
    let dim = m.len();
    for mask in 1u32..(1u32 << dim) {
        let idxs: Vec<usize> = (0..dim).filter(|&b| mask & (1 << b) != 0).collect();
        let sub: Vec<Vec<BigRational>> = idxs
            .iter()
            .map(|&r| idxs.iter().map(|&c| m[r][c].clone()).collect())
            .collect();
        if gaussian_elimination_det(sub).is_negative() {
            return false;
        }
    }
    true
}

/// Classify the definite sign of a quadratic form over ALL of ℝⁿ from its Gram
/// matrix `M` (the multivariate generalisation of [`UnivariateQuadratic::definite_sign`]).
///
/// `f(x) = [x;1]ᵀ M [x;1]` and `[x;1]` is never `0`, so:
/// - `M` PD ⟹ `f > 0 ∀x`     ([`DefiniteSign::AllPositive`]);
/// - `M` PSD (not PD) ⟹ `f ≥ 0 ∀x` ([`DefiniteSign::AllNonNegative`]);
/// - `−M` PD ⟹ `f < 0 ∀x`    ([`DefiniteSign::AllNegative`]);
/// - `−M` PSD (not PD) ⟹ `f ≤ 0 ∀x` ([`DefiniteSign::AllNonPositive`]);
/// - otherwise indefinite — NOT decided.
///
/// These are SUFFICIENT conditions (definite `M` ⟹ definite `f`); a form that is
/// non-negative only on the affine slice while `M` is indefinite is conservatively
/// declined (sound — incompleteness, never a false verdict).
fn quadratic_form_definite_sign(form: &QuadraticForm) -> DefiniteSign {
    let m = &form.matrix;
    if matrix_is_pd(m) {
        return DefiniteSign::AllPositive;
    }
    if matrix_is_psd(m) {
        return DefiniteSign::AllNonNegative;
    }
    let neg: Vec<Vec<BigRational>> = m
        .iter()
        .map(|row| row.iter().map(|e| -e.clone()).collect())
        .collect();
    if matrix_is_pd(&neg) {
        return DefiniteSign::AllNegative;
    }
    if matrix_is_psd(&neg) {
        return DefiniteSign::AllNonPositive;
    }
    DefiniteSign::Indefinite
}

/// Decide whether a single sign-constraint atom `q OP 0` on a MULTIVARIATE quadratic
/// form `q` is UNSATISFIABLE over the reals, by the definite-sign / PSD rule
/// (catalog §G-SOS). The multivariate generalisation of [`quadratic_atom_is_unsat`]
/// — e.g. `(x−y)² < 0` (`x²−2xy+y² < 0`) is UNSAT because the Gram matrix
/// `[[1,−1],[−1,1]]` is PSD ⇒ the form is `≥ 0` everywhere.
///
/// Returns `true` ONLY when `q OP 0` can NEVER hold for any real point — a SOUND
/// `UNSAT` witness for the whole conjunction. Declines (returns `false`) for a
/// non-quadratic / too-wide / indefinite form, and never asserts satisfiability.
/// Same soundness footing as the univariate rule: the classification is exact over
/// ℝ, and a real-domain `UNSAT` is a fortiori an integer-domain `UNSAT`.
pub fn quadratic_form_is_unsat(poly: &Polynomial, op: AtomCmp) -> bool {
    let Some(form) = recognize_quadratic_form(poly) else {
        return false;
    };
    match quadratic_form_definite_sign(&form) {
        // q > 0 everywhere ⇒ `q < 0`, `q ≤ 0`, `q = 0` impossible.
        DefiniteSign::AllPositive => matches!(op, AtomCmp::Lt | AtomCmp::Le | AtomCmp::Eq),
        // q < 0 everywhere ⇒ `q > 0`, `q ≥ 0`, `q = 0` impossible.
        DefiniteSign::AllNegative => matches!(op, AtomCmp::Gt | AtomCmp::Ge | AtomCmp::Eq),
        // q ≥ 0 everywhere (=0 somewhere) ⇒ ONLY `q < 0` impossible.
        DefiniteSign::AllNonNegative => matches!(op, AtomCmp::Lt),
        // q ≤ 0 everywhere ⇒ ONLY `q > 0` impossible.
        DefiniteSign::AllNonPositive => matches!(op, AtomCmp::Gt),
        // indefinite ⇒ decline (fall through to the existing nlsat/CAD path).
        DefiniteSign::Indefinite => false,
    }
}

/// Compute the determinant of a square matrix over BigRational via Gaussian elimination.
///
/// Uses partial pivoting to avoid division by zero. The determinant is computed
/// by tracking the product of pivot elements and the sign from row swaps.
fn gaussian_elimination_det(mut mat: Vec<Vec<BigRational>>) -> BigRational {
    let n = mat.len();
    if n == 0 {
        return BigRational::one();
    }

    let mut det = BigRational::one();

    for col in 0..n {
        // Find pivot row (first non-zero entry in this column at or below `col`)
        let pivot_row = (col..n).find(|&r| !mat[r][col].is_zero());

        let pivot_row = match pivot_row {
            Some(r) => r,
            None => return BigRational::zero(),
        };

        // Swap rows if needed
        if pivot_row != col {
            mat.swap(col, pivot_row);
            det = -det.clone();
        }

        let pivot = mat[col][col].clone();
        det *= &pivot;

        // Eliminate below
        for row in (col + 1)..n {
            if mat[row][col].is_zero() {
                continue;
            }
            let factor = mat[row][col].clone() / &pivot;
            // Subtract factor * pivot_row from current row
            let pivot_row_slice: Vec<BigRational> = mat[col][col..n].to_vec();
            for (offset, pv) in pivot_row_slice.into_iter().enumerate() {
                let sub = &factor * &pv;
                mat[row][col + offset] -= sub;
            }
        }
    }

    det
}

impl Default for DiscriminantAnalyzer {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_bigint::BigInt;

    fn constant(n: i32) -> Polynomial {
        Polynomial::constant(BigRational::from_integer(BigInt::from(n)))
    }

    #[test]
    fn test_analyzer_new() {
        let analyzer = DiscriminantAnalyzer::new();
        assert_eq!(analyzer.stats.num_computations, 0);
    }

    #[test]
    fn test_constant_polynomial() {
        let mut analyzer = DiscriminantAnalyzer::new();
        let poly = constant(5);
        let disc = analyzer.compute_discriminant(&poly);
        assert_eq!(disc, BigRational::from_integer(BigInt::from(1)));
    }

    #[test]
    fn test_linear_polynomial() {
        let mut analyzer = DiscriminantAnalyzer::new();
        // x + 1
        let x = Polynomial::from_var(0);
        let one = constant(1);
        let poly = Polynomial::add(&x, &one);

        let info = analyzer.analyze_roots(&poly);
        assert_eq!(info.min_roots, 1);
        assert_eq!(info.max_roots, 1);
        assert!(!info.has_repeated_roots);
    }

    #[test]
    fn test_cache_hit() {
        let mut analyzer = DiscriminantAnalyzer::new();
        let poly = Polynomial::from_var(0);

        // First computation
        let _disc1 = analyzer.compute_discriminant(&poly);
        assert_eq!(analyzer.stats.num_computations, 1);
        assert_eq!(analyzer.stats.num_cache_hits, 0);

        // Second computation (should hit cache)
        let _disc2 = analyzer.compute_discriminant(&poly);
        assert_eq!(analyzer.stats.num_computations, 1);
        assert_eq!(analyzer.stats.num_cache_hits, 1);
    }

    #[test]
    fn test_clear() {
        let mut analyzer = DiscriminantAnalyzer::new();
        let poly = Polynomial::from_var(0);

        analyzer.compute_discriminant(&poly);
        analyzer.clear();

        assert_eq!(analyzer.discriminant_cache.len(), 0);
        assert_eq!(analyzer.root_info_cache.len(), 0);
    }

    #[test]
    fn test_cache_hit_rate() {
        let mut analyzer = DiscriminantAnalyzer::new();
        assert_eq!(analyzer.cache_hit_rate(), 0.0);

        let poly = Polynomial::from_var(0);
        analyzer.compute_discriminant(&poly);
        analyzer.compute_discriminant(&poly);

        assert_eq!(analyzer.cache_hit_rate(), 0.5);
    }

    /// Build a univariate polynomial from integer coefficients.
    /// `coeffs[i]` is the coefficient of x^i (constant term first).
    fn poly_from_int_coeffs(var: u32, coeffs: &[i64]) -> Polynomial {
        let rat_coeffs: Vec<BigRational> = coeffs
            .iter()
            .map(|&c| BigRational::from_integer(BigInt::from(c)))
            .collect();
        Polynomial::univariate(var, &rat_coeffs)
    }

    #[test]
    fn test_discriminant_degree4_repeated_root() {
        // x^4 - x^2 = x^2 * (x^2 - 1) has a repeated root at 0, so disc = 0
        let mut analyzer = DiscriminantAnalyzer::new();
        // coefficients: [0, 0, -1, 0, 1] => 0 + 0*x + (-1)*x^2 + 0*x^3 + 1*x^4
        let poly = poly_from_int_coeffs(0, &[0, 0, -1, 0, 1]);
        let disc = analyzer.compute_discriminant(&poly);
        assert!(
            disc.is_zero(),
            "disc(x^4 - x^2) should be zero (repeated root at 0), got {disc:?}"
        );
    }

    #[test]
    fn test_discriminant_degree4_x4_minus_1() {
        // disc(x^4 - 1) = -256
        // x^4 - 1: coefficients [−1, 0, 0, 0, 1]
        let mut analyzer = DiscriminantAnalyzer::new();
        let poly = poly_from_int_coeffs(0, &[-1, 0, 0, 0, 1]);
        let disc = analyzer.compute_discriminant(&poly);
        let expected = BigRational::from_integer(BigInt::from(-256i64));
        assert_eq!(disc, expected, "disc(x^4 - 1) should be -256");
    }

    #[test]
    fn test_discriminant_degree4_x4_plus_1() {
        // disc(x^4 + 1) = 256  (positive; all roots are complex conjugate pairs, no real roots)
        // For n=4: (-1)^(4*3/2) = (-1)^6 = +1, so sign is positive.
        // x^4 + 1: coefficients [1, 0, 0, 0, 1]
        let mut analyzer = DiscriminantAnalyzer::new();
        let poly = poly_from_int_coeffs(0, &[1, 0, 0, 0, 1]);
        let disc = analyzer.compute_discriminant(&poly);
        let expected = BigRational::from_integer(BigInt::from(256i64));
        assert_eq!(disc, expected, "disc(x^4 + 1) should be 256");
    }

    #[test]
    fn test_discriminant_quadratic_correct() {
        // x^2 - 5x + 6 = (x-2)(x-3), disc = 25 - 24 = 1
        let mut analyzer = DiscriminantAnalyzer::new();
        let poly = poly_from_int_coeffs(0, &[6, -5, 1]);
        let disc = analyzer.compute_discriminant(&poly);
        let expected = BigRational::from_integer(BigInt::from(1i64));
        assert_eq!(disc, expected, "disc(x^2 - 5x + 6) should be 1");
    }

    #[test]
    fn test_discriminant_cubic_correct() {
        // x^3 - 3x + 2 = (x-1)^2*(x+2), disc = 0 (repeated root)
        let mut analyzer = DiscriminantAnalyzer::new();
        let poly = poly_from_int_coeffs(0, &[2, -3, 0, 1]);
        let disc = analyzer.compute_discriminant(&poly);
        assert!(
            disc.is_zero(),
            "disc(x^3 - 3x + 2) should be zero (repeated root), got {disc:?}"
        );
    }

    #[test]
    fn test_gaussian_elimination_det_2x2() {
        // det([[1, 2], [3, 4]]) = -2
        let mat = vec![
            vec![
                BigRational::from_integer(BigInt::from(1)),
                BigRational::from_integer(BigInt::from(2)),
            ],
            vec![
                BigRational::from_integer(BigInt::from(3)),
                BigRational::from_integer(BigInt::from(4)),
            ],
        ];
        let det = gaussian_elimination_det(mat);
        assert_eq!(det, BigRational::from_integer(BigInt::from(-2i64)));
    }

    // ---- Conic recognizer / classifier (catalog §A3). ----

    fn rat(n: i64) -> BigRational {
        BigRational::from_integer(BigInt::from(n))
    }

    /// Build `A x² + B xy + C y² + D x + E y + F` over vars (0=x, 1=y).
    fn conic_poly(a: i64, b: i64, c: i64, d: i64, e: i64, f: i64) -> Polynomial {
        let x = Polynomial::from_var(0);
        let y = Polynomial::from_var(1);
        let x2 = Polynomial::mul(&x, &x);
        let y2 = Polynomial::mul(&y, &y);
        let xy = Polynomial::mul(&x, &y);
        let mut p = Polynomial::zero();
        p = Polynomial::add(&p, &x2.scale(&rat(a)));
        p = Polynomial::add(&p, &xy.scale(&rat(b)));
        p = Polynomial::add(&p, &y2.scale(&rat(c)));
        p = Polynomial::add(&p, &x.scale(&rat(d)));
        p = Polynomial::add(&p, &y.scale(&rat(e)));
        Polynomial::add(&p, &Polynomial::constant(rat(f)))
    }

    #[test]
    fn test_recognize_circle_is_ellipse() {
        // x² + y² - 25 = 0 : the circle is the A=C, B=0 ellipse instance.
        let p = conic_poly(1, 0, 1, 0, 0, -25);
        let form = recognize_conic(&p).expect("circle is a conic");
        assert_eq!(form.classify(), ConicKind::Ellipse);
        assert!(form.is_circle());
        // discriminant B²-4AC = 0 - 4 = -4 < 0 (ellipse).
        assert_eq!(form.discriminant(), rat(-4));
    }

    #[test]
    fn test_recognize_proper_ellipse() {
        // x² + 4y² - 100 = 0 : ellipse (A=1, C=4, B=0), NOT a circle.
        let p = conic_poly(1, 0, 4, 0, 0, -100);
        let form = recognize_conic(&p).expect("ellipse is a conic");
        assert_eq!(form.classify(), ConicKind::Ellipse);
        assert!(!form.is_circle());
        assert_eq!(form.discriminant(), rat(-16)); // 0 - 16
    }

    #[test]
    fn test_recognize_hyperbola() {
        // x² - y² - 1 = 0 : hyperbola (B²-4AC = 0 - 4*1*(-1) = 4 > 0).
        let p = conic_poly(1, 0, -1, 0, 0, -1);
        let form = recognize_conic(&p).expect("hyperbola is a conic");
        assert_eq!(form.classify(), ConicKind::Hyperbola);
        assert_eq!(form.discriminant(), rat(4));
    }

    #[test]
    fn test_recognize_parabola() {
        // y - x² = 0 : parabola (A=1 on x², C=0, B=0 ⇒ disc = 0).
        let p = conic_poly(-1, 0, 0, 0, 1, 0); // -x² + y
        let form = recognize_conic(&p).expect("parabola is a conic");
        assert_eq!(form.classify(), ConicKind::Parabola);
        assert_eq!(form.discriminant(), rat(0));
    }

    #[test]
    fn test_recognize_rotated_conic_xy_term() {
        // xy - 1 = 0 : B=1, A=C=0 ⇒ disc = 1 > 0 ⇒ hyperbola (rotated).
        let p = conic_poly(0, 1, 0, 0, 0, -1);
        let form = recognize_conic(&p).expect("xy-1 is a conic");
        assert_eq!(form.classify(), ConicKind::Hyperbola);
        assert_eq!(form.discriminant(), rat(1));
    }

    #[test]
    fn test_recognize_declines_line() {
        // y - x = 0 : a LINE (total degree 1) is not a conic.
        let x = Polynomial::from_var(0);
        let y = Polynomial::from_var(1);
        let line = Polynomial::sub(&y, &x);
        assert!(recognize_conic(&line).is_none());
    }

    #[test]
    fn test_recognize_declines_univariate_and_cubic() {
        // x² - 2 (one variable) is not a *bivariate* conic.
        let x = Polynomial::from_var(0);
        let x2 = Polynomial::mul(&x, &x);
        let uni = Polynomial::sub(&x2, &Polynomial::constant(rat(2)));
        assert!(recognize_conic(&uni).is_none());

        // x³ + y² (total degree 3) is not degree-2.
        let y = Polynomial::from_var(1);
        let x3 = Polynomial::mul(&x2, &x);
        let y2 = Polynomial::mul(&y, &y);
        let cubic = Polynomial::add(&x3, &y2);
        assert!(recognize_conic(&cubic).is_none());
    }

    // ---- §G univariate-quadratic definite-sign by discriminant. ----

    /// Build `a·x² + b·x + c` over variable 0.
    fn quad(a: i64, b: i64, c: i64) -> Polynomial {
        Polynomial::univariate(0, &[rat(c), rat(b), rat(a)])
    }

    #[test]
    fn test_recognize_univariate_quadratic_basic() {
        // x² − 2x + 1 = (x−1)², a=1, b=−2, c=1, D = 4 − 4 = 0.
        let q = recognize_univariate_quadratic(&quad(1, -2, 1)).expect("is a quadratic");
        assert_eq!(q.a, rat(1));
        assert_eq!(q.b, rat(-2));
        assert_eq!(q.c, rat(1));
        assert_eq!(q.discriminant(), rat(0));
        assert_eq!(q.definite_sign(), DefiniteSign::AllNonNegative);
    }

    #[test]
    fn test_recognize_declines_non_quadratic() {
        // Linear x + 1 (degree 1): NOT a quadratic.
        let lin = Polynomial::add(&Polynomial::from_var(0), &Polynomial::constant(rat(1)));
        assert!(recognize_univariate_quadratic(&lin).is_none());
        // Constant 5: NOT a quadratic.
        assert!(recognize_univariate_quadratic(&Polynomial::constant(rat(5))).is_none());
        // Cubic x³: degree 3, NOT a quadratic.
        let x = Polynomial::from_var(0);
        let x3 = Polynomial::mul(&Polynomial::mul(&x, &x), &x);
        assert!(recognize_univariate_quadratic(&x3).is_none());
    }

    #[test]
    fn test_recognize_declines_multivariate() {
        // x² + y (two variables): NOT *univariate*.
        let x = Polynomial::from_var(0);
        let y = Polynomial::from_var(1);
        let x2 = Polynomial::mul(&x, &x);
        let bivar = Polynomial::add(&x2, &y);
        assert!(recognize_univariate_quadratic(&bivar).is_none());
    }

    #[test]
    fn test_definite_sign_classification() {
        // x² + 1: a=1, D = 0 − 4 = −4 < 0 ⇒ AllPositive.
        assert_eq!(quad(1, 0, 1).pipe_definite(), DefiniteSign::AllPositive);
        // −x² − 1: a=−1, D = 0 − 4·(−1)(−1) = −4 < 0 ⇒ AllNegative.
        assert_eq!(quad(-1, 0, -1).pipe_definite(), DefiniteSign::AllNegative);
        // x²: a=1, D = 0 ⇒ AllNonNegative (perfect square at root 0).
        assert_eq!(quad(1, 0, 0).pipe_definite(), DefiniteSign::AllNonNegative);
        // −x²: a=−1, D = 0 ⇒ AllNonPositive.
        assert_eq!(quad(-1, 0, 0).pipe_definite(), DefiniteSign::AllNonPositive);
        // x² − 1: a=1, D = 0 − 4·(−1) = 4 > 0 ⇒ Indefinite (roots ±1).
        assert_eq!(quad(1, 0, -1).pipe_definite(), DefiniteSign::Indefinite);
    }

    // tiny helper for the test above
    trait PipeDefinite {
        fn pipe_definite(&self) -> DefiniteSign;
    }
    impl PipeDefinite for Polynomial {
        fn pipe_definite(&self) -> DefiniteSign {
            recognize_univariate_quadratic(self)
                .expect("quadratic")
                .definite_sign()
        }
    }

    #[test]
    fn test_quadratic_atom_unsat_perfect_square() {
        // (x−1)² = x²−2x+1, perfect square ≥ 0. Atom `q < 0` is UNSAT; the
        // negated goal of the perfect-square repro.
        let q = quad(1, -2, 1);
        assert!(quadratic_atom_is_unsat(&q, AtomCmp::Lt));
        // But `q ≤ 0`, `q = 0`, `q > 0`, `q ≥ 0` are all SATISFIABLE (root x=1)
        // ⇒ must NOT be reported UNSAT.
        assert!(!quadratic_atom_is_unsat(&q, AtomCmp::Le));
        assert!(!quadratic_atom_is_unsat(&q, AtomCmp::Eq));
        assert!(!quadratic_atom_is_unsat(&q, AtomCmp::Gt));
        assert!(!quadratic_atom_is_unsat(&q, AtomCmp::Ge));
    }

    #[test]
    fn test_quadratic_atom_unsat_strictly_positive() {
        // x² + 1 > 0 everywhere (D < 0, a > 0). `< 0`, `≤ 0`, `= 0` impossible.
        let q = quad(1, 0, 1);
        assert!(quadratic_atom_is_unsat(&q, AtomCmp::Lt));
        assert!(quadratic_atom_is_unsat(&q, AtomCmp::Le));
        assert!(quadratic_atom_is_unsat(&q, AtomCmp::Eq));
        // `> 0`, `≥ 0` are valid ⇒ satisfiable ⇒ not UNSAT.
        assert!(!quadratic_atom_is_unsat(&q, AtomCmp::Gt));
        assert!(!quadratic_atom_is_unsat(&q, AtomCmp::Ge));
    }

    #[test]
    fn test_quadratic_atom_unsat_strictly_negative() {
        // −x² − 1 < 0 everywhere (D < 0, a < 0). `> 0`, `≥ 0`, `= 0` impossible.
        let q = quad(-1, 0, -1);
        assert!(quadratic_atom_is_unsat(&q, AtomCmp::Gt));
        assert!(quadratic_atom_is_unsat(&q, AtomCmp::Ge));
        assert!(quadratic_atom_is_unsat(&q, AtomCmp::Eq));
        assert!(!quadratic_atom_is_unsat(&q, AtomCmp::Lt));
        assert!(!quadratic_atom_is_unsat(&q, AtomCmp::Le));
    }

    #[test]
    fn test_quadratic_atom_x_squared_gt_zero_is_satisfiable() {
        // x² > 0 is FALSE at x=0 ⇒ `x² > 0` is satisfiable (not valid) and its
        // atom must NOT be a false UNSAT. (a>0, D=0 ⇒ AllNonNegative; only `<0`
        // is unsat.)
        let q = quad(1, 0, 0);
        assert!(!quadratic_atom_is_unsat(&q, AtomCmp::Gt));
        assert!(!quadratic_atom_is_unsat(&q, AtomCmp::Ge));
        assert!(!quadratic_atom_is_unsat(&q, AtomCmp::Eq));
        assert!(!quadratic_atom_is_unsat(&q, AtomCmp::Le));
        // Only `x² < 0` is impossible.
        assert!(quadratic_atom_is_unsat(&q, AtomCmp::Lt));
    }

    #[test]
    fn test_quadratic_atom_indefinite_never_unsat() {
        // x² − 1 (D = 4 > 0) changes sign ⇒ EVERY comparison is satisfiable ⇒
        // the rule must DECLINE all of them (never a false UNSAT).
        let q = quad(1, 0, -1);
        for op in [AtomCmp::Lt, AtomCmp::Le, AtomCmp::Gt, AtomCmp::Ge, AtomCmp::Eq] {
            assert!(
                !quadratic_atom_is_unsat(&q, op),
                "indefinite quadratic must not be decided UNSAT for {op:?}"
            );
        }
    }

    #[test]
    fn test_quadratic_atom_declines_non_quadratic() {
        // A linear polynomial is not a quadratic ⇒ decline for every op.
        let lin = Polynomial::add(&Polynomial::from_var(0), &Polynomial::constant(rat(1)));
        for op in [AtomCmp::Lt, AtomCmp::Le, AtomCmp::Gt, AtomCmp::Ge, AtomCmp::Eq] {
            assert!(!quadratic_atom_is_unsat(&lin, op));
        }
    }

    // ---- §G-SOS multivariate quadratic-form definite sign (PSD). ----

    #[test]
    fn test_form_sos_perfect_square_psd() {
        // (x − y)² = x² − 2xy + y² ⇒ Gram [[1,−1],[−1,1]] is PSD (eigenvalues 0,2),
        // so the form is ≥ 0 ∀(x,y) — its negation `< 0` is UNSAT.
        let p = conic_poly(1, -2, 1, 0, 0, 0);
        assert!(quadratic_form_is_unsat(&p, AtomCmp::Lt), "(x-y)² < 0 is UNSAT");
        // `≤ 0`, `= 0`, `> 0`, `≥ 0` are all SATISFIABLE (e.g. at x = y) ⇒ NOT unsat.
        for op in [AtomCmp::Le, AtomCmp::Eq, AtomCmp::Gt, AtomCmp::Ge] {
            assert!(
                !quadratic_form_is_unsat(&p, op),
                "(x-y)² is PSD-not-PD ⇒ only `< 0` is UNSAT, not {op:?}"
            );
        }
    }

    #[test]
    fn test_form_sum_of_squares_psd() {
        // x² + y² ⇒ PSD (=0 only at origin) ⇒ `< 0` UNSAT, `≤ 0` satisfiable.
        let p = conic_poly(1, 0, 1, 0, 0, 0);
        assert!(quadratic_form_is_unsat(&p, AtomCmp::Lt));
        assert!(!quadratic_form_is_unsat(&p, AtomCmp::Le));
        assert!(!quadratic_form_is_unsat(&p, AtomCmp::Eq));
    }

    #[test]
    fn test_form_positive_definite_with_constant() {
        // x² + y² + 1 ⇒ Gram diag(1,1,1) is PD ⇒ form > 0 ∀ ⇒ `< 0`, `≤ 0`, `= 0`
        // are ALL UNSAT.
        let p = conic_poly(1, 0, 1, 0, 0, 1);
        for op in [AtomCmp::Lt, AtomCmp::Le, AtomCmp::Eq] {
            assert!(quadratic_form_is_unsat(&p, op), "x²+y²+1 > 0 ∀ ⇒ {op:?} UNSAT");
        }
        // But `> 0` / `≥ 0` are SAT (true everywhere) ⇒ NOT unsat.
        assert!(!quadratic_form_is_unsat(&p, AtomCmp::Gt));
        assert!(!quadratic_form_is_unsat(&p, AtomCmp::Ge));
    }

    #[test]
    fn test_form_negative_definite() {
        // −x² − y² − 1 ⇒ form < 0 ∀ ⇒ `> 0`, `≥ 0`, `= 0` UNSAT; `< 0` SAT.
        let p = conic_poly(-1, 0, -1, 0, 0, -1);
        for op in [AtomCmp::Gt, AtomCmp::Ge, AtomCmp::Eq] {
            assert!(quadratic_form_is_unsat(&p, op), "−x²−y²−1 < 0 ∀ ⇒ {op:?} UNSAT");
        }
        assert!(!quadratic_form_is_unsat(&p, AtomCmp::Lt));
    }

    #[test]
    fn test_form_indefinite_declines() {
        // x² − y² (hyperbolic, indefinite) and 2xy (indefinite) change sign ⇒ the
        // PSD rule must DECLINE every comparison (never a false UNSAT).
        for p in [conic_poly(1, 0, -1, 0, 0, 0), conic_poly(0, 2, 0, 0, 0, 0)] {
            for op in [AtomCmp::Lt, AtomCmp::Le, AtomCmp::Gt, AtomCmp::Ge, AtomCmp::Eq] {
                assert!(
                    !quadratic_form_is_unsat(&p, op),
                    "indefinite form must never be decided UNSAT for {op:?}"
                );
            }
        }
    }

    #[test]
    fn test_form_agrees_with_univariate_on_perfect_square() {
        // The matrix path must agree with the §G univariate path on a univariate
        // input: x² − 2x + 1 = (x−1)², `< 0` UNSAT under BOTH recognisers.
        let q = quad(1, -2, 1);
        assert!(quadratic_atom_is_unsat(&q, AtomCmp::Lt));
        assert!(quadratic_form_is_unsat(&q, AtomCmp::Lt));
        // And both decline the indefinite x² − 1.
        let ind = quad(1, 0, -1);
        assert!(!quadratic_atom_is_unsat(&ind, AtomCmp::Lt));
        assert!(!quadratic_form_is_unsat(&ind, AtomCmp::Lt));
    }

    #[test]
    fn test_form_declines_non_quadratic() {
        // Linear (degree 1) and constant are not quadratic FORMS ⇒ decline.
        let lin = Polynomial::add(&Polynomial::from_var(0), &Polynomial::from_var(1));
        let c = Polynomial::constant(rat(3));
        for op in [AtomCmp::Lt, AtomCmp::Le, AtomCmp::Gt, AtomCmp::Ge, AtomCmp::Eq] {
            assert!(!quadratic_form_is_unsat(&lin, op));
            assert!(!quadratic_form_is_unsat(&c, op));
        }
    }
}
