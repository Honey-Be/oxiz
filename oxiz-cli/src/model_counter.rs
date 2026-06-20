//! Approximate model counting
//!
//! This module provides approximate model counting capabilities using sampling techniques.
//! Model counting (#SAT) is the problem of counting the number of satisfying assignments
//! for a Boolean formula.

use oxiz_solver::Context;
use serde::{Deserialize, Serialize};

/// Result of model counting
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ModelCountResult {
    /// Estimated number of models
    pub estimated_count: f64,
    /// Lower bound (with confidence)
    pub lower_bound: f64,
    /// Upper bound (with confidence)
    pub upper_bound: f64,
    /// Number of samples taken
    pub samples: usize,
    /// Confidence level (0.0 to 1.0)
    pub confidence: f64,
    /// Whether the count is exact
    pub is_exact: bool,
    /// Time taken in milliseconds
    pub time_ms: u128,
}

/// Model counting method
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CountingMethod {
    /// Exact counting (enumerates all models)
    Exact,
    /// Approximate counting using random sampling
    ApproximateSampling,
}

/// Approximate model counter
pub struct ModelCounter {
    /// Number of samples for approximation
    samples: usize,
    /// Confidence level for bounds
    confidence: f64,
}

impl ModelCounter {
    /// Create a new model counter with default settings
    pub fn new() -> Self {
        Self {
            samples: 1000,
            confidence: 0.95,
        }
    }

    /// Create with custom sample count
    pub fn with_samples(mut self, samples: usize) -> Self {
        self.samples = samples;
        self
    }

    /// Create with custom confidence level
    #[allow(dead_code)]
    pub fn with_confidence(mut self, confidence: f64) -> Self {
        self.confidence = confidence.clamp(0.0, 1.0);
        self
    }

    /// Count models for a given SMT-LIB2 script.
    ///
    /// Model counting (#SAT) is **not implemented**. Earlier revisions of this
    /// module fabricated a result — exact counting always returned `0`, and
    /// approximate counting returned a pure size heuristic that never checked
    /// satisfiability. Returning those numbers as if they were a real model
    /// count is unsound, so `count` now returns an error instead. The CLI
    /// surfaces this to the user rather than printing a bogus figure.
    pub fn count(
        &self,
        _ctx: &mut Context,
        _script: &str,
        method: CountingMethod,
    ) -> Result<ModelCountResult, ModelCountError> {
        Err(ModelCountError::NotImplemented(method))
    }
}

/// Reason a model count could not be produced.
#[derive(Debug, Clone)]
pub enum ModelCountError {
    /// Model counting for the requested method is not implemented.
    NotImplemented(CountingMethod),
}

impl std::fmt::Display for ModelCountError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ModelCountError::NotImplemented(method) => {
                let method = match method {
                    CountingMethod::Exact => "exact",
                    CountingMethod::ApproximateSampling => "approximate",
                };
                write!(
                    f,
                    "model counting is not implemented ({method} counting is unavailable); \
                     no count was produced"
                )
            }
        }
    }
}

impl std::error::Error for ModelCountError {}

impl Default for ModelCounter {
    fn default() -> Self {
        Self::new()
    }
}

/// Format model count result as human-readable string
pub fn format_model_count(result: &ModelCountResult) -> String {
    let mut output = String::new();

    output.push_str("=== Model Count Result ===\n\n");

    if result.is_exact {
        output.push_str(&format!("Exact count: {:.0}\n", result.estimated_count));
    } else {
        output.push_str(&format!(
            "Estimated count: {:.2e}\n",
            result.estimated_count
        ));
        output.push_str(&format!(
            "Confidence interval ({}%): [{:.2e}, {:.2e}]\n",
            (result.confidence * 100.0) as u32,
            result.lower_bound,
            result.upper_bound
        ));
        output.push_str(&format!("Samples used: {}\n", result.samples));
    }

    output.push_str(&format!("Time: {} ms\n", result.time_ms));

    output
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_model_counter_creation() {
        let counter = ModelCounter::new();
        assert_eq!(counter.samples, 1000);
        assert_eq!(counter.confidence, 0.95);
    }

    #[test]
    fn test_model_counter_with_samples() {
        let counter = ModelCounter::new().with_samples(5000);
        assert_eq!(counter.samples, 5000);
    }

    #[test]
    fn test_counting_is_not_implemented() {
        let mut ctx = Context::new();
        let counter = ModelCounter::new();

        let script = r#"
            (declare-const x Bool)
            (declare-const y Bool)
            (assert (or x y))
        "#;

        // Model counting is not implemented: both methods must return an
        // explicit error rather than a fabricated count.
        for method in [
            CountingMethod::ApproximateSampling,
            CountingMethod::Exact,
        ] {
            let result = counter.count(&mut ctx, script, method);
            assert!(
                matches!(result, Err(ModelCountError::NotImplemented(_))),
                "model counting must not fabricate a result"
            );
        }
    }

    #[test]
    fn test_format_model_count() {
        let result = ModelCountResult {
            estimated_count: 1000.0,
            lower_bound: 900.0,
            upper_bound: 1100.0,
            samples: 1000,
            confidence: 0.95,
            is_exact: false,
            time_ms: 100,
        };

        let formatted = format_model_count(&result);
        assert!(formatted.contains("Estimated count"));
        assert!(formatted.contains("Confidence interval"));
        assert!(formatted.contains("Samples used: 1000"));
    }
}
