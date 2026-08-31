//! DRAT and LRAT proof generation for SAT solving
//!
//! DRAT (Deletion Resolution Asymmetric Tautology) is a proof format
//! that allows verification of UNSAT results from SAT solvers.
//!
//! LRAT (Labelled Resolution Asymmetric Tautology) is an extension of DRAT
//! that includes clause IDs and resolution hints for more efficient verification.

use crate::literal::Lit;
#[allow(unused_imports)]
use crate::prelude::*;
use std::fs::File;
use std::io::{BufWriter, Write};
use std::path::Path;

/// DRAT proof emitter, parameterized over the underlying writer `W`.
///
/// Defaults to `BufWriter<File>` so existing callers using the bare
/// `DratWriter` type and the `enable(&path)` API see exactly the same
/// behavior as before; in-memory capture via `enable_writer` chooses
/// a different `W` (e.g. `Cursor<Vec<u8>>`).
///
/// `Debug` is derived so its output for `DratWriter<BufWriter<File>>`
/// — the upstream form — is byte-identical to pre-fork.
#[derive(Debug)]
pub struct DratWriter<W: Write + Send = BufWriter<File>> {
    writer: Option<W>,
    /// Whether proof logging is enabled
    enabled: bool,
}

impl DratWriter<BufWriter<File>> {
    /// Create a new DRAT proof logger (disabled). Defaults to the
    /// `BufWriter<File>` writer type so existing call sites
    /// `DratWriter::new()` (no annotation) compile and infer
    /// identically to upstream. To capture the proof in memory,
    /// build a typed instance via [`DratWriter::<W>::with_writer`].
    pub fn new() -> Self {
        Self {
            writer: None,
            enabled: false,
        }
    }

    /// Enable proof logging to a file.
    ///
    /// Internally wraps the file in a `BufWriter` exactly as before;
    /// no observable change in output bytes.
    pub fn enable(&mut self, path: impl AsRef<Path>) -> std::io::Result<()> {
        let file = File::create(path)?;
        self.writer = Some(BufWriter::new(file));
        self.enabled = true;
        Ok(())
    }
}

impl<W: Write + Send> DratWriter<W> {
    /// Construct a proof logger pre-configured with `w` as the
    /// writer sink. Equivalent to `let mut p = DratWriter::new();
    /// p.enable_writer(w);` but works for arbitrary `W` without
    /// requiring the default `BufWriter<File>` first.
    pub fn with_writer(w: W) -> Self {
        Self {
            writer: Some(w),
            enabled: true,
        }
    }

    /// Enable proof logging to an arbitrary writer sink.
    ///
    /// Mirrors [`DratWriter::enable`] but writes to the provided sink instead of
    /// opening a file. For any equivalent sequence of clauses the
    /// byte stream is identical; pass `Cursor<Vec<u8>>` to capture
    /// the DRAT proof in memory.
    ///
    /// The caller controls buffering — wrap in `BufWriter` to match
    /// `enable(&path)`'s buffering exactly.
    pub fn enable_writer(&mut self, w: W) -> std::io::Result<()> {
        self.writer = Some(w);
        self.enabled = true;
        Ok(())
    }

    /// Disable proof logging
    pub fn disable(&mut self) {
        self.enabled = false;
        if let Some(mut writer) = self.writer.take() {
            let _ = writer.flush();
        }
    }

    /// Check if proof logging is enabled
    pub fn is_enabled(&self) -> bool {
        self.enabled
    }

    /// Log clause addition
    pub fn add_clause(&mut self, lits: &[Lit]) -> std::io::Result<()> {
        if !self.enabled {
            return Ok(());
        }

        if let Some(writer) = &mut self.writer {
            // Write literals in DIMACS format
            for &lit in lits {
                write!(writer, "{} ", lit.to_dimacs())?;
            }
            writeln!(writer, "0")?;
        }

        Ok(())
    }

    /// Log clause deletion
    pub fn delete_clause(&mut self, lits: &[Lit]) -> std::io::Result<()> {
        if !self.enabled {
            return Ok(());
        }

        if let Some(writer) = &mut self.writer {
            // Deletion is marked with 'd' prefix
            write!(writer, "d ")?;
            for &lit in lits {
                write!(writer, "{} ", lit.to_dimacs())?;
            }
            writeln!(writer, "0")?;
        }

        Ok(())
    }

    /// Flush the proof to disk
    pub fn flush(&mut self) -> std::io::Result<()> {
        if let Some(writer) = &mut self.writer {
            writer.flush()?;
        }
        Ok(())
    }
}

/// Default specialized on the file-backed form so source-compat is
/// preserved for callers that rely on `DratWriter::default()`. Other
/// `W` use [`DratWriter::with_writer`] instead.
impl Default for DratWriter<BufWriter<File>> {
    fn default() -> Self {
        Self::new()
    }
}

impl<W: Write + Send> Drop for DratWriter<W> {
    fn drop(&mut self) {
        let _ = self.flush();
    }
}

/// LRAT proof emitter, parameterized over the underlying writer `W`.
///
/// Mirrors [`DratWriter`] — defaults to `BufWriter<File>` so existing
/// callers see no change; pass a different `W` to capture in memory.
///
/// `Debug` is derived so its output for `LratWriter<BufWriter<File>>`
/// — the upstream form — is byte-identical to pre-fork.
#[derive(Debug)]
pub struct LratWriter<W: Write + Send = BufWriter<File>> {
    writer: Option<W>,
    /// Whether proof logging is enabled
    enabled: bool,
    /// Next clause ID to assign
    next_id: u64,
}

impl LratWriter<BufWriter<File>> {
    /// Create a new LRAT proof logger (disabled). Default-typed for
    /// source compatibility — see [`DratWriter::new`].
    pub fn new() -> Self {
        Self {
            writer: None,
            enabled: false,
            next_id: 1,
        }
    }

    /// Enable proof logging to a file.
    ///
    /// Internally wraps the file in a `BufWriter` exactly as before;
    /// no observable change in output bytes.
    pub fn enable(&mut self, path: impl AsRef<Path>) -> std::io::Result<()> {
        let file = File::create(path)?;
        self.writer = Some(BufWriter::new(file));
        self.enabled = true;
        Ok(())
    }
}

impl<W: Write + Send> LratWriter<W> {
    /// Construct an LRAT logger pre-configured with `w`.
    pub fn with_writer(w: W) -> Self {
        Self {
            writer: Some(w),
            enabled: true,
            next_id: 1,
        }
    }

    /// Enable proof logging to an arbitrary writer sink. See
    /// [`DratWriter::enable_writer`] for the in-memory capture
    /// pattern.
    pub fn enable_writer(&mut self, w: W) -> std::io::Result<()> {
        self.writer = Some(w);
        self.enabled = true;
        Ok(())
    }

    /// Disable proof logging
    pub fn disable(&mut self) {
        self.enabled = false;
        if let Some(mut writer) = self.writer.take() {
            let _ = writer.flush();
        }
    }

    /// Check if proof logging is enabled
    pub fn is_enabled(&self) -> bool {
        self.enabled
    }

    /// Log clause addition with hints
    ///
    /// # Arguments
    /// * `lits` - The literals in the clause
    /// * `hints` - Clause IDs used in the derivation (for RAT checking)
    ///
    /// # Returns
    /// The ID assigned to this clause
    pub fn add_clause(&mut self, lits: &[Lit], hints: &[u64]) -> std::io::Result<u64> {
        if !self.enabled {
            let id = self.next_id;
            self.next_id += 1;
            return Ok(id);
        }

        let clause_id = self.next_id;
        self.next_id += 1;

        if let Some(writer) = &mut self.writer {
            // LRAT addition line: `<id> <lits> 0 <hints> 0`.
            //
            // BACKPORT from upstream v0.3.3, whose comment describes this
            // implementation exactly. The hint section is a mandatory part of
            // every LRAT *addition* line and MUST always be terminated by a
            // trailing `0`, even when there are no hints. Emitting a hint-less
            // line (`<id> <lits> 0`) — as this did for original clauses and any
            // clause added with an empty hint slice — produces a line with a
            // single `0` terminator, which a checker parses as "literals
            // continue" and then chokes on the missing second `0`. Writing the
            // second `0` unconditionally yields the well-formed
            // `<id> <lits> 0 0` for the empty-hint case.
            //
            // This was not academic: `oxiz-proof`'s newly-ported
            // `lrat_check::check_lrat_proof` rejected our own writer's output
            // with "line 1: addition line missing hint terminator 0", so the
            // producer and the checker in this same tree did not agree on the
            // format. `add_original_clause` passes empty hints ALWAYS, which
            // made every original-clause line unparseable.
            write!(writer, "{} ", clause_id)?;

            // Write literals, then their terminating `0`.
            for &lit in lits {
                write!(writer, "{} ", lit.to_dimacs())?;
            }
            write!(writer, "0 ")?;

            // Write hints (possibly none) followed by the mandatory terminating `0`.
            for &hint in hints {
                write!(writer, "{} ", hint)?;
            }
            writeln!(writer, "0")?;
        }

        Ok(clause_id)
    }

    /// Log original clause (from input formula)
    ///
    /// Original clauses are added with their sequential IDs
    pub fn add_original_clause(&mut self, lits: &[Lit]) -> std::io::Result<u64> {
        self.add_clause(lits, &[])
    }

    /// Consume the next sequential id for an ORIGINAL clause WITHOUT writing a
    /// line. BACKPORT from upstream v0.3.3.
    ///
    /// An LRAT checker numbers the input formula `1..=N` from the accompanying
    /// CNF, in file order, and never expects those clauses to reappear as
    /// addition lines — only DERIVED clauses and deletions do.
    /// [`Self::add_original_clause`] predates that distinction mattering here:
    /// it writes every original as a hint-less addition line, which is harmless
    /// for a checker that reads clause content out of the LRAT stream itself,
    /// and wrong for one handed the formula separately.
    ///
    /// Use this when a producer's original-clause ids must line up with an
    /// external CNF numbering — which is the case for `oxiz-proof`'s
    /// `lrat_check::check_lrat_proof`, the checker in this same tree.
    pub fn reserve_original_id(&mut self) -> u64 {
        let id = self.next_id;
        self.next_id += 1;
        id
    }

    /// Log clause deletion
    ///
    /// # Arguments
    /// * `clause_id` - The ID of the clause to delete
    pub fn delete_clause(&mut self, clause_id: u64) -> std::io::Result<()> {
        if !self.enabled {
            return Ok(());
        }

        if let Some(writer) = &mut self.writer {
            // LRAT deletion format: <id> d <clause_id> 0
            writeln!(writer, "{} d {} 0", self.next_id, clause_id)?;
            self.next_id += 1;
        }

        Ok(())
    }

    /// Log the empty clause (proof of UNSAT)
    pub fn add_empty_clause(&mut self, hints: &[u64]) -> std::io::Result<u64> {
        self.add_clause(&[], hints)
    }

    /// Flush the proof to disk
    pub fn flush(&mut self) -> std::io::Result<()> {
        if let Some(writer) = &mut self.writer {
            writer.flush()?;
        }
        Ok(())
    }

    /// Get the next clause ID that will be assigned
    pub fn next_id(&self) -> u64 {
        self.next_id
    }
}

/// Default specialized on the file-backed form (see [`DratWriter::default`]).
impl Default for LratWriter<BufWriter<File>> {
    fn default() -> Self {
        Self::new()
    }
}

impl<W: Write + Send> Drop for LratWriter<W> {
    fn drop(&mut self) {
        let _ = self.flush();
    }
}

/// Proof trimmer for removing unnecessary clauses
///
/// This analyzes a proof and removes clauses that are not needed for the final derivation
#[derive(Debug)]
pub struct ProofTrimmer {
    /// Clauses that are actually used in the proof
    used_clauses: crate::prelude::HashSet<u64>,
    /// The final clause ID (usually the empty clause)
    #[allow(dead_code)]
    final_clause_id: u64,
}

impl ProofTrimmer {
    /// Create a new proof trimmer
    pub fn new(final_clause_id: u64) -> Self {
        let mut used = crate::prelude::HashSet::new();
        used.insert(final_clause_id);

        Self {
            used_clauses: used,
            final_clause_id,
        }
    }

    /// Mark a clause and its dependencies as used
    pub fn mark_used(&mut self, clause_id: u64, dependencies: &[u64]) {
        if self.used_clauses.insert(clause_id) {
            // Also mark dependencies as used
            for &dep_id in dependencies {
                self.used_clauses.insert(dep_id);
            }
        }
    }

    /// Check if a clause is used in the trimmed proof
    pub fn is_used(&self, clause_id: u64) -> bool {
        self.used_clauses.contains(&clause_id)
    }

    /// Trim a proof by removing unused clauses
    ///
    /// This reads a proof file and writes a trimmed version
    pub fn trim_proof(
        &self,
        input_path: impl AsRef<Path>,
        output_path: impl AsRef<Path>,
    ) -> std::io::Result<usize> {
        use std::io::{BufRead, BufReader};

        let input = File::open(input_path)?;
        let reader = BufReader::new(input);

        let output = File::create(output_path)?;
        let mut writer = BufWriter::new(output);

        let mut trimmed_count = 0;

        for line in reader.lines() {
            let line = line?;
            let line = line.trim();

            if line.is_empty() {
                continue;
            }

            // Parse the clause ID from the line
            let parts: Vec<&str> = line.split_whitespace().collect();
            if parts.is_empty() {
                continue;
            }

            // First part should be the clause ID
            if let Ok(clause_id) = parts[0].parse::<u64>() {
                if self.is_used(clause_id) {
                    // Keep this clause
                    writeln!(writer, "{}", line)?;
                } else {
                    // Trim this clause
                    trimmed_count += 1;
                }
            } else {
                // Not a valid clause line, keep it (might be a comment)
                writeln!(writer, "{}", line)?;
            }
        }

        writer.flush()?;

        Ok(trimmed_count)
    }

    /// Get the number of used clauses
    pub fn num_used_clauses(&self) -> usize {
        self.used_clauses.len()
    }
}

impl Default for ProofTrimmer {
    fn default() -> Self {
        Self::new(0)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::literal::Var;
    use std::fs;
    use std::io::Read;
    use std::sync::{Arc, Mutex};

    /// In-memory writer sink whose accumulated bytes remain inspectable
    /// after the owning proof logger is dropped, via a shared
    /// `Arc<Mutex<Vec<u8>>>`. Wrap in `BufWriter` to match
    /// `enable(&path)`'s buffering exactly.
    struct SharedSink(Arc<Mutex<Vec<u8>>>);

    impl Write for SharedSink {
        fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
            self.0
                .lock()
                .expect("test operation should succeed")
                .extend_from_slice(buf);
            Ok(buf.len())
        }
        fn flush(&mut self) -> std::io::Result<()> {
            Ok(())
        }
    }

    /// Create a fresh shared byte buffer paired with a `BufWriter`-wrapped
    /// [`SharedSink`] writing into it.
    fn shared_sink() -> (Arc<Mutex<Vec<u8>>>, BufWriter<SharedSink>) {
        let captured: Arc<Mutex<Vec<u8>>> = Arc::new(Mutex::new(Vec::new()));
        let sink = BufWriter::new(SharedSink(captured.clone()));
        (captured, sink)
    }

    #[test]
    fn test_drat_proof() {
        let path = std::env::temp_dir().join("test_drat.proof");
        let mut proof = DratWriter::new();

        assert!(!proof.is_enabled());

        proof.enable(&path).expect("test operation should succeed");
        assert!(proof.is_enabled());

        let v0 = Var(0);
        let v1 = Var(1);

        // Add a clause: x0 ∨ x1
        proof
            .add_clause(&[Lit::pos(v0), Lit::pos(v1)])
            .expect("test operation should succeed");

        // Add a clause: ~x0
        proof
            .add_clause(&[Lit::neg(v0)])
            .expect("test operation should succeed");

        // Delete a clause
        proof
            .delete_clause(&[Lit::pos(v0), Lit::pos(v1)])
            .expect("test operation should succeed");

        proof.flush().expect("test operation should succeed");
        proof.disable();

        // Read the proof file and verify
        let mut file = File::open(&path).expect("file operation failed");
        let mut contents = String::new();
        file.read_to_string(&mut contents)
            .expect("test operation should succeed");

        assert!(contents.contains("1 2 0"));
        assert!(contents.contains("-1 0"));
        assert!(contents.contains("d 1 2 0"));

        // Clean up
        fs::remove_file(&path).expect("test operation should succeed");
    }

    #[test]
    fn test_disabled_proof() {
        let mut proof = DratWriter::new();

        // Should not error even though not enabled
        let v0 = Var(0);
        proof
            .add_clause(&[Lit::pos(v0)])
            .expect("test operation should succeed");
        proof
            .delete_clause(&[Lit::pos(v0)])
            .expect("test operation should succeed");
    }

    #[test]
    fn test_lrat_proof() {
        let path = std::env::temp_dir().join("test_lrat.proof");
        let mut proof = LratWriter::new();

        assert!(!proof.is_enabled());

        proof.enable(&path).expect("test operation should succeed");
        assert!(proof.is_enabled());

        let v0 = Var(0);
        let v1 = Var(1);

        // Add an original clause: x0 ∨ x1
        let id1 = proof
            .add_original_clause(&[Lit::pos(v0), Lit::pos(v1)])
            .expect("test operation should succeed");
        assert_eq!(id1, 1);

        // Add a clause with hints: ~x0 (derived from clause 1)
        let id2 = proof
            .add_clause(&[Lit::neg(v0)], &[1])
            .expect("test operation should succeed");
        assert_eq!(id2, 2);

        // Delete clause 1
        proof
            .delete_clause(id1)
            .expect("test operation should succeed");

        proof.flush().expect("test operation should succeed");
        proof.disable();

        // Read the proof file and verify
        let mut file = File::open(&path).expect("file operation failed");
        let mut contents = String::new();
        file.read_to_string(&mut contents)
            .expect("test operation should succeed");

        assert!(contents.contains("1 1 2 0"));
        assert!(contents.contains("2 -1 0 1 0"));
        assert!(contents.contains("d 1 0"));

        // Clean up
        fs::remove_file(&path).expect("test operation should succeed");
    }

    #[test]
    fn test_lrat_empty_clause() {
        let path = std::env::temp_dir().join("test_lrat_empty.proof");
        let mut proof = LratWriter::new();

        proof.enable(&path).expect("test operation should succeed");

        // Add empty clause (UNSAT proof) with hints
        let id = proof
            .add_empty_clause(&[1, 2, 3])
            .expect("test operation should succeed");
        assert_eq!(id, 1);

        proof.flush().expect("test operation should succeed");
        proof.disable();

        // Read the proof file
        let mut file = File::open(&path).expect("file operation failed");
        let mut contents = String::new();
        file.read_to_string(&mut contents)
            .expect("test operation should succeed");

        assert!(contents.contains("1 0 1 2 3 0"));

        // Clean up
        fs::remove_file(&path).expect("test operation should succeed");
    }

    // === enable_writer: in-memory DRAT/LRAT capture ===

    #[test]
    fn test_drat_enable_writer_captures_to_cursor() {
        use std::io::Cursor;
        let buffer = Cursor::new(Vec::<u8>::new());
        let mut proof = DratWriter::<Cursor<Vec<u8>>>::with_writer(buffer);

        let v0 = Var::new(0);
        let v1 = Var::new(1);
        proof
            .add_clause(&[Lit::pos(v0), Lit::pos(v1)])
            .expect("test operation should succeed");
        proof
            .add_clause(&[Lit::neg(v0)])
            .expect("test operation should succeed");
        proof
            .delete_clause(&[Lit::pos(v0), Lit::pos(v1)])
            .expect("test operation should succeed");
        proof.flush().expect("test operation should succeed");
        // The byte-identity guarantee is asserted by the parallel
        // file-vs-writer test; this test confirms the API surface
        // and that no panic / error occurs.
    }

    #[test]
    fn test_drat_debug_format_default_typed_matches_derive() {
        // Strict-superset guard: the `Debug` impl on the default-typed
        // form must produce the same shape as upstream's
        // `#[derive(Debug)]` did pre-fork. We can't import the
        // pre-fork output but we can pin the current derive output
        // and assert it contains the expected field names and values.
        let proof = DratWriter::new();
        let s = format!("{:?}", proof);
        assert!(s.starts_with("DratWriter {"));
        assert!(s.contains("writer: None"));
        assert!(s.contains("enabled: false"));
    }

    #[test]
    fn test_drat_writer_output_matches_file_path() {
        use std::io::Read;

        // Run the same sequence twice: once via enable(&path), once via
        // enable_writer(cursor). The byte streams must be identical.
        let path = std::env::temp_dir().join("oxiz_drat_strict_superset.proof");
        let v0 = Var::new(0);
        let v1 = Var::new(1);

        // Path variant
        {
            let mut proof = DratWriter::new();
            proof.enable(&path).expect("enable path");
            proof
                .add_clause(&[Lit::pos(v0), Lit::pos(v1)])
                .expect("test operation should succeed");
            proof
                .add_clause(&[Lit::neg(v0)])
                .expect("test operation should succeed");
            proof
                .delete_clause(&[Lit::pos(v0), Lit::pos(v1)])
                .expect("test operation should succeed");
            proof.flush().expect("test operation should succeed");
            proof.disable();
        }
        let mut file_contents = Vec::new();
        File::open(&path)
            .expect("test operation should succeed")
            .read_to_end(&mut file_contents)
            .expect("test operation should succeed");
        fs::remove_file(&path).ok();

        // Writer variant — a Vec<u8> behind a shared Mutex wrapped in a
        // BufWriter so the buffering matches `enable(&path)` exactly.
        let (captured, sink) = shared_sink();

        {
            let mut proof = DratWriter::<BufWriter<SharedSink>>::with_writer(sink);
            proof
                .add_clause(&[Lit::pos(v0), Lit::pos(v1)])
                .expect("test operation should succeed");
            proof
                .add_clause(&[Lit::neg(v0)])
                .expect("test operation should succeed");
            proof
                .delete_clause(&[Lit::pos(v0), Lit::pos(v1)])
                .expect("test operation should succeed");
            proof.flush().expect("test operation should succeed");
            proof.disable();
        }
        let writer_contents = captured
            .lock()
            .expect("test operation should succeed")
            .clone();

        assert_eq!(
            file_contents, writer_contents,
            "enable_writer must produce byte-identical output to enable(&path)"
        );
    }

    // === LRAT in-memory capture (mirrors the DRAT tests above) ===

    #[test]
    fn test_lrat_enable_writer_captures_to_cursor() {
        use std::io::Cursor;
        let buffer = Cursor::new(Vec::<u8>::new());
        let mut proof = LratWriter::<Cursor<Vec<u8>>>::with_writer(buffer);

        let v0 = Var::new(0);
        let v1 = Var::new(1);

        // Original clause: x0 ∨ x1 (id 1).
        let id1 = proof
            .add_clause(&[Lit::pos(v0), Lit::pos(v1)], &[])
            .expect("test operation should succeed");
        // Derived clause: ~x0 with a resolution hint on clause 1 (id 2).
        let _id2 = proof
            .add_clause(&[Lit::neg(v0)], &[id1])
            .expect("test operation should succeed");
        proof
            .delete_clause(id1)
            .expect("test operation should succeed");
        proof.flush().expect("test operation should succeed");
        // The byte-identity guarantee is asserted by the parallel
        // file-vs-writer test; this test confirms the API surface
        // and that no panic / error occurs.
    }

    #[test]
    fn test_lrat_writer_output_matches_file_path() {
        // Run the same LRAT sequence twice: once via enable(&path), once
        // via a BufWriter<SharedSink>. The byte streams must be identical.
        let path = std::env::temp_dir().join("oxiz_lrat_strict_superset.proof");
        let v0 = Var::new(0);
        let v1 = Var::new(1);

        // Path variant
        {
            let mut proof = LratWriter::new();
            proof.enable(&path).expect("enable path");
            let id1 = proof
                .add_clause(&[Lit::pos(v0), Lit::pos(v1)], &[])
                .expect("test operation should succeed");
            proof
                .add_clause(&[Lit::neg(v0)], &[id1])
                .expect("test operation should succeed");
            proof
                .delete_clause(id1)
                .expect("test operation should succeed");
            proof.flush().expect("test operation should succeed");
            proof.disable();
        }
        let mut file_contents = Vec::new();
        File::open(&path)
            .expect("test operation should succeed")
            .read_to_end(&mut file_contents)
            .expect("test operation should succeed");
        fs::remove_file(&path).ok();

        // Writer variant — shared Mutex<Vec<u8>> behind a BufWriter so the
        // buffering matches `enable(&path)` exactly.
        let (captured, sink) = shared_sink();

        {
            let mut proof = LratWriter::<BufWriter<SharedSink>>::with_writer(sink);
            let id1 = proof
                .add_clause(&[Lit::pos(v0), Lit::pos(v1)], &[])
                .expect("test operation should succeed");
            proof
                .add_clause(&[Lit::neg(v0)], &[id1])
                .expect("test operation should succeed");
            proof
                .delete_clause(id1)
                .expect("test operation should succeed");
            proof.flush().expect("test operation should succeed");
            proof.disable();
        }
        let writer_contents = captured
            .lock()
            .expect("test operation should succeed")
            .clone();

        assert_eq!(
            file_contents, writer_contents,
            "enable_writer must produce byte-identical output to enable(&path)"
        );
    }

    // === enable_writer reassignment: bytes land in the new sink ===

    #[test]
    fn test_drat_enable_writer_reassigns_sink() {
        let (sink_a_buf, sink_a) = shared_sink();
        let (sink_b_buf, sink_b) = shared_sink();

        let v0 = Var::new(0);
        let v1 = Var::new(1);

        let mut proof = DratWriter::<BufWriter<SharedSink>>::with_writer(sink_a);
        // Reassign the sink before writing anything.
        proof
            .enable_writer(sink_b)
            .expect("test operation should succeed");
        proof
            .add_clause(&[Lit::pos(v0), Lit::pos(v1)])
            .expect("test operation should succeed");
        proof.flush().expect("test operation should succeed");

        let a_bytes = sink_a_buf
            .lock()
            .expect("test operation should succeed")
            .clone();
        let b_bytes = sink_b_buf
            .lock()
            .expect("test operation should succeed")
            .clone();

        assert!(
            a_bytes.is_empty(),
            "original sink must stay empty after reassignment"
        );
        assert!(
            !b_bytes.is_empty(),
            "reassigned sink must receive the clause bytes"
        );
        assert_eq!(b_bytes, b"1 2 0\n");
    }

    #[test]
    fn test_lrat_enable_writer_reassigns_sink() {
        let (sink_a_buf, sink_a) = shared_sink();
        let (sink_b_buf, sink_b) = shared_sink();

        let v0 = Var::new(0);
        let v1 = Var::new(1);

        let mut proof = LratWriter::<BufWriter<SharedSink>>::with_writer(sink_a);
        // Reassign the sink before writing anything.
        proof
            .enable_writer(sink_b)
            .expect("test operation should succeed");
        proof
            .add_clause(&[Lit::pos(v0), Lit::pos(v1)], &[])
            .expect("test operation should succeed");
        proof.flush().expect("test operation should succeed");

        let a_bytes = sink_a_buf
            .lock()
            .expect("test operation should succeed")
            .clone();
        let b_bytes = sink_b_buf
            .lock()
            .expect("test operation should succeed")
            .clone();

        assert!(
            a_bytes.is_empty(),
            "original sink must stay empty after reassignment"
        );
        assert!(
            !b_bytes.is_empty(),
            "reassigned sink must receive the clause bytes"
        );
        // Empty-hint LRAT addition lines carry the mandatory trailing hint `0`,
        // so the well-formed form is `1 1 2 0 0` (literals `0`, then hints `0`).
        // This assertion previously pinned `1 1 2 0` — it was pinning the format
        // BUG, which is why the malformed output survived until the checker was
        // ported into this tree and rejected it.
        assert_eq!(b_bytes, b"1 1 2 0 0\n");
    }
}
