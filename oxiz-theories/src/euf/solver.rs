//! EUF Theory Solver

use super::union_find::UnionFind;
#[allow(unused_imports)]
use crate::prelude::*;
use crate::theory::{Theory, TheoryId, TheoryResult};
use core::mem;
use oxiz_core::ast::TermId;
use oxiz_core::error::Result;
use smallvec::SmallVec;

/// Capacity of the explanation cache: how many (a, b) -> reasons entries to retain.
/// Each entry records the BFS-derived reason set for a pair of E-graph node indices.
/// 1024 covers the vast majority of repeated sub-explanation queries that arise from
/// congruence closure without consuming significant memory.
const EUF_EXPL_CACHE_CAPACITY: usize = 1024;


/// Records an insertion into sig_table or fingerprint_table for undo on pop().
#[derive(Debug, Clone)]
enum SigTrailEntry {
    /// Inserted key into sig_table; undo removes this key.
    InsertedSig { key: (u32, SmallVec<[u32; 4]>) },
    /// Pushed node_idx into fingerprint_table[fp]; undo removes it from the bucket.
    InsertedFingerprint { fp: ENodeFingerprint, node_idx: u32 },
}

/// Function properties for dynamic arity support
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct FunctionProperties {
    /// Is the function associative? (e.g., +, *, and, or)
    pub associative: bool,
    /// Is the function commutative? (e.g., +, *, and, or)
    pub commutative: bool,
    /// Does the function have an identity element?
    pub has_identity: bool,
}

/// 64-bit fingerprint for fast congruence pre-filtering.
/// Before doing full signature comparison in the congruence table,
/// we compare fingerprints first (cheap u64 comparison) to avoid
/// expensive argument-level equality checks.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub struct ENodeFingerprint(u64);

impl ENodeFingerprint {
    /// Compute a fingerprint from a function symbol and canonical argument representatives.
    /// Uses a fast multiplicative hash to combine func and args into a single u64.
    #[must_use]
    pub fn compute(func: u32, args: &[u32]) -> Self {
        let mut h = func as u64;
        for &arg in args {
            h = h
                .wrapping_mul(0x517c_c1b7_2722_0a95)
                .wrapping_add(arg as u64);
        }
        Self(h)
    }

    /// Return the raw fingerprint value
    #[must_use]
    pub fn raw(self) -> u64 {
        self.0
    }
}

/// Congruence-closed view of one interned function application, produced by
/// [`EufSolver::function_application_entries`] for model extraction.
///
/// All representatives are canonical equivalence-class node indices (taken
/// through `find`), so applications whose arguments are pairwise congruent share
/// identical `arg_reps`/`result_rep` and collapse onto the same value class.
#[derive(Debug, Clone)]
pub struct FuncAppEntry {
    /// Canonical class representative (node index) of each argument, in order.
    pub arg_reps: SmallVec<[u32; 4]>,
    /// Every `TermId` interned into each argument's equivalence class, in the
    /// same order as `arg_reps`.  A model builder can scan these to find a
    /// member that carries a concrete value.
    pub arg_class_terms: SmallVec<[Vec<TermId>; 4]>,
    /// Canonical class representative (node index) of the application result.
    pub result_rep: u32,
    /// Every `TermId` interned into the result's equivalence class.
    pub result_class_terms: Vec<TermId>,
}

/// A term node in the E-graph
#[derive(Debug, Clone)]
struct ENode {
    /// Function symbol index; `u32::MAX` (= `ENode::NO_FUNC`) means leaf (no application).
    /// Placed first so that the hot `func` discriminant is at offset 0 of the struct.
    func: u32,
    /// 64-bit fingerprint for fast congruence pre-filtering.
    /// Placed second (after the 4-byte func + 4-byte implicit pad) so it aligns to 8 bytes
    /// without additional padding waste.
    fingerprint: ENodeFingerprint,
    /// Arguments (indices into nodes)
    args: SmallVec<[u32; 4]>,
    /// The original term
    term: TermId,
}

impl ENode {
    /// Sentinel value meaning "no function symbol" (leaf node).
    const NO_FUNC: u32 = u32::MAX;

    /// Create a leaf node (no function application).
    fn leaf(term: TermId) -> Self {
        ENode {
            func: Self::NO_FUNC,
            fingerprint: ENodeFingerprint::default(),
            args: SmallVec::new(),
            term,
        }
    }

    /// Create a function application node.
    fn app(
        func: u32,
        args: SmallVec<[u32; 4]>,
        fingerprint: ENodeFingerprint,
        term: TermId,
    ) -> Self {
        debug_assert!(
            func != Self::NO_FUNC,
            "func must not be u32::MAX (reserved sentinel)"
        );
        ENode {
            func,
            fingerprint,
            args,
            term,
        }
    }

    /// Returns true if this node is a function application (not a leaf).
    #[inline]
    fn is_app(&self) -> bool {
        self.func != Self::NO_FUNC
    }
}

/// Disequality constraint
#[derive(Debug, Clone)]
struct Diseq {
    /// First term
    lhs: u32,
    /// Second term
    rhs: u32,
    /// Reason for the disequality
    reason: TermId,
}

/// A merge reason: why two nodes became equal
#[derive(Debug, Clone)]
enum MergeReason {
    /// Direct equality assertion
    Assertion(TermId),
    /// Congruence: f(a1,...,an) = f(b1,...,bn) because ai = bi for all i
    Congruence {
        /// The terms that became equal by congruence
        term1: u32,
        term2: u32,
    },
}

/// A merge edge in the proof forest
#[derive(Debug, Clone)]
struct MergeEdge {
    /// The other node in the merge
    other: u32,
    /// The reason for the merge
    reason: MergeReason,
}

/// EUF Theory Solver using congruence closure
#[derive(Debug)]
pub struct EufSolver {
    /// Union-Find for equivalence classes
    uf: UnionFind,
    /// E-nodes
    nodes: Vec<ENode>,
    /// Term to node index mapping
    term_to_node: FxHashMap<TermId, u32>,
    /// Disequality constraints
    diseqs: Vec<Diseq>,
    /// Pending merges for congruence closure
    pending: Vec<(u32, u32, TermId)>,
    /// Use list: for each node, which applications use it as an argument
    use_list: Vec<SmallVec<[u32; 8]>>,
    /// Signature table for congruence closure
    sig_table: FxHashMap<(u32, SmallVec<[u32; 4]>), u32>,
    /// Fingerprint table: maps fingerprint -> list of node indices with that fingerprint.
    /// Used as a fast pre-filter before full signature comparison in congruence checks.
    fingerprint_table: FxHashMap<ENodeFingerprint, SmallVec<[u32; 4]>>,
    /// Context stack for push/pop
    context_stack: Vec<ContextState>,
    /// Proof forest: for each node, edges to explain equalities.
    /// SmallVec<[MergeEdge; 4]> avoids heap allocation for nodes with ≤4 proof edges,
    /// which covers the vast majority of E-graph nodes in practice.
    proof_forest: Vec<SmallVec<[MergeEdge; 4]>>,
    /// Function properties for dynamic arity support
    function_properties: FxHashMap<u32, FunctionProperties>,
    /// Reused queue for newly discovered propagations during congruence closure.
    propagation_buf: Vec<(u32, u32, TermId)>,
    /// Undo trail for sig_table and fingerprint_table insertions.
    sig_trail: Vec<SigTrailEntry>,
    /// Scope checkpoints into sig_trail, parallel to uf.trail_limits.
    sig_trail_limits: Vec<usize>,
    /// Undo trail for proof-forest edge insertions.  Each entry is the node
    /// index whose `proof_forest[idx]` had an edge appended; `pop()` pops these
    /// in LIFO order so that merge/congruence edges added inside a scope are
    /// removed when the scope is popped.  Without this, an edge appended to a
    /// node that SURVIVES the pop (index < `num_nodes`) would linger after its
    /// union was backtracked, and `explain_equality`'s BFS could route through
    /// the stale edge and return reasons for equalities that no longer hold —
    /// yielding an INVALID learned conflict clause and a spurious UNSAT.
    /// (`proof_forest.truncate(num_nodes)` only drops edges of the popped nodes
    /// themselves, never those leaked onto survivors.)
    proof_trail: Vec<u32>,
    /// Scope checkpoints into `proof_trail`, parallel to `uf.trail_limits`.
    proof_trail_limits: Vec<usize>,
    /// Undo trail for USE-LIST growth, `(node, length_before_the_append)`.
    ///
    /// The use-list has exactly the leak shape the `proof_trail` doc above
    /// describes, and for the same structural reason: `pop()`'s
    /// `use_list.truncate(num_nodes)` drops the lists OF the popped nodes, but
    /// entries appended to a SURVIVING node's list inside the scope — by
    /// `intern_app` (a new application registers itself under each argument's
    /// root) and by `propagate`'s use-list merge — outlive the pop. Without
    /// this trail they accumulate monotonically across every CDCL backtrack,
    /// so `propagate`'s per-merge scan (`for i in 0..use_len`) keeps re-walking
    /// entries whose merges were retracted long ago.
    ///
    /// Unlike the proof trail this is a PERFORMANCE fix, not a soundness one:
    /// a stale use-list entry only causes a redundant congruence check. The
    /// scan re-canonicalizes each user's arguments from current state and a
    /// `sig_table` hit means the two nodes really are congruent, so acting on
    /// a stale entry can only rediscover a true congruence — never invent one.
    /// It can still shift the search trajectory (a congruence found earlier
    /// than it otherwise would be), which is why the fix is gated by
    /// `OXIZ_EUF_NO_USELIST_TRAIL=1` for A/B rather than assumed inert.
    use_trail: Vec<(u32, u32)>,
    /// Scope checkpoints into `use_trail`, parallel to `uf.trail_limits`.
    use_trail_limits: Vec<usize>,
    /// `false` when `OXIZ_EUF_NO_USELIST_TRAIL=1` restores the pre-fix leaking
    /// behaviour (A/B kill-switch, read once per solver in [`Self::new`]).
    uselist_trail: bool,
    /// Merge counter, only consulted under `OXIZ_EUF_USELIST_DBG=1`.
    merge_count: u64,
    /// `OXIZ_EUF_USELIST_DBG=1`: periodically report use-list growth. Read once
    /// per solver so the hot path costs a bool test, not an env lookup.
    uselist_dbg: bool,
    /// Reusable BFS queue for explain_equality — avoids per-call VecDeque allocation.
    explain_queue: crate::prelude::VecDeque<u32>,
    /// Reusable visited flags for explain_equality — resized to proof_forest.len() and cleared at entry.
    explain_visited: Vec<bool>,
    /// Reusable parent-pointer table for explain_equality — parallel to explain_visited.
    explain_parent: Vec<Option<(u32, usize)>>,
    /// Bounded LRU cache for explanation results.
    ///
    /// Maps `(a, b)` node-index pairs to the `Vec<TermId>` reason set returned by
    /// `explain_equality`.  The cache is valid as long as no new merges have been
    /// applied; it is cleared eagerly in `merge()`, `pop()`, and `reset()` so that
    /// stale entries can never be observed.
    expl_cache: crate::lru_cache::LruCache<(u32, u32), Vec<TermId>>,
}

/// State to save for push/pop
#[derive(Debug, Clone)]
struct ContextState {
    num_nodes: usize,
    num_diseqs: usize,
}

impl Default for EufSolver {
    fn default() -> Self {
        Self::new()
    }
}

/// E2a: report the find/hop counters to stderr when the solver instance is
/// dropped and `OXIZ_EUF_STATS` is set (`var_os`, `OXIZ_MBQI_DBG` convention).
/// One line per `EufSolver` instance — a process that rebuilds its EUF core
/// prints one line per epoch. `std`-gated on top of the feature because both
/// `std::env` and a real `eprintln!` need `std`.
#[cfg(all(feature = "euf-find-stats", feature = "std"))]
impl Drop for EufSolver {
    fn drop(&mut self) {
        if std::env::var_os("OXIZ_EUF_STATS").is_some() {
            let (finds, hops) = self.uf.find_stats();
            #[allow(clippy::cast_precision_loss)]
            let avg = if finds == 0 {
                0.0
            } else {
                hops as f64 / finds as f64
            };
            eprintln!("[euf-stats] finds={finds} hops={hops} avg={avg:.2}");
        }
    }
}

impl EufSolver {
    /// Create a new EUF solver
    #[must_use]
    pub fn new() -> Self {
        Self {
            uf: UnionFind::new(0),
            nodes: Vec::new(),
            term_to_node: FxHashMap::default(),
            diseqs: Vec::new(),
            pending: Vec::new(),
            use_list: Vec::new(),
            sig_table: FxHashMap::default(),
            fingerprint_table: FxHashMap::default(),
            context_stack: Vec::new(),
            proof_forest: Vec::new(),
            function_properties: FxHashMap::default(),
            propagation_buf: Vec::new(),
            sig_trail: Vec::new(),
            sig_trail_limits: Vec::new(),
            proof_trail: Vec::new(),
            proof_trail_limits: Vec::new(),
            use_trail: Vec::new(),
            use_trail_limits: Vec::new(),
            // Read ONCE per solver, never in `propagate` (which runs per merge).
            // The switch can only move behaviour in the LEAKING direction, so it
            // is opt-in and never consulted unless explicitly set.
            uselist_trail: !std::env::var("OXIZ_EUF_NO_USELIST_TRAIL")
                .ok()
                .is_some_and(|v| v == "1" || v.eq_ignore_ascii_case("true")),
            merge_count: 0,
            uselist_dbg: std::env::var_os("OXIZ_EUF_USELIST_DBG").is_some(),
            explain_queue: crate::prelude::VecDeque::new(),
            explain_visited: Vec::new(),
            explain_parent: Vec::new(),
            expl_cache: crate::lru_cache::LruCache::new(EUF_EXPL_CACHE_CAPACITY),
        }
    }

    /// E2a: `(finds, hops)` accumulated by the union-find's `find_no_compress`
    /// since solver creation (or the last `reset_find_stats`).
    #[cfg(feature = "euf-find-stats")]
    #[must_use]
    pub fn find_stats(&self) -> (u64, u64) {
        self.uf.find_stats()
    }

    /// E2a: zero the union-find's `find_no_compress` counters.
    #[cfg(feature = "euf-find-stats")]
    pub fn reset_find_stats(&self) {
        self.uf.reset_find_stats();
    }

    /// Register a function with specific properties (for dynamic arity support)
    pub fn register_function(&mut self, func: u32, props: FunctionProperties) {
        self.function_properties.insert(func, props);
    }

    /// Get the properties of a function
    fn get_function_props(&self, func: u32) -> FunctionProperties {
        self.function_properties
            .get(&func)
            .copied()
            .unwrap_or_default()
    }

    /// Canonicalize arguments for commutative functions
    fn canonicalize_args(&self, func: u32, args: &[u32]) -> SmallVec<[u32; 4]> {
        let props = self.get_function_props(func);
        self.canonicalize_args_with_props(&props, args)
    }

    /// Canonicalize arguments given pre-fetched function properties.
    /// Used in hot paths to hoist the `get_function_props` hashmap lookup out of inner loops.
    fn canonicalize_args_with_props(
        &self,
        props: &FunctionProperties,
        args: &[u32],
    ) -> SmallVec<[u32; 4]> {
        let mut canonical: SmallVec<[u32; 4]> =
            args.iter().map(|&a| self.uf.find_no_compress(a)).collect();

        // For commutative functions, sort arguments by their canonical representative
        if props.commutative {
            canonical.sort_unstable();
        }

        canonical
    }

    /// Canonicalize arguments into a caller-owned buffer to avoid per-call allocation.
    /// Clears `buf` first, then pushes the canonical representative of each arg.
    /// For commutative functions the results are sorted in-place.
    ///
    /// This is the allocation-free variant used in the hot inner loop of `propagate`.
    /// Takes `&self`: its only self-use is `UnionFind::find_no_compress`, which is
    /// immutable — this lets callers pass `&self.nodes[..].args` directly without
    /// an intermediate copy.
    fn canonicalize_args_with_props_into(
        &self,
        props: &FunctionProperties,
        args: &[u32],
        buf: &mut SmallVec<[u32; 4]>,
    ) {
        buf.clear();
        for &a in args {
            buf.push(self.uf.find_no_compress(a));
        }
        if props.commutative {
            buf.sort_unstable();
        }
    }

    /// Flatten associative function applications
    /// For example: f(f(a, b), c) -> f(a, b, c)
    fn flatten_args(&self, func: u32, args: &[u32]) -> SmallVec<[u32; 4]> {
        let props = self.get_function_props(func);

        if !props.associative {
            return args.iter().copied().collect();
        }

        let mut flattened = SmallVec::new();
        for &arg in args {
            let arg_node = &self.nodes[arg as usize];
            // If the argument is an application of the same function, flatten it
            if arg_node.is_app() && arg_node.func == func {
                flattened.extend(arg_node.args.iter().copied());
            } else {
                flattened.push(arg);
            }
        }

        flattened
    }

    /// Intern a term, returning its node index
    #[inline]
    pub fn intern(&mut self, term: TermId) -> u32 {
        if let Some(&idx) = self.term_to_node.get(&term) {
            return idx;
        }

        let idx = self.nodes.len() as u32;
        self.nodes.push(ENode::leaf(term));
        self.uf.add();
        self.use_list.push(SmallVec::new());
        self.proof_forest.push(SmallVec::new());
        self.term_to_node.insert(term, idx);
        idx
    }

    /// Intern a function application
    #[inline]
    pub fn intern_app(
        &mut self,
        term: TermId,
        func: u32,
        args: impl IntoIterator<Item = u32>,
    ) -> u32 {
        if let Some(&idx) = self.term_to_node.get(&term) {
            return idx;
        }

        let args: SmallVec<[u32; 4]> = args.into_iter().collect();

        // Flatten for associative functions
        let flattened_args = self.flatten_args(func, &args);

        // Canonicalize arguments (handles commutativity and finds canonical reps)
        let canonical_args = self.canonicalize_args(func, &flattened_args);

        // Compute fingerprint for fast congruence pre-filtering
        let fp = ENodeFingerprint::compute(func, &canonical_args);

        let sig = (func, canonical_args.clone());
        if let Some(&existing) = self.sig_table.get(&sig) {
            self.term_to_node.insert(term, existing);
            return existing;
        }

        let idx = self.nodes.len() as u32;
        self.nodes
            .push(ENode::app(func, flattened_args.clone(), fp, term));
        self.uf.add();
        self.use_list.push(SmallVec::new());
        self.proof_forest.push(SmallVec::new());
        self.term_to_node.insert(term, idx);

        // Add to use lists. Inside a push scope the append is trailed: `arg` may
        // be a node that SURVIVES the matching pop while `idx` does not, and
        // `pop()`'s `use_list.truncate(num_nodes)` cannot reach an entry parked
        // on a survivor's list (see `use_trail`).
        let trail_uses = self.uselist_trail && !self.use_trail_limits.is_empty();
        for &arg in &flattened_args {
            if trail_uses {
                self.use_trail
                    .push((arg, self.use_list[arg as usize].len() as u32));
            }
            self.use_list[arg as usize].push(idx);
        }

        // Add to signature table. When inside a push scope, record the insertion
        // in the undo trail so pop() can remove it without rebuilding the table.
        // `canonical_args` is moved (no extra clone needed).
        if !self.sig_trail_limits.is_empty() {
            self.sig_trail.push(SigTrailEntry::InsertedSig {
                key: (func, canonical_args),
            });
        }
        self.sig_table.insert(sig, idx);

        // Add to fingerprint table for fast congruence pre-filtering
        self.fingerprint_table.entry(fp).or_default().push(idx);
        if !self.sig_trail_limits.is_empty() {
            self.sig_trail
                .push(SigTrailEntry::InsertedFingerprint { fp, node_idx: idx });
        }

        idx
    }

    /// Publish a node's signature into `sig_table` + `fingerprint_table`,
    /// trailing both when inside a push scope (#431).
    #[inline]
    fn publish_signature(
        &mut self,
        func: u32,
        args: SmallVec<[u32; 4]>,
        node: u32,
        fp: ENodeFingerprint,
        in_scope: bool,
    ) {
        if in_scope {
            self.sig_trail.push(SigTrailEntry::InsertedSig {
                key: (func, args.clone()),
            });
        }
        self.sig_table.insert((func, args), node);
        self.fingerprint_table.entry(fp).or_default().push(node);
        if in_scope {
            self.sig_trail
                .push(SigTrailEntry::InsertedFingerprint { fp, node_idx: node });
        }
    }

    /// Append a proof-forest edge to `node`, recording it in `proof_trail` when
    /// inside a push scope so `pop()` can undo it.  All proof-edge insertions go
    /// through here to keep the undo trail complete.
    #[inline]
    fn push_proof_edge(&mut self, node: u32, edge: MergeEdge) {
        self.proof_forest[node as usize].push(edge);
        if !self.proof_trail_limits.is_empty() {
            self.proof_trail.push(node);
        }
    }

    /// Merge two equivalence classes
    #[inline]
    pub fn merge(&mut self, a: u32, b: u32, reason: TermId) -> Result<()> {
        // Any pending merge invalidates previously cached explanations because the
        // proof forest will grow new edges that could shorten existing paths.
        self.expl_cache.clear();
        self.pending.push((a, b, reason));
        self.propagate()?;
        Ok(())
    }

    /// Propagate pending merges with optimized congruence closure:
    /// - Index-based use-list iteration (avoids cloning the use-list)
    /// - Batch signature updates (collects all updates, applies at once)
    /// - Fingerprint pre-filter (cheap u64 comparison before full signature match)
    fn propagate(&mut self) -> Result<()> {
        let mut propagation_buf = mem::take(&mut self.propagation_buf);
        propagation_buf.clear();

        while let Some((a, b, reason)) = self.pending.pop() {
            let root_a = self.uf.find_no_compress(a);
            let root_b = self.uf.find_no_compress(b);

            if root_a == root_b {
                continue;
            }

            // Record the merge in the proof forest (for explanation generation)
            self.push_proof_edge(
                a,
                MergeEdge {
                    other: b,
                    reason: MergeReason::Assertion(reason),
                },
            );
            self.push_proof_edge(
                b,
                MergeEdge {
                    other: a,
                    reason: MergeReason::Assertion(reason),
                },
            );

            // Union the classes
            self.uf.union(root_a, root_b);
            let new_root = self.uf.find_no_compress(root_a);

            // Congruence closure: check for new merges
            let other_root = if new_root == root_a { root_b } else { root_a };

            // --- Optimization 1: Index-based use-list iteration ---
            // Instead of cloning the entire use-list, iterate by index.
            // We snapshot the length so we only process existing entries.
            let use_len = self.use_list[other_root as usize].len();

            // --- Optimization 2: Batch signature updates ---
            // Collect all (new_signature, node_id) pairs first, then apply
            // to the sig_table in a single batch to avoid repeated hash lookups.
            // #431 — signatures are published EAGERLY, inside the scan below.
            // Batching them until after the scan made congruence between two
            // parents in the SAME use-list undetectable: the first parent's new
            // signature was not yet in `sig_table`, so the second parent's
            // lookup missed and both were batched. The fingerprint pre-filter
            // compounded it — the first parent's fingerprint was not published
            // either, so the second took the fast exit and never consulted
            // `sig_table` at all.
            let in_scope = !self.sig_trail_limits.is_empty();
            // Collect congruence merges to enqueue
            propagation_buf.clear();

            // --- Change A: Reusable canonicalization buffer ---
            // Declared once outside the loop so the SmallVec's heap backing (if it
            // ever spills past the inline capacity of 4) is allocated at most once
            // per merge event rather than once per use-list entry.
            let mut canon_buf: SmallVec<[u32; 4]> = SmallVec::new();

            for i in 0..use_len {
                let user = self.use_list[other_root as usize][i];
                if (user as usize) >= self.nodes.len() {
                    continue; // stale use-list entry — node was not allocated
                }
                let node_func_val = self.nodes[user as usize].func;
                if node_func_val == ENode::NO_FUNC {
                    continue;
                }
                let func = node_func_val;

                // Fetch function properties once per use-list entry (per unique func),
                // then pass to canonicalize_args_with_props_into to avoid repeated lookups.
                let props = self.get_function_props(func);

                // Canonicalize arguments into the reusable buffer (avoids per-iteration
                // alloc).  The node's args are borrowed in place — the canonicalizer is
                // `&self` and writes only into the caller-local `canon_buf`, so no
                // intermediate args copy is needed.
                self.canonicalize_args_with_props_into(
                    &props,
                    &self.nodes[user as usize].args,
                    &mut canon_buf,
                );

                // --- Optimization 3: Fingerprint pre-filter ---
                // Compute the new fingerprint for the updated canonical args
                let new_fp = ENodeFingerprint::compute(func, &canon_buf);

                // Fast-exit guard before costly sig_table.get:
                // `sig_table.get` hashes over (u32, SmallVec) which is expensive.
                // If no entry with this fingerprint exists in fingerprint_table, skip
                // the sig lookup — but still update sig_updates and the node fingerprint
                // so the invariant (fingerprint_table tracks all live fps) is maintained.
                // `canon_buf` is MOVED into the batched entry (it is cleared and refilled
                // at the top of canonicalize_args_with_props_into, so handing over a
                // freshly-empty buffer to the next iteration is fine).
                if !self.fingerprint_table.contains_key(&new_fp) {
                    let args = mem::take(&mut canon_buf);
                    self.publish_signature(func, args, user, new_fp, in_scope);
                    self.nodes[user as usize].fingerprint = new_fp;
                    continue;
                }

                // Check signature table for congruence match.  The key takes
                // ownership of canon_buf (no clone); on a HIT the buffer is
                // recovered below so later iterations keep reusing its backing.
                let sig = (func, mem::take(&mut canon_buf));
                if let Some(&existing) = self.sig_table.get(&sig) {
                    // Recover the buffer for the next iteration.
                    canon_buf = sig.1;
                    if !self.uf.same_no_compress(user, existing) {
                        // Congruence detected: record proof edges
                        self.push_proof_edge(
                            user,
                            MergeEdge {
                                other: existing,
                                reason: MergeReason::Congruence {
                                    term1: user,
                                    term2: existing,
                                },
                            },
                        );
                        self.push_proof_edge(
                            existing,
                            MergeEdge {
                                other: user,
                                reason: MergeReason::Congruence {
                                    term1: user,
                                    term2: existing,
                                },
                            },
                        );

                        propagation_buf.push((user, existing, TermId::new(0)));
                    }
                } else {
                    // No congruence match; publish NOW so a later parent in the
                    // same use-list can see it.
                    self.publish_signature(func, sig.1, user, new_fp, in_scope);
                }

                // Update the node's fingerprint
                self.nodes[user as usize].fingerprint = new_fp;
            }

            // Enqueue congruence merges
            for (user, existing, term) in propagation_buf.drain(..) {
                self.pending.push((user, existing, term));
            }

            // Merge use lists: append other_root's entries to new_root's.
            //
            // Done through `split_at_mut` rather than the previous
            // "copy into a temporary SmallVec, then extend" — that staged the
            // whole list through a fresh allocation on EVERY merge, which is
            // what the profile saw as ~27% self time in libc memcpy on
            // `fuel-recursion-3/ob07`. One copy now, no temporary.
            //
            // Trailed inside a push scope for the reason documented on
            // `use_trail`: `pop()`'s `use_list.truncate(num_nodes)` reaches the
            // lists OF popped nodes, never entries appended to a SURVIVOR's
            // list, so without this the merged-in entries accumulate across
            // every backtrack and the `for i in 0..use_len` scan above keeps
            // re-walking retracted merges.
            let (dst_i, src_i) = (new_root as usize, other_root as usize);
            if dst_i != src_i && use_len > 0 {
                if self.uselist_trail && !self.use_trail_limits.is_empty() {
                    self.use_trail
                        .push((new_root, self.use_list[dst_i].len() as u32));
                }
                if dst_i < src_i {
                    let (left, right) = self.use_list.split_at_mut(src_i);
                    left[dst_i].extend_from_slice(&right[0][..use_len]);
                } else {
                    let (left, right) = self.use_list.split_at_mut(dst_i);
                    right[0].extend_from_slice(&left[src_i][..use_len]);
                }
            }

            self.merge_count += 1;
            // Powers of two rather than a fixed stride: the interesting shape is
            // GROWTH, and a run may do a thousand merges or a billion. This way
            // the trace is log-scale and never needs tuning to the workload.
            if self.uselist_dbg && self.merge_count.is_power_of_two() {
                let total: usize = self.use_list.iter().map(SmallVec::len).sum();
                let max = self.use_list.iter().map(SmallVec::len).max().unwrap_or(0);
                let merges = self.merge_count;
                let nodes = self.nodes.len();
                eprintln!(
                    "[euf-uselist] merges={merges} nodes={nodes} use_entries={total} max_list={max}"
                );
            }
        }

        propagation_buf.clear();
        self.propagation_buf = propagation_buf;

        Ok(())
    }

    /// Assert a disequality
    pub fn assert_diseq(&mut self, a: u32, b: u32, reason: TermId) {
        self.diseqs.push(Diseq {
            lhs: a,
            rhs: b,
            reason,
        });
    }

    /// Check for conflicts
    pub fn check_conflicts(&mut self) -> Option<Vec<TermId>> {
        // First find the conflicting disequality by index so that we can drop
        // the shared borrow on `self.diseqs` before calling `explain_equality`
        // (which needs `&mut self`).
        let conflict_idx = self
            .diseqs
            .iter()
            .position(|d| self.uf.same_no_compress(d.lhs, d.rhs))?;

        let (lhs, rhs, reason) = {
            let d = &self.diseqs[conflict_idx];
            (d.lhs, d.rhs, d.reason)
        };

        // Borrow of self.diseqs is fully released here.
        let mut explanation = self.explain_equality(lhs, rhs);
        if !explanation.contains(&reason) {
            explanation.push(reason);
        }
        Some(explanation)
    }

    /// Explain why two nodes are equal.
    ///
    /// Uses BFS through the proof forest to find a path from `a` to `b`, then an
    /// explicit worklist (`pending`, a heap `Vec` — NOT recursion) to expand any
    /// `MergeReason::Congruence` edge on that path into its own argument-equality
    /// sub-explanation. This used to recurse one native call frame per congruence
    /// level; a long chain of nested congruence merges (e.g. a deep repeated
    /// selector/constructor application, or several cross-product OR-branch merges
    /// stacking up) could recurse deep enough to overflow the stack — a real crash
    /// found by #418's adversarial differential fuzzing (#419), on inputs that only
    /// became reachable once #418's own new reductions started closing more
    /// congruences. The worklist makes total work scale with heap memory instead
    /// of stack depth, with no bound on chain length. `pending_seen`/`reasons_seen`
    /// dedup by unordered node-pair / by `TermId` respectively, so a reason or a
    /// sub-explanation already produced is never redone (this also caps total work
    /// at O(V) pair-expansions, same asymptotic bound the recursive version had).
    /// Reusable buffers (`explain_queue`, `explain_visited`, `explain_parent`) are
    /// still moved out of `self` via `mem::take` for each BFS sub-call and restored
    /// immediately after, exactly as before.
    fn explain_equality(&mut self, a: u32, b: u32) -> Vec<TermId> {
        let mut reasons: Vec<TermId> = Vec::new();
        let mut reasons_seen: FxHashSet<TermId> = FxHashSet::default();
        let mut pending: Vec<(u32, u32)> = vec![(a, b)];
        let mut pending_seen: FxHashSet<(u32, u32)> = FxHashSet::default();

        while let Some((a, b)) = pending.pop() {
            if a == b {
                continue;
            }

            let n = self.proof_forest.len();
            // Guard against out-of-bounds indices
            if (a as usize) >= n || (b as usize) >= n {
                continue;
            }

            let key = if a < b { (a, b) } else { (b, a) };
            if !pending_seen.insert(key) {
                continue;
            }

            // Take reusable buffers out of self for this BFS sub-call.
            let mut queue = mem::take(&mut self.explain_queue);
            let mut visited = mem::take(&mut self.explain_visited);
            let mut parent = mem::take(&mut self.explain_parent);

            // Reset / resize in-place — existing heap capacity is retained.
            queue.clear();
            visited.clear();
            visited.resize(n, false);
            parent.clear();
            parent.resize(n, None);

            // BFS to find path from a to b
            queue.push_back(a);
            visited[a as usize] = true;

            let mut found = false;
            while let Some(node) = queue.pop_front() {
                if node == b {
                    found = true;
                    break;
                }

                if (node as usize) >= self.proof_forest.len() {
                    continue;
                }
                for (idx, edge) in self.proof_forest[node as usize].iter().enumerate() {
                    let other_idx = edge.other as usize;
                    if other_idx < n && !visited[other_idx] {
                        visited[other_idx] = true;
                        parent[other_idx] = Some((node, idx));
                        queue.push_back(edge.other);
                    }
                }
            }

            if !found {
                // Restore buffers before moving on so they are available for the next pair.
                self.explain_queue = queue;
                self.explain_visited = visited;
                self.explain_parent = parent;
                continue;
            }

            // Collect the (prev, edge_idx) pairs from the parent chain into a local
            // Vec before dropping the parent borrow.
            let mut path: Vec<(u32, usize)> = Vec::new();
            let mut current = b;
            while let Some((prev, edge_idx)) = parent[current as usize] {
                path.push((prev, edge_idx));
                current = prev;
            }

            // Restore buffers now.
            self.explain_queue = queue;
            self.explain_visited = visited;
            self.explain_parent = parent;

            // Reconstruct path and collect reasons
            for (prev, edge_idx) in path {
                let reason = self.proof_forest[prev as usize][edge_idx].reason.clone();

                match reason {
                    MergeReason::Assertion(term_id) => {
                        if term_id.raw() != 0 && reasons_seen.insert(term_id) {
                            reasons.push(term_id);
                        }
                    }
                    MergeReason::Congruence { term1, term2 } => {
                        // For congruence, we need to explain why the arguments are
                        // equal — push their (arg1, arg2) pairs onto the worklist
                        // instead of recursing.
                        let args1: SmallVec<[u32; 4]> = self.nodes[term1 as usize].args.clone();
                        let args2: SmallVec<[u32; 4]> = self.nodes[term2 as usize].args.clone();

                        for (&arg1, &arg2) in args1.iter().zip(args2.iter()) {
                            if arg1 != arg2 && self.uf.same_no_compress(arg1, arg2) {
                                pending.push((arg1, arg2));
                            }
                        }
                    }
                }
            }
        }

        reasons
    }

    /// Check if two terms are equivalent
    ///
    /// Uses the non-compressing query so that backtracking (`uf.pop`) can fully
    /// restore the parent array — path compression would write untracked parent
    /// pointers that a later `truncate(num_nodes)` could leave dangling.
    ///
    /// Total over *any* `u32`: a node index that is no longer live (≥ the
    /// current node count, e.g. a term interned in a scope that has since been
    /// popped) is treated as its own singleton class.  This keeps stale-index
    /// queries sound — two distinct stale indices are never equal, and a stale
    /// index is never equal to a live one — instead of indexing past the
    /// (now-truncated) union-find.
    #[inline]
    pub fn are_equal(&mut self, a: u32, b: u32) -> bool {
        if a == b {
            return true;
        }
        let live = self.nodes.len() as u32;
        if a >= live || b >= live {
            return false;
        }
        self.uf.same_no_compress(a, b)
    }

    /// Get the representative of a term
    ///
    /// Non-compressing for the same backtracking-safety reason as `are_equal`,
    /// and total: a non-live index (≥ the current node count) represents itself.
    #[inline]
    pub fn find(&mut self, a: u32) -> u32 {
        if (a as usize) >= self.nodes.len() {
            return a;
        }
        self.uf.find_no_compress(a)
    }

    /// Get the representative of a term without path compression (immutable)
    ///
    /// Total: a non-live index (≥ the current node count) represents itself.
    #[inline]
    pub fn find_immutable(&self, a: u32) -> u32 {
        if (a as usize) >= self.nodes.len() {
            return a;
        }
        self.uf.find_no_compress(a)
    }

    /// Check equivalence without mutation (immutable)
    ///
    /// Total over any `u32`; see `are_equal` for the stale-index contract.
    #[inline]
    pub fn are_equal_immutable(&self, a: u32, b: u32) -> bool {
        if a == b {
            return true;
        }
        let live = self.nodes.len() as u32;
        if a >= live || b >= live {
            return false;
        }
        self.uf.same_no_compress(a, b)
    }

    /// Are `a` and `b` PROVABLY disequal in the current congruence (immutable)?
    ///
    /// A **sound, conservative** test: returns `true` only when `a` and `b` fall
    /// in different classes AND some *asserted* disequality separates those two
    /// classes. It NEVER returns `true` for a pair that is merely "not provably
    /// equal" — that distinction is the whole point (the CCFV verdict-flip needs
    /// genuine `≄` entailment, not the weaker `¬equal`). Used by the clean-MBQI
    /// `Congruence::disequal` oracle as a building block; it does not mutate (no
    /// `explain_equality`, unlike the conflict path), so it is safe to call on the
    /// post-solve congruence. Total over any `u32` (stale indices → `false`).
    #[inline]
    pub fn are_disequal_immutable(&self, a: u32, b: u32) -> bool {
        if a == b {
            return false;
        }
        let live = self.nodes.len() as u32;
        if a >= live || b >= live {
            return false;
        }
        let ra = self.uf.find_no_compress(a);
        let rb = self.uf.find_no_compress(b);
        if ra == rb {
            return false; // same class ⇒ congruent, not disequal
        }
        self.diseqs.iter().any(|d| {
            let dl = self.uf.find_no_compress(d.lhs);
            let dr = self.uf.find_no_compress(d.rhs);
            (dl == ra && dr == rb) || (dl == rb && dr == ra)
        })
    }

    /// Get the number of E-graph nodes
    pub fn node_count(&self) -> usize {
        self.nodes.len()
    }

    /// Get the term associated with a node index
    pub fn node_term(&self, idx: u32) -> Option<TermId> {
        self.nodes.get(idx as usize).map(|n| n.term)
    }

    /// Get the function symbol of a node (if it is a function application)
    pub fn node_func(&self, idx: u32) -> Option<u32> {
        self.nodes
            .get(idx as usize)
            .and_then(|n| if n.is_app() { Some(n.func) } else { None })
    }

    /// Get the arguments of a node (if it is a function application)
    pub fn node_args(&self, idx: u32) -> Option<&SmallVec<[u32; 4]>> {
        let node = self.nodes.get(idx as usize)?;
        if node.is_app() {
            Some(&node.args)
        } else {
            None
        }
    }

    /// Look up the node index for a given TermId
    pub fn term_to_node(&self, term: TermId) -> Option<u32> {
        self.term_to_node.get(&term).copied()
    }

    /// The TermIds currently interned in this EUF context (the keys of the
    /// internal term→node map). Used by theory combination to enumerate the
    /// shared terms eligible for congruence-driven equality propagation — these
    /// are the function-application / constant sub-terms (e.g. `f(1)`, `5`),
    /// NOT the Bool atoms the SAT solver assigns.
    #[must_use]
    pub fn interned_term_ids(&self) -> Vec<TermId> {
        self.term_to_node.keys().copied().collect()
    }

    /// Iterate over all node indices that are function applications of a given function symbol.
    /// Returns a Vec of node indices.
    pub fn apps_by_func(&self, func_id: u32) -> Vec<u32> {
        let mut result = Vec::new();
        for (idx, node) in self.nodes.iter().enumerate() {
            if node.is_app() && node.func == func_id {
                result.push(idx as u32);
            }
        }
        result
    }

    /// Collect, for every interned application of `func_id`, the congruence-closed
    /// data a model builder needs to assemble a function interpretation.
    ///
    /// For each application node `f(a1, …, an)` the returned [`FuncAppEntry`]
    /// records:
    /// - `arg_reps`: the canonical equivalence-class representative (node index,
    ///   obtained via [`find_immutable`](Self::find_immutable)) of each argument,
    /// - `arg_class_terms`: every `TermId` interned into each argument's class —
    ///   so the caller can pick whichever member carries a concrete model value,
    /// - `result_rep`: the canonical class representative of the application
    ///   itself,
    /// - `result_class_terms`: every `TermId` interned into the result's class.
    ///
    /// Because the argument and result classes are taken through `find`, two
    /// applications whose arguments are pairwise congruent (e.g. `f(a)` and
    /// `f(b)` when `a = b`) yield identical `arg_reps` and `result_rep`. The
    /// caller can therefore deduplicate on `arg_reps` and rely on congruence
    /// having already collapsed them onto the same value class.
    ///
    /// This is a read-only `O(nodes)` scan (it never mutates the union-find, so
    /// no path compression occurs) and is intended for the post-`Sat` model
    /// extraction path, not the hot solving loop.
    #[must_use]
    pub fn function_application_entries(&self, func_id: u32) -> Vec<FuncAppEntry> {
        // Single O(nodes) pass: bucket every node's TermId under its canonical
        // class representative.  This avoids the O(apps × nodes) blow-up of
        // calling `class_members` once per application.
        let mut class_to_terms: FxHashMap<u32, Vec<TermId>> = FxHashMap::default();
        for idx in 0..self.nodes.len() as u32 {
            let rep = self.uf.find_no_compress(idx);
            class_to_terms
                .entry(rep)
                .or_default()
                .push(self.nodes[idx as usize].term);
        }

        let mut entries = Vec::new();
        for (idx, node) in self.nodes.iter().enumerate() {
            if !node.is_app() || node.func != func_id {
                continue;
            }

            // Canonical class rep of each argument plus the member TermIds of
            // that class (for value resolution by the caller).
            let mut arg_reps: SmallVec<[u32; 4]> = SmallVec::with_capacity(node.args.len());
            let mut arg_class_terms: SmallVec<[Vec<TermId>; 4]> =
                SmallVec::with_capacity(node.args.len());
            for &arg in &node.args {
                let rep = self.uf.find_no_compress(arg);
                arg_reps.push(rep);
                arg_class_terms.push(class_to_terms.get(&rep).cloned().unwrap_or_default());
            }

            let result_rep = self.uf.find_no_compress(idx as u32);
            let result_class_terms = class_to_terms.get(&result_rep).cloned().unwrap_or_default();

            entries.push(FuncAppEntry {
                arg_reps,
                arg_class_terms,
                result_rep,
                result_class_terms,
            });
        }
        entries
    }

    /// Get all members of an equivalence class (all node indices with the same representative).
    /// This is an O(n) scan; for performance-critical paths, consider caching.
    pub fn class_members(&self, class_rep: u32) -> Vec<u32> {
        let rep = self.uf.find_no_compress(class_rep);
        let mut members = Vec::new();
        for idx in 0..self.nodes.len() {
            if self.uf.find_no_compress(idx as u32) == rep {
                members.push(idx as u32);
            }
        }
        members
    }

    /// Iterate over all node indices (0..node_count)
    pub fn all_node_indices(&self) -> std::ops::Range<u32> {
        0..self.nodes.len() as u32
    }

    /// Get all distinct function symbols present in the E-graph
    pub fn all_func_symbols(&self) -> Vec<u32> {
        use rustc_hash::FxHashSet;
        let mut funcs = FxHashSet::default();
        for node in &self.nodes {
            if node.is_app() {
                funcs.insert(node.func);
            }
        }
        funcs.into_iter().collect()
    }

    /// Get the fingerprint table size (for testing/debugging)
    #[cfg(test)]
    fn fingerprint_table_len(&self) -> usize {
        self.fingerprint_table.len()
    }

    /// Get the sig table size (for testing/debugging)
    #[cfg(test)]
    fn sig_table_len(&self) -> usize {
        self.sig_table.len()
    }
}

impl Theory for EufSolver {
    fn id(&self) -> TheoryId {
        TheoryId::EUF
    }

    fn name(&self) -> &str {
        "EUF"
    }

    fn can_handle(&self, _term: TermId) -> bool {
        // EUF can handle equality and function applications
        true
    }

    fn assert_true(&mut self, term: TermId) -> Result<TheoryResult> {
        // Assuming term is an equality a = b
        // In a full implementation, we'd parse the term
        let _ = self.intern(term);
        Ok(TheoryResult::Sat)
    }

    fn assert_false(&mut self, term: TermId) -> Result<TheoryResult> {
        // Assuming term is an equality a = b, assert a != b
        let node = self.intern(term);
        self.assert_diseq(node, node, term); // Simplified - real impl needs parsing
        Ok(TheoryResult::Sat)
    }

    fn check(&mut self) -> Result<TheoryResult> {
        if let Some(conflict) = self.check_conflicts() {
            Ok(TheoryResult::Unsat(conflict))
        } else {
            Ok(TheoryResult::Sat)
        }
    }

    fn push(&mut self) {
        self.context_stack.push(ContextState {
            num_nodes: self.nodes.len(),
            num_diseqs: self.diseqs.len(),
        });
        self.uf.push();
        // Record sig_trail checkpoint, mirroring uf.trail_limits.push(...)
        self.sig_trail_limits.push(self.sig_trail.len());
        // Record proof_trail checkpoint, likewise mirroring uf.trail_limits.
        self.proof_trail_limits.push(self.proof_trail.len());
        // Record use_trail checkpoint, likewise mirroring uf.trail_limits.
        self.use_trail_limits.push(self.use_trail.len());
    }

    fn pop(&mut self) {
        if let Some(state) = self.context_stack.pop() {
            let num_nodes = state.num_nodes;

            // Backtracking changes both the union state and the proof forest, so
            // any cached explanation may now be stale.  Drop the cache (mirrors
            // the clear in `merge`).
            self.expl_cache.clear();

            self.nodes.truncate(num_nodes);
            self.diseqs.truncate(state.num_diseqs);
            self.uf.pop();
            // The union-find allocates one slot per E-node (`intern`/`intern_app`
            // call `uf.add()` alongside the `nodes.push`), but `uf.pop()` only
            // reverts *unions* — it leaves the slots added since the matching
            // push in place.  Truncate them away so `uf.len()` tracks
            // `nodes.len()`; otherwise the next `intern` desyncs the node index
            // from the uf slot and a later `find` returns a dangling root past
            // the (now shorter) `use_list` (the historical use_list OOB panic).
            // Sound because every in-scope union was just reverted and the
            // backtracked find paths do not compress (see `find_no_compress`
            // usage below), so no surviving node points past `num_nodes`.
            self.uf.truncate(num_nodes);

            // Undo proof-forest edges appended since the matching push, in LIFO
            // order, BEFORE truncating `proof_forest` (the trail may reference
            // popped node indices ≥ num_nodes that still exist until the
            // truncate below).  This removes edges that leaked onto SURVIVING
            // nodes during the scope — the ones `truncate(num_nodes)` cannot
            // reach — so `explain_equality` never routes through a retracted
            // merge.  Mirrors the sig_trail rewind.
            if let Some(proof_limit) = self.proof_trail_limits.pop() {
                while self.proof_trail.len() > proof_limit {
                    if let Some(node) = self.proof_trail.pop() {
                        self.proof_forest[node as usize].pop();
                    }
                }
            }

            // Rewind the use-list growth recorded since the matching push, in
            // LIFO order, BEFORE the truncate below — that truncate only drops
            // the lists OF popped nodes, never the entries this scope parked on
            // a SURVIVOR's list (see `use_trail`). LIFO is what makes the
            // recorded `old_len` the right restore point when several merges
            // extended the same root inside one scope.
            if let Some(use_limit) = self.use_trail_limits.pop() {
                while self.use_trail.len() > use_limit {
                    if let Some((node, old_len)) = self.use_trail.pop() {
                        if let Some(list) = self.use_list.get_mut(node as usize) {
                            list.truncate(old_len as usize);
                        }
                    }
                }
            }

            // Also truncate related structures
            self.use_list.truncate(num_nodes);
            self.proof_forest.truncate(num_nodes);

            // Remove term_to_node mappings that point to removed nodes
            self.term_to_node
                .retain(|_term, &mut idx| (idx as usize) < num_nodes);

            // Rewind sig_trail to the saved limit, undoing all sig/fp insertions
            // made since the matching push().  Mirrors UnionFind::pop() exactly.
            if let Some(sig_limit) = self.sig_trail_limits.pop() {
                while self.sig_trail.len() > sig_limit {
                    if let Some(entry) = self.sig_trail.pop() {
                        match entry {
                            SigTrailEntry::InsertedSig { key } => {
                                self.sig_table.remove(&key);
                            }
                            SigTrailEntry::InsertedFingerprint { fp, node_idx } => {
                                if let Some(bucket) = self.fingerprint_table.get_mut(&fp) {
                                    // Remove in LIFO order: the last push is the first to undo.
                                    if let Some(pos) = bucket.iter().rposition(|&n| n == node_idx) {
                                        bucket.swap_remove(pos);
                                    }
                                    if bucket.is_empty() {
                                        self.fingerprint_table.remove(&fp);
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    fn reset(&mut self) {
        self.uf = UnionFind::new(0);
        self.nodes.clear();
        self.term_to_node.clear();
        self.diseqs.clear();
        self.pending.clear();
        self.use_list.clear();
        self.sig_table.clear();
        self.fingerprint_table.clear();
        self.context_stack.clear();
        self.proof_forest.clear();
        self.function_properties.clear();
        self.sig_trail.clear();
        self.sig_trail_limits.clear();
        self.proof_trail.clear();
        self.proof_trail_limits.clear();
        self.use_trail.clear();
        self.use_trail_limits.clear();
        self.merge_count = 0;
        self.expl_cache.clear();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// #39 — the use-list must not survive the pop that retracts its merge.
    ///
    /// `pop()`'s `use_list.truncate(num_nodes)` reaches the lists OF popped
    /// nodes; it cannot reach entries this scope appended to a SURVIVOR's list.
    /// Without `use_trail` those entries accumulate on every backtrack, and
    /// because the union direction alternates across backtracks the growth is
    /// not linear but FIBONACCI: `A <- A+B`, then `B <- B+(A+B)`, then
    /// `A <- (A+B)+(A+2B)`. Measured on `fuel-recursion-3/ob07`: 371 nodes,
    /// 39.7 MILLION use-list entries with a single list holding 37.1 million,
    /// and `propagate` re-walking them on every merge.
    ///
    /// The pin is a length equality, not a wall-clock bound, so it cannot rot
    /// into a flaky timing test.
    #[test]
    fn use_list_growth_is_undone_by_pop() {
        const F: u32 = 7;
        let mut s = EufSolver::new();
        let a = s.intern(TermId::new(1));
        let b = s.intern(TermId::new(2));
        // Applications registered OUTSIDE any scope: these entries must survive.
        s.intern_app(TermId::new(10), F, [a]);
        s.intern_app(TermId::new(11), F, [b]);
        let base: Vec<usize> = s.use_list.iter().map(SmallVec::len).collect();

        // Ten push/merge/pop cycles over the same pair. Pre-fix, each cycle
        // leaves `use_list[root]` longer than it found it; post-fix every cycle
        // restores it exactly.
        for i in 0..10u32 {
            s.push();
            // A fresh application inside the scope registers itself under `a`
            // and `b` — the `intern_app` half of the leak.
            s.intern_app(TermId::new(100 + i), F, [a, b]);
            s.merge(a, b, TermId::new(0)).unwrap();
            s.pop();
            let now: Vec<usize> = s.use_list.iter().map(SmallVec::len).collect();
            assert_eq!(
                now, base,
                "cycle {i}: use-list lengths must be restored by pop()"
            );
        }
        // And the merge itself must still be retracted (the trail must not have
        // broken backtracking).
        assert!(!s.are_equal(a, b), "the merge was inside the popped scope");
    }

    /// The same cycle with the kill-switch semantics: when the trail is
    /// disabled the lists DO grow, which is what makes the pin above meaningful
    /// rather than vacuous.
    #[test]
    fn use_list_growth_without_the_trail_is_real() {
        const F: u32 = 7;
        let mut s = EufSolver::new();
        s.uselist_trail = false;
        let a = s.intern(TermId::new(1));
        let b = s.intern(TermId::new(2));
        s.intern_app(TermId::new(10), F, [a]);
        s.intern_app(TermId::new(11), F, [b]);
        let base: usize = s.use_list.iter().map(SmallVec::len).sum();
        for i in 0..10u32 {
            s.push();
            s.intern_app(TermId::new(100 + i), F, [a, b]);
            s.merge(a, b, TermId::new(0)).unwrap();
            s.pop();
        }
        let now: usize = s.use_list.iter().map(SmallVec::len).sum();
        assert!(
            now > base,
            "without the trail the use-list must accumulate ({now} vs {base}) \
             — if this ever stops holding, the test above is no longer testing anything"
        );
    }

    #[test]
    fn test_euf_basic() {
        let mut solver = EufSolver::new();

        let a = solver.intern(TermId::new(1));
        let b = solver.intern(TermId::new(2));
        let c = solver.intern(TermId::new(3));

        assert!(!solver.are_equal(a, b));

        solver.merge(a, b, TermId::new(0)).unwrap_or(());
        assert!(solver.are_equal(a, b));

        solver.merge(b, c, TermId::new(0)).unwrap_or(());
        assert!(solver.are_equal(a, c));
    }

    #[test]
    fn test_euf_diseq_conflict() {
        let mut solver = EufSolver::new();

        let a = solver.intern(TermId::new(1));
        let b = solver.intern(TermId::new(2));

        // Assert a != b
        solver.assert_diseq(a, b, TermId::new(10));
        assert!(solver.check_conflicts().is_none());

        // Then assert a = b -> conflict
        solver.merge(a, b, TermId::new(11)).unwrap_or(());
        assert!(solver.check_conflicts().is_some());
    }

    #[test]
    fn test_are_disequal_immutable_is_sound_and_conservative() {
        // The CCFV `Congruence::disequal` building block: true ONLY when an
        // asserted diseq separates the classes; false (not a panic) otherwise.
        let mut solver = EufSolver::new();
        let a = solver.intern(TermId::new(1));
        let b = solver.intern(TermId::new(2));
        let c = solver.intern(TermId::new(3));

        // Nothing asserted yet: not provably disequal (merely unknown).
        assert!(!solver.are_disequal_immutable(a, b));
        assert!(!solver.are_disequal_immutable(a, a)); // reflexive: never disequal

        // Assert a != b → now provably disequal, symmetric.
        solver.assert_diseq(a, b, TermId::new(10));
        assert!(solver.are_disequal_immutable(a, b));
        assert!(solver.are_disequal_immutable(b, a));
        // c is unconstrained → still not provably disequal from a or b.
        assert!(!solver.are_disequal_immutable(a, c));
        assert!(!solver.are_disequal_immutable(b, c));

        // Congruence: merge c=a, then b≠c follows from b≠a (a,c same class).
        solver.merge(a, c, TermId::new(11)).unwrap_or(());
        assert!(solver.are_disequal_immutable(b, c));
        // Stale indices are total → false, no panic.
        assert!(!solver.are_disequal_immutable(9999, 8888));
    }

    #[test]
    fn test_euf_congruence() {
        let mut solver = EufSolver::new();

        let a = solver.intern(TermId::new(1));
        let b = solver.intern(TermId::new(2));

        // f(a) and f(b)
        let fa = solver.intern_app(TermId::new(3), 0, [a]);
        let fb = solver.intern_app(TermId::new(4), 0, [b]);

        assert!(!solver.are_equal(fa, fb));

        // Merge a and b -> f(a) = f(b) by congruence
        solver.merge(a, b, TermId::new(0)).unwrap_or(());
        assert!(solver.are_equal(fa, fb));
    }

    #[test]
    fn test_euf_explanation_simple() {
        let mut solver = EufSolver::new();

        let a = solver.intern(TermId::new(1));
        let b = solver.intern(TermId::new(2));
        let c = solver.intern(TermId::new(3));

        // Assert a = b (reason 10)
        solver.merge(a, b, TermId::new(10)).unwrap_or(());

        // Assert b = c (reason 11)
        solver.merge(b, c, TermId::new(11)).unwrap_or(());

        // Assert a != c (reason 12)
        solver.assert_diseq(a, c, TermId::new(12));

        // Now check - should have conflict with explanation containing reasons 10, 11, 12
        let conflict = solver.check_conflicts();
        assert!(conflict.is_some());

        if let Some(reasons) = conflict {
            // Should contain the disequality reason
            assert!(reasons.contains(&TermId::new(12)));
            // Should contain at least one of the equality reasons
            assert!(reasons.len() >= 2);
        }
    }

    /// Regression for #419 (found via #418's differential fuzzing): a long chain
    /// of nested congruence merges must not blow the native call stack when
    /// `explain_equality` unwinds it. Builds two parallel `DEPTH`-deep chains
    /// `f^DEPTH(a)` / `f^DEPTH(b)`, merges the base case `a = b` (the synchronous,
    /// already-iterative `propagate()` congruence-closure cascade merges every
    /// level of both chains — that part was never the crashing path), then forces
    /// a disequality conflict at the TOP of the chains so `check_conflicts` ->
    /// `explain_equality` must walk back down through every congruence level to
    /// produce reasons. Before this fix, `explain_equality` recursed one native
    /// stack frame per level here; a chain as short as a few thousand deep (well
    /// within what a fuzzer-sized SMT-LIB input can trigger via a handful of
    /// repeated selector/constructor applications, e.g. `oxiz-solver`'s ground-DT
    /// tests) crashed with a stack overflow.
    #[test]
    fn test_explain_equality_does_not_recurse_on_deep_congruence_chain() {
        let mut solver = EufSolver::new();
        const DEPTH: usize = 20_000;
        const FUNC: u32 = 0;

        let a0 = solver.intern(TermId::new(1));
        let b0 = solver.intern(TermId::new(2));

        let mut a = a0;
        let mut b = b0;
        let mut next_term_id: u32 = 3;
        for _ in 0..DEPTH {
            a = solver.intern_app(TermId::new(next_term_id), FUNC, [a]);
            next_term_id += 1;
            b = solver.intern_app(TermId::new(next_term_id), FUNC, [b]);
            next_term_id += 1;
        }

        // Merging the base case cascades congruence all the way up both chains.
        // (Reason id 0 is a reserved "no reason" sentinel elsewhere in this file
        // — `term_id.raw() != 0` in explain_equality's Assertion arm — so a
        // nonzero id is used here to make sure it can actually show up below.)
        solver.merge(a0, b0, TermId::new(1_000_000)).unwrap_or(());
        assert!(
            solver.are_equal(a, b),
            "congruence closure should merge the top of both {DEPTH}-deep chains"
        );

        // Force a conflict at the top: explaining it must unwind DEPTH levels of
        // MergeReason::Congruence — this is the call path that used to recurse.
        solver.assert_diseq(a, b, TermId::new(999_999));
        let conflict = solver.check_conflicts();
        assert!(
            conflict.is_some(),
            "a disequality on two now-equal deep-chain tops must conflict"
        );
        let reasons = conflict.unwrap();
        assert!(
            reasons.contains(&TermId::new(999_999)),
            "explanation must cite the disequality reason"
        );
        assert!(
            reasons.contains(&TermId::new(1_000_000)),
            "explanation must trace all the way back to the base-case merge reason"
        );
    }

    #[test]
    fn test_euf_explanation_congruence() {
        let mut solver = EufSolver::new();

        let a = solver.intern(TermId::new(1));
        let b = solver.intern(TermId::new(2));

        // f(a) and f(b)
        let fa = solver.intern_app(TermId::new(3), 0, [a]);
        let fb = solver.intern_app(TermId::new(4), 0, [b]);

        // Assert f(a) != f(b) (reason 20)
        solver.assert_diseq(fa, fb, TermId::new(20));

        // Assert a = b (reason 21) -> causes f(a) = f(b) by congruence
        solver.merge(a, b, TermId::new(21)).unwrap_or(());

        // Check - should have conflict
        let conflict = solver.check_conflicts();
        assert!(conflict.is_some());

        if let Some(reasons) = conflict {
            // Should contain the disequality reason
            assert!(reasons.contains(&TermId::new(20)));
            // Should contain the equality reason that caused congruence
            assert!(reasons.contains(&TermId::new(21)));
        }
    }

    #[test]
    fn test_euf_transitivity_explanation() {
        let mut solver = EufSolver::new();

        let a = solver.intern(TermId::new(1));
        let b = solver.intern(TermId::new(2));
        let c = solver.intern(TermId::new(3));
        let d = solver.intern(TermId::new(4));

        // Assert a = b (reason 100)
        solver.merge(a, b, TermId::new(100)).unwrap_or(());

        // Assert b = c (reason 101)
        solver.merge(b, c, TermId::new(101)).unwrap_or(());

        // Assert c = d (reason 102)
        solver.merge(c, d, TermId::new(102)).unwrap_or(());

        // Assert a != d (reason 103)
        solver.assert_diseq(a, d, TermId::new(103));

        // Check - should have conflict
        let conflict = solver.check_conflicts();
        assert!(conflict.is_some());

        if let Some(reasons) = conflict {
            // Should contain the disequality reason
            assert!(reasons.contains(&TermId::new(103)));
            // Should have multiple reasons from the equality chain
            assert!(reasons.len() >= 2);
        }
    }

    #[test]
    fn test_commutative_function() {
        let mut solver = EufSolver::new();

        // Register a commutative function (e.g., addition)
        solver.register_function(
            0,
            FunctionProperties {
                associative: false,
                commutative: true,
                has_identity: false,
            },
        );

        let a = solver.intern(TermId::new(1));
        let b = solver.intern(TermId::new(2));

        // f(a, b) and f(b, a) should be the same due to commutativity
        let fab = solver.intern_app(TermId::new(3), 0, [a, b]);
        let fba = solver.intern_app(TermId::new(4), 0, [b, a]);

        // They should be the same node due to commutativity
        assert_eq!(fab, fba);
    }

    #[test]
    fn test_associative_function() {
        let mut solver = EufSolver::new();

        // Register an associative function (e.g., addition)
        solver.register_function(
            0,
            FunctionProperties {
                associative: true,
                commutative: false,
                has_identity: false,
            },
        );

        let a = solver.intern(TermId::new(1));
        let b = solver.intern(TermId::new(2));
        let c = solver.intern(TermId::new(3));

        // f(a, b)
        let fab = solver.intern_app(TermId::new(10), 0, [a, b]);

        // f(f(a, b), c) should be flattened to f(a, b, c)
        let fab_c = solver.intern_app(TermId::new(11), 0, [fab, c]);

        // Verify that the node has 3 arguments (flattened)
        let node = &solver.nodes[fab_c as usize];
        assert_eq!(node.args.len(), 3);
    }

    #[test]
    fn test_associative_commutative_function() {
        let mut solver = EufSolver::new();

        // Register an associative and commutative function (e.g., addition)
        solver.register_function(
            0,
            FunctionProperties {
                associative: true,
                commutative: true,
                has_identity: false,
            },
        );

        let a = solver.intern(TermId::new(1));
        let b = solver.intern(TermId::new(2));
        let c = solver.intern(TermId::new(3));

        // f(a, b)
        let fab = solver.intern_app(TermId::new(10), 0, [a, b]);

        // f(c, f(a, b)) should be flattened and canonicalized
        let c_fab = solver.intern_app(TermId::new(11), 0, [c, fab]);

        // f(f(b, a), c) should be flattened and canonicalized to the same thing
        let fba = solver.intern_app(TermId::new(12), 0, [b, a]);
        let fba_c = solver.intern_app(TermId::new(13), 0, [fba, c]);

        // Due to commutativity and associativity, they should be the same
        assert_eq!(c_fab, fba_c);
    }

    #[test]
    fn test_fingerprint_basic() {
        // Same func and args should produce the same fingerprint
        let fp1 = ENodeFingerprint::compute(0, &[1, 2, 3]);
        let fp2 = ENodeFingerprint::compute(0, &[1, 2, 3]);
        assert_eq!(fp1, fp2);

        // Different args should (almost certainly) produce different fingerprints
        let fp3 = ENodeFingerprint::compute(0, &[1, 2, 4]);
        assert_ne!(fp1, fp3);

        // Different func should produce different fingerprint
        let fp4 = ENodeFingerprint::compute(1, &[1, 2, 3]);
        assert_ne!(fp1, fp4);
    }

    #[test]
    fn test_fingerprint_empty_args() {
        let fp1 = ENodeFingerprint::compute(5, &[]);
        let fp2 = ENodeFingerprint::compute(5, &[]);
        assert_eq!(fp1, fp2);

        let fp3 = ENodeFingerprint::compute(6, &[]);
        assert_ne!(fp1, fp3);
    }

    #[test]
    fn test_congruence_with_fingerprint_prefilter() {
        // Verify congruence closure still works correctly with fingerprint optimization
        let mut solver = EufSolver::new();

        let a = solver.intern(TermId::new(1));
        let b = solver.intern(TermId::new(2));
        let c = solver.intern(TermId::new(3));

        // g(a, c) and g(b, c)
        let gac = solver.intern_app(TermId::new(10), 1, [a, c]);
        let gbc = solver.intern_app(TermId::new(11), 1, [b, c]);

        assert!(!solver.are_equal(gac, gbc));

        // Merge a and b -> g(a,c) = g(b,c) by congruence
        solver.merge(a, b, TermId::new(50)).unwrap_or(());
        assert!(solver.are_equal(gac, gbc));
    }

    #[test]
    fn test_fingerprint_table_populated() {
        let mut solver = EufSolver::new();

        let a = solver.intern(TermId::new(1));
        let b = solver.intern(TermId::new(2));

        let _fa = solver.intern_app(TermId::new(3), 0, [a]);
        let _fb = solver.intern_app(TermId::new(4), 0, [b]);

        // There should be entries in the fingerprint table
        assert!(solver.fingerprint_table_len() > 0);
    }

    #[test]
    fn test_push_pop_rebuilds_fingerprint_table() {
        use crate::theory::Theory;

        let mut solver = EufSolver::new();

        let a = solver.intern(TermId::new(1));

        solver.push();

        let b = solver.intern(TermId::new(2));
        let _fa = solver.intern_app(TermId::new(3), 0, [a]);
        let _fb = solver.intern_app(TermId::new(4), 0, [b]);

        let fp_count_before = solver.fingerprint_table_len();
        assert!(fp_count_before > 0);

        solver.pop();

        // After pop, fingerprint table should be rebuilt (possibly smaller)
        let fp_count_after = solver.fingerprint_table_len();
        assert!(fp_count_after <= fp_count_before);
    }

    #[test]
    fn test_batch_sig_updates_correctness() {
        // Test that batch signature updates produce correct congruence results
        // with multiple function applications
        let mut solver = EufSolver::new();

        let a = solver.intern(TermId::new(1));
        let b = solver.intern(TermId::new(2));
        let c = solver.intern(TermId::new(3));
        let d = solver.intern(TermId::new(4));

        // f(a, c) and f(b, d)
        let fac = solver.intern_app(TermId::new(10), 0, [a, c]);
        let fbd = solver.intern_app(TermId::new(11), 0, [b, d]);

        assert!(!solver.are_equal(fac, fbd));

        // Merge a=b and c=d -> should trigger congruence f(a,c) = f(b,d)
        solver.merge(a, b, TermId::new(50)).unwrap_or(());
        solver.merge(c, d, TermId::new(51)).unwrap_or(());
        assert!(solver.are_equal(fac, fbd));
    }

    #[test]
    fn test_reset_clears_fingerprint_table() {
        use crate::theory::Theory;

        let mut solver = EufSolver::new();

        let a = solver.intern(TermId::new(1));
        let _fa = solver.intern_app(TermId::new(2), 0, [a]);

        assert!(solver.fingerprint_table_len() > 0);

        solver.reset();

        assert_eq!(solver.fingerprint_table_len(), 0);
    }

    /// Test that the fingerprint pre-filter does not cause false negatives:
    /// - Merging unrelated args must NOT produce spurious congruence merges.
    /// - Merging the right args MUST still produce congruence merges.
    #[test]
    fn test_fingerprint_prefilter_short_circuits() {
        let mut solver = EufSolver::new();
        let a = solver.intern(TermId::new(1));
        let b = solver.intern(TermId::new(2));
        let c = solver.intern(TermId::new(3));
        let f_sym = 100u32;
        let fa = solver.intern_app(TermId::new(10), f_sym, [a]);
        let fb = solver.intern_app(TermId::new(11), f_sym, [b]);

        // Merge a = c (NOT a = b)
        solver.merge(a, c, TermId::new(20)).unwrap_or(());
        // f(a) and f(b) should NOT be merged (root(a) != root(b))
        assert!(
            !solver.are_equal(fa, fb),
            "f(a) and f(b) should not be merged without a=b"
        );

        // Now merge a = b (so root(a) == root(b))
        solver.merge(a, b, TermId::new(21)).unwrap_or(());
        // After a=b, congruence should derive f(a)=f(b)
        assert!(
            solver.are_equal(fa, fb),
            "f(a) and f(b) should be merged after a=b"
        );
    }

    /// Test the critical invariant: multi-step merges that route through an
    /// intermediate shared root must still produce congruence.
    /// This catches the bug where Change A's `continue` skips the fingerprint-table
    /// update, leaving the invariant broken for subsequent merges.
    #[test]
    fn test_fingerprint_prefilter_invariant_multi_merge() {
        let mut solver = EufSolver::new();
        let a = solver.intern(TermId::new(1));
        let b = solver.intern(TermId::new(2));
        let c = solver.intern(TermId::new(3));
        let f_sym = 200u32;
        let fa = solver.intern_app(TermId::new(10), f_sym, [a]);
        let fb = solver.intern_app(TermId::new(11), f_sym, [b]);

        // merge(a, c): fa re-canonicalizes to f([c]); new fp may not be in table yet.
        // The pre-filter must still update fingerprint_table so the next step works.
        solver.merge(a, c, TermId::new(20)).unwrap_or(());
        assert!(
            !solver.are_equal(fa, fb),
            "f(a) and f(b) should not be merged yet"
        );

        // merge(b, c): fb re-canonicalizes to f([c]); fp IS now in table; congruence fires.
        solver.merge(b, c, TermId::new(21)).unwrap_or(());
        assert!(
            solver.are_equal(fa, fb),
            "f(a) and f(b) should be merged after a=c and b=c (both share root c)"
        );
    }

    /// Verify that using the reusable canon_buf (Change A) does not corrupt results
    /// when two different intern_app calls with different arities share the same solver.
    /// The buffer is cleared and refilled each iteration, so results must remain correct
    /// even across applications with different argument lists.
    #[test]
    fn test_canonicalize_buf_is_reused() {
        let mut solver = EufSolver::new();

        let a = solver.intern(TermId::new(1));
        let b = solver.intern(TermId::new(2));
        let c = solver.intern(TermId::new(3));

        let f_sym = 300u32;

        // Two applications with different argument sets
        let fab = solver.intern_app(TermId::new(10), f_sym, [a, b]);
        let fbc = solver.intern_app(TermId::new(11), f_sym, [b, c]);

        // Neither should be equal to each other initially
        assert!(!solver.are_equal(fab, fbc));

        // Merging a = b triggers propagate, which exercises the reused canon_buf
        // on use-list entries for both f(a,b) and f(b,c).
        solver.merge(a, b, TermId::new(50)).unwrap_or(());

        // f(a,b) has canonical args [root(a), root(b)] = [r, r]; if root(b) = root(c) differs
        // they must still be distinct.
        assert!(!solver.are_equal(fab, fbc));

        // Now merge b = c so the solver exercises propagate again with the same buf
        solver.merge(b, c, TermId::new(51)).unwrap_or(());

        // After a=b and b=c, a=b=c.  f(a,b) canonical = [root, root], f(b,c) = [root, root]
        // so congruence must unify them.
        assert!(
            solver.are_equal(fab, fbc),
            "f(a,b) and f(b,c) must be equal once a=b=c"
        );
    }

    /// Verify that the incremental sig_trail correctly restores sig_table and
    /// fingerprint_table to exactly the pre-push state, matching what a full
    /// rebuild would have produced.
    #[test]
    fn test_incremental_sig_trail_matches_rebuild() {
        use crate::theory::Theory;

        let mut solver = EufSolver::new();
        let a = solver.intern(TermId::new(1));
        let b = solver.intern(TermId::new(2));
        let f_sym = 100u32;
        let fa = solver.intern_app(TermId::new(10), f_sym, [a]);
        // Capture state BEFORE push
        let sig_before = solver.sig_table_len();
        let fp_before = solver.fingerprint_table_len();

        solver.push();
        let c = solver.intern(TermId::new(3));
        let fc = solver.intern_app(TermId::new(11), f_sym, [c]);
        solver.merge(a, c, TermId::new(20)).expect("merge a=c");
        // Now pop — should restore to pre-push state
        solver.pop();

        let sig_after = solver.sig_table_len();
        let fp_after = solver.fingerprint_table_len();
        assert_eq!(
            sig_before, sig_after,
            "sig_table size should match pre-push state after pop"
        );
        assert_eq!(
            fp_before, fp_after,
            "fingerprint_table size should match pre-push state after pop"
        );
        // The merge done during the push scope must be undone
        assert!(
            !solver.are_equal(fa, fc),
            "terms merged during push scope should not be equal after pop"
        );
        let _ = (b, fc);
    }

    /// Verify that a 3-level push/pop stack completely rewinds all sig/fp state.
    #[test]
    fn test_push_pop_stack_depth_3() {
        use crate::theory::Theory;

        let mut solver = EufSolver::new();
        let f = 100u32;
        let a = solver.intern(TermId::new(1));

        // Level 1
        solver.push();
        let b = solver.intern(TermId::new(2));
        let fab = solver.intern_app(TermId::new(10), f, [a, b]);

        // Level 2
        solver.push();
        let c = solver.intern(TermId::new(3));
        let fbc = solver.intern_app(TermId::new(11), f, [b, c]);
        solver.merge(a, b, TermId::new(20)).expect("merge a=b");

        // Level 3
        solver.push();
        let d = solver.intern(TermId::new(4));
        solver.merge(b, c, TermId::new(21)).expect("merge b=c");

        // Pop all three levels
        solver.pop(); // back to level 2 state
        solver.pop(); // back to level 1 state
        solver.pop(); // back to initial state

        // After all pops, no merges should remain
        assert!(
            !solver.are_equal(a, b),
            "a and b should not be equal after full pop"
        );
        let _ = (fab, fbc, c, d);
    }

    /// Regression for the ground-audit bug `b` (bounded-injectivity spurious
    /// UNSAT): a merge made inside a push scope must not leave a proof-forest
    /// edge behind after `pop`.  A leaked edge lets `explain_equality` route
    /// through a retracted merge and cite a reason for an equality that no
    /// longer holds — yielding an invalid conflict clause downstream.
    #[test]
    fn test_pop_removes_stale_proof_edges() {
        use crate::theory::Theory;

        let mut s = EufSolver::new();
        let a = s.intern(TermId::new(1));
        let b = s.intern(TermId::new(2));

        // Merge a=b inside a scope with reason 100, then pop it away.
        s.push();
        s.merge(a, b, TermId::new(100)).expect("merge a=b");
        assert!(s.are_equal(a, b));
        s.pop();
        assert!(!s.are_equal(a, b), "merge must be undone by pop");

        // Re-merge with a DIFFERENT reason 200.
        s.merge(a, b, TermId::new(200)).expect("re-merge a=b");
        assert!(s.are_equal(a, b));

        // The explanation must cite only the live reason (200), never the
        // retracted reason (100) whose proof edge should have been removed.
        let reasons = s.explain_equality(a, b);
        assert!(
            reasons.contains(&TermId::new(200)),
            "explanation must cite the live merge reason 200, got {reasons:?}"
        );
        assert!(
            !reasons.contains(&TermId::new(100)),
            "explanation must NOT cite the popped merge reason 100, got {reasons:?}"
        );
    }

    /// A merge that survives across a pop (it was made at a shallower level than
    /// the pop) must KEEP its proof edge.  Guards against the proof-trail undo
    /// over-removing edges from outer scopes.
    #[test]
    fn test_pop_keeps_outer_scope_proof_edges() {
        use crate::theory::Theory;

        let mut s = EufSolver::new();
        let a = s.intern(TermId::new(1));
        let b = s.intern(TermId::new(2));
        let c = s.intern(TermId::new(3));

        // Outer merge a=b at level 1 (reason 10).
        s.push();
        s.merge(a, b, TermId::new(10)).expect("merge a=b");

        // Inner merge b=c at level 2 (reason 20), then pop level 2 away.
        s.push();
        s.merge(b, c, TermId::new(20)).expect("merge b=c");
        s.pop();

        // a=b must survive; b=c must be gone.
        assert!(s.are_equal(a, b), "outer-scope merge must survive the pop");
        assert!(!s.are_equal(b, c), "inner-scope merge must be undone");
        let reasons = s.explain_equality(a, b);
        assert!(
            reasons.contains(&TermId::new(10)),
            "explanation must still cite the surviving reason 10, got {reasons:?}"
        );
    }

    #[test]
    fn test_function_application_entries_basic() {
        // f(a) and g(b) with func ids 7 and 8 respectively.
        let mut solver = EufSolver::new();
        let a = solver.intern(TermId::new(1));
        let b = solver.intern(TermId::new(2));
        let _fa = solver.intern_app(TermId::new(3), 7, [a]);
        let _gb = solver.intern_app(TermId::new(4), 8, [b]);

        // Only the application of func 7 is reported.
        let entries = solver.function_application_entries(7);
        assert_eq!(entries.len(), 1, "exactly one application of func 7");
        let e = &entries[0];
        assert_eq!(e.arg_reps.len(), 1);
        // The argument class of a contains a's TermId (1).
        assert!(e.arg_class_terms[0].contains(&TermId::new(1)));
        // The result class contains the application term itself (3).
        assert!(e.result_class_terms.contains(&TermId::new(3)));

        // A function with no applications yields no entries.
        assert!(solver.function_application_entries(9).is_empty());
    }

    #[test]
    fn test_function_application_entries_congruence_collapses_arg_reps() {
        // f(a), f(b); after a = b the two applications must share arg_reps and
        // result_rep so a model builder deduplicates them into one entry.
        let mut solver = EufSolver::new();
        let a = solver.intern(TermId::new(1));
        let b = solver.intern(TermId::new(2));
        let f = 42u32;
        let _fa = solver.intern_app(TermId::new(10), f, [a]);
        let _fb = solver.intern_app(TermId::new(11), f, [b]);

        // Before merge: two applications with DISTINCT argument reps.
        let before = solver.function_application_entries(f);
        assert_eq!(before.len(), 2);
        assert_ne!(
            before[0].arg_reps, before[1].arg_reps,
            "f(a) and f(b) have distinct arg reps before a=b"
        );

        // Merge a = b -> congruence unifies f(a) and f(b).
        solver.merge(a, b, TermId::new(20)).expect("merge a=b");

        let after = solver.function_application_entries(f);
        assert_eq!(after.len(), 2, "still two application nodes are reported");
        // ...but they now share the same canonical argument and result class,
        // which is exactly the dedup key a model builder relies on.
        assert_eq!(
            after[0].arg_reps, after[1].arg_reps,
            "after a=b the two applications must share canonical arg reps"
        );
        assert_eq!(
            after[0].result_rep, after[1].result_rep,
            "after a=b the two applications are in the same result class"
        );
        // The shared result class contains both application terms.
        assert!(after[0].result_class_terms.contains(&TermId::new(10)));
        assert!(after[0].result_class_terms.contains(&TermId::new(11)));
    }

    #[test]
    fn test_function_application_entries_multi_arg() {
        // h(a, c) and h(b, c); after a = b they collapse on arg reps.
        let mut solver = EufSolver::new();
        let a = solver.intern(TermId::new(1));
        let b = solver.intern(TermId::new(2));
        let c = solver.intern(TermId::new(3));
        let h = 5u32;
        let _hac = solver.intern_app(TermId::new(10), h, [a, c]);
        let _hbc = solver.intern_app(TermId::new(11), h, [b, c]);

        solver.merge(a, b, TermId::new(20)).expect("merge a=b");

        let entries = solver.function_application_entries(h);
        assert_eq!(entries.len(), 2);
        // Both arg positions canonicalize identically (a~b, and shared c).
        assert_eq!(entries[0].arg_reps.len(), 2);
        assert_eq!(entries[0].arg_reps, entries[1].arg_reps);
    }

    #[test]
    fn test_enode_size_regression() {
        // Guards against ENode growing larger than expected.
        // ENode fields: func (4B), fingerprint (8B), args (SmallVec=32B), term (4B)
        // With alignment padding the size should be ≤ 56 bytes.
        let size = std::mem::size_of::<ENode>();
        assert!(size <= 56, "ENode size should be ≤56 bytes, got {}", size);
    }

    #[test]
    fn test_leaf_constructor_uses_sentinel() {
        let t = TermId::from(42u32);
        let node = ENode::leaf(t);
        assert!(!node.is_app(), "leaf node should not be an app");
        assert_eq!(
            node.func,
            ENode::NO_FUNC,
            "leaf node func should be NO_FUNC sentinel"
        );
        assert!(node.args.is_empty(), "leaf node should have no args");
    }

    /// Behavior-identity pin for the batched sig_table update path in
    /// `propagate()`.  The expected values below were generated by running this
    /// exact scenario against the pre-optimization code (commit 40da216, before
    /// the E1/E2 clone-elimination restructure); the restructure must keep the
    /// insertion SET and ORDER into sig_table/fingerprint_table — and the
    /// pending-merge processing sequence — exactly unchanged.
    ///
    /// Scenario A (duplicate-signature batch, "last insert wins"):
    ///   h(a,b) and h(b,a) both re-canonicalize to h([r,r]) in ONE use-list scan
    ///   after merge(a,b).  Both take the fingerprint-miss branch (the batch is
    ///   not applied mid-scan), so no congruence fires in-burst, and the batch
    ///   apply overwrites sig_table[(h,[r,r])] — the LAST batched node wins.
    ///   A later intern_app with the same signature must return that winner.
    ///
    /// Scenario B (multi-congruence burst, LIFO processing):
    ///   f(a),g(a),f(b),g(b); merge(a,b) discovers BOTH congruences in one
    ///   use-list scan, queues them in scan order, and processes them LIFO
    ///   (pending is a stack).  The resulting union-find orientation pins the
    ///   processing order.
    #[test]
    fn test_propagate_burst_pins_sig_insertion_order_and_merge_sequence() {
        // ---- Scenario A ----
        let mut s = EufSolver::new();
        let a = s.intern(TermId::new(1)); // node 0
        let b = s.intern(TermId::new(2)); // node 1
        let h = 7u32; // NOT commutative
        let hab = s.intern_app(TermId::new(10), h, [a, b]); // node 2
        let hba = s.intern_app(TermId::new(11), h, [b, a]); // node 3
        assert_eq!((a, b, hab, hba), (0, 1, 2, 3));

        s.merge(a, b, TermId::new(20)).expect("merge a=b");

        // Union orientation: equal ranks -> b becomes child of a; rep is a (0).
        assert_eq!(s.uf.find_no_compress(b), a, "b's class rep must be a");

        // #431 — THIS ASSERTION USED TO REQUIRE THE OPPOSITE, and in doing so
        // it froze a false-SAT. `h` is not commutative, but with `a = b` both
        // applications canonicalize to `h([r,r])`, so they ARE congruent: z3
        // and cvc5 both answer `unsat` for
        // `(= a b) AND (not (= (h a b) (h b a)))`. The old pin was generated as
        // a behaviour-identity snapshot of pre-optimization code, and a
        // behaviour-identity pin is only as sound as the behaviour it was taken
        // from.
        assert!(
            s.are_equal(hab, hba),
            "#431: the in-burst h(a,b)/h(b,a) congruence must fire"
        );

        // Eager publication means the FIRST node scanned owns the slot: it
        // publishes, and the second HITS that entry and merges instead of
        // publishing over it.
        let key: (u32, SmallVec<[u32; 4]>) = (h, SmallVec::from_slice(&[0u32, 0u32]));
        assert_eq!(
            s.sig_table.get(&key).copied(),
            Some(hab),
            "the first publisher owns the sig_table slot"
        );

        // ...and the fingerprint bucket lists only that node, because the
        // second one merged instead of publishing.
        let fp = ENodeFingerprint::compute(h, &[0, 0]);
        assert_eq!(
            s.fingerprint_table.get(&fp).map(|v| v.as_slice()),
            Some(&[hab][..]),
            "only the publisher is in the fingerprint bucket"
        );

        // Publicly observable consequence: a new application with the same
        // canonical signature resolves to the published node, and the two are
        // in one class either way.
        let joined = s.intern_app(TermId::new(12), h, [a, b]);
        assert_eq!(joined, hab, "intern_app must return the published node");
        assert!(s.are_equal(joined, hba), "and it is congruent to h(b,a)");

        // ---- Scenario B ----
        let mut s = EufSolver::new();
        let a = s.intern(TermId::new(1)); // node 0
        let b = s.intern(TermId::new(2)); // node 1
        let f = 100u32;
        let g = 200u32;
        let fa = s.intern_app(TermId::new(10), f, [a]); // node 2
        let ga = s.intern_app(TermId::new(11), g, [a]); // node 3
        let fb = s.intern_app(TermId::new(12), f, [b]); // node 4
        let gb = s.intern_app(TermId::new(13), g, [b]); // node 5

        s.merge(a, b, TermId::new(30)).expect("merge a=b");

        assert!(s.are_equal(fa, fb), "congruence f(a)=f(b) must fire");
        assert!(s.are_equal(ga, gb), "congruence g(a)=g(b) must fire");

        // Scan order over use_list[b] is [fb, gb]; both hit sig_table and are
        // queued in that order; pending is popped LIFO so (gb,ga) is unioned
        // FIRST, then (fb,fa).  With equal ranks union makes the second
        // argument's root a child of the first (user wins), so the class reps
        // are the b-side application nodes.
        assert_eq!(s.uf.find_no_compress(a), a);
        assert_eq!(s.uf.find_no_compress(b), a);
        assert_eq!(
            s.uf.find_no_compress(fa),
            fb,
            "f-class rep pins union orientation of the congruence merge"
        );
        assert_eq!(
            s.uf.find_no_compress(ga),
            gb,
            "g-class rep pins union orientation of the congruence merge"
        );

        // Explanation-sequence pin: exact reason vector (order included) for a
        // conflict routed through the congruence edge.
        s.assert_diseq(fa, fb, TermId::new(40));
        let conflict = s.check_conflicts().expect("fa=fb conflicts with diseq");
        assert_eq!(
            conflict,
            vec![TermId::new(30), TermId::new(40)],
            "explanation reason sequence must be stable"
        );
    }
}
