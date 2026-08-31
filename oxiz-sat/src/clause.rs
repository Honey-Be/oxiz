//! Clause representation and database

use crate::literal::Lit;
#[allow(unused_imports)]
use crate::prelude::*;
use smallvec::SmallVec;

/// Unique identifier for a clause
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ClauseId(pub u32);

impl ClauseId {
    /// The null clause ID (indicates no clause)
    pub const NULL: Self = Self(u32::MAX);

    /// Create a new clause ID
    #[must_use]
    pub const fn new(id: u32) -> Self {
        Self(id)
    }

    /// Check if this is a null ID
    #[must_use]
    pub const fn is_null(self) -> bool {
        self.0 == u32::MAX
    }

    /// Get the raw index
    #[must_use]
    pub const fn index(self) -> usize {
        self.0 as usize
    }
}

/// Clause tier for tiered database management
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum ClauseTier {
    /// Tier 3: Local clauses (recently learned, deleted aggressively)
    Local = 3,
    /// Tier 2: Mid-tier clauses (useful but not essential, deleted conservatively)
    Mid = 2,
    /// Tier 1: Core/GLUE clauses (very high quality, rarely deleted)
    Core = 1,
}

/// A clause is a disjunction of literals
///
/// Cache-line aligned for better memory performance
#[derive(Debug, Clone)]
#[repr(align(64))]
pub struct Clause {
    /// Activity for clause deletion heuristic
    pub activity: f64,
    /// Whether this is a learned clause
    pub learned: bool,
    /// LBD (Literal Block Distance) for quality metric
    pub lbd: u32,
    /// Keep hot metadata at the front of the struct so propagation and clause
    /// management usually touch a single cache line before reading literals.
    pub deleted: bool,
    /// The literals in this clause
    pub lits: SmallVec<[Lit; 4]>,
    /// Tier for tiered database management (only used for learned clauses)
    pub tier: ClauseTier,
    /// Number of times this clause was used in conflict analysis (for tier promotion)
    pub usage_count: u32,
}

impl Clause {
    /// Create a new clause
    #[must_use]
    pub fn new(lits: impl IntoIterator<Item = Lit>, learned: bool) -> Self {
        Self {
            activity: 0.0,
            learned,
            lbd: 0,
            deleted: false,
            lits: lits.into_iter().collect(),
            tier: ClauseTier::Local, // All learned clauses start in Local tier
            usage_count: 0,
        }
    }

    /// Create an original (non-learned) clause
    #[must_use]
    pub fn original(lits: impl IntoIterator<Item = Lit>) -> Self {
        Self::new(lits, false)
    }

    /// Create a learned clause
    #[must_use]
    pub fn learned(lits: impl IntoIterator<Item = Lit>) -> Self {
        Self::new(lits, true)
    }

    /// Get the number of literals
    #[must_use]
    pub fn len(&self) -> usize {
        self.lits.len()
    }

    /// Check if empty
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.lits.is_empty()
    }

    /// Check if this is a unit clause
    #[must_use]
    pub fn is_unit(&self) -> bool {
        self.lits.len() == 1
    }

    /// Check if this is a binary clause
    #[must_use]
    pub fn is_binary(&self) -> bool {
        self.lits.len() == 2
    }

    /// Get the first literal (for unit clauses)
    #[must_use]
    pub fn unit_lit(&self) -> Option<Lit> {
        if self.is_unit() {
            Some(self.lits[0])
        } else {
            None
        }
    }

    /// Swap literals at indices i and j
    pub fn swap(&mut self, i: usize, j: usize) {
        self.lits.swap(i, j);
    }

    /// Increment usage count and potentially promote tier
    pub fn record_usage(&mut self) {
        self.usage_count += 1;

        // Promote to Mid tier after 3 uses
        if self.usage_count >= 3 && self.tier == ClauseTier::Local {
            self.tier = ClauseTier::Mid;
        }
        // Promote to Core tier after 10 uses or if LBD ≤ 2
        else if (self.usage_count >= 10 || self.lbd <= 2) && self.tier == ClauseTier::Mid {
            self.tier = ClauseTier::Core;
        }
    }

    /// Promote clause to Core tier (for GLUE clauses)
    pub fn promote_to_core(&mut self) {
        self.tier = ClauseTier::Core;
    }

    /// Normalize clause: remove duplicates, sort literals, check for tautology
    /// Returns true if clause is a tautology (contains both l and ~l)
    pub fn normalize(&mut self) -> bool {
        if self.lits.is_empty() {
            return false;
        }

        // Sort literals for better cache locality and faster operations
        self.lits.sort_unstable_by_key(|lit| lit.code());

        // Remove duplicates and check for tautology in a single pass
        let mut write_idx = 0;
        let mut prev_lit = self.lits[0];

        for read_idx in 1..self.lits.len() {
            let curr_lit = self.lits[read_idx];

            // Check for tautology (complementary literals)
            if curr_lit == prev_lit.negate() {
                return true;
            }

            // Skip duplicates
            if curr_lit != prev_lit {
                write_idx += 1;
                self.lits[write_idx] = curr_lit;
                prev_lit = curr_lit;
            }
        }

        // Truncate to remove duplicates
        self.lits.truncate(write_idx + 1);
        false
    }

    /// Check if this clause subsumes another clause
    /// A clause C subsumes D if C ⊆ D (all literals of C are in D)
    #[must_use]
    pub fn subsumes(&self, other: &Clause) -> bool {
        if self.lits.len() > other.lits.len() {
            return false;
        }

        // Both clauses should be sorted for efficient checking
        let mut i = 0;
        let mut j = 0;

        while i < self.lits.len() && j < other.lits.len() {
            if self.lits[i] == other.lits[j] {
                i += 1;
                j += 1;
            } else if self.lits[i].code() < other.lits[j].code() {
                // Literal from self not in other
                return false;
            } else {
                j += 1;
            }
        }

        i == self.lits.len()
    }

    /// Check if this clause is a self-subsuming resolvent of another clause
    /// Returns the literal to remove from other if self-subsumption is possible
    #[must_use]
    pub fn self_subsuming_resolvent(&self, other: &Clause) -> Option<Lit> {
        if self.lits.len() >= other.lits.len() {
            return None;
        }

        let mut diff_lit = None;
        let mut matches = 0;

        for &other_lit in &other.lits {
            if self.lits.contains(&other_lit) {
                matches += 1;
            } else if self.lits.contains(&other_lit.negate()) {
                if diff_lit.is_some() {
                    return None; // More than one difference
                }
                diff_lit = Some(other_lit);
            }
        }

        // Self-subsuming resolution requires exactly one complementary literal
        // and all other literals of self must be in other
        if matches == self.lits.len() - 1 && diff_lit.is_some() {
            diff_lit
        } else {
            None
        }
    }
}

/// Sink for every **id-keyed side index** that must be detached from a clause
/// before that clause's [`ClauseId`] is freed.
///
/// # Why this trait exists (the invariant it enforces)
///
/// [`ClauseDatabase::remove`] does **not** destroy a clause: it marks the slot
/// `deleted` and pushes the id onto a free list. The very next
/// [`ClauseDatabase::add`] pops that id and overwrites the slot **in place,
/// clearing `deleted`**. So an id is not a stable name for a clause — it is a
/// recycled handle.
///
/// Every structure that stores a `ClauseId` (the two-watched-literal watch
/// lists, the binary-implication graph, occurrence lists, …) therefore holds a
/// *dangling* reference the moment a clause is removed, and that reference
/// silently re-points at a completely unrelated clause as soon as the id is
/// recycled. A `deleted`-flag check at the consumption site cannot catch this:
/// the recycled slot is live again. In `oxiz-sat` this has produced spurious
/// `Sat` **and** spurious `Unsat` verdicts — i.e. it is a soundness bug class,
/// not a performance bug — and it was fixed as a one-off at four separate call
/// sites before this trait existed (`reduce_clause_database`,
/// `forget_learned_since`, the assertion-scope `pop` handler, and
/// `check_subsumption` / issue #428).
///
/// Making the sink a **required argument of `remove`** is what stops the fifth
/// recurrence: there is no way to free an id without naming the indexes that
/// have to be scrubbed, so the compiler asks the question at every call site.
///
/// # The guarantee is ONE-SIDED — read this before relying on it
///
/// It covers the **single-clause** path, and only that. Two limits, both of
/// which have already misled a reader (me, 2026-08-31, while scoping an LRAT
/// producer that would have keyed a proof-id map off this invariant):
///
/// 1. **Bulk invalidation bypasses it entirely.** `Solver::reset` does
///    `self.clauses = ClauseDatabase::new()`, which invalidates every id at
///    once and re-issues from `0` on the next `add` — with no `remove` call, no
///    `scrub_clause` call, and no question asked by the compiler. It is correct
///    today only because `reset` then clears each id-keyed structure BY HAND,
///    which is precisely the discipline this trait exists to abolish. It is
///    reachable from SMT-LIB `(reset)` / `(reset-assertions)`.
///
/// 2. **The solver's sink is two structures; there are more.**
///    `Solver::clause_indexes` builds it from `watches` and `binary_graph`.
///    Also keyed on `ClauseId`, and NOT scrubbed here: the trail's
///    `Reason::Propagation(ClauseId)`, `learned_clause_ids`, and
///    `clause_ledger`. The trail is deliberately outside — a reason cannot be
///    detached, so removal sites guard with a locked-clause check instead — but
///    the other two are each pruned ad hoc at their own call sites, which is
///    how `check_subsumption` came to leave stale ids behind for as long as it
///    did.
///
/// So: "the compiler will not let an id be freed unsafely" is true of one path
/// and false as a general statement about this solver. Anything that keys a
/// long-lived map off `ClauseId` — a proof-id table, an external index — needs
/// to handle bulk invalidation on its own.
///
/// # Contract
///
/// `scrub_clause` is called with the clause's *current* literals, **before**
/// the slot is marked deleted or pushed onto the free list. An implementation
/// must remove every entry keyed on `id` from every index it owns. A clause's
/// watchers/implication edges are keyed on the **negations** of its own
/// literals (see [`crate::Solver`]'s installer sites), so the canonical
/// implementation loops `for &lit in lits { index.remove(lit.negate(), id) }`.
///
/// # The guarantee, as a compiler check
///
/// Freeing a clause id without naming an index sink does not compile:
///
/// ```compile_fail
/// use oxiz_sat::{ClauseDatabase, Lit, Var};
/// let mut db = ClauseDatabase::new();
/// let id = db.add_original([Lit::pos(Var::new(0)), Lit::neg(Var::new(1))]);
/// db.remove(id); // error: this method takes 2 arguments but 1 was supplied
/// ```
///
/// The caller has to say which indexes are being scrubbed — and, if the answer
/// is genuinely "none", say that out loud:
///
/// ```
/// use oxiz_sat::{ClauseDatabase, Lit, NoClauseIndex, Var};
/// let mut db = ClauseDatabase::new();
/// let id = db.add_original([Lit::pos(Var::new(0)), Lit::neg(Var::new(1))]);
/// db.remove(id, &mut NoClauseIndex); // this database has no watchers
/// assert_eq!(db.len(), 0);
/// ```
pub trait ClauseIndexScrub {
    /// Detach every entry keyed on `id` from this index.
    ///
    /// `lits` are the removed clause's literals, read from the database just
    /// before the slot is freed.
    fn scrub_clause(&mut self, id: ClauseId, lits: &[Lit]);
}

/// The empty [`ClauseIndexScrub`]: a claim that the [`ClauseDatabase`] being
/// mutated has **no id-keyed side index attached at all**.
///
/// Valid only for a free-standing database — a preprocessing/analysis pass that
/// owns its own `ClauseDatabase` and never installs watchers, or a unit test.
///
/// **Passing this from inside a solver that owns watch lists or a binary
/// implication graph reintroduces the exact soundness bug documented on
/// [`ClauseIndexScrub`]** (issue #428 and its three siblings). If you are
/// holding a `Solver`, you want its real index sink, not this. The
/// `debug_assert`s in the solver's propagation loop are the backstop that
/// catches the mistake, but they only fire in debug builds — do not rely on
/// them instead of passing the real sink.
#[derive(Debug, Clone, Copy, Default)]
pub struct NoClauseIndex;

impl ClauseIndexScrub for NoClauseIndex {
    #[inline]
    fn scrub_clause(&mut self, _id: ClauseId, _lits: &[Lit]) {}
}

impl<T: ClauseIndexScrub + ?Sized> ClauseIndexScrub for &mut T {
    #[inline]
    fn scrub_clause(&mut self, id: ClauseId, lits: &[Lit]) {
        (**self).scrub_clause(id, lits);
    }
}

/// Statistics for clause database
#[derive(Debug, Clone, Default)]
pub struct ClauseDatabaseStats {
    /// Number of clauses in each tier
    pub tier_counts: [usize; 3], // [Core, Mid, Local]
    /// Total LBD sum for computing average
    pub total_lbd: u64,
    /// Number of clauses with LBD counted
    pub lbd_count: usize,
    /// Distribution of clause sizes
    pub size_distribution: [usize; 10], // [binary, ternary, 4-lit, ..., 10+]
    /// Number of clause promotions
    pub promotions: usize,
    /// Number of clause demotions
    pub demotions: usize,
}

impl ClauseDatabaseStats {
    /// Get average LBD across all learned clauses
    #[must_use]
    pub fn avg_lbd(&self) -> f64 {
        if self.lbd_count == 0 {
            0.0
        } else {
            self.total_lbd as f64 / self.lbd_count as f64
        }
    }

    /// Display statistics
    pub fn display(&self) {
        println!("Clause Database Statistics:");
        println!("  Tier distribution:");
        println!("    Core:  {}", self.tier_counts[0]);
        println!("    Mid:   {}", self.tier_counts[1]);
        println!("    Local: {}", self.tier_counts[2]);
        println!("  Average LBD: {:.2}", self.avg_lbd());
        println!("  Size distribution:");
        for (i, &count) in self.size_distribution.iter().enumerate() {
            if count > 0 {
                let size = if i < 9 {
                    format!("{}", i + 2)
                } else {
                    "10+".to_string()
                };
                println!("    {} literals: {}", size, count);
            }
        }
        println!(
            "  Promotions: {}, Demotions: {}",
            self.promotions, self.demotions
        );
    }
}

/// Database of clauses with memory pool
#[derive(Debug)]
pub struct ClauseDatabase {
    /// All clauses
    clauses: Vec<Clause>,
    /// Number of original clauses
    num_original: usize,
    /// Number of learned clauses
    num_learned: usize,
    /// Free list for reusing deleted clause slots (memory pool)
    free_list: Vec<ClauseId>,
    /// Statistics
    stats: ClauseDatabaseStats,
}

impl Default for ClauseDatabase {
    fn default() -> Self {
        Self::new()
    }
}

impl ClauseDatabase {
    /// Create a new clause database
    #[must_use]
    pub fn new() -> Self {
        Self {
            clauses: Vec::new(),
            num_original: 0,
            num_learned: 0,
            free_list: Vec::new(),
            stats: ClauseDatabaseStats::default(),
        }
    }

    /// Get statistics about the clause database
    #[must_use]
    pub fn stats(&self) -> &ClauseDatabaseStats {
        &self.stats
    }

    /// Update statistics for a clause
    fn update_stats_add(&mut self, clause: &Clause) {
        if clause.learned {
            // Update tier count
            let tier_idx = match clause.tier {
                ClauseTier::Core => 0,
                ClauseTier::Mid => 1,
                ClauseTier::Local => 2,
            };
            self.stats.tier_counts[tier_idx] += 1;

            // Update LBD stats
            if clause.lbd > 0 {
                self.stats.total_lbd += clause.lbd as u64;
                self.stats.lbd_count += 1;
            }
        }

        // Update size distribution (only for clauses with 2+ literals)
        if clause.len() >= 2 {
            let size_idx = if clause.len() >= 12 {
                9 // 10+ bucket
            } else {
                clause.len() - 2
            };
            self.stats.size_distribution[size_idx] += 1;
        }
    }

    /// Update statistics when removing a clause
    fn update_stats_remove(&mut self, clause: &Clause) {
        if clause.learned {
            // Update tier count
            let tier_idx = match clause.tier {
                ClauseTier::Core => 0,
                ClauseTier::Mid => 1,
                ClauseTier::Local => 2,
            };
            if self.stats.tier_counts[tier_idx] > 0 {
                self.stats.tier_counts[tier_idx] -= 1;
            }

            // Update LBD stats
            if clause.lbd > 0 && self.stats.lbd_count > 0 {
                self.stats.total_lbd = self.stats.total_lbd.saturating_sub(clause.lbd as u64);
                self.stats.lbd_count -= 1;
            }
        }

        // Update size distribution (only for clauses with 2+ literals)
        if clause.len() >= 2 {
            let size_idx = if clause.len() >= 12 {
                9 // 10+ bucket
            } else {
                clause.len() - 2
            };
            if self.stats.size_distribution[size_idx] > 0 {
                self.stats.size_distribution[size_idx] -= 1;
            }
        }
    }

    /// Add a clause to the database
    ///
    /// Uses the memory pool (free list) to reuse deleted clause slots when available
    pub fn add(&mut self, clause: Clause) -> ClauseId {
        // Update statistics
        self.update_stats_add(&clause);

        // Try to reuse a slot from the free list
        if let Some(id) = self.free_list.pop() {
            // Reuse this slot
            if let Some(slot) = self.clauses.get_mut(id.index()) {
                *slot = clause.clone();
                if clause.learned {
                    self.num_learned += 1;
                } else {
                    self.num_original += 1;
                }
                return id;
            }
        }

        // No free slot available, allocate new
        let id = ClauseId::new(self.clauses.len() as u32);
        if clause.learned {
            self.num_learned += 1;
        } else {
            self.num_original += 1;
        }
        self.clauses.push(clause);
        id
    }

    /// Add an original clause
    pub fn add_original(&mut self, lits: impl IntoIterator<Item = Lit>) -> ClauseId {
        self.add(Clause::original(lits))
    }

    /// Add a learned clause
    pub fn add_learned(&mut self, lits: impl IntoIterator<Item = Lit>) -> ClauseId {
        self.add(Clause::learned(lits))
    }

    /// Get a clause by ID
    #[must_use]
    pub fn get(&self, id: ClauseId) -> Option<&Clause> {
        self.clauses.get(id.index())
    }

    /// Get a mutable reference to a clause
    pub fn get_mut(&mut self, id: ClauseId) -> Option<&mut Clause> {
        self.clauses.get_mut(id.index())
    }

    /// Mark a clause as deleted, first detaching it from every id-keyed side
    /// index.
    ///
    /// The deleted clause slot is added to the free list for reuse (memory
    /// pool), so `id` is handed straight back out by the next
    /// [`Self::add`] — see [`ClauseIndexScrub`] for why that makes the
    /// `indexes` argument mandatory rather than advisory. `scrub_clause` runs
    /// **before** the slot is marked deleted or pushed onto the free list, and
    /// runs even when the slot is already `deleted` (scrubbing is idempotent,
    /// and a double-remove must not leave half a clause's entries behind).
    ///
    /// Pass the solver's index sink here. [`NoClauseIndex`] is the explicit —
    /// and load-bearing — claim that this database has no watchers, no binary
    /// implication graph and no occurrence lists pointing at it.
    pub fn remove(&mut self, id: ClauseId, indexes: &mut impl ClauseIndexScrub) {
        let Some(clause) = self.clauses.get_mut(id.index()) else {
            return;
        };

        // Detach BEFORE the id can be recycled. Not conditional on `deleted`:
        // the pre-existing hand-written scrubs at the four historical call
        // sites were unconditional too, and an entry that outlives its clause
        // is exactly what this whole mechanism exists to prevent.
        indexes.scrub_clause(id, &clause.lits);

        if clause.deleted {
            return;
        }

        // Clone necessary info for stats update
        let clause_copy = clause.clone();

        clause.deleted = true;
        if clause.learned {
            self.num_learned -= 1;
        } else {
            self.num_original -= 1;
        }
        // Add to free list for reuse
        self.free_list.push(id);

        // Update statistics after marking as deleted
        self.update_stats_remove(&clause_copy);
    }

    /// Compact the database by removing deleted clauses from the free list
    ///
    /// This should be called periodically to prevent the free list from growing too large
    pub fn compact(&mut self) {
        // Limit free list size to avoid memory bloat
        const MAX_FREE_LIST_SIZE: usize = 1000;

        if self.free_list.len() > MAX_FREE_LIST_SIZE {
            // Keep only the most recent freed slots
            self.free_list
                .drain(0..self.free_list.len() - MAX_FREE_LIST_SIZE);
        }
    }

    /// Get the number of active clauses
    #[must_use]
    pub fn len(&self) -> usize {
        self.num_original + self.num_learned
    }

    /// Check if empty
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Get the number of original clauses
    #[must_use]
    pub fn num_original(&self) -> usize {
        self.num_original
    }

    /// Get the number of learned clauses
    #[must_use]
    pub fn num_learned(&self) -> usize {
        self.num_learned
    }

    /// Iterate over all non-deleted clause IDs
    pub fn iter_ids(&self) -> impl Iterator<Item = ClauseId> + '_ {
        self.clauses
            .iter()
            .enumerate()
            .filter(|(_, c)| !c.deleted)
            .map(|(i, _)| ClauseId::new(i as u32))
    }

    /// Bump activity of a clause
    pub fn bump_activity(&mut self, id: ClauseId, increment: f64) {
        if let Some(clause) = self.get_mut(id) {
            clause.activity += increment;
        }
    }

    /// Decay all clause activities
    pub fn decay_activity(&mut self, factor: f64) {
        for clause in &mut self.clauses {
            if !clause.deleted {
                clause.activity *= factor;
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::literal::Var;

    #[test]
    fn test_clause_creation() {
        let lits = vec![
            Lit::pos(Var::new(0)),
            Lit::neg(Var::new(1)),
            Lit::pos(Var::new(2)),
        ];
        let clause = Clause::original(lits.clone());

        assert_eq!(clause.len(), 3);
        assert!(!clause.is_unit());
        assert!(!clause.is_binary());
        assert!(!clause.learned);
    }

    #[test]
    fn test_clause_database() {
        let mut db = ClauseDatabase::new();

        let c1 = db.add_original([Lit::pos(Var::new(0)), Lit::neg(Var::new(1))]);
        let _c2 = db.add_learned([Lit::pos(Var::new(2))]);

        assert_eq!(db.len(), 2);
        assert_eq!(db.num_original(), 1);
        assert_eq!(db.num_learned(), 1);

        db.remove(c1, &mut NoClauseIndex);
        assert_eq!(db.len(), 1);
        assert_eq!(db.num_original(), 0);
    }

    #[test]
    fn remove_scrubs_side_indexes_before_the_id_is_recycled() {
        // The bug class in one test: `remove` frees an id, the next `add`
        // hands the SAME id back, and anything still keyed on that id now
        // aliases an unrelated clause. `remove` must hand the literals to the
        // index sink first.
        struct RecordingIndex {
            scrubbed: Vec<(ClauseId, Vec<Lit>)>,
        }
        impl ClauseIndexScrub for RecordingIndex {
            fn scrub_clause(&mut self, id: ClauseId, lits: &[Lit]) {
                self.scrubbed.push((id, lits.to_vec()));
            }
        }

        let mut db = ClauseDatabase::new();
        let a = Lit::pos(Var::new(0));
        let b = Lit::neg(Var::new(1));
        let c = Lit::pos(Var::new(2));

        let old = db.add_original([a, b]);
        let mut index = RecordingIndex {
            scrubbed: Vec::new(),
        };
        db.remove(old, &mut index);

        // The sink saw the OLD clause's literals, keyed on the OLD id ...
        assert_eq!(index.scrubbed.len(), 1);
        assert_eq!(index.scrubbed[0].0, old);
        assert_eq!(index.scrubbed[0].1, vec![a, b]);

        // ... and it saw them *before* recycling, which is the point: the id
        // really is handed straight back out, so a sink that ran afterwards
        // would have scrubbed the wrong clause's entries.
        let new = db.add_original([c]);
        assert_eq!(new, old, "free list recycles the id on the very next add");
        assert!(!db.get(new).expect("recycled slot is live").deleted);
    }

    #[test]
    fn test_clause_normalize() {
        let mut clause = Clause::original([
            Lit::pos(Var::new(2)),
            Lit::pos(Var::new(0)),
            Lit::pos(Var::new(2)), // duplicate
            Lit::pos(Var::new(1)),
        ]);

        let is_tautology = clause.normalize();
        assert!(!is_tautology);
        assert_eq!(clause.len(), 3); // duplicate removed
        // Check sorted order
        assert_eq!(clause.lits[0], Lit::pos(Var::new(0)));
        assert_eq!(clause.lits[1], Lit::pos(Var::new(1)));
        assert_eq!(clause.lits[2], Lit::pos(Var::new(2)));
    }

    #[test]
    fn test_clause_normalize_tautology() {
        let mut clause = Clause::original([
            Lit::pos(Var::new(0)),
            Lit::neg(Var::new(0)), // tautology
            Lit::pos(Var::new(1)),
        ]);

        let is_tautology = clause.normalize();
        assert!(is_tautology);
    }

    #[test]
    fn test_clause_subsumes() {
        let mut c1 = Clause::original([Lit::pos(Var::new(0)), Lit::pos(Var::new(1))]);
        let mut c2 = Clause::original([
            Lit::pos(Var::new(0)),
            Lit::pos(Var::new(1)),
            Lit::pos(Var::new(2)),
        ]);

        c1.normalize();
        c2.normalize();

        assert!(c1.subsumes(&c2)); // c1 ⊆ c2
        assert!(!c2.subsumes(&c1)); // c2 ⊈ c1
    }

    #[test]
    fn test_clause_self_subsuming_resolvent() {
        // C1: (a v b), C2: (~a v b v c)
        // C1 can strengthen C2 to (b v c) by removing ~a
        let mut c1 = Clause::original([Lit::pos(Var::new(0)), Lit::pos(Var::new(1))]);
        let mut c2 = Clause::original([
            Lit::neg(Var::new(0)),
            Lit::pos(Var::new(1)),
            Lit::pos(Var::new(2)),
        ]);

        c1.normalize();
        c2.normalize();

        if let Some(lit_to_remove) = c1.self_subsuming_resolvent(&c2) {
            assert_eq!(lit_to_remove, Lit::neg(Var::new(0)));
        } else {
            panic!("Expected self-subsuming resolvent");
        }
    }
}
