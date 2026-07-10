//! Term Manager - Arena allocation for terms

use super::term::{Term, TermId, TermKind};
use super::traversal::get_children;
#[cfg(feature = "arena")]
use crate::ast::arena::TermArena;
use crate::interner::{Rodeo, Spur};
#[allow(unused_imports)]
use crate::prelude::*;
use crate::sort::{Sort, SortId, SortManager};
use portable_atomic::{AtomicU32, Ordering};
use smallvec::SmallVec;

mod builder;
mod query;

/// Statistics for garbage collection
#[derive(Debug, Clone, Default)]
pub struct GCStatistics {
    /// Number of GC runs
    pub gc_count: usize,
    /// Total terms collected across all GC runs
    pub total_collected: usize,
    /// Total cache entries removed across all GC runs
    pub total_cache_removed: usize,
    /// Last GC collection count
    pub last_collected: usize,
    /// Last GC cache removal count
    pub last_cache_removed: usize,
}

/// Manager for term allocation and interning
#[derive(Debug)]
pub struct TermManager {
    /// Append-only term arena behind an `Arc` so a cheap read-only head
    /// (`read_view`) can be shared with the §4 theory-hooks path (Phase 2) as a
    /// `'static + Send + Sync` object. Appends go through `Arc::make_mut`, which is
    /// O(1) while no read-head is outstanding (the read-head only lives for the span
    /// of a single solve, during which the arena is not extended). Terms are
    /// hash-consed/immutable once created, so the prefix a read-head captures never
    /// changes.
    pub(super) terms: Arc<Vec<Term>>,
    /// Next term ID
    pub(super) next_id: AtomicU32,
    /// String interner for symbols
    pub(super) interner: Rodeo,
    /// Sort manager
    pub sorts: SortManager,
    /// Cache for structural sharing
    pub(super) cache: FxHashMap<TermKind, TermId>,
    /// Variable hash-consing keyed by (name, SORT) — `TermKind::Var(spur)`
    /// alone cannot key the main cache: two same-named variables of DIFFERENT
    /// sorts are distinct terms, but a kind-only key made the first intern win
    /// (`mk_var("x!", Poly)` then `mk_var("x!", Int)` returned the Poly term).
    /// In the verus AIR stream a quantifier's bound `x!: Poly` collides with a
    /// later query-local `x!: Int` constant this way: the goal's ground term
    /// literally BECAME the axiom's bound variable, so its instances were
    /// dropped as "retains a bound var" → order-sensitive spurious
    /// unknown/sat (adsmt #397 part C).
    pub(super) var_cache: FxHashMap<(Spur, SortId), TermId>,
    /// True constant
    pub true_id: TermId,
    /// False constant
    pub false_id: TermId,
    /// GC statistics
    pub(super) gc_stats: GCStatistics,
    /// Optional bump arena for fast allocation (feature-gated)
    #[cfg(feature = "arena")]
    pub(super) arena: TermArena,
}

impl Default for TermManager {
    fn default() -> Self {
        Self::new()
    }
}

impl TermManager {
    /// Create a new term manager
    #[must_use]
    pub fn new() -> Self {
        let sorts = SortManager::new();
        let bool_sort = sorts.bool_sort;

        let mut manager = Self {
            terms: Arc::new(Vec::with_capacity(1024)),
            next_id: AtomicU32::new(0),
            interner: Rodeo::default(),
            sorts,
            cache: FxHashMap::default(),
            var_cache: FxHashMap::default(),
            true_id: TermId(0),
            false_id: TermId(1),
            gc_stats: GCStatistics::default(),
            #[cfg(feature = "arena")]
            arena: TermArena::with_capacity(64 * 1024),
        };

        // Pre-allocate true and false
        manager.true_id = manager.intern(TermKind::True, bool_sort);
        manager.false_id = manager.intern(TermKind::False, bool_sort);

        manager
    }

    /// Intern a term kind with an explicit sort, returning its unique ID.
    ///
    /// This is the public-facing version of the internal `intern` method,
    /// intended for use by crates that need to construct term kinds directly
    /// (e.g. when rebuilding quantifiers with substituted bodies).
    pub fn intern_term(&mut self, kind: TermKind, sort: SortId) -> TermId {
        self.intern(kind, sort)
    }

    /// Intern a term, returning its unique ID
    pub(crate) fn intern(&mut self, kind: TermKind, sort: SortId) -> TermId {
        // A variable's identity is (name, sort) — the kind alone conflates
        // same-named variables of different sorts (see `var_cache`).
        if let TermKind::Var(spur) = kind {
            if let Some(&id) = self.var_cache.get(&(spur, sort)) {
                return id;
            }
        } else if let Some(&id) = self.cache.get(&kind) {
            return id;
        }

        let id = TermId(self.next_id.fetch_add(1, Ordering::Relaxed));
        let term = Term {
            id,
            kind: kind.clone(),
            sort,
        };
        // When the arena feature is enabled, also allocate in the bump arena
        #[cfg(feature = "arena")]
        {
            let _ = self.arena.alloc_term(id, kind.clone(), sort);
        }

        Arc::make_mut(&mut self.terms).push(term);
        if let TermKind::Var(spur) = kind {
            self.var_cache.insert((spur, sort), id);
        } else {
            self.cache.insert(kind, id);
        }
        id
    }

    /// Get arena statistics (only available with `arena` feature)
    #[cfg(feature = "arena")]
    #[must_use]
    pub fn arena_stats(&self) -> crate::ast::arena::ArenaStats {
        self.arena.stats()
    }

    /// Reset the arena allocator, freeing all arena memory
    #[cfg(feature = "arena")]
    pub fn reset_arena(&mut self) {
        self.arena.reset();
    }

    /// Get a term by its ID
    #[must_use]
    pub fn get(&self, id: TermId) -> Option<&Term> {
        self.terms.get(id.0 as usize)
    }

    /// #423 item 2 — read-only lookup for the (already-interned) manifest
    /// NULLARY `DtConstructor` term for `constructor`, if one has ever been
    /// built. `&self`-only (not `&mut`) so callers holding only a shared
    /// `&TermManager` (e.g. `check_dt.rs`'s constraint collector) can use it
    /// without threading `&mut TermManager` through their whole call chain.
    ///
    /// A nullary constructor's own hash-cons KEY is exactly `TermKind::
    /// DtConstructor { constructor, args: <empty> }` — the cache has no
    /// separate sort component (`self.cache: FxHashMap<TermKind, TermId>`,
    /// see its field doc), so this lookup is valid with no sort argument.
    /// Returns `None` on a miss — defensively safe: a nullary constructor
    /// term not yet interned (in practice, always already present via
    /// `encode.rs`'s eager cover-axiom construction whenever the datatype is
    /// used at all) simply means the caller's derivation is skipped, never
    /// fabricated from nothing.
    #[must_use]
    pub fn find_nullary_dt_constructor_term(&self, constructor: Spur) -> Option<TermId> {
        self.cache
            .get(&TermKind::DtConstructor { constructor, args: SmallVec::new() })
            .copied()
    }

    /// Intern a string, returning its key
    pub fn intern_str(&mut self, s: &str) -> Spur {
        self.interner.get_or_intern(s)
    }

    /// Resolve an interned string
    #[must_use]
    pub fn resolve_str(&self, key: Spur) -> &str {
        self.interner.resolve(&key)
    }

    /// Get the number of terms allocated
    #[must_use]
    pub fn len(&self) -> usize {
        self.terms.len()
    }

    /// Check if the manager is empty (only contains true/false)
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.terms.len() <= 2
    }

    // ========================== Garbage Collection ==========================

    /// Perform garbage collection on unreachable terms
    ///
    /// This method performs a mark-and-sweep garbage collection:
    /// 1. Marks all terms reachable from the given root set
    /// 2. Removes unmarked entries from the cache
    ///
    /// Note: This doesn't actually free memory from the arena (terms vector),
    /// but it does clean up the cache to prevent unbounded growth.
    ///
    /// # Arguments
    /// * `roots` - Set of root term IDs to keep (and their descendants)
    ///
    /// # Returns
    /// Number of cache entries removed
    pub fn gc(&mut self, roots: &FxHashSet<TermId>) -> usize {
        // Mark phase: find all reachable terms
        let mut reachable = FxHashSet::default();
        let mut worklist: Vec<TermId> = roots.iter().copied().collect();

        // Always keep true and false
        worklist.push(self.true_id);
        worklist.push(self.false_id);

        while let Some(id) = worklist.pop() {
            if !reachable.insert(id) {
                continue; // Already visited
            }

            // Mark children as reachable
            if let Some(term) = self.get(id) {
                for child in get_children(&term.kind) {
                    if !reachable.contains(&child) {
                        worklist.push(child);
                    }
                }
            }
        }

        // Sweep phase: remove unreachable entries from cache
        let original_cache_size = self.cache.len() + self.var_cache.len();
        self.cache.retain(|_, &mut id| reachable.contains(&id));
        self.var_cache.retain(|_, &mut id| reachable.contains(&id));
        let removed = original_cache_size - self.cache.len() - self.var_cache.len();

        // Update statistics
        self.gc_stats.gc_count += 1;
        self.gc_stats.total_cache_removed += removed;
        self.gc_stats.last_cache_removed = removed;
        self.gc_stats.last_collected = removed;
        self.gc_stats.total_collected += removed;

        removed
    }

    /// Perform aggressive garbage collection
    ///
    /// Similar to `gc()` but more thorough. It also shrinks the cache capacity
    /// to fit the retained entries, potentially freeing more memory.
    ///
    /// # Arguments
    /// * `roots` - Set of root term IDs to keep (and their descendants)
    ///
    /// # Returns
    /// Number of cache entries removed
    pub fn gc_aggressive(&mut self, roots: &FxHashSet<TermId>) -> usize {
        let removed = self.gc(roots);
        self.cache.shrink_to_fit();
        self.var_cache.shrink_to_fit();
        removed
    }

    /// Get garbage collection statistics
    #[must_use]
    pub fn gc_statistics(&self) -> &GCStatistics {
        &self.gc_stats
    }

    /// Get the current cache size (number of hash-consed terms)
    #[must_use]
    pub fn cache_size(&self) -> usize {
        self.cache.len() + self.var_cache.len()
    }

    /// Get the total number of terms allocated
    #[must_use]
    pub fn term_count(&self) -> usize {
        self.terms.len()
    }

    /// Clear all GC statistics
    pub fn reset_gc_stats(&mut self) {
        self.gc_stats = GCStatistics::default();
    }
}

/// Builder for constructing substitutions incrementally with optimizations
///
/// This provides better performance than repeatedly calling substitute when
/// building up complex substitutions, especially when:
/// - Composing multiple substitutions
/// - Applying the same substitution to many terms
/// - Building substitutions incrementally
#[derive(Debug, Clone)]
pub struct SubstitutionBuilder {
    /// The substitution mapping
    mapping: FxHashMap<TermId, TermId>,
    /// Shared cache for substitution results
    cache: FxHashMap<TermId, TermId>,
}

impl SubstitutionBuilder {
    /// Create a new empty substitution builder
    #[must_use]
    pub fn new() -> Self {
        Self {
            mapping: FxHashMap::default(),
            cache: FxHashMap::default(),
        }
    }

    /// Create a builder with initial capacity
    #[must_use]
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            mapping: FxHashMap::with_capacity_and_hasher(capacity, Default::default()),
            cache: FxHashMap::with_capacity_and_hasher(capacity * 2, Default::default()),
        }
    }

    /// Add a substitution mapping
    pub fn add(&mut self, from: TermId, to: TermId) -> &mut Self {
        // Invalidate cache when adding new mapping
        self.cache.clear();
        self.mapping.insert(from, to);
        self
    }

    /// Add multiple substitution mappings
    pub fn add_many(&mut self, mappings: impl IntoIterator<Item = (TermId, TermId)>) -> &mut Self {
        self.cache.clear();
        self.mapping.extend(mappings);
        self
    }

    /// Compose this substitution with another
    ///
    /// The resulting substitution applies `other` first, then `self`.
    /// This is optimized to share structure where possible.
    pub fn compose(&mut self, other: &SubstitutionBuilder, manager: &mut TermManager) -> &mut Self {
        // For each mapping in self, substitute using other
        let mut new_mapping = FxHashMap::default();
        let mut temp_cache = FxHashMap::default();

        for (&from, &to) in &self.mapping {
            let new_to = if other.mapping.contains_key(&to) {
                manager.substitute_cached(to, &other.mapping, &mut temp_cache)
            } else {
                to
            };
            new_mapping.insert(from, new_to);
        }

        // Add mappings from other that aren't in self
        for (&from, &to) in &other.mapping {
            new_mapping.entry(from).or_insert(to);
        }

        self.mapping = new_mapping;
        self.cache.clear();
        self
    }

    /// Apply the substitution to a term
    ///
    /// This uses a persistent cache across multiple applications,
    /// making it more efficient when substituting many terms.
    pub fn apply(&mut self, id: TermId, manager: &mut TermManager) -> TermId {
        manager.substitute_cached(id, &self.mapping, &mut self.cache)
    }

    /// Apply the substitution to multiple terms efficiently
    ///
    /// Uses the shared cache to avoid redundant work.
    pub fn apply_many(&mut self, ids: &[TermId], manager: &mut TermManager) -> Vec<TermId> {
        ids.iter().map(|&id| self.apply(id, manager)).collect()
    }

    /// Get the underlying mapping
    #[must_use]
    pub fn mapping(&self) -> &FxHashMap<TermId, TermId> {
        &self.mapping
    }

    /// Check if the substitution is empty
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.mapping.is_empty()
    }

    /// Get the number of mappings
    #[must_use]
    pub fn len(&self) -> usize {
        self.mapping.len()
    }

    /// Clear the substitution
    pub fn clear(&mut self) {
        self.mapping.clear();
        self.cache.clear();
    }

    /// Reset the cache (useful for freeing memory)
    pub fn reset_cache(&mut self) {
        self.cache.clear();
    }

    /// Get cache statistics (for debugging/optimization)
    #[must_use]
    pub fn cache_stats(&self) -> (usize, usize) {
        (self.cache.len(), self.cache.capacity())
    }
}

impl Default for SubstitutionBuilder {
    fn default() -> Self {
        Self::new()
    }
}

/// Read-only access to a term + sort arena. Implemented by BOTH the read-write
/// `TermManager` and the cheap read-only `TermReadView`, so theory code that only
/// reads terms/sorts can be written generically over `&impl TermRead` and reused
/// on both the legacy (borrowing) and the §4 hooks (owning) paths.
pub trait TermRead {
    /// Get a term by id.
    fn get(&self, id: TermId) -> Option<&Term>;
    /// Get a sort by id.
    fn sort_of(&self, id: SortId) -> Option<&Sort>;
    /// The interned `true` term id.
    fn true_id(&self) -> TermId;
    /// The interned `false` term id.
    fn false_id(&self) -> TermId;
}

impl TermRead for TermManager {
    fn get(&self, id: TermId) -> Option<&Term> {
        self.terms.get(id.0 as usize)
    }
    fn sort_of(&self, id: SortId) -> Option<&Sort> {
        self.sorts.get(id)
    }
    fn true_id(&self) -> TermId {
        self.true_id
    }
    fn false_id(&self) -> TermId {
        self.false_id
    }
}

/// A cheap, shareable READ-ONLY head over the term + sort arenas — the data the
/// theory `process_constraint`-style work reads during a solve. Cloning it is two
/// `Arc` pointer-bumps (no DAG copy); it is `'static + Send + Sync`, so it can be
/// owned by a `Box<dyn TheoryHooks>` installed on the SAT trail (§4 Phase 2). The
/// arenas are append-only/hash-consed, so the prefix this view captures is stable
/// for the view's lifetime.
#[derive(Clone)]
pub struct TermReadView {
    terms: Arc<Vec<Term>>,
    sorts: Arc<Vec<Sort>>,
    true_id: TermId,
    false_id: TermId,
}

impl TermRead for TermReadView {
    fn get(&self, id: TermId) -> Option<&Term> {
        self.terms.get(id.0 as usize)
    }
    fn sort_of(&self, id: SortId) -> Option<&Sort> {
        self.sorts.get(id.0 as usize)
    }
    fn true_id(&self) -> TermId {
        self.true_id
    }
    fn false_id(&self) -> TermId {
        self.false_id
    }
}

impl TermManager {
    /// Take a cheap read-only head (`Arc` pointer-bumps) over the current term/sort
    /// arenas. Valid for as long as the returned view lives; new terms appended
    /// afterwards extend the arena beyond it (and, since terms are immutable once
    /// created, never change what the view sees).
    #[must_use]
    pub fn read_view(&self) -> TermReadView {
        TermReadView {
            terms: Arc::clone(&self.terms),
            sorts: self.sorts.sorts_arc(),
            true_id: self.true_id,
            false_id: self.false_id,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_constants() {
        let manager = TermManager::new();
        assert_ne!(manager.mk_true(), manager.mk_false());
        assert_eq!(manager.mk_bool(true), manager.mk_true());
        assert_eq!(manager.mk_bool(false), manager.mk_false());
    }

    #[test]
    fn test_not_simplification() {
        let mut manager = TermManager::new();
        let t = manager.mk_true();
        let f = manager.mk_false();

        assert_eq!(manager.mk_not(t), f);
        assert_eq!(manager.mk_not(f), t);

        let x = manager.mk_var("x", manager.sorts.bool_sort);
        let not_x = manager.mk_not(x);
        let not_not_x = manager.mk_not(not_x);
        assert_eq!(not_not_x, x);
    }

    #[test]
    fn test_and_simplification() {
        let mut manager = TermManager::new();
        let t = manager.mk_true();
        let f = manager.mk_false();
        let x = manager.mk_var("x", manager.sorts.bool_sort);

        assert_eq!(manager.mk_and([t, x]), x);
        assert_eq!(manager.mk_and([f, x]), f);
        assert_eq!(manager.mk_and([t, t]), t);
        assert_eq!(manager.mk_and(core::iter::empty()), t);
    }

    #[test]
    fn test_or_simplification() {
        let mut manager = TermManager::new();
        let t = manager.mk_true();
        let f = manager.mk_false();
        let x = manager.mk_var("x", manager.sorts.bool_sort);

        assert_eq!(manager.mk_or([f, x]), x);
        assert_eq!(manager.mk_or([t, x]), t);
        assert_eq!(manager.mk_or([f, f]), f);
        assert_eq!(manager.mk_or(core::iter::empty()), f);
    }

    #[test]
    fn test_eq_canonicalization() {
        let mut manager = TermManager::new();
        let x = manager.mk_var("x", manager.sorts.int_sort);
        let y = manager.mk_var("y", manager.sorts.int_sort);

        let eq1 = manager.mk_eq(x, y);
        let eq2 = manager.mk_eq(y, x);
        assert_eq!(eq1, eq2);
    }

    #[test]
    fn test_ite_simplification() {
        let mut manager = TermManager::new();
        let t = manager.mk_true();
        let f = manager.mk_false();
        let x = manager.mk_var("x", manager.sorts.bool_sort);
        let y = manager.mk_var("y", manager.sorts.bool_sort);

        assert_eq!(manager.mk_ite(t, x, y), x);
        assert_eq!(manager.mk_ite(f, x, y), y);
        assert_eq!(manager.mk_ite(x, t, f), x);
    }

    #[test]
    fn test_interning() {
        let mut manager = TermManager::new();
        let x1 = manager.mk_var("x", manager.sorts.int_sort);
        let x2 = manager.mk_var("x", manager.sorts.int_sort);
        assert_eq!(x1, x2);

        let y = manager.mk_var("y", manager.sorts.int_sort);
        assert_ne!(x1, y);
    }

    #[test]
    fn test_term_size() {
        let mut manager = TermManager::new();
        let x = manager.mk_var("x", manager.sorts.int_sort);
        let y = manager.mk_var("y", manager.sorts.int_sort);
        let z = manager.mk_var("z", manager.sorts.int_sort);

        assert_eq!(manager.term_size(x), 1);

        let add_xy = manager.mk_add([x, y]);
        assert_eq!(manager.term_size(add_xy), 3);

        let add_xyz = manager.mk_add([x, y, z]);
        assert_eq!(manager.term_size(add_xyz), 4);

        let nested = manager.mk_add([add_xy, z]);
        // add_xy has size 3, z has size 1, outer add has size 1
        // But x and y appear only once each due to hash-consing
        assert_eq!(manager.term_size(nested), 5);
    }

    #[test]
    fn test_term_depth() {
        let mut manager = TermManager::new();
        let x = manager.mk_var("x", manager.sorts.int_sort);
        let y = manager.mk_var("y", manager.sorts.int_sort);

        assert_eq!(manager.term_depth(x), 0);

        let add_xy = manager.mk_add([x, y]);
        assert_eq!(manager.term_depth(add_xy), 1);

        let nested = manager.mk_add([add_xy, x]);
        assert_eq!(manager.term_depth(nested), 2);
    }

    #[test]
    fn test_substitute() {
        let mut manager = TermManager::new();
        let x = manager.mk_var("x", manager.sorts.int_sort);
        let y = manager.mk_var("y", manager.sorts.int_sort);
        let c = manager.mk_int(42);

        let expr = manager.mk_add([x, y]);

        let mut subst = FxHashMap::default();
        subst.insert(x, c);

        let result = manager.substitute(expr, &subst);

        let expected = manager.mk_add([c, y]);
        assert_eq!(result, expected);
    }

    #[test]
    fn test_free_vars() {
        let mut manager = TermManager::new();
        let x = manager.mk_var("x", manager.sorts.int_sort);
        let y = manager.mk_var("y", manager.sorts.int_sort);
        let c = manager.mk_int(42);

        let expr = manager.mk_add([x, y, c]);
        let vars = manager.free_vars(expr);
        assert_eq!(vars.len(), 2);
        assert!(vars.contains(&x));
        assert!(vars.contains(&y));

        let const_expr = manager.mk_int(100);
        let vars = manager.free_vars(const_expr);
        assert!(vars.is_empty());
    }

    // ==================== Quantifier Pattern Tests ====================

    #[test]
    fn test_forall_without_patterns() {
        let mut manager = TermManager::new();
        let int_sort = manager.sorts.int_sort;
        let bool_sort = manager.sorts.bool_sort;

        let x = manager.mk_var("x", int_sort);
        let zero = manager.mk_int(0);
        let gt_zero = manager.mk_gt(x, zero);

        let forall = manager.mk_forall([("x", int_sort)], gt_zero);
        let term = manager.get(forall).expect("forall term should exist");

        assert_eq!(term.sort, bool_sort);
        match &term.kind {
            TermKind::Forall {
                vars,
                body,
                patterns,
            } => {
                assert_eq!(vars.len(), 1);
                assert_eq!(*body, gt_zero);
                assert!(patterns.is_empty(), "should have no patterns");
            }
            _ => panic!("expected Forall term"),
        }
    }

    #[test]
    fn test_forall_with_patterns() {
        let mut manager = TermManager::new();
        let int_sort = manager.sorts.int_sort;
        let bool_sort = manager.sorts.bool_sort;

        let x = manager.mk_var("x", int_sort);
        let f_x = manager.mk_apply("f", [x], int_sort);
        let zero = manager.mk_int(0);
        let gt_zero = manager.mk_gt(f_x, zero);

        let forall = manager.mk_forall_with_patterns([("x", int_sort)], gt_zero, [[f_x]]);
        let term = manager.get(forall).expect("forall term should exist");

        assert_eq!(term.sort, bool_sort);
        match &term.kind {
            TermKind::Forall {
                vars,
                body,
                patterns,
            } => {
                assert_eq!(vars.len(), 1);
                assert_eq!(*body, gt_zero);
                assert_eq!(patterns.len(), 1, "should have 1 pattern");
                assert_eq!(patterns[0].len(), 1, "pattern should have 1 term");
                assert_eq!(patterns[0][0], f_x, "pattern term should be f(x)");
            }
            _ => panic!("expected Forall term"),
        }
    }

    #[test]
    fn test_forall_with_multiple_patterns() {
        let mut manager = TermManager::new();
        let int_sort = manager.sorts.int_sort;

        let x = manager.mk_var("x", int_sort);
        let f_x = manager.mk_apply("f", [x], int_sort);
        let g_x = manager.mk_apply("g", [x], int_sort);
        let zero = manager.mk_int(0);
        let body = manager.mk_gt(f_x, zero);

        // Two patterns: (f x) and (g x)
        let forall = manager.mk_forall_with_patterns([("x", int_sort)], body, [[f_x], [g_x]]);

        match &manager.get(forall).expect("forall term should exist").kind {
            TermKind::Forall { patterns, .. } => {
                assert_eq!(patterns.len(), 2, "should have 2 patterns");
            }
            _ => panic!("expected Forall term"),
        }
    }

    #[test]
    fn test_forall_with_multi_term_pattern() {
        let mut manager = TermManager::new();
        let int_sort = manager.sorts.int_sort;

        let x = manager.mk_var("x", int_sort);
        let y = manager.mk_var("y", int_sort);
        let f_x = manager.mk_apply("f", [x], int_sort);
        let g_y = manager.mk_apply("g", [y], int_sort);
        let body = manager.mk_gt(f_x, g_y);

        // One pattern with two terms: (f x) (g y)
        let forall =
            manager.mk_forall_with_patterns([("x", int_sort), ("y", int_sort)], body, [[f_x, g_y]]);

        match &manager.get(forall).expect("forall term should exist").kind {
            TermKind::Forall { patterns, .. } => {
                assert_eq!(patterns.len(), 1, "should have 1 pattern");
                assert_eq!(patterns[0].len(), 2, "pattern should have 2 terms");
            }
            _ => panic!("expected Forall term"),
        }
    }

    #[test]
    fn test_exists_with_patterns() {
        let mut manager = TermManager::new();
        let int_sort = manager.sorts.int_sort;

        let x = manager.mk_var("x", int_sort);
        let f_x = manager.mk_apply("f", [x], int_sort);
        let zero = manager.mk_int(0);
        let body = manager.mk_gt(f_x, zero);

        let exists = manager.mk_exists_with_patterns([("x", int_sort)], body, [[f_x]]);

        match &manager.get(exists).expect("exists term should exist").kind {
            TermKind::Exists { patterns, .. } => {
                assert_eq!(patterns.len(), 1);
            }
            _ => panic!("expected Exists term"),
        }
    }
}
