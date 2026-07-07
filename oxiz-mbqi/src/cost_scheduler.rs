//! The cost-scheduled instantiation priority queue (design
//! `FUEL_AWARE_COST_SCHEDULER.md` §5) — the substrate half (P0).
//!
//! A **monotone Age-Weight-Ratio (AWR) two-queue** over one append-only arena:
//!  * the **weight** side is a flat Dial bucket queue keyed on a small bounded
//!    integer `cost` (`0..=CAP`; `cost > CAP` saturates into the `CAP` overflow
//!    bucket — **DEFER, never DROP**), drained cheapest-tier-first and, within a
//!    tier, in a caller-supplied **content-derived `sort_key`** order (so the
//!    release order is a function of E-graph content, not insertion order — R7);
//!  * the **age** side is a FIFO over insertion order, pulsed once every
//!    `age_ratio` of `age_ratio + weight_ratio` steps, so a deep candidate the
//!    weight side defers is guaranteed to eventually fire (fairness) rather than
//!    be permanently suppressed — the anti-zero-sum lever. `age_ratio = 0` is the
//!    degenerate single-min-tier mode (a config flip, not a second impl).
//!
//! **Monotone**: candidates accumulate within a solve and are never rolled back
//! (the clean-MBQI engine is monotone by design — [[oxiz_mbqi_rewrite]]); a fired
//! entry stays in the arena marked `fired` and is skipped thereafter. Dedup is on
//! the **exact** `(q, σ)` key (no lossy hash). Merit-promotion re-buckets a live
//! candidate cheaper via a fresh entry + a `superseded` flag on the old one
//! (lazy-delete, no decrease-key).
//!
//! This module is host-agnostic: it never touches the term language. The consumer
//! (the engine's scheduled round fixpoint, `round_cost_scheduled`) computes each
//! candidate's `cost` (from `weight + generation + fuel_gradient`) and `sort_key`
//! (from the host's `content_key`) and hands them in at `insert`, then `drain`s
//! cheapest-first (single-tier) or through the AWR age-weight pulse
//! (`age_ratio > 0`). Live behind the `cost_schedule` flag (default off); the
//! P3a wall-clock guard bounds the fixpoint so a diverging quantifier cannot hang.

use crate::term::Sig;
use rustc_hash::FxHashSet;

/// The cost-bucket ceiling. A candidate whose computed cost exceeds `CAP`
/// saturates into the `CAP` overflow bucket — it is **deferred** (still queued,
/// fires only once everything cheaper is drained), never dropped. Sized a little
/// above Z3's `lazy_threshold` (20) with fuel headroom; a few KB of buckets,
/// cache-resident.
pub const CAP: u16 = 48;

struct Cand<S: Sig> {
    q: u32,
    sigma: Vec<S::Term>,
    cost: u16,
    /// Content-derived total-order tie-break within a cost tier (R7). Supplied by
    /// the consumer; compared lexicographically. Empty ⇒ ties fall back to arena
    /// order (only for hosts with no content key).
    sort_key: Box<[u64]>,
    fired: bool,
    superseded: bool,
}

/// The monotone AWR cost-scheduler priority queue.
pub struct CostScheduler<S: Sig> {
    arena: Vec<Cand<S>>,
    /// `buckets[c]` = arena indices of candidates whose cost is `c` (len `CAP+1`).
    buckets: Vec<Vec<u32>>,
    /// Insertion-order FIFO for the age side; `age_cursor` walks it forward,
    /// skipping fired/superseded entries. O(1) amortized — the efficient fairness
    /// structure.
    ///
    /// **R7 caveat (design §5.2).** This is *discovery* order, which an assertion
    /// shuffle can permute, so with `age_ratio > 0` the release schedule is not
    /// provably shuffle-invariant (the weight side, sorted by the content-derived
    /// `sort_key`, is). The design's content-derived age key (`born = generation`)
    /// would need an efficient ordered structure to avoid an O(n²) per-pop scan
    /// over a whole-solve age list; kept as the O(1) FIFO here. The `age_ratio = 0`
    /// default has no age pulse ⇒ fully weight-sorted ⇒ R7-clean; the sweep MUST
    /// run the §11.3 assertion-shuffle differential before adopting `age_ratio > 0`.
    age: Vec<u32>,
    age_cursor: usize,
    /// Exact `(q, σ)` dedup — no lossy hash (design fix #3).
    seen: FxHashSet<(u32, Vec<S::Term>)>,
    age_ratio: u32,
    weight_ratio: u32,
    tick: u32,
}

impl<S: Sig> CostScheduler<S> {
    /// A fresh scheduler with the given age:weight pulse ratio. `age_ratio = 0`
    /// ⇒ pure cheapest-first (single-tier mode). The weight ratio is floored at 1
    /// so the weight side always retains a share.
    pub fn new(age_ratio: u32, weight_ratio: u32) -> Self {
        CostScheduler {
            arena: Vec::new(),
            buckets: (0..=CAP).map(|_| Vec::new()).collect(),
            age: Vec::new(),
            age_cursor: 0,
            seen: FxHashSet::default(),
            age_ratio,
            weight_ratio: weight_ratio.max(1),
            tick: 0,
        }
    }

    /// Insert a candidate `(q, σ)` scored `cost`, with content tie-break
    /// `sort_key`. Dedups on the exact `(q, σ)` key. `cost` saturates into the
    /// `CAP` overflow bucket (DEFER, never DROP). Returns `false` (and inserts
    /// nothing) if `(q, σ)` was already queued.
    pub fn insert(&mut self, q: u32, sigma: Vec<S::Term>, cost: u16, sort_key: Box<[u64]>) -> bool {
        if !self.seen.insert((q, sigma.clone())) {
            return false;
        }
        let c = cost.min(CAP);
        let ix = self.arena.len() as u32;
        self.arena.push(Cand { q, sigma, cost: c, sort_key, fired: false, superseded: false });
        self.buckets[c as usize].push(ix);
        self.age.push(ix);
        true
    }

    /// Merit-promotion (design fix #4): re-bucket a live `(q, σ)` candidate at the
    /// cheaper `new_cost` so it fires sooner. Lazy-delete — the old entry is flagged
    /// `superseded` (skipped on drain) and a fresh entry is queued at `new_cost`
    /// WITHOUT re-checking dedup (the `(q, σ)` is already in `seen`). Returns
    /// `false` if no live entry matches. The promoted entry is reachable via the
    /// weight side only (it was made cheap on purpose).
    pub fn promote(&mut self, q: u32, sigma: Vec<S::Term>, new_cost: u16) -> bool {
        let Some(pos) = self
            .arena
            .iter()
            .position(|c| !c.fired && !c.superseded && c.q == q && c.sigma == sigma)
        else {
            return false;
        };
        let nc = new_cost.min(CAP);
        let sort_key = self.arena[pos].sort_key.clone();
        self.arena[pos].superseded = true;
        let ix = self.arena.len() as u32;
        self.arena.push(Cand { q, sigma, cost: nc, sort_key, fired: false, superseded: false });
        self.buckets[nc as usize].push(ix);
        true
    }

    /// `true` iff every queued candidate has fired (or been superseded).
    pub fn is_empty(&self) -> bool {
        self.arena.iter().all(|c| c.fired || c.superseded)
    }

    /// The number of live (un-fired, un-superseded) candidates.
    pub fn live_len(&self) -> usize {
        self.arena.iter().filter(|c| !c.fired && !c.superseded).count()
    }

    /// Pop the next candidate to fire, per the AWR pulse: an **age** step (FIFO
    /// over insertion order) on `tick mod (age_ratio+weight_ratio) < age_ratio`,
    /// otherwise the cheapest live **weight** tier in `sort_key` order. If the
    /// chosen side is empty, the other side is used; `None` only when every
    /// candidate has fired. Marks the winner `fired` and **moves** its `σ` out
    /// (no clone — design fix #6; the arena keeps the emptied, fired shell).
    pub fn next(&mut self) -> Option<(u32, Vec<S::Term>)> {
        let total = self.age_ratio + self.weight_ratio;
        let age_first = self.age_ratio > 0 && (self.tick % total) < self.age_ratio;
        self.tick = self.tick.wrapping_add(1);
        if age_first {
            if let Some(r) = self.pop_age() {
                return Some(r);
            }
            return self.pop_weight();
        }
        if let Some(r) = self.pop_weight() {
            return Some(r);
        }
        self.pop_age()
    }

    /// Drain up to `budget` candidates. In single-tier mode (`age_ratio == 0`,
    /// the default) this uses the efficient cheapest-tier path: scan up the
    /// buckets to the cheapest non-empty one, sort its live entries by `sort_key`
    /// ONCE, and take them in order — O(tier·log tier) per drained tier, not the
    /// O(n) linear-min scan `next` does per candidate. With an age pulse it falls
    /// back to the per-candidate AWR interleave.
    pub fn drain(&mut self, budget: usize) -> Vec<(u32, Vec<S::Term>)> {
        if self.age_ratio == 0 {
            return self.drain_weight(budget);
        }
        let mut out = Vec::new();
        while out.len() < budget {
            match self.next() {
                Some(c) => out.push(c),
                None => break,
            }
        }
        out
    }

    fn drain_weight(&mut self, budget: usize) -> Vec<(u32, Vec<S::Term>)> {
        let mut out = Vec::new();
        'outer: for c in 0..self.buckets.len() {
            let mut live: Vec<u32> = self.buckets[c]
                .iter()
                .copied()
                .filter(|&ix| {
                    let cd = &self.arena[ix as usize];
                    !cd.fired && !cd.superseded
                })
                .collect();
            if live.is_empty() {
                continue;
            }
            live.sort_unstable_by(|&a, &b| {
                self.arena[a as usize]
                    .sort_key
                    .cmp(&self.arena[b as usize].sort_key)
            });
            for ix in live {
                if out.len() >= budget {
                    break 'outer;
                }
                out.push(self.take(ix));
            }
        }
        out
    }

    fn take(&mut self, ix: u32) -> (u32, Vec<S::Term>) {
        let c = &mut self.arena[ix as usize];
        c.fired = true;
        (c.q, std::mem::take(&mut c.sigma))
    }

    fn pop_age(&mut self) -> Option<(u32, Vec<S::Term>)> {
        while self.age_cursor < self.age.len() {
            let ix = self.age[self.age_cursor];
            self.age_cursor += 1;
            let c = &self.arena[ix as usize];
            if !c.fired && !c.superseded {
                return Some(self.take(ix));
            }
        }
        None
    }

    fn pop_weight(&mut self) -> Option<(u32, Vec<S::Term>)> {
        // The cheapest non-empty bucket that holds a live entry; within it, the
        // lexicographically-least `sort_key`. (Linear per pop — correct and
        // cache-friendly at these sizes; a sort-once / heap refinement is a
        // perf follow-up, not a correctness concern.)
        let mut best: Option<u32> = None;
        for bucket in &self.buckets {
            for &ix in bucket {
                let cand = &self.arena[ix as usize];
                if cand.fired || cand.superseded {
                    continue;
                }
                match best {
                    None => best = Some(ix),
                    Some(b) if cand.sort_key < self.arena[b as usize].sort_key => best = Some(ix),
                    _ => {}
                }
            }
            if best.is_some() {
                break; // cheapest non-empty tier found
            }
        }
        best.map(|ix| self.take(ix))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::toy::ToySig;

    fn sched(a: u32, w: u32) -> CostScheduler<ToySig> {
        CostScheduler::new(a, w)
    }
    fn key(k: u64) -> Box<[u64]> {
        vec![k].into_boxed_slice()
    }

    #[test]
    fn exact_dedup() {
        let mut s = sched(0, 1);
        assert!(s.insert(1, vec![10], 5, key(0)));
        assert!(!s.insert(1, vec![10], 3, key(1)), "same (q,σ) is a duplicate");
        assert!(s.insert(1, vec![11], 5, key(0)), "different σ is not");
        assert!(s.insert(2, vec![10], 5, key(0)), "different q is not");
        assert_eq!(s.live_len(), 3);
    }

    #[test]
    fn weight_cheapest_first() {
        let mut s = sched(0, 1); // pure weight
        s.insert(1, vec![1], 8, key(0));
        s.insert(1, vec![2], 2, key(0));
        s.insert(1, vec![3], 5, key(0));
        let order: Vec<_> = s.drain(10).into_iter().map(|(_, sig)| sig[0]).collect();
        assert_eq!(order, vec![2, 3, 1], "drained in ascending cost");
        assert!(s.is_empty());
    }

    #[test]
    fn within_tier_sorted_by_content_key() {
        let mut s = sched(0, 1);
        // Same cost, inserted out of key order → must drain in sort_key order.
        s.insert(1, vec![30], 5, key(30));
        s.insert(1, vec![10], 5, key(10));
        s.insert(1, vec![20], 5, key(20));
        let order: Vec<_> = s.drain(10).into_iter().map(|(_, sig)| sig[0]).collect();
        assert_eq!(order, vec![10, 20, 30], "deterministic content-key order, not insertion order");
    }

    #[test]
    fn overflow_cost_is_deferred_not_dropped() {
        let mut s = sched(0, 1);
        s.insert(1, vec![1], 1000, key(0)); // > CAP → overflow bucket
        s.insert(1, vec![2], 3, key(0));
        let order: Vec<_> = s.drain(10).into_iter().map(|(_, sig)| sig[0]).collect();
        assert_eq!(order, vec![2, 1], "the over-CAP candidate fires LAST, never dropped");
        assert!(s.is_empty());
    }

    #[test]
    fn awr_pulse_interleaves_age_and_weight() {
        // age:weight = 1:1. Insert a deep (expensive) candidate FIRST, then cheap
        // ones. Pure weight would starve the deep one to last; the age pulse must
        // surface it early (fairness).
        let mut s = sched(1, 1);
        s.insert(9, vec![99], 40, key(0)); // deep, inserted first → oldest in age FIFO
        s.insert(1, vec![1], 1, key(0));
        s.insert(2, vec![2], 2, key(0));
        // tick 0: age → the deep one (oldest); tick 1: weight → cheapest (cost 1);
        // tick 2: age → next oldest live = cost-1? already fired → cost-2; ...
        let first = s.next().unwrap();
        assert_eq!(first.1[0], 99, "age pulse surfaces the deep candidate first");
        let second = s.next().unwrap();
        assert_eq!(second.1[0], 1, "weight pulse then takes the cheapest");
        // remaining drains without loss
        let rest: Vec<_> = s.drain(10).into_iter().map(|(_, sig)| sig[0]).collect();
        assert_eq!(rest, vec![2]);
        assert!(s.is_empty());
    }

    #[test]
    fn ratio_zero_is_pure_cheapest_first() {
        let mut s = sched(0, 5);
        s.insert(9, vec![99], 40, key(0)); // deep, first
        s.insert(1, vec![1], 1, key(0));
        let order: Vec<_> = s.drain(10).into_iter().map(|(_, sig)| sig[0]).collect();
        assert_eq!(order, vec![1, 99], "no age pulse → strictly cheapest-first");
    }

    #[test]
    fn promote_fires_earlier_and_supersedes_the_old() {
        let mut s = sched(0, 1);
        s.insert(1, vec![1], 10, key(0));
        s.insert(2, vec![2], 5, key(0));
        // Promote the cost-10 candidate below the cost-5 one.
        assert!(s.promote(1, vec![1], 1));
        assert!(!s.promote(9, vec![9], 1), "no live match → false");
        let order: Vec<_> = s.drain(10).into_iter().map(|(_, sig)| sig[0]).collect();
        assert_eq!(order, vec![1, 2], "promoted candidate fires first; old entry superseded, not double-fired");
        assert!(s.is_empty());
    }
}
