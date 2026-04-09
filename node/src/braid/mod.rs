use crate::bead::Bead;
use crate::utils::BeadHash;
use bitcoin::{Target, Work};
use std::collections::{HashMap, HashSet};
use std::mem;
use std::time::{Duration, Instant};

pub mod algorithms;

// A type alias which represents an index into Braid::beads
pub type BeadIdx = usize;
// A type representing parents, children, ancestors, or descendants
pub type Relatives = HashMap<BeadIdx, HashSet<BeadIdx>>;
// A type representing a set of beads indexed in Braid::beads
pub type BeadSet = HashSet<BeadIdx>;
// A type representing the work for each bead
pub type BeadWork = HashMap<BeadIdx, Work>;
// A type representing a cohort (a set of beads indexed in Braid::beads)
pub type Cohort = HashSet<BeadIdx>;
// A type alias which represents an index into Braid::cohorts
pub type CohortIdx = usize;

#[derive(Debug, Clone, PartialEq)]
pub enum AddBeadStatus {
    /// Bead already exists in the DAG (duplicate)
    DuplicateBead,
    /// Alias for DuplicateBead (sprint-agents compatibility)
    DagAlreadyContainsBead,
    InvalidBead,
    BeadAdded,
    /// Parents not yet in DAG, bead added to orphanage
    ParentsMissing,
    /// Alias for ParentsMissing (sprint-agents compatibility)  
    ParentsNotYetReceived,
}

#[derive(Debug, Clone)]
pub enum GenesisCheckStatus {
    GenesisBeadsValid,
    MissingGenesisBead,
    GenesisBeadsCountMismatch,
}

#[derive(Debug, Clone)]
pub enum BeadMessage {
    NewBead { bead: Bead },
    InvalidateBead { beadhash: BeadHash },
}

#[derive(Clone, Debug, Copy, PartialEq, Eq, Hash)]
pub enum ExtendStrategy {
    /// Optimized heuristic approach (default)
    Heuristic,
    /// Original approach but maintaining cache (incremental cache + algorithms::cohorts)
    Cached,
    /// Original unoptimized approach (clear cache + algorithms::cohorts)
    NoCache,
}

impl Default for ExtendStrategy {
    fn default() -> Self {
        ExtendStrategy::Heuristic
    }
}

#[derive(Debug, Clone)]
pub struct Braid {
    pub beads: Vec<Bead>,
    pub bead_work: BeadWork,
    pub tips: BeadSet,
    pub cohorts: Vec<Cohort>,
    pub geneses: BeadSet,
    pub index: HashMap<BeadHash, BeadIdx>,
    pub parents: Relatives,
    pub children: Relatives,
    pub orphanage: HashMap<BeadHash, Bead>,
    // Performance optimization caches (public to crate only -- no one else should need them)
    pub(crate) ancestor_cache: Relatives,
    pub(crate) descendant_cache: Relatives,
    pub(crate) tail_cache: Vec<BeadSet>,
    pub(crate) cohort_map: HashMap<BeadIdx, CohortIdx>,
    // Orphan reverse index (parent hash -> orphan hash)
    pub(crate) missing_parents: HashMap<BeadHash, HashSet<BeadHash>>,
    pub extend_strategy: ExtendStrategy,
    occupancy_events: Vec<(Instant, u64, u64)>, // (time, occupancy, cumulative area micros)
}

impl Default for Braid {
    fn default() -> Self {
        let now = Instant::now();
        Braid {
            beads: Vec::new(),
            bead_work: HashMap::new(),
            tips: HashSet::new(),
            cohorts: Vec::new(),
            geneses: HashSet::new(),
            index: HashMap::new(),
            parents: HashMap::new(),
            children: HashMap::new(),
            orphanage: HashMap::new(),
            ancestor_cache: HashMap::new(),
            descendant_cache: HashMap::new(),
            tail_cache: Vec::new(),
            cohort_map: HashMap::new(),
            missing_parents: HashMap::new(),
            extend_strategy: ExtendStrategy::default(),
            occupancy_events: vec![(now, 0, 0)],
        }
    }
}

impl Braid {
    // ==================== Construction ====================

    ///Initializing the Braid object for keeping track of current state of Braid
    pub fn new(beads: impl IntoIterator<Item = Bead>) -> Self {
        Self::new_with_strategy(beads, ExtendStrategy::default())
    }

    pub fn new_with_strategy(
        beads: impl IntoIterator<Item = Bead>,
        strategy: ExtendStrategy,
    ) -> Self {
        let mut braid = Braid {
            extend_strategy: strategy,
            ..Default::default()
        };
        for bead in beads {
            let _ = braid.extend(&bead);
        }
        braid
    }

    // ==================== Compatibility Accessors (sprint-agents naming) ====================

    /// Compatibility accessor: returns reference to `index` (sprint-agents called it `bead_index_mapping`)
    pub fn bead_index_mapping(&self) -> &HashMap<BeadHash, BeadIdx> {
        &self.index
    }

    /// Compatibility accessor: returns reference to `geneses` (sprint-agents called it `genesis_beads`)
    pub fn genesis_beads(&self) -> &BeadSet {
        &self.geneses
    }

    // ==================== Public API ====================

    /// Creates a BeadSet from an iterator over bead hashes.
    /// Panics if any hash is not found in the braid index.
    pub fn indices<I>(&self, bead_hashes: I) -> BeadSet
    where
        I: IntoIterator<Item = BeadHash>,
    {
        bead_hashes.into_iter().map(|b| self.index[&b]).collect()
    }

    /// Gets parent BeadSet for a bead.
    /// Panics if any parent hash is not found in the braid index.
    pub fn parent_indices(&self, bead: &Bead) -> BeadSet {
        bead.committed_metadata
            .parents
            .iter()
            .map(|h| self.index[h])
            .collect()
    }

    /// Records the occupancy integral up to `now`, appending an event.
    fn occupancy_event(&mut self, now: Instant) {
        if let Some((last_t, _, last_area)) = self.occupancy_events.last().copied() {
            let delta = now.duration_since(last_t).as_micros();
            let occ = self.orphanage.len() as u64;
            // Saturate to avoid overflow; orphan stays ~1s, so micros is sufficient
            let area = last_area
                .saturating_add((delta.saturating_mul(occ as u128)).min(u64::MAX as u128) as u64);
            self.occupancy_events.push((now, occ, area));
        } else {
            let occ = self.orphanage.len() as u64;
            self.occupancy_events.push((now, occ, 0));
        }
    }

    /// Returns the average orphanage occupancy over the last `interval`, using the event history.
    /// Keeps all events needed for overlapping windows; prunes older ones beyond the maximum lookback observed.
    pub fn orphanage_occupancy(&mut self, interval: Duration) -> Option<f64> {
        let now = Instant::now();
        self.occupancy_event(now);

        let start = now
            .checked_sub(interval)
            .unwrap_or_else(|| Instant::now() - Duration::from_secs(0));

        // Find the event just before or at `start`
        let mut idx = None;
        for (i, (t, _, _)) in self.occupancy_events.iter().enumerate().rev() {
            if *t <= start {
                idx = Some(i);
                break;
            }
        }

        let (prev_t, prev_occ, prev_area) = if let Some(i) = idx {
            self.occupancy_events[i]
        } else {
            // No earlier event: use the first
            self.occupancy_events.first().copied().unwrap()
        };

        let area_at_start = {
            let delta = start.duration_since(prev_t).as_micros();
            let incr = (delta.saturating_mul(prev_occ as u128)).min(u64::MAX as u128) as u64;
            prev_area.saturating_add(incr)
        };

        let (_, _, area_now) = *self.occupancy_events.last().unwrap();
        let window_area = area_now.saturating_sub(area_at_start);
        let interval_us = interval.as_micros();
        if interval_us == 0 {
            return None;
        }
        Some(window_area as f64 / interval_us as f64)
    }

    /// Rebuild caches (ancestor, descendant, tail, cohort_map) for cohorts starting at `start_idx`.
    fn rebuild_suffix(&mut self, start_idx: CohortIdx) {
        assert!(
            start_idx <= self.cohorts.len(),
            "rebuild_suffix: start_idx {} out of bounds (len={})",
            start_idx,
            self.cohorts.len()
        );

        self.tail_cache.truncate(start_idx);
        self.cohort_map.retain(|_, idx| *idx < start_idx);
        for cohort in self.cohorts.iter().skip(start_idx) {
            for &bead in cohort {
                self.ancestor_cache.remove(&bead);
                self.descendant_cache.remove(&bead);
            }
        }

        for (cohort_idx, cohort) in self.cohorts.iter().enumerate().skip(start_idx) {
            for &bead in cohort {
                self.cohort_map.insert(bead, cohort_idx);
                self.descendant_cache
                    .entry(bead)
                    .or_insert_with(HashSet::new);
            }

            let sub_parents = algorithms::sub_braid(cohort, &self.parents);
            let sub_children = algorithms::reverse(&sub_parents);
            let mut local_ancestors = Relatives::new();
            for &bead in cohort {
                algorithms::all_ancestors(bead, &sub_parents, &mut local_ancestors);
            }

            for (&bead, ancestors) in local_ancestors.iter() {
                self.ancestor_cache.insert(bead, ancestors.clone());
                for &ancestor in ancestors {
                    self.descendant_cache
                        .entry(ancestor)
                        .or_insert_with(HashSet::new)
                        .insert(bead);
                }
            }

            self.tail_cache
                .push(algorithms::cohort_tail(cohort, &sub_parents, &sub_children));
        }
    }

    fn adopt_orphans(&mut self, parent_hash: &BeadHash) {
        if let Some(children) = self.missing_parents.remove(parent_hash) {
            let now = Instant::now();
            self.occupancy_event(now);
            let mut ready = Vec::new();
            for child_hash in children {
                if let Some(orphan_bead) = self.orphanage.get(&child_hash) {
                    let all_parents_present = orphan_bead
                        .committed_metadata
                        .parents
                        .iter()
                        .all(|p| self.index.contains_key(p));
                    if all_parents_present {
                        let ready_bead = self.orphanage.remove(&child_hash).unwrap();
                        for p in &ready_bead.committed_metadata.parents {
                            if let Some(bucket) = self.missing_parents.get_mut(p) {
                                bucket.remove(&child_hash);
                                if bucket.is_empty() {
                                    self.missing_parents.remove(p);
                                }
                            }
                        }
                        ready.push(ready_bead);
                    }
                }
            }
            if !ready.is_empty() {
                self.occupancy_event(now);
            }
            for bead in ready {
                let _ = self.extend(&bead);
            }
        }
    }

    // ==================== Private: Graph Updates ====================

    /// Attempts to extend the braid with the given bead.
    /// Returns true if the bead successfully extended the braid, false otherwise.
    pub fn extend(&mut self, bead: &Bead) -> AddBeadStatus {
        let bead_hash = bead.hash();
        if self.index.contains_key(&bead_hash) {
            return AddBeadStatus::DuplicateBead;
        }
        if self.orphanage.contains_key(&bead_hash) {
            return AddBeadStatus::DuplicateBead;
        }

        let missing_parents: Vec<_> = bead
            .committed_metadata
            .parents
            .iter()
            .filter(|&&h| !self.index.contains_key(&h))
            .copied()
            .collect();
        if !missing_parents.is_empty() {
            let now = Instant::now();
            self.occupancy_event(now);
            self.orphanage.insert(bead_hash, bead.clone());
            for parent_hash in missing_parents {
                self.missing_parents
                    .entry(parent_hash)
                    .or_default()
                    .insert(bead_hash);
            }
            self.occupancy_event(now);
            return AddBeadStatus::ParentsMissing;
        }

        let bead_parents = self.parent_indices(bead);

        // Insert bead into storage
        self.beads.push(bead.clone());
        let new_bead_index = self.beads.len() - 1;
        self.index.insert(bead_hash, new_bead_index);
        self.bead_work.insert(
            new_bead_index,
            Target::from_compact(bead.committed_metadata.weak_target).to_work(),
        );

        for &parent_index in &bead_parents {
            self.children
                .entry(parent_index)
                .or_default()
                .insert(new_bead_index);
        }
        self.parents.insert(new_bead_index, bead_parents.clone());
        self.children.entry(new_bead_index).or_default();

        for &parent_index in &bead_parents {
            self.tips.remove(&parent_index);
        }
        self.tips.insert(new_bead_index);
        if bead_parents.is_empty() {
            self.geneses.insert(new_bead_index);
        }

        // --- Strategy-Specific Cohort Updates ---
        match self.extend_strategy {
            ExtendStrategy::Heuristic => {
                // --- O(W) Heuristic Cohort Update ---
                // Logic:
                // 1. Find the range [idx_min, idx_max] of cohorts containing parents.
                // 2. If idx_min < idx_max, merge all cohorts in that range.
                // 3. Identify tail of the (possibly merged) parent cohort.
                // 4. If the new bead's parents include ALL of the tail, it extends the cohort (New Cohort).
                // 5. Otherwise, it merges into that cohort (Merge).

                let parent_indices_set = &bead_parents;

                if parent_indices_set.is_empty() {
                    let new_idx = self.cohorts.len();
                    let mut cohort = Cohort::new();
                    cohort.insert(new_bead_index);
                    self.cohorts.push(cohort);
                    self.rebuild_suffix(new_idx);
                    self.adopt_orphans(&bead_hash);
                    return AddBeadStatus::BeadAdded;
                }

                let mut idx_max = None;
                let mut idx_min = None;
                let mut parents_found_count = 0;
                let total_parents = parent_indices_set.len();

                for (i, cohort) in self.cohorts.iter().enumerate().rev() {
                    let count_in_cohort = parent_indices_set
                        .iter()
                        .filter(|&p| cohort.contains(p))
                        .count();
                    if count_in_cohort > 0 {
                        if idx_max.is_none() {
                            idx_max = Some(i);
                        }
                        idx_min = Some(i);
                        parents_found_count += count_in_cohort;

                        if parents_found_count == total_parents {
                            break;
                        }
                    }
                }

                let insertion_idx = if let (Some(max), Some(min)) = (idx_max, idx_min) {
                    // Check if parents cover all internal tips of the latest parent cohort.
                    // Use the cached tail (which represents internal tips).
                    // If we span multiple cohorts (min < max), the effective tail of the merged group
                    // is the tail of the latest cohort (max).
                    const DENSE_TAIL_LIMIT: usize = 256;
                    let tail = &self.tail_cache[max];
                    let tail_len = tail.len();
                    let covers_tips = if tail_len > DENSE_TAIL_LIMIT {
                        false
                    } else {
                        tail.is_subset(parent_indices_set)
                    };

                    // Merge Spanned Cohorts if necessary
                    if min < max {
                        for i in (min + 1)..=max {
                            let merged = mem::take(&mut self.cohorts[i]);
                            self.cohorts[min].extend(merged);
                        }

                        self.cohorts.drain((min + 1)..=max);
                    }

                    // If we cover tips, we extend (min + 1). Else we merge into min.
                    if covers_tips {
                        min + 1
                    } else {
                        min
                    }
                } else {
                    0
                };

                // Apply changes
                if insertion_idx == self.cohorts.len() {
                    self.cohorts.push(HashSet::new());
                }

                self.cohorts[insertion_idx].insert(new_bead_index);

                if insertion_idx < self.cohorts.len() - 1 {
                    for i in (insertion_idx + 1)..self.cohorts.len() {
                        let beads_to_merge: Vec<_> = self.cohorts[i].iter().copied().collect();
                        self.cohorts[insertion_idx].extend(beads_to_merge);
                    }
                    self.cohorts.truncate(insertion_idx + 1);
                }

                let rebuild_start = idx_min.unwrap_or(insertion_idx);
                self.rebuild_suffix(rebuild_start);
                self.adopt_orphans(&bead_hash);
            }
            ExtendStrategy::Cached => {
                // Determine earliest cohort that includes any parent (with a small backstep for internal links)
                let start_cohort_idx = if self.cohorts.is_empty() || bead_parents.is_empty() {
                    0
                } else {
                    let mut idx = 0;
                    for (i, cohort) in self.cohorts.iter().enumerate() {
                        if cohort.iter().any(|p| bead_parents.contains(p)) {
                            idx = i;
                            break;
                        }
                    }
                    if idx > 0 {
                        let cohort = &self.cohorts[idx];
                        let has_internal_links = cohort.iter().any(|&b| {
                            self.parents
                                .get(&b)
                                .map_or(false, |parents| parents.iter().any(|p| cohort.contains(p)))
                        });
                        if has_internal_links {
                            idx -= 1;
                        }
                    }
                    idx
                };

                let initial_cohort = self
                    .cohorts
                    .get(start_cohort_idx)
                    .cloned()
                    .unwrap_or_else(|| algorithms::geneses(&self.parents));

                if start_cohort_idx < self.cohorts.len() {
                    self.cohorts.truncate(start_cohort_idx);
                }

                let mut scratch = Relatives::new();
                let new_cohorts = algorithms::cohorts(
                    &self.parents,
                    &self.children,
                    &initial_cohort,
                    &mut scratch,
                );

                self.cohorts.extend(new_cohorts);
                self.rebuild_suffix(start_cohort_idx);
                self.adopt_orphans(&bead_hash);
            }
            ExtendStrategy::NoCache => {
                let geneses = algorithms::geneses(&self.parents);
                let mut scratch = Relatives::new();

                self.cohorts =
                    algorithms::cohorts(&self.parents, &self.children, &geneses, &mut scratch);

                self.ancestor_cache.clear();
                self.descendant_cache.clear();
                self.tail_cache.clear();
                self.cohort_map.clear();
                self.rebuild_suffix(0);
                self.adopt_orphans(&bead_hash);
            }
        }

        AddBeadStatus::BeadAdded
    }

    // FIXME What is this for? Is it just overly defensive?
    pub fn check_geneses(&self, geneses: &[BeadHash]) -> GenesisCheckStatus {
        if geneses.len() != self.geneses.len() {
            return GenesisCheckStatus::GenesisBeadsCountMismatch;
        }
        let all_exist = geneses.iter().all(|h| {
            self.index
                .get(h)
                .map_or(false, |idx| self.geneses.contains(idx))
        });
        if all_exist {
            GenesisCheckStatus::GenesisBeadsValid
        } else {
            GenesisCheckStatus::MissingGenesisBead
        }
    }

    /// Compatibility alias for check_geneses (sprint-agents naming)
    pub fn check_genesis_beads(&self, genesis_beads: &Vec<BeadHash>) -> GenesisCheckStatus {
        self.check_geneses(genesis_beads)
    }

    pub fn insert_geneses(&mut self, geneses: Vec<Bead>) {
        for bead in geneses {
            let bead_hash = bead.hash();
            if !self.index.contains_key(&bead_hash) {
                self.beads.push(bead.clone());
                let new_index = self.beads.len() - 1;
                self.index.insert(bead_hash, new_index);
                self.geneses.insert(new_index);
            }
        }
    }

    /// Compatibility alias for insert_geneses (sprint-agents naming)
    pub fn insert_genesis_beads(&mut self, genesis_beads: Vec<Bead>) {
        self.insert_geneses(genesis_beads)
    }

    /// Utility function for GetBeadsAfter request (IBD sync)
    /// Returns beads that come after the given tips, or all beads if tips is empty
    pub fn get_beads_after(&self, old_tips: Vec<BeadHash>) -> Option<Vec<Bead>> {
        let old_tips_set: HashSet<BeadHash> = old_tips.into_iter().collect();
        tracing::debug!(
            old_tips=?old_tips_set, "Tips received for IBD sync"
        );

        // If no tips provided, return all beads
        if old_tips_set.is_empty() {
            return Some(self.beads.clone());
        }

        // Find the smallest index among the old tips
        let mut smallest_index = usize::MAX;
        for hash in &old_tips_set {
            if let Some(&index) = self.index.get(hash) {
                if index < smallest_index {
                    smallest_index = index;
                }
            }
        }

        // If no tips matched, return all beads as fallback
        if smallest_index == usize::MAX {
            return Some(self.beads.clone());
        }

        tracing::debug!(smallest_index, "Starting from bead index");

        // Find the cohort containing the smallest index using cohort_map cache
        let smallest_cohort_index = self
            .cohort_map
            .get(&smallest_index)
            .copied()
            .unwrap_or_else(|| {
                // Fallback: search cohorts linearly
                for (idx, cohort) in self.cohorts.iter().enumerate() {
                    if cohort.contains(&smallest_index) {
                        return idx;
                    }
                }
                usize::MAX
            });

        if smallest_cohort_index == usize::MAX {
            return Some(self.beads.clone());
        }

        tracing::debug!(smallest_cohort_index, "Starting from cohort index");

        // Collect beads from the smallest cohort onward, excluding old tips
        let mut response_beads = Vec::new();
        for cohort in self.cohorts.iter().skip(smallest_cohort_index) {
            for &bead_index in cohort {
                let bead = &self.beads[bead_index];
                if !old_tips_set.contains(&bead.hash()) {
                    response_beads.push(bead.clone());
                }
            }
        }

        if response_beads.is_empty() {
            None
        } else {
            Some(response_beads)
        }
    }
}

#[cfg(test)]
mod algorithm_tests;
#[cfg(test)]
mod tests;
