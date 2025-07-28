use crate::bead::Bead;
use crate::utils::{retrieve_bead, BeadHash};
use num::BigUint;
use serde::Serialize;
use std::cmp::Ordering;
use std::collections::VecDeque;
use std::collections::{HashMap, HashSet};
#[derive(Clone, Debug, Serialize, PartialEq)]

pub struct Cohort(HashSet<usize>);
#[derive(Debug, Clone)]
pub enum AddBeadStatus {
    DagAlreadyContainsBead,
    InvalidBead,
    BeadAdded,
    ParentsNotYetReceived,
}
#[derive(Debug, Clone)]

pub enum GenesisCheckStatus {
    GenesisBeadsValid,
    MissingGenesisBead,
    GenesisBeadsCountMismatch,
}

#[derive(Clone, Debug)]

pub struct Braid {
    pub beads: Vec<Bead>,
    pub tips: HashSet<usize>,
    pub cohorts: Vec<Cohort>,
    pub cohort_tips: Vec<HashSet<usize>>,
    pub orphan_beads: Vec<Bead>,
    pub genesis_beads: HashSet<usize>,
    pub bead_index_mapping: HashMap<BeadHash, usize>,
}

impl Braid {
    ///Initializing the Braid object for keeping track of current state of Braid
    pub fn new(genesis_beads: Vec<Bead>) -> Self {
        let mut beads = Vec::new();
        let mut bead_indices = HashSet::new();
        let mut bead_index_mapping = HashMap::new();

        for (index, bead) in genesis_beads.into_iter().enumerate() {
            beads.push(bead.clone());
            bead_indices.insert(index);
            bead_index_mapping.insert(bead.block_header.block_hash(), index);
        }
        let mut genesis_cohort: Vec<Cohort> = Vec::new();
        if bead_indices.len() != 0 {
            genesis_cohort.push(Cohort(HashSet::from(bead_indices.clone())));
        }
        Braid {
            beads,
            tips: bead_indices.clone(),
            cohorts: genesis_cohort,
            cohort_tips: vec![HashSet::from(bead_indices.clone())],
            orphan_beads: Vec::new(),
            genesis_beads: bead_indices,
            bead_index_mapping,
        }
    }
}
#[allow(unused)]
impl Braid {
    /// Attempts to extend the braid with the given bead.
    /// Returns true if the bead successfully extended the braid, false otherwise.
    pub fn extend(&mut self, bead: &Bead) -> AddBeadStatus {
        // If the braid is empty and bead has no parents, treat as genesis bead
        if self.beads.is_empty() && bead.committed_metadata.parents.is_empty() {
            *self = Braid::new(vec![bead.clone()]);
            return AddBeadStatus::BeadAdded;
        }
        // No parents: bad block i.e. the extend will add beads after the genesis
        //bead is done and the extension of genesis beads to Braid shall be done via Braid::new
        if bead.committed_metadata.parents.is_empty() {
            return AddBeadStatus::InvalidBead;
        }
        // Don't have all parents
        for parent_hash in &bead.committed_metadata.parents {
            let parent_exists = self.bead_index_mapping.contains_key(parent_hash);

            if !parent_exists {
                // Try to retrieve the parent
                if let Some(retrieved_bead) = retrieve_bead(*parent_hash) {
                    self.extend(&retrieved_bead);
                } else {
                    // Parent not found and can't be retrieved
                    self.orphan_beads.push(bead.clone());
                    return AddBeadStatus::ParentsNotYetReceived;
                }
            }
        }
        // Already seen this bead
        let bead_hash = bead.block_header.block_hash();
        if self
            .beads
            .iter()
            .any(|b| b.block_header.block_hash() == bead_hash)
        {
            return AddBeadStatus::DagAlreadyContainsBead;
        }

        // Insert bead into beads vector
        self.beads.push(bead.clone());
        let new_bead_index = self.beads.len() - 1;
        self.bead_index_mapping.insert(bead_hash, new_bead_index);

        // Find earliest parent of bead in cohorts and nuke all cohorts after that
        let mut found_parent_indices = HashSet::new();
        let mut dangling = HashSet::new();
        dangling.insert(new_bead_index);

        // We'll collect the indices to remove from cohorts
        let mut remove_after = None;
        for (i, cohort) in self.cohorts.iter().enumerate().rev() {
            // Find which parent indices are in this cohort
            for parent_hash in &bead.committed_metadata.parents {
                if let Some(&parent_index) = self.bead_index_mapping.get(parent_hash) {
                    if cohort.0.contains(&parent_index) {
                        found_parent_indices.insert(parent_index);
                    }
                }
            }
            // If this cohort contains exactly all parent beads or all the tips
            // and nothing else, we've found the right cohort - no need to look
            // further back
            if !found_parent_indices.is_empty()
                && found_parent_indices.len() == bead.committed_metadata.parents.len()
                && (self.cohort_tips[i] == found_parent_indices)
            {
                remove_after = Some(i + 1);
                dangling.insert(new_bead_index);
                break;
            } else {
                // Add all bead indices in this cohort to dangling
                for idx in &cohort.0 {
                    dangling.insert(*idx);
                }
                if found_parent_indices.len() == bead.committed_metadata.parents.len() {
                    remove_after = Some(i);
                    break;
                }
            }
        }

        // Remove all cohorts after the found index
        if let Some(idx) = remove_after {
            self.cohorts.truncate(idx);
            self.cohort_tips.truncate(idx);
        } else {
            self.cohorts.clear();
            self.cohort_tips.clear();
        }

        // Remove parents from tips if present
        for parent_hash in &bead.committed_metadata.parents {
            // Find the index of the parent bead
            if let Some(&parent_index) = self.bead_index_mapping.get(parent_hash) {
                self.tips.remove(&parent_index);
            }
        }

        // Add the new bead's index to tips
        self.tips.insert(new_bead_index);

        // Construct a sub-braid from dangling and compute any new cohorts
        // Here, we just create a new cohort with dangling beads
        if !dangling.is_empty() {
            self.cohorts.push(Cohort(dangling));
            self.cohort_tips.push(self.tips.clone());
        }

        self.process_orphan_beads();

        AddBeadStatus::BeadAdded
    }

    /// Process orphan beads to see if any can now be added to the braid
    /// This method checks if all parents of orphan beads are now available
    /// and recursively extends the braid with those beads
    fn process_orphan_beads(&mut self) {
        // Process orphans in reverse order to maintain proper indexing
        let mut i = self.orphan_beads.len();
        while i > 0 {
            i -= 1;

            // Check if all parents are now available for this orphan
            let mut all_parents_available = true;
            for parent_hash in &self.orphan_beads[i].committed_metadata.parents {
                if !self.bead_index_mapping.contains_key(parent_hash) {
                    all_parents_available = false;
                    break;
                }
            }

            if all_parents_available {
                // Remove the orphan bead first, then process it
                let orphan_bead = self.orphan_beads.remove(i);

                // Now extend with the orphan bead
                match self.extend(&orphan_bead) {
                    AddBeadStatus::BeadAdded => {
                        // Recursively process remaining orphans as this addition
                        // might enable more orphans to be processed
                        self.process_orphan_beads();
                        return; // Exit current processing as recursion will handle the rest
                    }
                    AddBeadStatus::DagAlreadyContainsBead => {
                        continue;
                    }
                    AddBeadStatus::InvalidBead => {
                        continue;
                    }
                    AddBeadStatus::ParentsNotYetReceived => {
                        self.orphan_beads.push(orphan_bead);
                    }
                }
            }
        }
    }

    pub fn check_genesis_beads(&self, genesis_beads: &Vec<BeadHash>) -> GenesisCheckStatus {
        if (genesis_beads.len() != self.genesis_beads.len()) {
            return GenesisCheckStatus::GenesisBeadsCountMismatch;
        }
        for bead_hash in genesis_beads {
            let index = self.bead_index_mapping.get(bead_hash);
            let bead_exists = match index {
                Some(idx) => self.genesis_beads.contains(idx),
                None => false,
            };
            if !bead_exists {
                return GenesisCheckStatus::MissingGenesisBead;
            }
        }
        return GenesisCheckStatus::GenesisBeadsValid;
    }

    pub fn insert_genesis_beads(&mut self, genesis_beads: Vec<Bead>) {
        for bead in genesis_beads {
            let bead_hash = bead.block_header.block_hash();
            if !self.bead_index_mapping.contains_key(&bead_hash) {
                self.beads.push(bead.clone());
                let new_index = self.beads.len() - 1;
                self.bead_index_mapping.insert(bead_hash, new_index);
                self.genesis_beads.insert(new_index);
            }
        }
    }
}
#[allow(unused)]
mod consensus_functions {
    use num::{One, Zero};

    use super::*;
    use crate::error::BraidError;
    use crate::error::BraidError::{HighestWorkBeadFetchFailed, MissingAncestorWork};
    /// Returns the set of **genesis beads** from a given Braid object.
    ///
    /// A **genesis bead** is defined as a bead that has no parents, i.e., it is a root node in the Braid DAG.
    /// These beads represent the starting points in the Braidpool architecture, with no dependencies upstream.
    ///
    /// # Arguments
    ///
    /// * `braid_obj` - A reference to the `Braid` object.  
    ///   While not directly used in the logic here, it is included to align with interface expectations or future-proofing.
    ///
    /// * `parents` - A map from bead indices to their parent bead indices.
    ///   Each entry represents a bead and its set of parent beads.
    ///
    /// # Returns
    ///
    /// A `HashSet<usize>` containing the indices of all beads that do not have any parents.
    ///
    /// # Reference
    ///
    /// For architectural context, refer to the [Braidpool Specification](https://github.com/braidpool/braidpool/blob/dev/docs/braidpool_spec.md).
    pub fn genesis(braid_obj: &Braid, parents: &HashMap<usize, HashSet<usize>>) -> HashSet<usize> {
        let mut genesis_bead_indices: HashSet<usize> = HashSet::new();
        for bead in parents {
            if parents[&*bead.0].is_empty() == true {
                genesis_bead_indices.insert(*bead.0);
            }
        }
        return genesis_bead_indices;
    }
    /// Returns the set of **tip beads** from a given Braid object.
    ///
    /// A **tip bead** is defined as a bead that has no children (i.e., no other bead references it as a parent).
    /// These beads represent the leaves or endpoints in the Braid DAG structure.
    ///
    /// # Arguments
    ///
    /// * `braid_obj` - A reference to the `Braid` object, used to access bead metadata and index mappings.
    /// * `parents` - A map from each bead index to a `HashSet` of its parent bead indices.
    ///
    /// # Returns
    ///
    /// A `HashSet<usize>` containing the indices of all beads that are **not referenced** as a parent by any other bead.
    pub fn tips(braid_obj: &Braid, parents: &HashMap<usize, HashSet<usize>>) -> HashSet<usize> {
        let mut bead_indices_mapping: HashMap<usize, usize> = HashMap::new();
        let mut tips_indices: HashSet<usize> = HashSet::new();
        for parent_bead_idx in parents {
            bead_indices_mapping.insert(*parent_bead_idx.0, 0);
        }
        //tips are the beads having no childs//
        //utilizing the passed arguments as of parents instead of the internal braid one
        let current_beads = &braid_obj.beads;
        for bead in current_beads {
            let current_bead_index = braid_obj.bead_index_mapping[&bead.block_header.block_hash()];
            let parents = match parents.get(&current_bead_index) {
                Some(b) => b,
                _ => {
                    continue;
                }
            };
            for parent_bead in parents {
                if let Some(val) = bead_indices_mapping.get_mut(&parent_bead) {
                    *val = *val + 1;
                }
            }
        }
        for (key, value) in bead_indices_mapping.iter() {
            if *value == 0 {
                tips_indices.insert(*key);
            }
        }
        tips_indices
    }
    /// Reverses the parent mapping of beads to generate a child mapping.
    ///
    /// Given a mapping from each bead to its parent beads (`parents`), this function constructs
    /// the reverse: a mapping from each bead to the set of **children** beads that reference it as a parent.
    ///
    /// This is useful for traversing the Braid DAG in the **forward** direction (from ancestors to descendants),
    /// whereas the original parent map is used for **backward** traversal.
    ///
    /// # Arguments
    ///
    /// * `braid_obj` - A reference to the `Braid` object, required to resolve bead indices.
    /// * `parents` - A `HashMap` where each key is a bead index, and the value is a `HashSet` of its parent bead indices.
    ///
    /// # Returns
    ///
    /// A `HashMap<usize, HashSet<usize>>` where each key is a bead index, and the value is a set of its children.
    pub fn reverse(
        braid_obj: &Braid,
        parents: &HashMap<usize, HashSet<usize>>,
    ) -> HashMap<usize, HashSet<usize>> {
        let mut bead_children_mapping: HashMap<usize, HashSet<usize>> =
            parents.keys().map(|&idx| (idx, HashSet::new())).collect();

        let current_beads = &braid_obj.beads;
        for bead in current_beads {
            let current_bead_idx = braid_obj.bead_index_mapping[&bead.block_header.block_hash()];
            let parents = &parents[&current_bead_idx];

            for parent_bead_idx in parents.iter() {
                bead_children_mapping
                    .get_mut(&parent_bead_idx)
                    .unwrap()
                    .insert(current_bead_idx);
            }
        }
        return bead_children_mapping;
    }
    /// Returns the complete set of **child beads** for a given set of bead indices.
    ///
    /// This function computes the immediate children of a set of beads using either a provided
    /// bead-to-children map or by computing one on the fly via the reverse of the parent map.
    ///
    /// It is useful when traversing a Braid structure **forward** from a set of beads
    /// to explore their direct descendants.
    ///
    /// # Arguments
    ///
    /// * `braid_obj` - A reference to the `Braid` object, used only when `children` is `None`.
    /// * `beads_indices` - A `HashSet` of bead indices whose children need to be found.
    /// * `children` - An optional reference to a `HashMap` representing bead → children mappings.
    ///   If `None`, the mapping is generated using the `reverse` function and an empty parent map (as a fallback).
    ///
    /// # Returns
    ///
    /// A `HashSet<usize>` containing all bead indices that are children of the given input beads.
    pub fn generation(
        braid_obj: &Braid,
        beads_indices: &HashSet<usize>,
        children: Option<&HashMap<usize, HashSet<usize>>>,
    ) -> HashSet<usize> {
        let mut children_set: HashSet<usize> = HashSet::new();
        let mut parents: HashMap<usize, HashSet<usize>> = HashMap::new();
        for idx in beads_indices {
            parents.insert(*idx, HashSet::new());
        }
        //values of children beads/mapping is always provided though
        let bead_children_mapping = match children {
            Some(children) => children,
            None => &reverse(braid_obj, &parents),
        };
        for bead in beads_indices {
            if let Some(child_beads) = bead_children_mapping.get(&bead) {
                children_set.extend(child_beads.iter());
            }
        }
        return children_set;
    }

    /// Updates the ancestors of a given bead within a Braid DAG using an iterative DFS traversal.
    ///
    /// This function computes the complete set of **ancestors** for the bead corresponding to `current_block_hash`.
    /// It uses an **iterative DFS** approach to avoid recursion stack overflows and updates a shared
    /// `ancestors` mapping (`HashMap<usize, HashSet<usize>>`) in-place.
    ///
    /// # Arguments
    ///
    /// * `braid_obj` - A reference to the `Braid` object, which provides bead metadata and index mapping.
    /// * `current_block_hash` - The hash of the bead whose ancestors need to be computed.
    /// * `ancestors` - A mutable reference to the global bead-to-ancestors map that will be updated.
    /// * `parents` - A mapping from bead indices to their parent bead indices.
    ///
    /// # Returns
    ///
    /// A mutable reference to the updated `ancestors` map where:
    /// - `ancestors[i]` contains all ancestor indices (direct and transitive) of bead `i`.
    pub fn updating_ancestors<'a>(
        braid_obj: &Braid,
        current_block_hash: BeadHash,
        ancestors: &'a mut HashMap<usize, HashSet<usize>>,
        parents: &HashMap<usize, HashSet<usize>>,
    ) -> &'a mut HashMap<usize, HashSet<usize>> {
        let mut dequeue: VecDeque<(usize, bool)> = VecDeque::new();
        let current_bead_index = braid_obj.bead_index_mapping[&current_block_hash];
        dequeue.push_back((current_bead_index, false));
        while let Some((current, is_processed)) = dequeue.pop_back() {
            if is_processed {
                if let Some(current_ancestor) = ancestors.get_mut(&current) {
                    current_ancestor.clear();
                    if let Some(parents_beads) = parents.get(&current) {
                        current_ancestor.extend(parents_beads.iter());
                    }
                } else {
                    let mut val_set: HashSet<usize> = HashSet::new();
                    if let Some(parents_beads) = parents.get(&current) {
                        val_set.extend(parents_beads);
                    }
                    ancestors.insert(current, val_set);
                }
                if let Some(parent_indices) = parents.get(&current) {
                    let ancestor_ref = ancestors.to_owned();
                    for parent_idx in parent_indices {
                        if let Some(current_ancestors) = ancestors.get_mut(&current) {
                            if let Some(beads) = ancestor_ref.get(parent_idx) {
                                current_ancestors.extend(beads);
                            }
                        } else {
                            let mut val_set: HashSet<usize> = HashSet::new();
                            if let Some(beads) = ancestor_ref.get(parent_idx) {
                                val_set.extend(beads);
                            }
                            ancestors.insert(current, val_set);
                        }
                    }
                }
            } else {
                dequeue.push_back((current, true));
                if let Some(parents) = parents.get(&current) {
                    for parent in parents {
                        if !ancestors.contains_key(parent) {
                            dequeue.push_back((*parent, false));
                        }
                    }
                }
            }
        }

        return ancestors;
    }
    /// Computes and returns the complete set of **ancestors** for all beads up to a given bead
    /// in a Braid DAG (Directed Acyclic Graph).
    ///
    /// This function ensures that the provided `ancestors` mapping is updated for each bead in the ancestry
    /// chain of `current_block_hash`. It traverses recursively through the parent hierarchy and
    /// builds the transitive closure of ancestors.
    ///
    /// # Arguments
    ///
    /// * `braid_obj` - A reference to the `Braid` object, providing bead metadata and index resolution.
    /// * `current_block_hash` - The block hash of the bead for which ancestors (and all predecessors) should be updated.
    /// * `ancestors` - A mutable reference to a global map where each bead index maps to its ancestors.
    /// * `parents` - A mapping from bead index to the set of its parent bead indices.
    ///
    /// # Returns
    ///
    /// A mutable reference to the updated `ancestors` map.
    ///
    /// # Notes
    ///
    /// - If a bead is already present in the `ancestors` map, it is recalculated.
    /// - The function uses `updating_ancestors` internally for deferred DFS-style expansion.
    /// - Avoids redundant computation by checking `ancestors.contains_key(...)` before updating parent entries.
    pub fn get_all_ancestors<'a>(
        braid_obj: &Braid,
        current_block_hash: BeadHash,
        ancestors: &'a mut HashMap<usize, HashSet<usize>>,
        parents: &HashMap<usize, HashSet<usize>>,
    ) -> &'a mut HashMap<usize, HashSet<usize>> {
        let current_block_idx = braid_obj.bead_index_mapping[&current_block_hash];
        //if bead entry already exists in the current ancestor mapping
        if let Some(current_bead_ancestors) = ancestors.get_mut(&current_block_idx) {
            current_bead_ancestors.clear();
            let parents_current_block: &HashSet<usize> = &parents[&current_block_idx];
            current_bead_ancestors.extend(parents_current_block.iter());
        }
        //if bead entry does not exists in the current ancestor mapping
        else {
            let parents_current_block: &HashSet<usize> = &parents[&current_block_idx];
            let mut value_set: HashSet<usize> = HashSet::new();
            value_set.extend(parents_current_block.iter());
            ancestors.insert(current_block_idx, value_set);
        }
        for parent_idx in &parents[&current_block_idx] {
            let current_parent_blockhash = braid_obj.beads[*parent_idx].block_header.block_hash();
            if ancestors.contains_key(&parent_idx) == false {
                updating_ancestors(&braid_obj, current_parent_blockhash, ancestors, &parents);
            }
            let ancestor_ref = ancestors.to_owned();
            if let Some(current_bead_ancestors) = ancestors.get_mut(&current_block_idx) {
                let parent_ancestors: &HashSet<usize> = &ancestor_ref[&parent_idx];
                current_bead_ancestors.extend(parent_ancestors.iter());
            } else {
                let parent_ancestors: &HashSet<usize> = &ancestors[&parent_idx];
                let mut value_set = HashSet::new();
                value_set.extend(parent_ancestors.iter());
                ancestors.insert(current_block_idx, value_set);
            }
        }

        return ancestors;
    }
    /// Computes the **cohorts** in a Braid DAG, representing layered subgraphs (slices) bounded by graph cuts.
    ///
    /// A **cohort** is a set of bead indices forming a layer where all included beads share the same
    /// topological generation, i.e., all their ancestors lie strictly in earlier cohorts.
    ///
    /// Graphically, this corresponds to a **graph cut**: a boundary line across the DAG such that
    /// every bead on the right side of the cut has all beads on the left side as its ancestors.
    ///
    /// # Arguments
    ///
    /// * `braid_obj` - A reference to the `Braid` object, which holds all bead metadata and index mappings.
    /// * `parents` - A map from bead index to its parent indices, used for ancestry traversal.
    /// * `children_or_not` - Optional map from bead index to its child indices (precomputed). If `None`, it is derived via `reverse()`.
    /// * `inital_cohort` - Optional starting cohort (e.g., genesis beads). If `None`, it defaults to `genesis(...)`.
    ///
    /// # Returns
    ///
    /// A `Vec<HashSet<usize>>`, where each set represents a **cohort** in topological order.
    /// Each cohort is disjoint and collectively they partition the beads in the Braid up to time `T`.
    ///
    /// # Key Concepts
    ///
    /// - **Tips** are beads with no children — they represent terminal points in the DAG.
    /// - The function maintains a `head` (current working cohort) and `tail` (future candidate beads).
    /// - A loop iteratively grows the frontier (`cohort`) until all tips are included.
    pub fn cohort(
        braid_obj: &Braid,
        parents: &HashMap<usize, HashSet<usize>>,
        children_or_not: Option<&HashMap<usize, HashSet<usize>>>,
        inital_cohort: Option<HashSet<usize>>,
    ) -> Vec<HashSet<usize>> {
        let children = match children_or_not {
            Some(val) => val,
            None => &reverse(braid_obj, parents),
        };
        let braid_tips = tips(braid_obj, parents);
        let mut cohort = match inital_cohort {
            Some(inital_cohort) => inital_cohort,
            None => genesis(braid_obj, parents),
        };
        let mut generator: Vec<HashSet<usize>> = Vec::new();
        let mut oldcohort: HashSet<usize> = HashSet::new();
        let mut head = cohort.clone();
        let mut tail = cohort.clone();
        let mut loop_flag = false;
        loop {
            let mut ancestor: HashMap<usize, HashSet<usize>> = HashMap::new();
            for b in &head {
                ancestor.insert(*b, HashSet::new());
            }

            cohort = head.to_owned();
            loop {
                if head.is_empty() == true {
                    loop_flag = true;
                    break;
                }

                for bead in cohort.difference(&oldcohort) {
                    if let Some(children) = children.get(bead) {
                        tail.extend(children.iter());
                    }
                }
                for bead in oldcohort.difference(&cohort) {
                    tail.insert(*bead);
                }
                let mut has_tips = false;
                for tip in &braid_tips {
                    if cohort.contains(tip) {
                        has_tips = true;
                        break;
                    }
                }
                if has_tips == true {
                    for bead in braid_tips.difference(&cohort) {
                        tail.insert(*bead);
                    }
                } else {
                    for t in &cohort {
                        tail.remove(t);
                    }
                }
                oldcohort = cohort.clone();
                let mut key_set: HashSet<usize> = ancestor.keys().copied().collect();
                for bead in tail.difference(&key_set) {
                    let current_bead_blockhash = braid_obj.beads[*bead].block_header.block_hash();
                    updating_ancestors(braid_obj, current_bead_blockhash, &mut ancestor, parents);
                }

                cohort = HashSet::new();
                for (_key, val) in &ancestor {
                    cohort.extend(val);
                }
                //cohort is the superset
                let cohort_intersection_tips: HashSet<&usize> =
                    cohort.intersection(&braid_tips).collect();
                //if all tips are present in cohort then the size of a.len = braid.tips.len
                if cohort_intersection_tips.len() == braid_tips.len() {
                    head.clear();
                    break;
                }
                if cohort.is_empty() == false {
                    let mut flag = false;
                    for t in &tail {
                        if let Some(value) = &ancestor.get(&t) {
                            if cohort != **value {
                                flag = true;
                                break;
                            }
                        }
                    }
                    if !flag {
                        head = tail.clone();
                        break;
                    }
                }
                if cohort == oldcohort {
                    let set: HashSet<&usize> = tail.intersection(&braid_tips).collect();
                    //tail contains all the tips
                    if set.len() == braid_tips.len() {
                        head.clear();
                        cohort.extend(tail.iter());
                        tail.clear();
                        break;
                    }
                    cohort.extend(tail.iter());
                }
            }
            if loop_flag == true {
                break;
            }
            if !cohort.is_empty() {
                generator.push(cohort);
            }
            oldcohort.clear();
        }
        generator
    }
    /// Determines and returns the **head** of a given cohort in a Braid DAG.
    ///
    /// The head of a cohort is the set of beads that immediately follow the given cohort
    /// in the DAG structure — i.e., the "next generation" of beads.
    /// These are computed by finding children of the current cohort,
    /// removing those that already belong to the cohort,
    /// and then finding the children of the resulting set (the *tail*).
    ///
    /// In the special case where the *tail* is empty or overlaps with **genesis tips**,
    /// the function returns the tips instead.
    ///
    /// # Arguments
    ///
    /// * `braid_obj` - A reference to the `Braid` object for accessing metadata and bead index mappings.
    /// * `cohort` - A reference to a `HashSet<usize>` representing the current cohort (layer) of bead indices.
    /// * `parents` - A reference to the bead → parent mapping.
    /// * `children` - An optional bead → children mapping; if `None`, it is computed as needed.
    ///
    /// # Returns
    ///
    /// A `HashSet<usize>` representing the next possible head cohort — either:
    /// - The set of children that follow this cohort, or
    /// - The **genesis tips**, if the tail is empty or intersects with them.
    pub fn cohort_head(
        braid_obj: &Braid,
        cohort: &HashSet<usize>,
        parents: &HashMap<usize, HashSet<usize>>,
        children: Option<&HashMap<usize, HashSet<usize>>>,
    ) -> HashSet<usize> {
        let cohort_children: HashSet<usize> = generation(braid_obj, &cohort, Some(parents));
        let mut cohort_children_ref: HashSet<usize> =
            cohort_children.difference(&cohort).copied().collect();
        let tail = generation(braid_obj, &cohort_children_ref, children);
        let cohort_tips = genesis(braid_obj, parents);
        let flag = tail.iter().any(|t| cohort_tips.contains(t));

        if tail.is_empty() == true || flag {
            return cohort_tips;
        }

        return tail;
    }
    /// Returns the **tail** of a given cohort in a Braid DAG.
    ///
    /// The **tail** refers to the immediate set of beads that follow the current cohort,
    /// based on child relationships. It is essentially the "head" of the reverse graph traversal,
    /// where parent and child roles are flipped.
    ///
    /// Internally, this function computes the child mapping (if not provided), and delegates to
    /// `cohort_head()` using the reversed direction (i.e., children become parents and vice versa).
    ///
    /// # Arguments
    ///
    /// * `braid_obj` - Reference to the `Braid` object containing all bead metadata and mappings.
    /// * `cohort` - The current cohort whose tail (i.e., next layer) is to be determined.
    /// * `parents` - The original bead → parent mapping used to reverse relationships if needed.
    /// * `children` - Optional bead → children mapping. If `None`, it is computed via `reverse(...)`.
    ///
    /// # Returns
    ///
    /// A `HashSet<usize>` representing the **tail** of the cohort, based on topological progression.
    pub fn cohort_tail(
        braid_obj: &Braid,
        cohort: &HashSet<usize>,
        parents: &HashMap<usize, HashSet<usize>>,
        children: Option<HashMap<usize, HashSet<usize>>>,
    ) -> HashSet<usize> {
        let childs = match children {
            Some(childrens) => childrens,
            None => reverse(braid_obj, parents),
        };

        return cohort_head(braid_obj, cohort, &childs, Some(parents));
    }
    /// Constructs a **sub-braid** from a specified set of bead indices within a Braid DAG.
    ///
    /// A *sub-braid* is defined as the subgraph induced by a subset of beads —
    /// that is, only the beads in the input `beads` set are considered, and only the parent
    /// relationships between those beads are retained.
    ///
    /// This is especially useful in contexts like:
    /// - **Pruning** parts of the DAG.
    /// - **Cohort isolation** or localized validation.
    /// - Visualization of subgraphs or ancestry scopes.
    ///
    /// # Arguments
    ///
    /// * `braid_obj` - A reference to the full `Braid` object (not directly used here, but useful for consistency).
    /// * `beads` - A set of bead indices to include in the sub-braid.
    /// * `parents` - A mapping from each bead index to its set of parent bead indices (the full parent DAG).
    ///
    /// # Returns
    ///
    /// A `HashMap<usize, HashSet<usize>>` where:
    /// - Keys are bead indices from the `beads` set.
    /// - Values are sets of **parents also within the `beads` set**.
    pub fn get_sub_braid(
        braid_obj: &Braid,
        beads: &HashSet<usize>,
        parents: &HashMap<usize, HashSet<usize>>,
    ) -> HashMap<usize, HashSet<usize>> {
        let mut sub_braid: HashMap<usize, HashSet<usize>> = HashMap::new();
        for bead in beads {
            let mut current_bead_sub: HashSet<usize> = HashSet::new();
            if let Some(current_bead_parent) = parents.get(bead) {
                for parent_bead_idx in current_bead_parent {
                    if beads.contains(parent_bead_idx) {
                        current_bead_sub.insert(*parent_bead_idx);
                    }
                }
            }
            sub_braid.insert(*bead, current_bead_sub);
        }
        return sub_braid;
    }
    /// Computes the **descendant work** for each bead in the Braid DAG.
    ///
    /// In Braidpool’s Proof-of-Work (PoW) model, each bead has intrinsic work (e.g., hash difficulty),
    /// and the total work includes contributions from all its **descendants** in the DAG.
    ///
    /// This function traverses the DAG in **cohort-reversed** (topological reverse) order
    /// and accumulates the descendant work for each bead, i.e., the sum of its own work and
    /// all work contributed by beads that descend from it.
    ///
    /// # Parameters
    ///
    /// * `braid_obj` - Reference to the complete `Braid` DAG object.
    /// * `parents` - A map from bead indices to their immediate parents.
    /// * `children_or_not` - Optional map from bead indices to their children. If `None`, it is computed by reversing `parents`.
    /// * `bead_work_or_not` - Optional map of bead index to intrinsic work (`BigUint`). If `None`, assigns all beads a default `FIXED_BEAD_WORK`.
    /// * `in_cohorts_or_not` - Optional precomputed cohort list. If `None`, it is generated using `cohort(...)`.
    ///
    /// # Returns
    ///
    /// A map from bead indices to their **descendant work** value.
    /// That is:
    /// ```text
    /// descendant_work[b] = work(b) + Σ work(descendant(b))
    /// ```
    pub fn descendant_work(
        braid_obj: &Braid,
        parents: &HashMap<usize, HashSet<usize>>,
        children_or_not: Option<&HashMap<usize, HashSet<usize>>>,
        bead_work_or_not: Option<&HashMap<usize, BigUint>>,
        in_cohorts_or_not: Option<Vec<HashSet<usize>>>,
    ) -> HashMap<usize, BigUint> {
        let children = match children_or_not {
            Some(val) => val,
            None => &reverse(braid_obj, parents),
        };
        //This is done for increasing the scope
        //therefore trading of with iteration each time the function is called but it avoids `cloning` which may be expensive
        let work: HashMap<usize, BigUint> = parents.keys().map(|&k| (k, BigUint::one())).collect();
        let bead_work = match bead_work_or_not {
            Some(val) => val,
            None => &work,
        };
        let mut previous_work: BigUint = BigUint::zero();
        let rev_cohorts = match in_cohorts_or_not {
            Some(val) => {
                let mut val_ref = val;
                val_ref.reverse();
                val_ref
            }
            None => cohort(braid_obj, &children, Some(parents), None),
        };
        let mut ret_val: HashMap<usize, BigUint> = HashMap::new();
        for curr_cohort in rev_cohorts {
            let sub_children = get_sub_braid(braid_obj, &curr_cohort, &children);
            let mut sub_descendants: HashMap<usize, HashSet<usize>> = HashMap::new();
            for bead in &curr_cohort {
                let current_bead_hash = braid_obj.beads[*bead].block_header.block_hash();
                get_all_ancestors(
                    braid_obj,
                    current_bead_hash,
                    &mut sub_descendants,
                    &sub_children,
                );
                let work_summation = sub_descendants
                    .get(&bead)
                    .map(|descendants| descendants.iter().map(|d| &bead_work[d]).sum())
                    .unwrap_or(BigUint::zero());
                ret_val.insert(
                    *bead,
                    previous_work.clone() + &bead_work[bead] + work_summation,
                );
            }
            let work_summation: BigUint = curr_cohort.iter().map(|bead| &bead_work[bead]).sum();
            previous_work += work_summation;
        }
        return ret_val;
    }
    /// Comparator function for ordering bead indices in Braidpool consensus logic.
    ///
    /// The comparison follows a strict priority:
    /// 1. **Descendant Work** (`dwork`)
    /// 2. **Ancestor Work** (`awork`)
    /// 3. **Bead Index** (in reverse; i.e., smaller index wins last)
    ///
    /// This comparator is designed to be used in sorting and priority queues where
    /// consensus-based ordering of beads is necessary (e.g., tip selection, leader election).
    ///
    /// # Arguments
    ///
    /// * `a` - Index of bead A.
    /// * `b` - Index of bead B.
    /// * `dwork` - Map of bead index to its **descendant work** (must be provided).
    /// * `awork_or_not` - Optional map of bead index to **ancestor work**; required for full comparison.
    ///
    /// # Returns
    ///
    /// An `Ordering` (`Less`, `Greater`, or `Equal`) indicating the relative ranking of bead A vs B.
    ///
    pub fn bead_cmp(
        a: usize,
        b: usize,
        dwork: &HashMap<usize, BigUint>,
        awork: &HashMap<usize, BigUint>,
    ) -> Result<Ordering, BraidError> {
        if dwork[&a] < dwork[&b] {
            return Ok(Ordering::Less);
        }
        if dwork[&a] > dwork[&b] {
            return Ok(Ordering::Greater);
        }

        if awork[&a] < awork[&b] {
            return Ok(Ordering::Less);
        }
        if awork[&a] > awork[&b] {
            return Ok(Ordering::Greater);
        }

        if a > b {
            return Ok(Ordering::Less);
        }
        if a < b {
            return Ok(Ordering::Greater);
        }

        Ok(Ordering::Equal)
    }
    /// Computes the **highest-work path** in the Braid DAG.
    ///
    /// This function identifies the most "valuable" path in terms of cumulative **Proof-of-Work (PoW)**
    /// starting from a genesis bead and ending at a tip bead, which is particularly useful for:
    /// - Conflict resolution due to simultaneous bead proposals.
    /// - Establishing a canonical chain or subchain in a DAG-based consensus.
    ///
    /// The "highest work" path is selected by:
    /// 1. Choosing the genesis bead with the maximum **descendant work** (and then ancestor work, and then index).
    /// 2. Repeatedly walking forward by selecting the child with the highest work according to the same criteria.
    /// 3. Continuing until a tip bead is reached.
    ///
    /// # Parameters
    ///
    /// * `braid_obj` - The full `Braid` structure representing the DAG.
    /// * `parents` - Map of bead index to its immediate parents.
    /// * `children_or_none` - Optional child map (bead index → set of children); computed if `None`.
    /// * `bead_work_or_not` - Optional work map for beads; if `None`, a constant work value is used for each bead.
    ///
    /// # Returns
    ///
    /// A `Vec<usize>` representing the highest-work path as a sequence of bead indices from genesis to tip.
    ///
    /// /// # Consensus Rule
    /// Sorting order uses `bead_cmp(...)`, which prioritizes:
    /// - Descendant Work
    /// - Ancestor Work
    /// - Bead Index (reverse order)
    pub fn highest_work_path(
        braid_obj: &Braid,
        parents: &HashMap<usize, HashSet<usize>>,
        children_or_none: Option<&HashMap<usize, HashSet<usize>>>,
        bead_work_or_not: Option<HashMap<usize, BigUint>>,
    ) -> Result<Vec<usize>, BraidError> {
        let children = match children_or_none {
            Some(child) => child,
            None => &reverse(braid_obj, parents),
        };
        let bead_work = match bead_work_or_not {
            Some(work) => work,
            None => {
                let mut work: HashMap<usize, BigUint> =
                    parents.keys().map(|&k| (k, BigUint::one())).collect();
                work
            }
        };
        let descendant_work_braid =
            descendant_work(braid_obj, parents, Some(children), Some(&bead_work), None);
        let ancestor_work =
            descendant_work(braid_obj, children, Some(parents), Some(&bead_work), None);
        //getting the genesis beads and for each evaluating the highest
        //work genesis bead to be included inside the highest work path
        let genesis_beads = genesis(braid_obj, parents);
        //getting the maxima out of the genesis beads
        let max_gensis_bead = genesis_beads
            .iter()
            .max_by(|a, b| bead_cmp(**a, **b, &descendant_work_braid, &ancestor_work).unwrap())
            .ok_or(HighestWorkBeadFetchFailed)
            .unwrap();
        //populating the highest work path with indices representing the beads involved from the
        //entire braid for computation of highest work path
        let mut highest_work_path: Vec<usize> = vec![*max_gensis_bead];
        //getting the tip beads
        let tips_beads: HashSet<usize> = tips(braid_obj, parents);
        //computing while iterating and processing the previous best nodes and generating all
        //its corresponding set of childrens for getting further best maximum work path nodes
        while tips_beads.contains(&highest_work_path[highest_work_path.len() - 1]) == false {
            let mut beads_indices: HashSet<usize> = HashSet::new();
            beads_indices.insert(highest_work_path[highest_work_path.len() - 1]);
            //generating the child sets for the previous best bead
            let current_bead_children_set = generation(braid_obj, &beads_indices, Some(children));
            //getting the maximum via comparator
            let max_bead = current_bead_children_set
                .iter()
                .max_by(|a, b| bead_cmp(**a, **b, &descendant_work_braid, &ancestor_work).unwrap())
                .ok_or(HighestWorkBeadFetchFailed)
                .unwrap();
            highest_work_path.push(*max_bead);
        }

        return Ok(highest_work_path);
    }

    /// Validates the **structural integrity of a cohort** in both forward and backward directions within the Braid DAG.
    ///
    /// This function checks whether a given set of bead indices (`cohort`) forms a valid subgraph in terms of:
    /// - All ancestors of any bead in the cohort being present in the cohort (`backward check`)
    /// - All descendants of any bead in the cohort being present in the cohort (`forward check`)
    ///
    /// This ensures the cohort is closed under transitive ancestry and descent, forming a **fully-connected induced subgraph**.
    /// It's often used during pruning, consensus validation, or snapshot isolation.
    ///
    /// # Parameters
    ///
    /// * `braid_obj` - Reference to the full `Braid` object.
    /// * `cohort` - Set of bead indices to validate.
    /// * `parents` - Mapping from bead index to its parent set.
    /// * `children_or_none` - Optional child mapping. If `None`, it is computed from `parents`.
    ///
    /// # Returns
    ///
    /// * `true` if the cohort passes both ancestor and descendant checks.
    /// * `false` if any external bead influences or is influenced by beads in the cohort.
    ///
    pub fn check_cohort(
        braid_obj: &Braid,
        cohort: &HashSet<usize>,
        parents: &HashMap<usize, HashSet<usize>>,
        children_or_none: Option<&HashMap<usize, HashSet<usize>>>,
    ) -> bool {
        let children = match children_or_none {
            Some(childs) => childs,
            None => &reverse(braid_obj, parents),
        };
        return check_cohort_ancestors(braid_obj, Some(children), cohort, parents)
            && check_cohort_ancestors(braid_obj, Some(parents), cohort, children);
    }
    /// Validates that all ancestors of a given cohort are contained within the cohort itself,
    /// or are part of its "cohort head" (i.e., entry points).
    ///
    /// This function ensures that the cohort is **ancestrally closed**:
    /// - All ancestors of all beads in the cohort must either:
    ///     - Belong to the cohort itself, or
    ///     - Be part of its head (i.e., minimal external dependencies).
    ///
    /// This check is useful for confirming if the cohort forms a self-contained component
    /// of the Braid DAG that could be used for pruning, consensus snapshots, or isolation.
    ///
    /// # Parameters
    ///
    /// * `braid_obj` - Reference to the Braid DAG.
    /// * `children_or_none` - Optional child mapping (used for generating children of missing ancestors).
    ///                        If `None`, it is computed using `reverse(...)`.
    /// * `cohort` - Set of bead indices representing the cohort.
    /// * `parents` - Parent mapping of the entire braid (used for ancestor traversal).
    ///
    /// # Returns
    ///
    /// `true` if the cohort is valid with respect to its ancestors (no invalid external ancestry),
    /// `false` otherwise.
    pub fn check_cohort_ancestors(
        braid_obj: &Braid,
        children_or_none: Option<&HashMap<usize, HashSet<usize>>>,
        cohort: &HashSet<usize>,
        parents: &HashMap<usize, HashSet<usize>>,
    ) -> bool {
        let children = match children_or_none {
            Some(child) => child,
            None => &reverse(braid_obj, parents),
        };
        let mut ancestors: HashMap<usize, HashSet<usize>> = HashMap::new();
        let mut all_ancestors: HashSet<usize> = HashSet::new();

        let head = cohort_head(braid_obj, cohort, parents, Some(children));

        for bead in cohort {
            let current_bead_hash = braid_obj.beads[*bead].block_header.block_hash();
            get_all_ancestors(braid_obj, current_bead_hash, &mut ancestors, parents);
            if let Some(ancestor_beads) = ancestors.get(&bead) {
                for ancestor_bead in ancestor_beads {
                    if !cohort.contains(ancestor_bead) {
                        all_ancestors.insert(*ancestor_bead);
                    }
                }
            }
        }
        if all_ancestors.is_empty() == false {
            let generated_child_set = generation(braid_obj, &all_ancestors, Some(children));
            let diff: HashSet<usize> = generated_child_set
                .difference(&all_ancestors)
                .copied()
                .collect();
            if diff != head {
                return false;
            }
        }

        return true;
    }
}

#[cfg(test)]
mod tests;
