use crate::bead::Bead;
use crate::utils::{retrieve_bead, BeadHash};
use serde::Serialize;
use std::cmp::Ordering;
use std::collections::{HashMap, HashSet};

pub const FIXED_BEAD_WORK: u32 = 1;
#[derive(Clone, Debug, Serialize, PartialEq)]

pub(crate) struct Cohort(HashSet<usize>);

pub enum AddBeadStatus {
    DagAlreadyContainsBead,
    InvalidBead,
    BeadAdded,
    ParentsNotYetReceived,
}

#[derive(Clone, Debug)]

pub struct Braid {
    pub(crate) beads: Vec<Bead>,
    pub(crate) tips: HashSet<usize>,
    pub(crate) cohorts: Vec<Cohort>,
    pub(crate) orphan_beads: Vec<usize>,
    pub(crate) genesis_beads: HashSet<usize>,
    pub(crate) bead_index_mapping: HashMap<BeadHash, usize>,
}

impl Braid {
    // All public funtions go here!
    pub fn new(genesis_beads: HashSet<Bead>) -> Self {
        let mut beads = Vec::new();
        let mut bead_indices = HashSet::new();
        let mut bead_index_mapping = HashMap::new();

        for (index, bead) in genesis_beads.into_iter().enumerate() {
            beads.push(bead.clone());
            bead_indices.insert(index);
            bead_index_mapping.insert(bead.block_header.block_hash(), index);
        }

        Braid {
            beads,
            tips: bead_indices.clone(),
            cohorts: vec![Cohort(bead_indices.clone())],
            orphan_beads: Vec::new(),
            genesis_beads: bead_indices,
            bead_index_mapping,
        }
    }
}

impl Braid {
    /// Attempts to extend the braid with the given bead.
    /// Returns true if the bead successfully extended the braid, false otherwise.
    pub fn extend(&mut self, bead: &Bead) -> bool {
        // No parents: bad block
        if bead.committed_metadata.parents.is_empty() {
            return false;
        }
        // Don't have all parents
        for parent_hash in &bead.committed_metadata.parents {
            // Check if we already have this parent in our beads
            let parent_exists = self
                .beads
                .iter()
                .any(|b| b.block_header.block_hash() == *parent_hash);

            if !parent_exists {
                // Try to retrieve the parent
                if let Some(retrieved_bead) = retrieve_bead(*parent_hash) {
                    self.extend(&retrieved_bead);
                } else {
                    // Parent not found and can't be retrieved
                    return false;
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
            return false;
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
                if let Some(parent_index) = self
                    .beads
                    .iter()
                    .position(|b| b.block_header.block_hash() == *parent_hash)
                {
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
                && (self.tips.len() == found_parent_indices.len()
                    || cohort.0.len() == found_parent_indices.len())
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
        } else {
            self.cohorts.clear();
        }

        // Remove parents from tips if present
        for parent_hash in &bead.committed_metadata.parents {
            // Find the index of the parent bead
            if let Some(parent_index) = self
                .beads
                .iter()
                .position(|b| b.block_header.block_hash() == *parent_hash)
            {
                self.tips.remove(&parent_index);
            }
        }

        // Add the new bead's index to tips
        self.tips.insert(new_bead_index);

        // Construct a sub-braid from dangling and compute any new cohorts
        // Here, we just create a new cohort with dangling beads
        if !dangling.is_empty() {
            self.cohorts.push(Cohort(dangling));
        }

        true
    }

    //returning the genesis indices
    fn genesis(&mut self, parents: HashMap<usize, HashSet<usize>>) -> HashSet<usize> {
        let mut current_beads: Vec<Bead> = Vec::new();
        for bead_idx in parents {
            let current_bead = self.beads[bead_idx.0].clone();
            current_beads.push(current_bead.clone());
        }
        let mut genesis_bead_indices: HashSet<usize> = HashSet::new();
        let mut idx = 0;
        for bead in current_beads {
            let bead_parents = bead.committed_metadata.parents;
            if bead_parents.len() == 0 {
                genesis_bead_indices.insert(idx);
            }
            idx += 1;
        }
        return genesis_bead_indices;
    }

    fn tips(&mut self, parents: HashMap<usize, HashSet<usize>>) -> HashSet<usize> {
        let mut bead_indices_mapping: HashMap<usize, usize> = HashMap::new();
        let mut tips_indices: HashSet<usize> = HashSet::new();
        for parent_bead_idx in parents {
            bead_indices_mapping.insert(parent_bead_idx.0, 0);
        }
        let current_beads = self.beads.clone();
        for bead in current_beads {
            let parents = bead.committed_metadata.parents;
            for blockhash in parents.iter() {
                let parent_idx = self.bead_index_mapping[blockhash];
                if let Some(val) = bead_indices_mapping.get_mut(&parent_idx) {
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

    fn reverse(
        &mut self,
        parents: HashMap<usize, HashSet<usize>>,
    ) -> HashMap<usize, HashSet<usize>> {
        let mut bead_children_mapping: HashMap<usize, HashSet<usize>> = HashMap::new();
        for bead_idx in parents {
            bead_children_mapping.insert(bead_idx.0, HashSet::new());
        }
        let current_beads = self.beads.clone();
        for bead in current_beads {
            let parents = bead.committed_metadata.parents;
            for blockhash in parents.iter() {
                let parent_idx = self.bead_index_mapping[blockhash];
                if let Some(val) = bead_children_mapping.get_mut(&parent_idx) {
                    let current_bead_idx = self.bead_index_mapping[&bead.block_header.block_hash()];
                    val.insert(current_bead_idx);
                }
            }
        }
        return bead_children_mapping;
    }

    fn generation(
        &mut self,
        beads_indices: HashSet<usize>,
        children: Option<HashMap<usize, HashSet<usize>>>,
    ) -> HashSet<usize> {
        let children_set: HashSet<usize> = HashSet::new();
        let mut parents: HashMap<usize, HashSet<usize>> = HashMap::new();
        for idx in beads_indices {
            parents.insert(idx, HashSet::new());
        }
        //values of children beads/mapping is always provided though
        let bead_children_mapping = match children {
            Some(children) => children,
            None => self.reverse(parents),
        };
        let children_set_ref = children_set.clone();
        for (_bead, children_beads_set) in bead_children_mapping.iter() {
            let set_val: HashSet<&usize> = children_set_ref.union(children_beads_set).collect();
            for val in set_val {
                children_set_ref.clone().insert(*val);
            }
        }

        return children_set_ref;
    }

    fn get_all_ancestors<'a>(
        &mut self,
        current_block_hash: BeadHash,
        ancestors: &'a mut HashMap<usize, HashSet<usize>>,
        parents: HashMap<usize, HashSet<usize>>,
    ) -> &'a mut HashMap<usize, HashSet<usize>> {
        let current_block_idx = self.bead_index_mapping[&current_block_hash];
        if let Some(current_bead_ancestors) = ancestors.get_mut(&current_block_idx) {
            current_bead_ancestors.clear();
            let parents_current_block = parents[&current_block_idx].clone();
            for idx in parents_current_block {
                current_bead_ancestors.insert(idx);
            }
        }
        for parent_idx in parents[&current_block_idx].clone() {
            let current_parent_blockhash = self.beads[parent_idx].block_header.block_hash();
            if ancestors.contains_key(&parent_idx) {
                self.get_all_ancestors(current_parent_blockhash, ancestors, parents.clone());
            }
            if let Some(current_bead_ancestors) = ancestors.clone().get_mut(&current_block_idx) {
                let parent_ancestors = ancestors[&parent_idx].clone();
                for ancestor in parent_ancestors {
                    current_bead_ancestors.insert(ancestor);
                }
            }
        }
        return ancestors;
    }

    fn cohort(
        &mut self,
        parents: HashMap<usize, HashSet<usize>>,
        children_or_not: Option<HashMap<usize, HashSet<usize>>>,
        inital_cohort: Option<&mut HashSet<usize>>,
    ) -> Vec<HashSet<usize>> {
        let children = match children_or_not {
            Some(val) => val,
            None => self.reverse(parents.clone()),
        };
        let braid_tips = self.tips(parents.clone());
        let cohort = match inital_cohort {
            Some(inital_cohort) => inital_cohort,
            None => &mut self.genesis(parents.clone()),
        };
        let mut generator: Vec<HashSet<usize>> = Vec::new();
        let mut oldcohort: HashSet<usize> = HashSet::new();
        let mut head = cohort.clone();
        let mut tail = cohort.clone();

        loop {
            let mut ancestor: HashMap<usize, HashSet<usize>> = HashMap::new();
            for b in head.clone() {
                ancestor.insert(b, HashSet::new());
            }

            let cohort = head.clone();
            loop {
                if head.len() == 0 {
                    break;
                }
                for bead in cohort.difference(&oldcohort) {
                    if let Some(children) = children.get(bead) {
                        for child in children {
                            tail.insert(*child);
                        }
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

                if has_tips {
                    for bead in braid_tips.difference(&cohort) {
                        tail.insert(*bead);
                    }
                } else {
                    for t in cohort.clone() {
                        tail.remove(&t);
                    }
                }
                let oldcohort = cohort.clone();
                let mut key_set: HashSet<usize> = HashSet::new();
                let t: HashSet<&usize> = ancestor.keys().collect();
                for temp in t {
                    key_set.insert(*temp);
                }
                for bead in tail.difference(&key_set) {
                    let current_bead_blockhash =
                        self.beads[*bead].clone().block_header.block_hash();
                    self.get_all_ancestors(current_bead_blockhash, &mut ancestor, parents.clone());
                }

                let mut cohort: HashSet<usize> = HashSet::new();
                for (_key, val) in ancestor.clone() {
                    for ancestor_value in val {
                        cohort.insert(ancestor_value);
                    }
                }
                let a: HashSet<&usize> = cohort.intersection(&braid_tips).collect();
                if a.len() == cohort.len() {
                    head.clear();
                    break;
                }
                if cohort.is_empty() == false {
                    let mut flag = false;
                    for t in tail.clone() {
                        if let Some(value) = ancestor.get(&t) {
                            for current_ancestor_val in value {
                                if cohort.contains(current_ancestor_val) == false {
                                    flag = true;
                                    break;
                                }
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
                        for bead in tail.clone() {
                            cohort.insert(bead);
                        }
                        tail.clear();
                        break;
                    }
                    for bead in tail.clone() {
                        cohort.insert(bead);
                    }
                }
            }
            if !cohort.is_empty() {
                generator.push(cohort.clone());
            }

            oldcohort.clear();
        }
        generator
    }

    fn cohort_head(
        &mut self,
        cohort: HashSet<usize>,
        parents: HashMap<usize, HashSet<usize>>,
        children: Option<HashMap<usize, HashSet<usize>>>,
    ) -> HashSet<usize> {
        let mut bead_indices: HashSet<usize> = HashSet::new();
        for cohort_bead_idx in cohort.clone() {
            bead_indices.insert(cohort_bead_idx);
        }
        let cohort_children: HashSet<usize> =
            self.generation(bead_indices.clone(), Some(parents.clone()));
        let cohort_children_ref: HashSet<usize> = cohort_children.clone();
        let diff: HashSet<&usize> = cohort_children_ref.difference(&cohort).collect();
        let mut cohort_children_ref: HashSet<usize> = HashSet::new();
        for child in diff {
            cohort_children_ref.insert(*child);
        }
        let tail = self.generation(cohort_children_ref, children.clone());

        let cohort_tips = self.genesis(parents);
        let mut flag = false;
        for t in tail.clone() {
            if cohort_tips.contains(&t) {
                flag = true;
                break;
            }
        }
        if tail.clone().is_empty() || flag {
            return cohort_tips;
        }

        return tail;
    }

    fn cohort_tail(
        &mut self,
        cohort: HashSet<usize>,
        parents: HashMap<usize, HashSet<usize>>,
        children: Option<HashMap<usize, HashSet<usize>>>,
    ) -> HashSet<usize> {
        let childs = match children.clone() {
            Some(childrens) => childrens,
            None => self.reverse(parents.clone()),
        };

        return self.cohort_head(cohort, childs, Some(parents));
    }
    fn get_sub_braid(
        &mut self,
        beads: HashSet<usize>,
        parents: HashMap<usize, HashSet<usize>>,
    ) -> HashMap<usize, HashSet<usize>> {
        let mut sub_braid: HashMap<usize, HashSet<usize>> = HashMap::new();
        for bead in beads.clone() {
            let mut current_bead_sub: HashSet<usize> = HashSet::new();
            if let Some(current_bead_parent) = parents.get(&bead) {
                for parent_bead_idx in current_bead_parent {
                    if beads.clone().contains(parent_bead_idx) {
                        current_bead_sub.insert(*parent_bead_idx);
                    }
                }
            }
            sub_braid.insert(bead, current_bead_sub);
        }

        return sub_braid;
    }
    //descendant work for braidpool based POW (Proof of Work)
    fn descendant_work(
        &mut self,
        parents: HashMap<usize, HashSet<usize>>,
        children_or_not: Option<HashMap<usize, HashSet<usize>>>,
        bead_work_or_not: Option<HashMap<usize, u32>>,
        in_cohorts_or_not: Option<Vec<HashSet<usize>>>,
    ) -> HashMap<usize, u32> {
        let children = match children_or_not {
            Some(val) => val,
            None => self.reverse(parents.clone()),
        };
        let bead_work = match bead_work_or_not {
            Some(val) => val,
            None => {
                let mut work: HashMap<usize, u32> = HashMap::new();
                for bead_idx in parents.clone() {
                    work.insert(bead_idx.0, FIXED_BEAD_WORK);
                }
                work
            }
        };
        let mut previous_work: u32 = 0;
        let rev_cohorts = match in_cohorts_or_not {
            Some(val) => {
                let mut val_ref = val;
                val_ref.reverse();
                val_ref
            }
            None => self.cohort(children.clone(), None, None),
        };
        let mut ret_val: HashMap<usize, u32> = HashMap::new();
        for curr_cohort in rev_cohorts {
            let sub_children = self.get_sub_braid(curr_cohort.clone(), children.clone());
            let mut sub_descendants: HashMap<usize, HashSet<usize>> = HashMap::new();
            for bead in curr_cohort.clone() {
                let current_bead_hash = self.beads[bead].block_header.block_hash();
                self.get_all_ancestors(
                    current_bead_hash,
                    &mut sub_descendants,
                    sub_children.clone(),
                );
                let mut work_summation: u32 = 0;
                if let Some(descendants) = sub_descendants.get(&bead) {
                    for descendant in descendants {
                        work_summation = work_summation + bead_work[descendant];
                    }
                }
                ret_val.insert(bead, previous_work + bead_work[&bead] + work_summation);
            }
            let mut work_summation: u32 = 0;
            for bead in curr_cohort {
                work_summation += bead_work[&bead];
            }
            previous_work = previous_work + work_summation;
        }
        return ret_val;
    }
    //we will have to return the Ordering type for comparator

    fn bead_cmp<'a>(
        &mut self,
        a: usize,
        b: usize,
        dwork: HashMap<usize, u32>,
        awork_or_not: Option<HashMap<usize, u32>>,
    ) -> Ordering {
        if dwork[&a] < dwork[&b] {
            return Ordering::Less;
        }
        if dwork[&a] > dwork[&b] {
            return Ordering::Greater;
        }

        let awork = match awork_or_not {
            Some(val) => val,
            None => {
                panic!("No ancestor work supplied");
            }
        };
        if awork[&a] < awork[&b] {
            return Ordering::Less;
        }
        if awork[&a] > awork[&b] {
            return Ordering::Greater;
        }
        if a > b {
            return Ordering::Less;
        }
        if a < b {
            return Ordering::Greater;
        }
        return Ordering::Equal;
    }

    fn work_sort_key(
        &mut self,
        parents: HashMap<usize, HashSet<usize>>,
        children_or_none: Option<HashMap<usize, HashSet<usize>>>,
        bead_work_or_not: Option<HashMap<usize, u32>>,
    ) -> impl Fn(usize, usize) -> Ordering {
        let children = match children_or_none {
            Some(child) => child,
            None => self.reverse(parents.clone()),
        };
        let bead_work = match bead_work_or_not {
            Some(work) => work,
            None => {
                let mut work: HashMap<usize, u32> = HashMap::new();
                for bead in parents.clone() {
                    work.insert(bead.0, FIXED_BEAD_WORK);
                }
                work
            }
        };
        let descendant_work = self.descendant_work(
            parents.clone(),
            Some(children.clone()),
            Some(bead_work.clone()),
            None,
        );
        let ancestor_work = self.descendant_work(
            children.clone(),
            Some(parents),
            Some(bead_work.clone()),
            None,
        );

        // Pre-calculate all the comparisons and store them in a struct that implements Copy
        move |a: usize, b: usize| {
            // Compare descendant work
            if descendant_work[&a] < descendant_work[&b] {
                return Ordering::Less;
            }
            if descendant_work[&a] > descendant_work[&b] {
                return Ordering::Greater;
            }

            // Compare ancestor work
            if ancestor_work[&a] < ancestor_work[&b] {
                return Ordering::Less;
            }
            if ancestor_work[&a] > ancestor_work[&b] {
                return Ordering::Greater;
            }

            // Compare indices
            if a > b {
                return Ordering::Less;
            }
            if a < b {
                return Ordering::Greater;
            }

            Ordering::Equal
        }
    }

    fn highest_work_path(
        &mut self,
        parents: HashMap<usize, HashSet<usize>>,
        children_or_none: Option<HashMap<usize, HashSet<usize>>>,
        bead_work_or_not: Option<HashMap<usize, u32>>,
    ) -> Vec<usize> {
        let children = match children_or_none {
            Some(child) => child,
            None => self.reverse(parents.clone()),
        };
        let bead_work = match bead_work_or_not {
            Some(work) => work,
            None => {
                let mut work: HashMap<usize, u32> = HashMap::new();
                for bead in parents.clone() {
                    work.insert(bead.0, FIXED_BEAD_WORK);
                }
                work
            }
        };
        let descendant_work = self.descendant_work(
            parents.clone(),
            Some(children.clone()),
            Some(bead_work.clone()),
            None,
        );
        let ancestor_work = self.descendant_work(
            children.clone(),
            Some(parents.clone()),
            Some(bead_work.clone()),
            None,
        );
        //getting the genesis beads and for each evaluating the highest
        //work genesis bead to be included inside the highest work path
        let genesis_beads = self.genesis(parents.clone());
        //getting the maxima out of the genesis beads
        let max_gensis_bead = match genesis_beads.iter().max_by(|a, b| {
            self.bead_cmp(
                **a,
                **b,
                descendant_work.clone(),
                Some(ancestor_work.clone()),
            )
            .clone()
        }) {
            Some(val) => val,
            None => {
                panic!("An error occurred while fetching the highest work bead");
            }
        };
        //populating the highest work path with indices representing the beads involved from the
        //entire braid for computation of highest work path
        let mut highest_work_path: Vec<usize> = vec![*max_gensis_bead];
        //getting the tip beads
        let tips_beads: HashSet<usize> = self.tips(parents.clone());
        //computing while iterating and processing the previous best nodes and generating all
        //its corresponding set of childrens for getting further best maximum work path nodes
        while !tips_beads.contains(&highest_work_path[highest_work_path.len() - 1]) {
            let mut beads_indices: HashSet<usize> = HashSet::new();
            beads_indices.insert(highest_work_path[highest_work_path.len() - 1]);
            //generating the child sets for the previous best bead
            let current_bead_children_set = self.generation(beads_indices, Some(children.clone()));
            //getting the maximum via comparator
            let max_bead = match current_bead_children_set.iter().max_by(|a, b| {
                self.bead_cmp(
                    **a,
                    **b,
                    descendant_work.clone(),
                    Some(ancestor_work.clone()),
                )
                .clone()
            }) {
                Some(val) => val,
                None => {
                    panic!()
                }
            };
            highest_work_path.push(*max_bead);
        }

        return Vec::new();
    }

    fn check_cohort(
        &mut self,
        cohort: HashSet<usize>,
        parents: HashMap<usize, HashSet<usize>>,
        children_or_none: Option<HashMap<usize, HashSet<usize>>>,
    ) -> bool {
        let children = match children_or_none {
            Some(childs) => childs,
            None => self.reverse(parents.clone()),
        };
        return self.check_cohort_ancestors(
            Some(children.clone()),
            cohort.clone(),
            parents.clone(),
        ) & self.check_cohort_ancestors(Some(parents.clone()), cohort.clone(), children);
    }
    fn check_cohort_ancestors(
        &mut self,
        children_or_none: Option<HashMap<usize, HashSet<usize>>>,
        cohort: HashSet<usize>,
        parents: HashMap<usize, HashSet<usize>>,
    ) -> bool {
        let children = match children_or_none {
            Some(child) => child,
            None => self.reverse(parents.clone()),
        };
        let mut ancestors: HashMap<usize, HashSet<usize>> = HashMap::new();
        let mut all_ancestors: HashSet<usize> = HashSet::new();

        let head = self.cohort_head(cohort.clone(), parents.clone(), Some(children.clone()));
        for bead in cohort.clone() {
            let current_bead_hash = self.beads[bead].block_header.block_hash();
            self.get_all_ancestors(current_bead_hash, &mut ancestors, parents.clone());
            if let Some(ancestor_beads) = ancestors.get(&bead) {
                for ancestor_bead in ancestor_beads {
                    all_ancestors.insert(*ancestor_bead);
                }
            }
        }
        let diff: HashSet<&usize> = all_ancestors.difference(&cohort).collect();
        let mut all_ancestors_ref = all_ancestors.clone();
        for bead in diff {
            if all_ancestors.contains(bead) {
                all_ancestors_ref.remove(bead);
            }
        }
        if all_ancestors.is_empty() == false {
            let generated_child_set =
                self.generation(all_ancestors.clone(), Some(children.clone()));
            let diff: HashSet<&usize> = generated_child_set.difference(&all_ancestors).collect();
            let mut diff_ref: HashSet<usize> = HashSet::new();
            for bead in diff {
                diff_ref.insert(*bead);
            }
            if diff_ref != head {
                return false;
            }
        }

        return true;
    }
}

#[cfg(test)]
mod tests;
