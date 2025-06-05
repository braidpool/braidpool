//! Braid data structure and algorithms
//!
//! This module provides tools for manipulating braids, which are directed acyclic graphs (DAGs)
//! where each node (bead) can have multiple parents and children.

use std::collections::{HashMap, HashSet};

pub mod io_json;

use num::BigUint;

/// A type alias for a bead (A 256-bit uint representing a block hash)
pub type BeadHash = BigUint;

/// A type alias for work (A 256-bit uint representing work)
pub type Work = BigUint;

/// A type alias for target (A 256-bit uint representing work)
#[allow(dead_code)] // this is only used by the simulator so far
pub type Target = BigUint;

/// A type alias for a map from bead to its parents or children
pub type Relatives = HashMap<BeadHash, HashSet<BeadHash>>;

/// A type alias for a map from bead to its work
pub type BeadWork = HashMap<BeadHash, Work>;

/// Given a dict of {bead: {parents}}, return the set of beads which have no parents
pub fn geneses(parents: &Relatives) -> HashSet<BeadHash> {
    let mut retval = HashSet::new();
    for (b, p) in parents {
        if p.is_empty() {
            retval.insert(b.clone());
        }
    }
    retval
}

/// Given a dict of {bead: {parents}}, return the set of beads which have no children
pub fn tips(parents: &Relatives, children: Option<&Relatives>) -> HashSet<BeadHash> {
    let children_map = match children {
        Some(c) => c.clone(),
        None => reverse(parents),
    };
    geneses(&children_map)
}

/// Given a dict of {bead: {parents}}, compute the corresponding {bead: {children}} (or vice-versa)
pub fn reverse(parents: &Relatives) -> Relatives {
    let mut children: Relatives = HashMap::new();

    // Add all parent-child relationships
    for (bead, bparents) in parents {
        for p in bparents {
            children
                .entry(p.clone())
                .or_insert_with(HashSet::new)
                .insert(bead.clone());
        }

        // Ensure all beads are in the children map, even if they have no children
        children.entry(bead.clone()).or_insert_with(HashSet::new);
    }

    children
}

/// Given a set of beads, compute the set of all children of all beads
pub fn generation(beads: &HashSet<BeadHash>, children: &Relatives) -> HashSet<BeadHash> {
    let mut retval = HashSet::new();
    for b in beads {
        if let Some(child_set) = children.get(b) {
            for child in child_set {
                retval.insert(child.clone());
            }
        }
    }
    retval
}

/// Gets all ancestors for a bead, filling in ancestors of any other ancestors encountered
pub fn all_ancestors<'a>(
    b: &BeadHash,
    parents: &Relatives,
    ancestors: &'a mut HashMap<BeadHash, HashSet<BeadHash>>,
) -> &'a HashMap<BeadHash, HashSet<BeadHash>> {
    let mut work_stack = vec![(b.clone(), false)]; // (bead, is_processed)

    while !work_stack.is_empty() {
        let (current, is_processed) = work_stack.pop().unwrap();

        if is_processed {
            // We've finished processing all parents, compute ancestors
            let mut current_ancestors = HashSet::new();
            if let Some(current_parents) = parents.get(&current) {
                for p in current_parents {
                    current_ancestors.insert(p.clone());
                }

                // Update with ancestors of all parents
                for p in current_parents {
                    if let Some(parent_ancestors) = ancestors.get(p) {
                        for a in parent_ancestors {
                            current_ancestors.insert(a.clone());
                        }
                    }
                }
            }

            ancestors.insert(current, current_ancestors);
        } else {
            // Mark as being processed
            work_stack.push((current.clone(), true));

            // Add any unprocessed parents to the stack
            if let Some(current_parents) = parents.get(&current) {
                for p in current_parents {
                    if !ancestors.contains_key(p) {
                        work_stack.push((p.clone(), false));
                    }
                }
            }
        }
    }

    ancestors
}

/// Given the seed of the next cohort, build an ancestor/descendant set for each visited bead
pub fn cohorts(
    parents: &Relatives,
    children: Option<&Relatives>,
    initial_cohort: Option<&HashSet<BeadHash>>,
) -> Vec<HashSet<BeadHash>> {
    let child_map = match children {
        Some(c) => c.clone(),
        None => reverse(parents),
    };

    let dag_tips = tips(parents, Some(&child_map));
    let mut cohort = match initial_cohort {
        Some(c) => c.clone(),
        None => geneses(parents),
    };

    let mut result = Vec::new();
    let mut oldcohort = HashSet::new();
    let mut head = cohort.clone();
    let mut tail = cohort.clone();

    'outer: loop {
        let mut ancestors: HashMap<BeadHash, HashSet<BeadHash>> = HashMap::new();
        for h in &head {
            ancestors.insert(h.clone(), HashSet::new()); // Don't let head have ancestors to stop iteration
        }

        cohort = head.clone(); // Initial cohort is the head

        'inner: loop {
            // Calculate new tail
            if head.is_empty() {
                break 'outer; // StopIteration and return
            }

            for b in cohort.difference(&oldcohort) {
                if let Some(children_set) = child_map.get(b) {
                    for child in children_set {
                        tail.insert(child.clone());
                    }
                }
            }

            // Add any beads in oldcohort but not in cohort
            for b in oldcohort.difference(&cohort) {
                tail.insert(b.clone());
            }

            // If there are any tips in cohort, add tips to tail
            let mut has_tips = false;
            for tip in &dag_tips {
                if cohort.contains(tip) {
                    has_tips = true;
                    break;
                }
            }

            if has_tips {
                for tip in &dag_tips {
                    if !cohort.contains(tip) {
                        tail.insert(tip.clone());
                    }
                }
            } else {
                // If there are no tips in cohort subtract off cohort
                tail = tail.difference(&cohort).cloned().collect();
            }

            oldcohort = cohort.clone(); // Copy so we can tell if new tail has changed anything

            // Calculate ancestors
            for t in &tail {
                if !ancestors.contains_key(t) {
                    all_ancestors(t, parents, &mut ancestors);
                }
            }

            // Calculate cohort
            cohort = HashSet::new();
            for (_, ancestor_set) in &ancestors {
                for a in ancestor_set {
                    cohort.insert(a.clone());
                }
            }

            // Check termination cases
            let all_tips_in_cohort = dag_tips.iter().all(|tip| cohort.contains(tip));

            if all_tips_in_cohort {
                // Cohort contains all tips
                head.clear(); // StopIteration and return
                break 'inner; // and yield the current cohort
            }

            let all_ancestors_match_cohort = !tail.is_empty()
                && tail
                    .iter()
                    .all(|t| ancestors.get(t).map_or(false, |a| *a == cohort));

            if !cohort.is_empty() && all_ancestors_match_cohort {
                // Standard cohort case
                head = tail.clone(); // Head of next cohort is tail from previous iteration
                break 'inner; // Yield successful cohort
            }

            if cohort == oldcohort {
                // Cohort hasn't changed, we may be looping
                let all_tips_in_tail = dag_tips.iter().all(|tip| tail.contains(tip));

                if all_tips_in_tail {
                    // Tail contains all tips but we didn't form a cohort
                    head.clear();
                    for t in &tail {
                        cohort.insert(t.clone());
                    }
                    tail.clear();
                    break 'inner; // Yield cohort+tail
                }

                for t in &tail {
                    cohort.insert(t.clone());
                }
            }
        }

        if !cohort.is_empty() {
            result.push(cohort.clone());
        }

        oldcohort.clear();
    }

    result
}

/// Given a cohort as a set of beads, compute its tail
#[allow(dead_code)]
pub fn cohort_tail(
    cohort: &HashSet<BeadHash>,
    parents: &Relatives,
    children: Option<&Relatives>,
) -> HashSet<BeadHash> {
    let children_map = match children {
        Some(c) => c.clone(),
        None => reverse(parents),
    };

    // In Python: cohort_head(cohort, parents=children, children=parents)
    // This means we need to swap parents and children
    cohort_head(cohort, &children_map, Some(parents))
}

/// Given a cohort as a set of beads, compute its head
pub fn cohort_head(
    cohort: &HashSet<BeadHash>,
    parents: &Relatives,
    children: Option<&Relatives>,
) -> HashSet<BeadHash> {
    let children_map = match children {
        Some(c) => c.clone(),
        None => reverse(parents),
    };

    // In Python: generation(generation(cohort, parents) - cohort, children)
    let parent_gen = generation(cohort, parents);
    let parent_gen_minus_cohort: HashSet<_> = parent_gen.difference(cohort).cloned().collect();
    let tail = generation(&parent_gen_minus_cohort, &children_map);

    let cohort_tips = geneses(parents);

    if tail.is_empty() || tail.iter().any(|t| cohort_tips.contains(t)) {
        return cohort_tips;
    }

    tail
}

/// Given a set of beads (which generally will be a cohort), return the sub-DAG corresponding
/// to only those beads. That is, compute the parents dict: {p: {children} for p in beads} such
/// that the returned parents dict contains only the beads in <beads> and the parents of all
/// beads are only those parents within <beads>.
///
/// The result has the properties:
///     geneses(sub_braid(beads, parents)) = cohort_head(beads, parents)
///     tips(sub_braid(beads, parents)) = cohort_tail(beads, parents)
///     cohorts(sub_braid(beads, parents)) == [beads]
pub fn sub_braid(beads: &HashSet<BeadHash>, parents: &Relatives) -> Relatives {
    let mut result = Relatives::new();

    for b in beads {
        let mut sub_parents = HashSet::new();
        if let Some(bparents) = parents.get(b) {
            for p in bparents {
                if beads.contains(p) {
                    sub_parents.insert(p.clone());
                }
            }
        }
        result.insert(b.clone(), sub_parents);
    }

    result
}

/// Find the work in descendants
pub fn descendant_work(
    parents: &Relatives,
    children: Option<&Relatives>,
    bead_work: &BeadWork,
    in_cohorts: Option<&Vec<HashSet<BeadHash>>>,
) -> HashMap<BeadHash, Work> {
    let children_map = match children {
        Some(c) => c.clone(),
        None => reverse(parents),
    };

    let mut previous_work = Work::from(0u64);
    let cohorts = match in_cohorts {
        Some(c) => c.iter().rev().cloned().collect::<Vec<_>>(),
        None => cohorts(&children_map, Some(parents), None),
    };

    let mut retval = HashMap::new();

    for c in cohorts {
        let sub_children = sub_braid(&c, &children_map);
        let mut sub_descendants = HashMap::new();

        // Calculate work for each bead in this cohort
        for b in &c {
            all_ancestors(b, &sub_children, &mut sub_descendants);

            // Start with the bead's own work
            let mut b_work = bead_work.get(b).cloned().unwrap();

            // Add work from descendants within this cohort
            if let Some(descendants) = sub_descendants.get(b) {
                for a in descendants {
                    b_work += bead_work.get(a).cloned().unwrap();
                }
            }

            // Add work from all previous cohorts
            b_work += previous_work.clone();

            retval.insert(b.clone(), b_work);
        }

        // Update previous_work with sum of all work in this cohort
        previous_work += c
            .iter()
            .map(|b| bead_work.get(b).cloned().unwrap())
            .sum::<Work>();
    }

    retval
}

/// A custom comparison function for sorting beads
pub fn bead_cmp(
    a: &BeadHash,
    b: &BeadHash,
    dwork: &HashMap<BeadHash, Work>,
    awork: &HashMap<BeadHash, Work>,
) -> std::cmp::Ordering {
    let zero = Work::from(0u64);
    let a_dwork = dwork.get(a).unwrap_or(&zero);
    let b_dwork = dwork.get(b).unwrap_or(&zero);

    if a_dwork < b_dwork {
        return std::cmp::Ordering::Less;
    }
    if a_dwork > b_dwork {
        return std::cmp::Ordering::Greater;
    }

    let a_awork = awork.get(a).unwrap_or(&zero);
    let b_awork = awork.get(b).unwrap_or(&zero);

    if a_awork < b_awork {
        return std::cmp::Ordering::Less;
    }
    if a_awork > b_awork {
        return std::cmp::Ordering::Greater;
    }

    // Same work, fall back on block hash comparison
    if a > b {
        return std::cmp::Ordering::Less;
    }
    if a < b {
        return std::cmp::Ordering::Greater;
    }
    std::cmp::Ordering::Equal
}

/// Return a sorting function for beads based on work
#[allow(dead_code)]
pub fn work_sort_key<'a>(
    parents: &'a Relatives,
    children: Option<&'a Relatives>,
    bead_work: &'a BeadWork,
) -> impl Fn(&BeadHash, &BeadHash) -> std::cmp::Ordering + 'a {
    let children = match children {
        Some(c) => c.clone(),
        None => reverse(parents),
    };

    let dwork = descendant_work(parents, Some(&children), &bead_work, None);
    let awork = descendant_work(&children, Some(parents), &bead_work, None);

    move |a, b| bead_cmp(a, b, &dwork, &awork)
}

/// Find the highest (descendant) work path, by following the highest weights through the DAG
#[allow(dead_code)]
pub fn highest_work_path(
    parents: &Relatives,
    children: Option<&Relatives>,
    bead_work: &BeadWork,
) -> Vec<BeadHash> {
    let children = match children {
        Some(c) => c.clone(),
        None => reverse(parents),
    };

    // Calculate descendant and ancestor work for proper tie-breaking
    let dwork = descendant_work(parents, Some(&children), &bead_work, None);
    let awork = descendant_work(&children, Some(parents), &bead_work, None);

    // Find the genesis bead with maximum work using full comparison logic
    let genesis_beads = geneses(parents);
    let max_genesis = genesis_beads
        .iter()
        .max_by(|a, b| bead_cmp(a, b, &dwork, &awork))
        .unwrap()
        .clone();

    let mut hwpath = vec![max_genesis];
    let dag_tips = tips(parents, Some(&children));

    // Follow the highest work path until we reach a tip
    while !dag_tips.contains(&hwpath[hwpath.len() - 1]) {
        // Get the children of the last bead in the path
        let last_bead = &hwpath[hwpath.len() - 1];
        let children_set = match children.get(last_bead) {
            Some(c) => c,
            None => break,
        };

        // Find child with maximum work using full comparison logic
        let max_child = children_set
            .iter()
            .max_by(|a, b| bead_cmp(a, b, &dwork, &awork))
            .unwrap()
            .clone();

        hwpath.push(max_child);
    }

    hwpath
}

/// Number the beads in a braid sequentially in topological order starting at genesis
#[allow(dead_code)]
pub fn number_beads(hashed_parents: &Relatives) -> Relatives {
    let mut bead_id: u64 = 0;
    let mut parents = Relatives::new();
    let mut bead_ids = HashMap::new();
    let mut reverse_bead_ids = HashMap::new();

    // First handle genesis beads
    for bead_hash in geneses(hashed_parents) {
        bead_ids.insert(bead_hash.clone(), BeadHash::from(bead_id));
        reverse_bead_ids.insert(BeadHash::from(bead_id), bead_hash);
        parents.insert(BeadHash::from(bead_id), HashSet::new());
        bead_id += 1;
    }

    // Traverse the DAG in BFS in the descendant direction
    let hashed_children = reverse(hashed_parents);
    let mut next_parents = parents.clone();

    while !next_parents.is_empty() {
        let working_parents = next_parents.clone();
        next_parents = Relatives::new();

        for (parent, _) in working_parents {
            if let Some(parent_hash) = reverse_bead_ids.get(&parent) {
                if let Some(children_set) = hashed_children.get(parent_hash) {
                    for bead_hash in children_set {
                        let this_id;

                        if let Some(id) = bead_ids.get(bead_hash) {
                            this_id = id.clone();
                        } else {
                            this_id = BeadHash::from(bead_id);
                            bead_ids.insert(bead_hash.clone(), this_id.clone());
                            reverse_bead_ids.insert(this_id.clone(), bead_hash.clone());
                            bead_id += 1;
                        }

                        parents
                            .entry(this_id.clone())
                            .or_insert_with(HashSet::new)
                            .insert(parent.clone());
                        next_parents
                            .entry(this_id)
                            .or_insert_with(HashSet::new)
                            .insert(parent.clone());
                    }
                }
            }
        }
    }

    parents
}

#[cfg(test)]
mod tests;
