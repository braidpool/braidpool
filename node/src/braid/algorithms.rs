use super::{BeadIdx, BeadSet, Cohort, Relatives};
use bitcoin::pow::Work;
use std::cmp::Ordering;
use std::collections::{HashMap, HashSet};

/// Helper to create Work from bytes for zero value
fn zero_work() -> Work {
    Work::from_be_bytes([0u8; 32])
}

/// Returns the set of **genesis beads** from a given Braid object.
///
/// A **genesis bead** is defined as a bead that has no parents, i.e., it is a root node in the Braid.
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
/// A `BeadSet` containing the indices of all beads that do not have any parents.
///
/// # Reference
///
/// For architectural context, refer to the [Braidpool Specification](https://github.com/braidpool/braidpool/blob/dev/docs/braidpool_spec.md).
pub fn geneses(parents: &Relatives) -> BeadSet {
    parents
        .iter()
        .filter(|(_, parent_set)| parent_set.is_empty())
        .map(|(bead_idx, _)| *bead_idx)
        .collect()
}

/// Returns the set of **tip beads** from child relationships.
///
/// A **tip bead** is defined as a bead that has no children (i.e., no other bead references it as a parent).
/// These beads represent the leaves or endpoints in the Braid structure.
///
/// # Arguments
///
/// * `children` - A map from each bead index to a `HashSet` of its child bead indices.
///
/// # Returns
///
/// A `BeadSet` containing the indices of all beads that are **not referenced** as a parent by any other bead.
pub fn tips(children: &Relatives) -> BeadSet {
    geneses(children)
}

/// Reverses the parent mapping of beads to generate a child mapping.
///
/// Given a mapping from each bead to its parent beads (`parents`), this function constructs
/// the reverse: a mapping from each bead to the set of **children** beads that reference it as a parent.
///
/// # Arguments
///
/// * `parents` - A `HashMap` where each key is a bead index, and the value is a `HashSet` of its parent bead indices.
///
/// # Returns
///
/// A `Relatives` where each key is a bead index, and the value is a set of its children.
pub fn reverse(parents: &Relatives) -> Relatives {
    let mut children = Relatives::new();

    for (bead, bparents) in parents {
        children.entry(*bead).or_default();
        for parent in bparents {
            children.entry(*parent).or_default().insert(*bead);
        }
    }
    children
}

/// Returns the complete set of **child beads** for a given set of bead indices.
///
/// This function computes the immediate children of a set of beads.
///
/// It is useful when traversing a Braid structure **forward** from a set of beads
/// to explore their direct descendants.
///
/// # Arguments
///
/// * `beads` - A `BeadSet` of bead indices whose children need to be found.
/// * `children` - A reference to a `Relatives` map representing bead → children mappings.
///
/// # Returns
///
/// A `BeadSet` containing all bead indices that are children of the given input beads.
pub fn generation(beads: &BeadSet, children: &Relatives) -> BeadSet {
    beads.iter().flat_map(|b| &children[b]).copied().collect()
}

/// Computes all ancestors for a set of beads using an iterative DFS algorithm with caching.
///
/// This function calculates the complete set of **ancestors** for each bead in the input `beads` set.
/// It uses an iterative Depth-First Search (DFS) approach to avoid recursion stack overflows and
/// efficiently builds the transitive closure of ancestors.
///
/// Ancestors are stored in the `ancestors` map (passed as `&mut Relatives`), where `ancestors[i]`
/// contains all direct and transitive parent indices of bead `i`.
///
/// It leverages a `cache` (`&mut Relatives`) to store and reuse previously computed ancestor sets,
/// processing only beads whose ancestors are not already fully cached.
/// This also helps in avoiding redundant computations across calls.
///
/// # Arguments
///
/// * `beads` - A `BeadSet` of bead indices for which to compute ancestors.
/// * `parents` - A `Relatives` map from bead index to its parent bead indices.
/// * `ancestors` - A mutable `Relatives` map to store the computed ancestors. It will be updated in-place.
/// * `cache` - A mutable `Relatives` map used to store and retrieve cached ancestor computations.
pub fn all_ancestors(bead: BeadIdx, parents: &Relatives, ancestors: &mut Relatives) {
    // If already computed, use cached result
    if ancestors.contains_key(&bead) {
        return;
    }

    // Build work stack for DFS (bead, is_processed)
    let mut work_stack: Vec<(BeadIdx, bool)> = vec![(bead, false)];

    while let Some((current, is_processed)) = work_stack.pop() {
        if is_processed {
            // We've finished processing all parents, compute ancestors
            let mut current_ancestors = BeadSet::new();

            // Add direct parents
            if let Some(parent_set) = parents.get(&current) {
                current_ancestors.extend(parent_set);
            }

            // Update with ancestors of all parents
            if let Some(parent_set) = parents.get(&current) {
                for parent_idx in parent_set {
                    if let Some(parent_ancestors) = ancestors.get(&parent_idx) {
                        current_ancestors.extend(parent_ancestors.iter().copied());
                    }
                }
            }

            // Insert into ancestors map
            ancestors.insert(current, current_ancestors.clone());
        } else {
            // Mark as being processed
            work_stack.push((current, true));

            // Add any unprocessed parents to the stack
            if let Some(parent_set) = parents.get(&current) {
                for parent_idx in parent_set {
                    if !ancestors.contains_key(parent_idx) {
                        work_stack.push((*parent_idx, false));
                    }
                }
            }
        }
    }
}

/// Computes the **cohorts** in a Braid, representing subgraphs (slices) bounded by graph cuts.
///
/// A **cohort** is a set of bead indices forming a layer where all included beads share the same
/// topological generation, i.e., all their ancestors lie strictly in earlier cohorts, and all
/// descendants lie strictly in later cohorts.
///
/// Graphically, this corresponds to a **graph cut**: a boundary line across the DAG such that
/// every bead on the right side of the cut has all beads on the left side as its ancestors.
///
/// # Arguments
///
/// * `parents` - A map from bead index to its parent indices, used for ancestry traversal.
/// * `children` - A map from bead index to its child indices. Required parameter.
/// * `initial_cohort` - Optional starting cohort (e.g., genesis beads). If `None`, it defaults to `geneses(parents)`.
/// * `ancestor_cache` - A mutable Relatives map of ancestors. Returns only ancestors *within* the cohort.
///
/// # Returns
///
/// A generator that yields `Cohort`, where each set represents a **cohort** in topological order.
/// Each cohort is disjoint and collectively they partition the beads in the Braid by graph cuts
pub fn cohorts(
    parents: &Relatives,
    children: &Relatives,
    initial_cohort: &Cohort,
    ancestor_cache: &mut Relatives,
) -> Vec<Cohort> {
    let dag_tips = tips(children);
    let mut cohort = if initial_cohort.is_empty() {
        geneses(parents)
    } else {
        initial_cohort.clone()
    };
    let mut oldcohort = Cohort::new();
    let mut head = cohort.clone(); // Starting boundary condition
    let mut tail = cohort.clone(); //  New bead frontier, expands by BFS to collect new ancestors
    let mut result = Vec::new();

    // Each iteration produces a cohort
    loop {
        // Create a local ancestors map which lets us see cohort boundaries
        let mut ancestors = Relatives::new();
        // Give the head no ancestors so that the algorithm doesn't look outside this cohort
        for h in &head {
            ancestors.insert(*h, BeadSet::new());
        }
        // The starting cohort for iteration is the head beads
        cohort = head.clone();

        // Expand until we find a graph cut (tail beads have same ancestors as cohort iteration)
        loop {
            // The head being empty is the flag set by the termination conditions that we'r done.
            if head.is_empty() {
                return result; // No cohort
            }

            // Add children of the newly added beads so we can compute their ancestors and see if
            // they should join the cohort.
            for b in cohort.difference(&oldcohort) {
                tail.extend(&children[b]);
            }

            // If there are any tips in cohort, add tips to tail
            if cohort.iter().any(|b| dag_tips.contains(b)) {
                tail.extend(dag_tips.difference(&cohort));
            } else {
                // If there are no tips in cohort subtract off cohort
                tail.retain(|t| !cohort.contains(t));
            }
            // Copy so we can tell if new tail has changed anything in the next iteration and prevent looping
            oldcohort.clear();
            oldcohort.extend(&cohort);

            // Calculate ancestors for beads in the tail, which recursively generates all ancestors
            for t in &tail {
                if !ancestors.contains_key(t) {
                    all_ancestors(*t, parents, &mut ancestors);
                }
            }

            // Calculate cohort, which is the union of all ancestors
            cohort.clear();
            cohort.extend(ancestors.values().flatten().copied());

            // We've reached the end of the Braid, yield everything left as the cohort
            if dag_tips.is_subset(&cohort) {
                head.clear();
                break;
            }
            // If everything in the tail is exactly the same and the same as the cohort, yield
            if !cohort.is_empty() && tail.iter().all(|t| ancestors.get(t) == Some(&cohort)) {
                head = tail.clone(); // Head of next cohort is tail from previous iteration
                break;
            }
            if cohort == oldcohort {
                // We hit the tips. Yield cohort (union of all tail ancestors) + tail
                if dag_tips.is_subset(&tail) {
                    head.clear();
                    cohort.extend(&tail);
                    break;
                } else {
                    // We haven't hit any tips, add the tail to the cohort so we don't loop here
                    cohort.extend(&tail);
                }
            }
        }

        // Add the computed ancestor set *within* the cohort to the cache
        ancestor_cache.extend(ancestors);
        // We found a cohort, there is no oldcohort
        oldcohort.clear();
        if !cohort.is_empty() {
            result.push(cohort);
        }
    }
}

/// Returns the **tail** of a given cohort in a Braid.
///
/// The **tail** refers to the immediate set of beads that topologically follow the current cohort
/// based on child relationships. It is conceptually the "head" of the reverse graph traversal,
/// where parent and child roles are conceptually flipped.
///
/// Internally, this function delegates to `cohort_head()` using the reversed direction
/// (i.e., treating children as parents and parents as children for the head calculation).
///
/// # Arguments
///
/// * `cohort` - The current `Cohort` whose tail is to be determined.
/// * `parents` - The `Relatives` map representing bead-to-parent relationships in the full DAG.
/// * `children` - The `Relatives` map representing bead-to-child relationships in the full DAG.
///
/// # Returns
///
/// A `Cohort` representing the **tail** of the input cohort, based on topological progression.
pub fn cohort_tail(cohort: &Cohort, parents: &Relatives, children: &Relatives) -> Cohort {
    cohort_head(cohort, children, parents)
}

/// Determines and returns the **head** of a given cohort in a Braid.
///
/// The head of a cohort is the set of beads that immediately precede the given cohort
/// in the DAG structure — i.e., the "next generation" of beads from the perspective
/// of moving forward through the Braid.
///
/// It is computed by:
/// 1. Finding all parents of the beads in the `cohort` (`generation(cohort, parents)`).
/// 2. Removing any of those parents that are *also* within the `cohort` itself.
/// 3. Then, finding the children of this resulting set (`tail`).
///
/// In the special case where this derived `tail` is empty or if it contains any of the
/// overall `parents` (genesis beads of the DAG), the function returns the overall DAG's
/// `geneses` as the cohort head.
///
/// # Arguments
///
/// * `cohort` - A reference to a `Cohort` representing the current layer of bead indices.
/// * `parents` - A `Relatives` map representing bead-to-parent relationships in the full DAG.
/// * `children` - A `Relatives` map representing bead-to-child relationships in the full DAG.
///
/// # Returns
///
/// A `Cohort` representing the head of the input cohort, based on topological progression.
pub fn cohort_head(cohort: &Cohort, parents: &Relatives, children: &Relatives) -> Cohort {
    let tail = generation(
        &generation(cohort, parents)
            .difference(cohort)
            .copied()
            .collect::<HashSet<_>>(),
        children,
    );
    let cohort_geneses = geneses(parents);

    if tail.is_empty() || !tail.is_disjoint(&cohort_geneses) {
        cohort_geneses
    } else {
        tail
    }
}

/// Constructs a **sub-braid** from a specified set of bead indices within a Braid.
///
/// A *sub-braid* is defined as the subgraph induced by a subset of beads —
/// that is, only the beads in the input `beads` set are considered, and only the parent
/// relationships between those beads are retained.
///
/// This is especially useful in contexts like:
/// - **Pruning** parts of the DAG
/// - **Cohort isolation** for localized validation. sub_braid works on
///     parents/children/ancestors/descendants equally well.
/// - Visualization of subgraphs or ancestry scopes.
///
/// The result has the properties:
///     geneses(sub_braid(beads, parents)) == cohort_head(beads, parents)
///     tips(sub_braid(beads, parents)) == cohort_tail(beads, parents)
///     cohorts(sub_braid(beads, parents)) == [beads]
///
/// # Arguments
///
/// * `beads` - A set of bead indices to include in the sub-braid.
/// * `parents` - A mapping from each bead index to its set of parent bead indices (the full parent DAG).
///
/// # Returns
///
/// A `Relatives` where:
/// - Keys are bead indices from the `beads` set.
/// - Values are sets of **parents also within the `beads` set**.
pub fn sub_braid(beads: &BeadSet, parents: &Relatives) -> Relatives {
    beads
        .iter()
        .map(|b| {
            let parent_set: BeadSet = parents.get(b).map_or(BeadSet::new(), |ps| {
                ps.intersection(beads).copied().collect()
            });
            (*b, parent_set)
        })
        .collect()
}

/// Computes the **descendant work** for each bead in the Braid.
///
/// In Braidpool’s Proof-of-Work (PoW) model, each bead has intrinsic work (e.g., hash difficulty),
/// and the total work includes contributions from all its **descendants** in the DAG.
///
/// This function traverses the DAG in **cohort-reversed** (topological reverse) order
/// and accumulates the descendant work for each bead, i.e., the sum of its own work and
/// all work contributed by beads that descend from it.
///
/// The calculation for a bead `b` is: `descendant_work[b] = work(b) + Σ work(descendant(b))`.
///
/// # Arguments
///
/// * `children` - A `Relatives` map from bead index to its child indices. Used for descendant traversal.
/// * `bead_work` - A `HashMap` where each bead index maps to its intrinsic `Work` value.
/// * `cohorts` - A slice of `Cohort`s, representing the topologically sorted layers of beads.
///
/// # Returns
///
/// A `HashMap<BeadIdx, Work>` mapping each bead index to its total **descendant work** value.
pub fn descendant_work(
    children: &Relatives,
    bead_work: &HashMap<BeadIdx, Work>,
    cohorts: &[Cohort],
    //FIXME add descendant_cache
) -> HashMap<BeadIdx, Work> {
    let mut previous_work = zero_work();
    let rev_cohorts: Vec<super::Cohort> = cohorts.iter().rev().cloned().collect();

    let mut retval = HashMap::new();

    for cohort in rev_cohorts {
        let sub_children = sub_braid(&cohort, children);
        let mut sub_descendants = HashMap::new();

        // Compute descendants by passing children here instead of parents
        // Call for each bead in the cohort
        for &bead in &cohort {
            all_ancestors(bead, &sub_children, &mut sub_descendants);
        }

        for b in &cohort {
            let descendant_sum: Work = if let Some(descendants) = sub_descendants.get(b) {
                descendants
                    .iter()
                    .map(|d| bead_work[d])
                    .fold(zero_work(), |acc, w| acc + w)
            } else {
                zero_work()
            };
            retval.insert(*b, previous_work + bead_work[b] + descendant_sum);
        }

        // All beads in the next cohort have ALL beads in this cohort as descendants.
        let cohort_work_sum: Work = cohort
            .iter()
            .map(|b| bead_work[b])
            .fold(zero_work(), |acc, w| acc + w);
        previous_work = previous_work + cohort_work_sum;
    }

    retval
}

/// Custom comparison function for ordering bead indices in Braidpool consensus logic.
///
/// The comparison follows a strict priority:
/// 1.  **Descendant Work** (`dwork`): Higher descendant work takes precedence.
/// 2.  **Ancestor Work** (`awork`): If descendant work is equal, higher ancestor work takes precedence.
/// 3.  **Bead Index**: If both work values are equal, a smaller bead index is considered "greater"
///     (a tie-breaking rule, often referred to as "luck" in some contexts, based on hash or identifier).
///
/// This comparator is designed to be used in sorting and priority queues where
/// consensus-based ordering of beads is necessary (e.g., tip selection, highest work path determination).
///
/// # Arguments
///
/// * `a` - The `BeadIdx` of bead A.
/// * `b` - The `BeadIdx` of bead B.
/// * `dwork` - A `HashMap` mapping `BeadIdx` to its total **descendant work**.
/// * `awork` - A `HashMap` mapping `BeadIdx` to its total **ancestor work**.
///
/// # Returns
///
/// An `Ordering` (`Less`, `Greater`, or `Equal`) indicating the relative ranking of bead A vs B.
pub fn bead_cmp(
    a: BeadIdx,
    b: BeadIdx,
    dwork: &HashMap<BeadIdx, Work>,
    awork: &HashMap<BeadIdx, Work>,
) -> Ordering {
    if dwork[&a] < dwork[&b] {
        Ordering::Less // highest work
    } else if dwork[&a] > dwork[&b] {
        Ordering::Greater
    } else if awork[&a] < awork[&b] {
        Ordering::Less
    } else if awork[&a] > awork[&b] {
        Ordering::Greater
    } else if a > b {
        Ordering::Less // same work, fall back on block hash ("luck")
    } else if a < b {
        Ordering::Greater
    } else {
        Ordering::Equal
    }
}

/// Returns a closure suitable for sorting beads by their accumulated work.
///
/// This function computes the descendant and ancestor work for all relevant beads
/// and then returns a closure (`impl Fn(&BeadIdx, &BeadIdx) -> Ordering`) that can be used
/// with sorting methods (e.g., `Vec::sort_by`, `Iterator::max_by`) to order beads
/// according to the Braidpool consensus rules.
///
/// The sorting criteria, applied by the internal `bead_cmp` function, prioritizes:
/// 1. Highest Descendant Work
/// 2. Highest Ancestor Work (if descendant work is equal)
/// 3. Bead Index (as a tie-breaker, smaller index first)
///
/// # Arguments
///
/// * `parents` - A reference to the `Relatives` map of bead parents.
/// * `children` - A reference to the `Relatives` map of bead children.
/// * `bead_work` - A reference to a `HashMap` mapping `BeadIdx` to its intrinsic `Work` value.
///
/// # Returns
///
/// An `impl Fn(&BeadIdx, &BeadIdx) -> Ordering` closure that can be used to compare two beads
/// based on their work and index according to consensus rules.
fn work_sort_key_fn<'a>(
    parents: &'a Relatives,
    children: &'a Relatives,
    bead_work: &'a HashMap<BeadIdx, Work>,
    // FIXME add descendant_cache
) -> impl Fn(&BeadIdx, &BeadIdx) -> Ordering + 'a {
    // Compute cohorts for descendant work calculation
    let mut cohort_cache = Relatives::new();
    let geneses_set = geneses(parents);
    let parent_cohorts = cohorts(parents, children, &geneses_set, &mut cohort_cache);

    // For descendant work, we swap parents/children
    let mut desc_cohort_cache = Relatives::new();
    let desc_geneses_set = geneses(children);
    let desc_cohorts = cohorts(children, parents, &desc_geneses_set, &mut desc_cohort_cache);

    let dwork = descendant_work(children, bead_work, &desc_cohorts);
    let awork = descendant_work(parents, bead_work, &parent_cohorts);

    move |a: &BeadIdx, b: &BeadIdx| bead_cmp(*a, *b, &dwork, &awork)
}

/// Computes the **highest-work path** in the Braid.
///
/// This function identifies the most "valuable" path in terms of cumulative **Proof-of-Work (PoW)**
/// starting from a genesis bead and ending at a tip bead. This is particularly useful for:
/// - Conflict resolution due to simultaneous bead proposals.
/// - Establishing a canonical chain or subchain in a DAG-based consensus.
///
/// The "highest work" path is selected by:
/// 1. Choosing the genesis bead from `geneses(parents)` with the maximum work based on `bead_cmp`.
/// 2. Repeatedly walking forward by selecting the child (from `children` map) with the highest work
///    according to the same `bead_cmp` criteria.
/// 3. Continuing this process until a tip bead (from `tips(children)`) is reached.
///
/// # Consensus Rule
/// Sorting order uses `bead_cmp(...)`, which prioritizes:
/// - Descendant Work
/// - Ancestor Work
/// - Bead Index (tie-breaker)
///
/// # Arguments
///
/// * `parents` - A `Relatives` map from bead index to its parent indices.
/// * `children` - A `Relatives` map from bead index to its child indices.
/// * `bead_work` - A `HashMap` mapping `BeadIdx` to its intrinsic `Work` value.
///
/// # Returns
///
/// A `Vec<BeadIdx>` representing the highest-work path as a sequence of bead indices from genesis to tip.
pub fn highest_work_path(
    parents: &Relatives,
    children: &Relatives,
    bead_work: &HashMap<BeadIdx, Work>,
    // FIXME add descendant_cache
) -> Vec<BeadIdx> {
    let sort_key_fn = work_sort_key_fn(parents, children, bead_work);
    let mut hwpath = vec![*geneses(parents)
        .iter()
        .max_by(|a, b| sort_key_fn(a, b))
        .unwrap()];

    let dag_tips = tips(children);
    while !dag_tips.contains(hwpath.last().unwrap()) {
        let max_child = children[hwpath.last().unwrap()]
            .iter()
            .max_by(|a, b| sort_key_fn(a, b))
            .unwrap();
        hwpath.push(*max_child);
    }

    hwpath
}
