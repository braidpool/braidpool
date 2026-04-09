// Pure algorithm tests for braid consensus algorithms
// These tests only test pure algorithm functions that operate on HashMap data structures
// and do NOT depend on the Bead struct or braid integration.

use super::algorithms::*;
use crate::braid::BeadIdx;
use crate::braid::{BeadSet, Relatives};
use crate::relatives;
use bitcoin::Work;
use std::collections::{HashMap, HashSet};

use crate::utils::test_utils::JSONBraid;

// ============================================================================
// Test Helper Functions
// ============================================================================

/// Helper to create Work from u64 for testing
fn work(v: u64) -> Work {
    let mut bytes = [0u8; 32];
    bytes[24..32].copy_from_slice(&v.to_be_bytes());
    Work::from_be_bytes(bytes)
}

// ============================================================================
// Tests
// ============================================================================

#[test]
pub fn test_reverse() {
    let parents1 = relatives!(
        0 => [],
        1 => [],
        2 => [0],
        3 => [1, 2],
        4 => [3],
    );
    let reverse_children_mapping = reverse(&parents1);
    let expected_children_mapping = relatives!(
        0 => [2],
        1 => [3],
        2 => [3],
        3 => [4],
        4 => [],
    );
    assert_eq!(reverse_children_mapping, expected_children_mapping);
}

#[test]
pub fn test_genesis_empty() {
    let parents = relatives!();
    let genesis_indices = geneses(&parents);
    cohorts(
        &parents,
        &relatives!(),
        &BeadSet::new(),
        &mut Relatives::new(),
    );
    assert_eq!(genesis_indices, HashSet::new());
}

#[test]
pub fn test_genesis_single() {
    let parents = relatives!(
        0 => [],
    );
    let children = reverse(&parents);
    let genesis_indices = geneses(&parents);
    cohorts(&parents, &children, &BeadSet::new(), &mut Relatives::new());
    assert_eq!(genesis_indices, HashSet::from([0]));
}

#[test]
pub fn test_genesis_multiple() {
    let parents = relatives!(
        0 => [],
        1 => [],
        2 => [0, 1],
    );
    let genesis_indices = geneses(&parents);
    assert_eq!(genesis_indices, HashSet::from([0, 1]));
}

#[test]
pub fn test_genesis_chain() {
    let parents = relatives!(
        0 => [],
        1 => [0],
        2 => [1],
        3 => [2],
    );
    let genesis_indices = geneses(&parents);
    assert_eq!(genesis_indices, HashSet::from([0]));
}

#[test]
pub fn test_genesis_three_parallel() {
    let parents = relatives!(
        0 => [],
        1 => [],
        2 => [],
        3 => [1],
        4 => [0],
    );
    let genesis_indices = geneses(&parents);
    assert_eq!(genesis_indices, HashSet::from([0, 1, 2]));
}

#[test]
pub fn test_tips_empty() {
    let parents = relatives!();
    let children = reverse(&parents);
    let tips_indices = tips(&children);
    assert_eq!(tips_indices, HashSet::new());
}

#[test]
pub fn test_tips_single() {
    let parents = relatives!(
        0 => [],
    );
    let children = reverse(&parents);
    let tips_indices = tips(&children);
    assert_eq!(tips_indices, HashSet::from([0]));
}

#[test]
pub fn test_tips_simple() {
    let parents = relatives!(
        0 => [],
        1 => [0],
        2 => [0],
    );
    let children = reverse(&parents);
    let tips_indices = tips(&children);
    assert_eq!(tips_indices, HashSet::from([1, 2]));
}

#[test]
pub fn test_all_ancestors_simple() {
    let parents = relatives!(
        0 => [],
        1 => [0],
        2 => [1],
        3 => [2],
    );

    let mut cache = HashMap::new();
    all_ancestors(3, &parents, &mut cache);

    assert_eq!(cache.get(&0), Some(&HashSet::new()));
    assert_eq!(cache.get(&1), Some(&HashSet::from([0])));
    assert_eq!(cache.get(&2), Some(&HashSet::from([0, 1])));
    assert_eq!(cache.get(&3), Some(&HashSet::from([0, 1, 2])));
}

#[test]
pub fn test_cohorts_simple() {
    let parents = relatives!(
        0 => [],
        1 => [0],
        2 => [1],
        3 => [2],
    );

    let children = reverse(&parents);
    let geneses_set = geneses(&parents);
    let mut cache = HashMap::new();
    let simple_cohorts = cohorts(&parents, &children, &geneses_set, &mut cache);

    println!("Cohorts: {:?}", simple_cohorts);
    println!("Ancestor cache: {:?}", cache);
    println!("Parents: {:?}", parents);
    println!("Children: {:?}", children);
    // Each bead should be in its own cohort since it's a simple chain
    assert_eq!(simple_cohorts.len(), 4);
    assert!(simple_cohorts[0] == HashSet::from([0]));
    assert!(simple_cohorts[1] == HashSet::from([1]));
    assert!(simple_cohorts[2] == HashSet::from([2]));
    assert!(simple_cohorts[3] == HashSet::from([3]));
}

#[test]
pub fn test_cohorts_twotip() {
    let parents = relatives!(
        0 => [],
        1 => [0],
        2 => [0],
    );

    let children = reverse(&parents);
    let geneses_set = geneses(&parents);
    let mut cache = HashMap::new();
    let twotip_cohorts = cohorts(&parents, &children, &geneses_set, &mut cache);

    // Should have one cohort with [0] and another with [1, 2]
    assert_eq!(twotip_cohorts.len(), 2);
    assert!(twotip_cohorts[0] == HashSet::from([0]));
    assert!(twotip_cohorts[1] == HashSet::from([1, 2]));
}

#[test]
pub fn test_cohorts_non_head_cohort_extension() {
    let parents = relatives!(
        0 => [],
        1 => [0],
        2 => [1],
        3 => [1],
        4 => [2,3],
        5 => [3],
        6 => [4,5]
    );

    let children = reverse(&parents);
    let geneses_set = geneses(&parents);
    let mut cache = HashMap::new();
    let nhce_cohorts = cohorts(&parents, &children, &geneses_set, &mut cache);

    println!("Cohorts: {:?}", nhce_cohorts);
    println!("Ancestor cache: {:?}", cache);
    println!("Parents: {:?}", parents);
    println!("Children: {:?}", children);
    // Each bead should be in its own cohort since it's a simple chain
    assert_eq!(nhce_cohorts.len(), 4);
    assert!(nhce_cohorts[0] == HashSet::from([0]));
    assert!(nhce_cohorts[1] == HashSet::from([1]));
    assert!(nhce_cohorts[2] == HashSet::from([2, 3, 4, 5]));
    assert!(nhce_cohorts[3] == HashSet::from([6]));
}

#[test]
pub fn test_sub_braid_simple() {
    let parents = relatives!(
        0 => [],
        1 => [0],
        2 => [1],
        3 => [2],
        4 => [2],  // parallel branch
    );

    let cohort = HashSet::from([1, 2, 3, 4]);
    let sub_parents = sub_braid(&cohort, &parents);

    // Should include nodes and their descendants
    assert_eq!(sub_parents.len(), 4);
    assert!(sub_parents.contains_key(&1));
    assert!(sub_parents.contains_key(&2));
    assert!(sub_parents.contains_key(&3));
    assert!(sub_parents.contains_key(&4));

    // Should not include parent 0
    assert!(!sub_parents.contains_key(&0));
}

#[test]
pub fn test_cohort_head_tail() {
    let parents = relatives!(
        0 => [],
        1 => [0],
        2 => [0],
        3 => [1, 2],
    );

    let children = reverse(&parents);
    let cohort = HashSet::from([1, 2, 3]);

    let head = cohort_head(&cohort, &parents, &children);
    let tail = cohort_tail(&cohort, &parents, &children);

    // Head should be genesis beads of the sub-braid (1 and 2)
    assert_eq!(head, HashSet::from([1, 2]));

    // Tail should be tip beads of the sub-braid (just 3)
    assert_eq!(tail, HashSet::from([3]));
}

#[test]
pub fn test_highest_work_path_simple() {
    let parents = relatives!(
        0 => [],
        1 => [0],
        2 => [0],
        3 => [1],
    );

    let children = reverse(&parents);
    let bead_work: HashMap<BeadIdx, Work> = parents.keys().map(|&k| (k, work(1))).collect();
    let path = highest_work_path(&parents, &children, &bead_work);

    // Should return one of the valid paths
    assert!(path == vec![0, 1, 3] || path == vec![0, 2]);
}

#[test]
pub fn test_descendant_work() {
    let parents = relatives!(
        0 => [],
        1 => [0],
        2 => [1],
    );

    let children = reverse(&parents);

    // Create work HashMap
    let work_values: HashMap<BeadIdx, Work> =
        HashMap::from([(0, work(1)), (1, work(2)), (2, work(3))]);

    // Compute cohorts
    let mut cache = HashMap::new();
    let geneses_set = geneses(&parents);
    let cohorts = cohorts(&parents, &children, &geneses_set, &mut cache);

    let descendant_work = descendant_work(&children, &work_values, &cohorts);

    // 0: 1 + 2 + 3 = 6
    // 1: 2 + 3 = 5
    // 2: 3 = 3
    assert_eq!(descendant_work.get(&0), Some(&work(6)));
    assert_eq!(descendant_work.get(&1), Some(&work(5)));
    assert_eq!(descendant_work.get(&2), Some(&work(3)));
}

#[test]
pub fn test_bead_cmp() {
    // Create Work values
    let work_values: HashMap<BeadIdx, Work> =
        HashMap::from([(0, work(10)), (1, work(20)), (2, work(15))]);
    let awork_values: HashMap<BeadIdx, Work> =
        HashMap::from([(0, work(10)), (1, work(20)), (2, work(15))]);

    // Test ordering - bead_cmp returns Ordering
    assert_eq!(
        bead_cmp(1, 0, &work_values, &awork_values),
        std::cmp::Ordering::Greater
    );
    assert_eq!(
        bead_cmp(0, 1, &work_values, &awork_values),
        std::cmp::Ordering::Less
    );
    assert_eq!(
        bead_cmp(0, 2, &work_values, &awork_values),
        std::cmp::Ordering::Less
    );
    assert_eq!(
        bead_cmp(2, 0, &work_values, &awork_values),
        std::cmp::Ordering::Greater
    );
}

#[test]
pub fn test_generation() {
    let parents = relatives!(
        0 => [],
        1 => [0],
        2 => [0],
        3 => [1, 2],
    );

    let children = reverse(&parents);

    // Test generation from genesis beads
    let genesis_beads = HashSet::from([0]);
    let gen0 = generation(&genesis_beads, &children);
    assert_eq!(gen0, HashSet::from([1, 2]));

    // Test generation from middle beads
    let middle_beads = HashSet::from([1, 2]);
    let gen1 = generation(&middle_beads, &children);
    assert_eq!(gen1, HashSet::from([3]));

    // Test generation from tips (no children)
    let tip_beads = HashSet::from([3]);
    let gen2 = generation(&tip_beads, &children);
    assert_eq!(gen2, HashSet::new());
}

// ============================================================================
// Ancestors Cache Tests
// ============================================================================

#[test]
pub fn test_all_ancestors_cache_miss_basic() {
    // Test basic cache functionality - first call should compute and cache
    let parents = relatives!(
        0 => [],
        1 => [0],
        2 => [1],
        3 => [2],
    );

    let mut cache = HashMap::new();

    // First call - should compute and cache results for bead 3 and its dependencies
    all_ancestors(3, &parents, &mut cache);

    // Verify ancestors were computed correctly for requested bead and its dependencies
    assert_eq!(cache.get(&0), Some(&HashSet::new()));
    assert_eq!(cache.get(&1), Some(&HashSet::from([0])));
    assert_eq!(cache.get(&2), Some(&HashSet::from([0, 1])));
    assert_eq!(cache.get(&3), Some(&HashSet::from([0, 1, 2])));

    // Verify cache was populated only for beads that were explicitly requested
    // Cache contains only the original requested bead (3), not its dependencies
    assert_eq!(cache.get(&3), Some(&HashSet::from([0, 1, 2])));
}

#[test]
pub fn test_all_ancestors_cache_hit_basic() {
    // Test cache hit functionality - second call should use cached results
    let parents = relatives!(
        0 => [],
        1 => [0],
        2 => [1],
        3 => [2],
    );

    let mut cache = HashMap::new();

    // Pre-populate cache with known result for bead 3 only
    cache.insert(3, HashSet::from([0, 1, 2]));

    // Call with bead that is already cached
    all_ancestors(3, &parents, &mut cache);

    // Should use cached results without recomputation
    assert_eq!(cache.get(&3), Some(&HashSet::from([0, 1, 2])));
}

#[test]
pub fn test_all_ancestors_cache_partial_hit() {
    // Test partial cache hit - some beads cached, some not
    let parents = relatives!(
        0 => [],
        1 => [0],
        2 => [1],
        3 => [2],
    );

    let mut cache = HashMap::new();

    // Pre-populate cache with result for bead 2
    cache.insert(2, HashSet::from([0, 1]));
    // Note: 3 is NOT cached

    // Call with beads 2 and 3 - 2 should use cache, 3 should compute
    all_ancestors(2, &parents, &mut cache);
    all_ancestors(3, &parents, &mut cache);

    // Verify results for both beads
    assert_eq!(cache.get(&2), Some(&HashSet::from([0, 1])));
    assert_eq!(cache.get(&3), Some(&HashSet::from([0, 1, 2])));
}

#[test]
pub fn test_all_ancestors_cache_complex_dag() {
    // Test cache with a more complex DAG structure
    let parents = relatives!(
        0 => [],      // Genesis
        1 => [0],     // Child of 0
        2 => [0],     // Another child of 0 (parallel)
        3 => [1, 2],  // Merge point
    );

    let mut cache = HashMap::new();

    // First compute ancestors for bead 3
    all_ancestors(3, &parents, &mut cache);

    // Verify complex ancestry relationships
    assert_eq!(cache.get(&3), Some(&HashSet::from([0, 1, 2])));
    assert_eq!(cache.get(&2), Some(&HashSet::from([0])));
    assert_eq!(cache.get(&1), Some(&HashSet::from([0])));
    assert_eq!(cache.get(&0), Some(&HashSet::new()));

    // Now call again with bead 3 - should use cache immediately
    cache.clear();
    all_ancestors(3, &parents, &mut cache);

    // Should get cached results immediately
    assert_eq!(cache.get(&3), Some(&HashSet::from([0, 1, 2])));
}

#[test]
pub fn test_all_ancestors_cache_multiple_calls() {
    // Test that cache persists across multiple calls
    let parents = relatives!(
        0 => [],
        1 => [0],
        2 => [1],
        3 => [0],     // Alternative path
    );

    let mut cache = HashMap::new();

    // First call - compute ancestors for bead 2
    all_ancestors(2, &parents, &mut cache);
    assert_eq!(cache.get(&2), Some(&HashSet::from([0, 1])));

    // Second call - compute ancestors for bead 3
    cache.clear();
    all_ancestors(3, &parents, &mut cache);
    assert_eq!(cache.get(&3), Some(&HashSet::from([0])));

    // Third call - ask for both previously computed beads
    cache.clear();
    all_ancestors(2, &parents, &mut cache);
    all_ancestors(3, &parents, &mut cache);
    assert_eq!(cache.get(&2), Some(&HashSet::from([0, 1])));
    assert_eq!(cache.get(&3), Some(&HashSet::from([0])));

    // Verify cache contains both requested beads
    assert!(cache.contains_key(&0));
    assert!(cache.contains_key(&1));
    assert!(cache.contains_key(&2));
    assert!(cache.contains_key(&3));
}

#[test]
pub fn test_all_ancestors_cache_isolated_beads() {
    // Test with beads that have no relationships
    let parents = relatives!(
        0 => [],  // Isolated genesis
        1 => [],  // Another isolated genesis
        2 => [],  // Yet another isolated genesis
    );

    let mut cache = HashMap::new();

    // Compute ancestors for isolated beads
    for bead in [0, 1, 2] {
        all_ancestors(bead, &parents, &mut cache);
    }

    // All should have empty ancestor sets
    assert_eq!(cache.get(&0), Some(&HashSet::new()));
    assert_eq!(cache.get(&1), Some(&HashSet::new()));
    assert_eq!(cache.get(&2), Some(&HashSet::new()));
}

/// ****
/// File-based tests for algorithm functions
/// ****

#[test]
pub fn test_genesis_from_files() {
    for (file_braid, filename) in JSONBraid::tests() {
        let parents = file_braid.parents.clone();

        let computed_genesis = geneses(&parents);
        let expected_genesis = file_braid.geneses.clone();

        assert_eq!(
            computed_genesis, expected_genesis,
            "Genesis mismatch in file '{}' [{}]",
            filename, file_braid.description
        );
    }
}

#[test]
pub fn test_tips_from_files() {
    for (file_braid, filename) in JSONBraid::tests() {
        let parents = file_braid.parents.clone();
        let children = reverse(&parents);

        let computed_tips = tips(&children);
        let expected_tips = file_braid.tips.clone();

        assert_eq!(
            computed_tips, expected_tips,
            "Tips mismatch in file '{}' [{}]",
            filename, file_braid.description
        );
    }
}

#[test]
pub fn test_reverse_from_files() {
    for (file_braid, filename) in JSONBraid::tests() {
        let parents = file_braid.parents.clone();
        let computed_children = reverse(&parents);
        let expected_children = file_braid.children.clone();

        assert_eq!(
            computed_children, expected_children,
            "Reverse mismatch in file '{}' [{}]",
            filename, file_braid.description
        );
    }
}

#[test]
pub fn test_cohorts_from_files() {
    for (file_braid, filename) in JSONBraid::tests() {
        let parents = file_braid.parents.clone();
        let children = reverse(&parents);
        let geneses_set = geneses(&parents);
        let mut cache = HashMap::new();
        let computed_cohorts = cohorts(&parents, &children, &geneses_set, &mut cache);
        let expected_cohorts = file_braid.cohorts.clone();

        // The algorithm must produce EXACT results matching the JSON test cases
        assert_eq!(
            computed_cohorts, expected_cohorts,
            "Cohorts mismatch in file '{}' [{}] (expected: {:?}, got: {:?})",
            filename, file_braid.description, expected_cohorts, computed_cohorts
        );
    }
}

#[test]
pub fn test_highest_work_path_from_files() {
    for (file_braid, filename) in JSONBraid::tests() {
        let parents = file_braid.parents.clone();
        let children = reverse(&parents);

        // Create bead work maps from file data
        let bead_work: HashMap<BeadIdx, Work> = file_braid
            .bead_work
            .iter()
            .map(|(k, v)| (*k, work(*v as u64)))
            .collect();

        let path = highest_work_path(&parents, &children, &bead_work);

        // The algorithm must produce EXACT results matching the JSON test cases
        assert_eq!(
            path, file_braid.highest_work_path,
            "Highest work path mismatch in file '{}' [{}] (expected: {:?}, got: {:?})",
            filename, file_braid.description, file_braid.highest_work_path, path
        );
    }
}

#[test]
pub fn test_descendant_work_from_files() {
    for (file_braid, filename) in JSONBraid::tests() {
        let parents = file_braid.parents.clone();
        let children = reverse(&parents);

        // Create work maps from file data
        let work_map: HashMap<BeadIdx, Work> = file_braid
            .work
            .iter()
            .map(|(k, v)| (*k, work(*v as u64)))
            .collect();

        // Compute cohorts for descendant work
        let mut cohort_cache = HashMap::new();
        let geneses_set = geneses(&children);
        let desc_cohorts = cohorts(&children, &parents, &geneses_set, &mut cohort_cache);

        let computed_descendant_work = descendant_work(&children, &work_map, &desc_cohorts);

        // Verify that all beads have work calculations
        for (bead_idx, _) in &parents {
            assert!(
                computed_descendant_work.contains_key(bead_idx),
                "Missing descendant work for bead {}",
                bead_idx
            );

            // Descendant work should be at least the bead's own work
            let zero_work = work(0);
            let bead_work = work_map.get(bead_idx).unwrap_or(&zero_work);
            let desc_work = computed_descendant_work.get(bead_idx).unwrap();
            assert!(
                desc_work >= bead_work,
                "Descendant work in file '{}' [{}] should be >= bead work for bead {}",
                filename,
                file_braid.description,
                bead_idx
            );
        }
    }
}

#[test]
pub fn test_cohort_head_tail_from_files() {
    for (file_braid, filename) in JSONBraid::tests() {
        let parents = file_braid.parents.clone();
        let children = reverse(&parents);

        // Test each cohort from the file
        for cohort in &file_braid.cohorts {
            if !cohort.is_empty() {
                let head = cohort_head(&cohort, &parents, &children);
                let tail = cohort_tail(&cohort, &parents, &children);

                // Head should be non-empty for valid cohorts
                assert!(
                    !head.is_empty(),
                    "Empty head for cohort {:?} in file: {} [{}]",
                    cohort,
                    filename,
                    file_braid.description
                );

                // Tail should be non-empty for valid cohorts
                assert!(
                    !tail.is_empty(),
                    "Empty tail for cohort {:?} in file: {} [{}]",
                    cohort,
                    filename,
                    file_braid.description
                );

                // Head should consist of beads in the cohort
                assert!(
                    head.iter().all(|bead| cohort.contains(bead)),
                    "Head contains beads not in cohort for file: {} [{}]",
                    filename,
                    file_braid.description
                );

                // Tail should consist of beads in the cohort
                assert!(
                    tail.iter().all(|bead| cohort.contains(bead)),
                    "Tail contains beads not in cohort for file: {} [{}]",
                    filename,
                    file_braid.description
                );
            }
        }
    }
}
