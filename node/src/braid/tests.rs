use super::algorithms::*;
use super::{AddBeadStatus, BeadIdx, Braid};
use crate::make_test_braid;
use crate::utils::test_utils::emit_Bead;
use crate::utils::test_utils::JSONBraid;
use crate::{beadset, cohorts, relatives};
use bitcoin::Work;
use rand::{rngs::StdRng, seq::SliceRandom, Rng, SeedableRng};
use std::collections::{HashMap, HashSet};
use std::thread;
use std::time::Duration;

/// Validates that caches are populated and all relationships are localized within cohorts
fn check_cache(braid: &Braid) {
    println!("\n=== Cache Validation ===");

    // Count beads across all cohorts
    let total_beads: usize = braid.cohorts.iter().map(|c| c.len()).sum();

    // Check ancestor_cache population
    println!("Ancestor cache size: {}", braid.ancestor_cache.len());
    println!("Total beads in cohorts: {}", total_beads);

    // For linear blockchain (single bead per cohort), each bead should have an entry with an empty set
    // For braids with multiple beads per cohort, entries should be populated with intra-cohort ancestors

    // Check descendant_cache population
    println!("Descendant cache size: {}", braid.descendant_cache.len());

    // Descendant cache should have entries for beads that have descendants in their cohort
    // For linear chains, this might be empty or have entries with empty sets
    // The important thing is to check that populated entries are properly localized

    // Check tail_cache population
    println!("Tail cache size: {}", braid.tail_cache.len());
    assert_eq!(
        braid.tail_cache.len(),
        braid.cohorts.len(),
        "Tail cache should have one entry per cohort"
    );

    // Build a map from bead to its cohort for validation
    let mut bead_to_cohort: HashMap<BeadIdx, usize> = HashMap::new();
    for (cohort_idx, cohort) in braid.cohorts.iter().enumerate() {
        for &bead_idx in cohort {
            bead_to_cohort.insert(bead_idx, cohort_idx);
        }
    }

    // Validate ancestor_cache: all ancestors should be within the same cohort
    let mut ancestor_violations = 0;
    for (bead_idx, ancestors) in &braid.ancestor_cache {
        if let Some(&cohort_idx) = bead_to_cohort.get(bead_idx) {
            let cohort = &braid.cohorts[cohort_idx];
            for ancestor in ancestors {
                if !cohort.contains(ancestor) {
                    ancestor_violations += 1;
                    println!(
                        "Bead {} in cohort {} has ancestor {} outside the cohort",
                        bead_idx, cohort_idx, ancestor
                    );
                }
            }
        }
    }
    assert_eq!(
        ancestor_violations, 0,
        "Found {} ancestors outside their cohort boundaries",
        ancestor_violations
    );

    // Validate descendant_cache: all descendants should be within the same cohort
    let mut descendant_violations = 0;
    for (bead_idx, descendants) in &braid.descendant_cache {
        if let Some(&cohort_idx) = bead_to_cohort.get(bead_idx) {
            let cohort = &braid.cohorts[cohort_idx];
            for descendant in descendants {
                if !cohort.contains(descendant) {
                    descendant_violations += 1;
                    println!(
                        "⚠️  Bead {} in cohort {} has descendant {} outside the cohort",
                        bead_idx, cohort_idx, descendant
                    );
                }
            }
        }
    }
    assert_eq!(
        descendant_violations, 0,
        "Found {} descendants outside their cohort boundaries",
        descendant_violations
    );

    println!("All cache entries are properly localized within cohorts");
}

/// Helper to create Work from u64 for testing
fn work(v: u64) -> Work {
    let mut bytes = [0u8; 32];
    bytes[24..32].copy_from_slice(&v.to_be_bytes());
    Work::from_be_bytes(bytes)
}

#[test]
pub fn test_orphanage_occupancy() {
    // Construct a braid with a single genesis bead
    let genesis = emit_Bead(&[]);
    let parent = emit_Bead(&[&genesis]);
    let orphan_child = emit_Bead(&[&parent]); // will be missing parent initially

    let mut braid = Braid::new(vec![genesis.clone()]);

    // Extend with parent so its hash is known
    assert_eq!(braid.extend(&parent), AddBeadStatus::BeadAdded);

    // Add orphaned child with missing parent (parent hash removed from index)
    // Simulate missing parent by clearing index entry temporarily
    let parent_hash = parent.hash();
    let saved = braid.index.remove(&parent_hash).unwrap();
    let status = braid.extend(&orphan_child);
    assert_eq!(status, AddBeadStatus::ParentsMissing);

    // Occupancy should be >0 immediately after orphan enters
    let occ_now = braid.orphanage_occupancy(Duration::from_micros(1));
    assert!(occ_now.is_some());

    // Wait a bit to accumulate occupancy time
    thread::sleep(Duration::from_millis(5));
    let occ_avg = braid
        .orphanage_occupancy(Duration::from_millis(1))
        .expect("should have enough elapsed time");
    assert!(
        occ_avg >= 1.0,
        "average occupancy should be at least 1, got {}",
        occ_avg
    );

    // Restore parent so orphan can be adopted
    braid.index.insert(parent_hash, saved);
    braid.adopt_orphans(&parent_hash);

    // After adoption, occupancy should go to 0
    thread::sleep(Duration::from_millis(1));
    let occ_after = braid
        .orphanage_occupancy(Duration::from_millis(1))
        .expect("should have elapsed time");
    assert!(
        occ_after < 1.0,
        "occupancy should drop after adoption, got {}",
        occ_after
    );
}

#[test]
pub fn test_extend_functionality() {
    // Create a braid with one bead.
    let test_bead_0 = emit_Bead(&[]);

    let mut test_braid = Braid::new(vec![test_bead_0.clone()]);

    // Verify initial state
    assert_eq!(test_braid.beads.len(), 1);
    assert_eq!(test_braid.cohorts, cohorts!([0]));

    // Test simple chain extension: 0 -> 1 -> 2
    let test_bead_1 = emit_Bead(&[&test_bead_0]);
    let result = test_braid.extend(&test_bead_1);
    assert_eq!(result, AddBeadStatus::BeadAdded);
    assert_eq!(test_braid.beads.len(), 2);
    assert_eq!(test_braid.cohorts, cohorts!([0], [1]));

    let test_bead_2 = emit_Bead(&[&test_bead_1]);
    let result = test_braid.extend(&test_bead_2);
    assert_eq!(result, AddBeadStatus::BeadAdded);
    assert_eq!(test_braid.beads.len(), 3);
    assert_eq!(test_braid.cohorts, cohorts!([0], [1], [2])); // Should have at least 3 cohorts

    // Test branching: beads 3 and 4 both branch from bead 2
    let test_bead_3 = emit_Bead(&[&test_bead_2]);
    let test_bead_4 = emit_Bead(&[&test_bead_2]);
    let result = test_braid.extend(&test_bead_3);
    assert_eq!(result, AddBeadStatus::BeadAdded);
    let result = test_braid.extend(&test_bead_4);
    assert_eq!(result, AddBeadStatus::BeadAdded);
    assert_eq!(test_braid.beads.len(), 5);
    assert_eq!(test_braid.cohorts, cohorts!([0], [1], [2], [3, 4]));

    // Test merge: bead 5 merges from beads 3 and 4
    let test_bead_5 = emit_Bead(&[&test_bead_3, &test_bead_4]);
    let result = test_braid.extend(&test_bead_5);
    //println!(
    //    "\nFinal cohorts before multi-cohort reference: {:?}",
    //    test_braid.cohorts
    //);
    assert_eq!(result, AddBeadStatus::BeadAdded);
    assert_eq!(test_braid.beads.len(), 6);
    assert_eq!(test_braid.cohorts, cohorts!([0], [1], [2], [3, 4], [5]));

    // Verify braid integrity
    assert_eq!(test_braid.geneses, beadset![0]); // Still only one genesis
    assert_eq!(test_braid.tips, beadset![5]); // Bead 5 is the only tip
    assert!(
        test_braid.orphanage.is_empty() && test_braid.missing_parents.is_empty(),
        "No orphans should remain"
    );

    // CRITICAL TEST: Add bead 6 that references a parent from multiple cohorts back (bead 1)
    println!(
        "\nFinal cohorts before multi-cohort reference: {:?}",
        test_braid.cohorts
    );
    println!(
        "Ancestor cache size before: {}",
        test_braid.ancestor_cache.len()
    );

    let test_bead_6 = emit_Bead(&[&test_bead_1]); // Parent from 3 cohorts back!

    let result = test_braid.extend(&test_bead_6);
    assert_eq!(result, AddBeadStatus::BeadAdded);

    println!(
        "Final cohorts after multi-cohort reference: {:?}",
        test_braid.cohorts
    );
    println!(
        "Ancestor cache size after: {}",
        test_braid.ancestor_cache.len()
    );

    // This should expose if the cache needs updating
    assert_eq!(test_braid.beads.len(), 7);
    assert!(test_braid.cohorts.iter().any(|c| c.contains(&6))); // Contains bead 6

    // Check if cache was properly updated for bead 6
    if test_braid.ancestor_cache.contains_key(&6) {
        println!(
            "Bead 6 ancestors in cache: {:?}",
            test_braid.ancestor_cache[&6]
        );
        // Should contain bead 1 as ancestor if cache is properly updated
        if test_braid.ancestor_cache[&6].contains(&1) {
            println!("✅ Cache correctly contains bead 1 as ancestor of bead 6");
        } else {
            println!("❌ Cache MISSING bead 1 as ancestor of bead 6 - this indicates cache is not being updated!");
        }
    } else {
        println!("❌ WARNING: Bead 6 not found in ancestor cache - cache not being updated!");
    }

    // CRITICAL: Verify cohorts are not incorrectly merged
    println!("Final cohort structure: {:?}", test_braid.cohorts);
    let final_cohort_count = test_braid.cohorts.len();

    // EXPOSED BUG: The cache truncation during cohort formation is causing massive cohort merging!
    if final_cohort_count == 1 {
        panic!("🚨 CRITICAL BUG DETECTED: All beads merged into a single cohort! This is caused by cache truncation in cohorts() function.
                Expected: multiple separate cohorts, Got: {:?}", test_braid.cohorts);
    }

    // Should NOT have all beads merged into one cohort
    assert!(
        final_cohort_count > 1,
        "Cohorts should NOT be merged into a single cohort! Found: {:?}",
        test_braid.cohorts
    );

    // Verify we still have separate cohorts
    let mut has_multiple_cohorts = false;
    for cohort in &test_braid.cohorts {
        if cohort.len() < 6 {
            // No single cohort should contain all beads
            has_multiple_cohorts = true;
            break;
        }
    }
    assert!(
        has_multiple_cohorts,
        "Should have multiple separate cohorts, not merged into one"
    );
}

#[test]
pub fn test_non_head_cohort_extension() {
    // This test validates that cohorts maintain proper boundaries when extending
    // with a bead that does not point to the tail (head) of the braid.
    //
    // The braid looks like this:
    //
    // 0 - 1 - 2 - 4 - 6
    //       \   /    /
    //         3-----5
    //
    // Test that the cohorts after 0,1,2,3,4 are added are:
    //   {0} {1} {2,3} {4}
    // After adding 5, the cohorts must be:
    //   {0} {1} {2,3,4,5} with tips {4, 5}
    // After adding 6, the cohorts must be:
    //   {0} {1} {2,3,4,5} {6}
    //

    // Create initial braid with beads 0, 1, 2, 3, 4
    let mut test_braid = make_test_braid!(
        0 => [],
        1 => [0],
        2 => [1],
        3 => [1],
        4 => [2,3],
    );

    // This should print [{0}, {1}, {2,3}, {4}]
    println!("Cohorts after adding 0,1,2,3,4: {:?}", test_braid.cohorts);

    // Verify correct behavior: beads 2 and 3 should be in the same cohort
    // because they both have the same ancestors {0}, making them topologically equivalent
    assert_eq!(
        test_braid.cohorts.len(),
        4,
        "Correct behavior: should have 4 cohorts: {{0}} {{1}} {{2,3}} {{4}}"
    );

    // Add bead 5 (references both 3 and 4, which should merge middle cohorts)
    let test_bead_5 = emit_Bead(&[&test_braid.beads[3]]);
    test_braid.extend(&test_bead_5);

    println!("Cohorts after adding 5: {:?}", test_braid.cohorts);

    // Expected: adding 5 should merge cohorts {2,3}, {4} into one and add itself
    // Result: {2, 3, 4, 5}
    assert_eq!(
        test_braid.cohorts.len(),
        3,
        "After adding bead 5 (references 3 and 4), should have 3 cohorts: {{0}} {{1}}, {{2,3,4,5}}"
    );

    // Add bead 6 (references 5, which is now in the head cohort)
    let test_bead_6 = emit_Bead(&[&test_braid.beads[4], &test_braid.beads[5]]);
    test_braid.extend(&test_bead_6);

    println!("Cohorts after adding 6: {:?}", test_braid.cohorts);

    // Expected: bead 6 should form a new cohort
    assert_eq!(
        test_braid.cohorts.len(),
        4,
        "After adding bead 6, should have 4 cohorts: {{0}} {{1}} {{2,3,4,5}} {{6}}"
    );
}

#[test]
pub fn test_json_braid_end_to_end() {
    // This test validates orphan processing by adding beads in random order, which also exercises
    // our ancestor_cache in finding cohorts.
    // After all beads are added (and orphans processed), the final braid structure
    // should match the expected structure from the JSON file.

    // Test with ALL available JSON braid files
    for (json_braid, filename) in JSONBraid::tests() {
        println!("\n=== Testing with {} ===", filename);
        println!(
            "JSON braid has {} beads and {} cohorts",
            json_braid.parents.len(),
            json_braid.cohorts.len()
        );

        // Create beads based on the JSON structure using JSONBraid::make_Braid()
        let reference_braid = json_braid.make_Braid();

        println!(
            "Created reference braid with {} beads",
            reference_braid.beads.len()
        );
        println!("Reference cohorts: {:?}", reference_braid.cohorts);

        // Separate genesis and non-genesis beads for random order testing
        let mut genesis_beads = Vec::new();
        let mut non_genesis_beads = Vec::new();

        for bead in &reference_braid.beads {
            if bead.committed_metadata.parents.is_empty() {
                genesis_beads.push(bead.clone());
            } else {
                non_genesis_beads.push(bead.clone());
            }
        }

        // Use PRNG with seed to shuffle non-genesis beads for extend order testing
        let seed: u64 = rand::thread_rng().gen();
        let mut rng = StdRng::seed_from_u64(seed);

        println!("Using PRNG seed: {} for bead ordering", seed);

        non_genesis_beads.shuffle(&mut rng);

        // Create braid with genesis beads first
        let mut braid = Braid::new(genesis_beads);

        // Extend with other beads in random order
        for (i, bead) in non_genesis_beads.iter().enumerate() {
            let result = braid.extend(bead);

            match result {
                AddBeadStatus::BeadAdded => {
                    // Successfully added
                }
                AddBeadStatus::ParentsMissing => {
                    // This is acceptable for this test - we just want to see cohort behavior
                }
                ref other => {
                    panic!("Unexpected result when adding bead {}: {:?}", i, other);
                }
            }
        }

        println!(
            "Final cohort structure for {}: {:?}",
            filename, braid.cohorts
        );
        println!("Final cohort count: {}", braid.cohorts.len());

        // Verify all orphans have been processed
        assert!(
            braid.orphanage.is_empty() && braid.missing_parents.is_empty(),
            "File {}: All orphans should be processed. Remaining: orphanage={}, missing_parents={}",
            filename,
            braid.orphanage.len(),
            braid.missing_parents.len()
        );

        // Verify all beads are present
        assert_eq!(
            braid.beads.len(),
            reference_braid.beads.len(),
            "File {}: Expected {} beads, got {}",
            filename,
            reference_braid.beads.len(),
            braid.beads.len()
        );

        // Build hash-to-index mappings for both braids to compare structures
        let ref_hash_to_idx: HashMap<_, _> = reference_braid
            .beads
            .iter()
            .enumerate()
            .map(|(idx, bead)| (bead.hash(), idx))
            .collect();

        let test_hash_to_idx: HashMap<_, _> = braid
            .beads
            .iter()
            .enumerate()
            .map(|(idx, bead)| (bead.hash(), idx))
            .collect();

        // Compare geneses by index (already stored as BeadSet/BeadIdx)
        //assert_eq!(
        //    braid.geneses, reference_braid.geneses,
        //    "File {}: Geneses mismatch",
        //    filename
        //);
        assert_eq!(
            braid
                .geneses
                .iter()
                .map(|&i| braid.beads[i].hash())
                .collect::<HashSet<_>>(),
            reference_braid
                .geneses
                .iter()
                .map(|&i| reference_braid.beads[i].hash())
                .collect::<HashSet<_>>(),
            "File {}: Geneses mismatch",
            filename
        );

        // Compare tips by index (already stored as BeadSet/BeadIdx)
        //assert_eq!(
        //    braid.tips, reference_braid.tips,
        //    "File {}: Tips mismatch",
        //    filename
        //);
        assert_eq!(
            braid
                .tips
                .iter()
                .map(|&i| braid.beads[i].hash())
                .collect::<HashSet<_>>(),
            reference_braid
                .tips
                .iter()
                .map(|&i| reference_braid.beads[i].hash())
                .collect::<HashSet<_>>(),
            "File {}: Tips mismatch",
            filename
        );

        // Compare parent relationships by index (much more readable than hashes)
        //        for (hash, &test_idx) in &test_hash_to_idx {
        //            let test_parent_indices: HashSet<_> =
        //                braid.parents[&test_idx].iter().copied().collect();
        //
        //            let ref_idx = ref_hash_to_idx[hash];
        //            let ref_parent_indices: HashSet<_> =
        //                reference_braid.parents[&ref_idx].iter().copied().collect();
        //
        //            assert_eq!(
        //                test_parent_indices, ref_parent_indices,
        //                "File {}: Parent mismatch for bead with hash {:?}",
        //                filename, hash
        //            );
        //        }
        for (hash, &test_idx) in &test_hash_to_idx {
            let test_parent_set = braid.parents.get(&test_idx).cloned().unwrap_or_default();
            let test_parent_hashes: HashSet<_> = test_parent_set
                .iter()
                .map(|&p| braid.beads[p].hash())
                .collect();

            let ref_idx = *ref_hash_to_idx.get(hash).unwrap();
            let ref_parent_set = reference_braid
                .parents
                .get(&ref_idx)
                .cloned()
                .unwrap_or_default();
            let ref_parent_hashes: HashSet<_> = ref_parent_set
                .iter()
                .map(|&p| reference_braid.beads[p].hash())
                .collect();

            assert_eq!(
                test_parent_hashes, ref_parent_hashes,
                "File {}: Parent mismatch for bead with hash {:?}",
                filename, hash
            );
        }

        // Validate cache integrity before checking cohort structure
        check_cache(&braid);
        // Compare cohorts by index (much more readable than hashes)
        let test_cohort_indices: Vec<HashSet<_>> = braid
            .cohorts
            .iter()
            .map(|cohort| cohort.iter().copied().collect())
            .collect();
        let ref_cohort_indices: Vec<HashSet<_>> = reference_braid
            .cohorts
            .iter()
            .map(|cohort| cohort.iter().copied().collect())
            .collect();
        assert_eq!(
            test_cohort_indices, ref_cohort_indices,
            "File {}: Cohorts mismatch.\n  Expected: {:?}\n  Got: {:?}",
            filename, ref_cohort_indices, test_cohort_indices
        );

        let test_cohort_hashes: Vec<HashSet<_>> = braid
            .cohorts
            .iter()
            .map(|cohort| cohort.iter().map(|&i| braid.beads[i].hash()).collect())
            .collect();
        let ref_cohort_hashes: Vec<HashSet<_>> = reference_braid
            .cohorts
            .iter()
            .map(|cohort| {
                cohort
                    .iter()
                    .map(|&i| reference_braid.beads[i].hash())
                    .collect()
            })
            .collect();
        assert_eq!(
            test_cohort_hashes, ref_cohort_hashes,
            "File {}: Cohorts mismatch.\n  Expected: {:?}\n  Got: {:?}",
            filename, ref_cohort_hashes, test_cohort_hashes
        );

        println!("✅ {} passed all validation checks", filename);
    }
}

#[test]
pub fn test_diamond_path_highest_work() {
    // Test diamond pattern: 0 -> (1,2) -> 3
    // This tests highest work path selection in a complex braid structure
    let parents = relatives!(
        0 => [],
        1 => [0],
        2 => [0],
        3 => [1, 2],
    );

    let children = reverse(&parents);

    // Test the highest work path algorithm
    let bead_work: HashMap<BeadIdx, Work> = parents.keys().map(|&k| (k, work(1))).collect();
    let path = highest_work_path(&parents, &children, &bead_work);

    // Should return one of the valid paths in the diamond
    // Path 0->1->3 or path 0->2->3, both are valid
    assert!(path == vec![0, 1, 3] || path == vec![0, 2, 3]);

    // The path should start at genesis (0) and end at tip (3)
    assert_eq!(path[0], 0);
    assert_eq!(path[path.len() - 1], 3);
}

#[test]
pub fn test_make_test_braid_macro() {
    // Test the make_test_braid! macro with a simple braid structure:
    // 0 -> 1 -> 2
    //       -> 3
    let braid = make_test_braid!(
        0 => [],
        1 => [0],
        2 => [1],
        3 => [1],
    );

    println!("Beads: {}", braid.beads.len());
    println!("Cohorts: {:?}", braid.cohorts);
    println!("Tips: {:?}", braid.tips);

    // Verify the braid has 4 beads
    assert_eq!(braid.beads.len(), 4);

    // Verify there are 2 tips (beads 2 and 3)
    assert_eq!(braid.tips.len(), 2);

    // Verify we have the correct number of cohorts
    // Expected: [{0}, {1}, {2,3}]
    assert_eq!(braid.cohorts.len(), 3);
}
