use super::AddBeadStatus;
use super::Bead;
use super::Braid;
use super::OrphanPool;
use super::DEFAULT_MAX_ORPHAN_BEADS;
use crate::braid::consensus_functions::check_cohort;
use crate::braid::consensus_functions::cohort;
use crate::braid::consensus_functions::cohort_head;
use crate::braid::consensus_functions::cohort_tail;
use crate::braid::consensus_functions::descendant_work;
use crate::braid::consensus_functions::genesis;
use crate::braid::consensus_functions::get_all_ancestors;
use crate::braid::consensus_functions::get_sub_braid;
use crate::braid::consensus_functions::highest_work_path;
use crate::braid::consensus_functions::reverse;
use crate::braid::consensus_functions::tips;
use crate::braid::consensus_functions::updating_ancestors;
use crate::braid::Cohort;
use crate::config::PoolNetwork;
use crate::utils::compute_block_hash;
use crate::utils::test_utils::test_utility_functions::loading_braid_from_file;
use crate::utils::test_utils::test_utility_functions::*;
use crate::utils::BeadHash;
use bitcoin::BlockHash;
use num::BigUint;
use std::collections::HashMap;
use std::collections::HashSet;
use std::path::Path;
use std::str::FromStr;
#[test]
pub fn test_extend_functionality() {
    // Create a braid with one bead.
    let test_bead_0 = emit_bead();

    let mut test_braid = Braid {
        beads: vec![test_bead_0.clone()],
        genesis_beads: HashSet::from([0]),
        tips: HashSet::from([0]),
        orphan_beads: OrphanPool::new(DEFAULT_MAX_ORPHAN_BEADS),
        cohorts: vec![Cohort(HashSet::from([0]))],
        cohort_tips: vec![HashSet::from([0])],
        bead_index_mapping: std::collections::HashMap::from([(
            compute_block_hash(&test_bead_0.block_header, PoolNetwork::Cpunet),
            0,
        )]),
        network: PoolNetwork::Cpunet,
    };
    assert_eq!(
        test_braid.cohorts,
        vec![Cohort(HashSet::from([0]))],
        "Initial cohort should contain only the genesis bead"
    );

    // Let's add two beads to create a chain structure.

    let mut test_bead_1 = emit_bead();
    test_bead_1
        .committed_metadata
        .parents
        .push(compute_block_hash(
            &test_bead_0.block_header,
            PoolNetwork::Cpunet,
        ));

    test_braid.extend(&test_bead_1);
    // After adding a new bead that extends the zeroth one, we should have two cohorts
    assert_eq!(
        test_braid.cohorts,
        vec![Cohort(HashSet::from([0])), Cohort(HashSet::from([1]))],
        "After adding the second bead, there should be two cohorts"
    );

    let mut test_bead_2 = emit_bead();
    test_bead_2
        .committed_metadata
        .parents
        .push(compute_block_hash(
            &test_bead_1.block_header,
            PoolNetwork::Cpunet,
        ));
    test_braid.extend(&test_bead_2);

    // After adding the second bead, we should have three cohorts
    assert_eq!(
        test_braid.cohorts,
        vec![
            Cohort(HashSet::from([0])),
            Cohort(HashSet::from([1])),
            Cohort(HashSet::from([2]))
        ],
        "After adding the third bead, there should be three cohorts"
    );

    // Let's add a few more beads to create a more complex braid structure

    // Structure will be:
    // - Bead(s) 3-5 will branch from bead 2
    // - Bead(s) 6-8 will branch from bead 4
    // - Bead(s) 9-11 will branch from bead 5
    // - Bead(s) 12 will merge all the tips.

    // This will create a structure like:
    //           /-- 3 --------------------\
    // 0 -- 1 -- 2 -- 4 -- 6 -- 7 -- 8 --  12 -- 13
    //           \-- 5 -- 9 -- 10 -- 11 -- /

    // Create bead 3 with parent 2
    let mut test_bead_3 = emit_bead();
    test_bead_3
        .committed_metadata
        .parents
        .push(compute_block_hash(
            &test_bead_2.block_header,
            PoolNetwork::Cpunet,
        ));
    test_braid.extend(&test_bead_3);

    // Create bead 4 with parent 2
    let mut test_bead_4 = emit_bead();
    test_bead_4
        .committed_metadata
        .parents
        .push(compute_block_hash(
            &test_bead_2.block_header,
            PoolNetwork::Cpunet,
        ));
    test_braid.extend(&test_bead_4);

    // Create bead 5 with parent 2
    let mut test_bead_5 = emit_bead();
    test_bead_5
        .committed_metadata
        .parents
        .push(compute_block_hash(
            &test_bead_2.block_header,
            PoolNetwork::Cpunet,
        ));
    test_braid.extend(&test_bead_5);

    assert_eq!(
        test_braid.cohorts,
        vec![
            Cohort(HashSet::from([0])),
            Cohort(HashSet::from([1])),
            Cohort(HashSet::from([2])),
            Cohort(HashSet::from([3, 4, 5])),
        ],
        "After adding the sixth bead, there should be four cohorts"
    );

    // Create beads 6-8 with chain from bead 4
    let mut test_bead_6 = emit_bead();
    test_bead_6
        .committed_metadata
        .parents
        .push(compute_block_hash(
            &test_bead_4.block_header,
            PoolNetwork::Cpunet,
        ));
    test_braid.extend(&test_bead_6);

    let mut test_bead_7 = emit_bead();
    test_bead_7
        .committed_metadata
        .parents
        .push(compute_block_hash(
            &test_bead_6.block_header,
            PoolNetwork::Cpunet,
        ));
    test_braid.extend(&test_bead_7);

    let mut test_bead_8 = emit_bead();
    test_bead_8
        .committed_metadata
        .parents
        .push(compute_block_hash(
            &test_bead_7.block_header,
            PoolNetwork::Cpunet,
        ));
    test_braid.extend(&test_bead_8);

    assert_eq!(
        test_braid.cohorts,
        vec![
            Cohort(HashSet::from([0])),
            Cohort(HashSet::from([1])),
            Cohort(HashSet::from([2])),
            Cohort(HashSet::from([3, 4, 5, 6, 7, 8])),
        ]
    );

    // Create beads 9-11 with chain from bead 5
    let mut test_bead_9 = emit_bead();
    test_bead_9
        .committed_metadata
        .parents
        .push(compute_block_hash(
            &test_bead_5.block_header,
            PoolNetwork::Cpunet,
        ));
    test_braid.extend(&test_bead_9);

    let mut test_bead_10 = emit_bead();
    test_bead_10
        .committed_metadata
        .parents
        .push(compute_block_hash(
            &test_bead_9.block_header,
            PoolNetwork::Cpunet,
        ));
    test_braid.extend(&test_bead_10);

    let mut test_bead_11 = emit_bead();
    test_bead_11
        .committed_metadata
        .parents
        .push(compute_block_hash(
            &test_bead_10.block_header,
            PoolNetwork::Cpunet,
        ));
    test_braid.extend(&test_bead_11);

    assert_eq!(
        test_braid.cohorts,
        vec![
            Cohort(HashSet::from([0])),
            Cohort(HashSet::from([1])),
            Cohort(HashSet::from([2])),
            Cohort(HashSet::from([3, 4, 5, 6, 7, 8, 9, 10, 11])),
        ]
    );

    let mut test_bead_12 = emit_bead();
    test_bead_12
        .committed_metadata
        .parents
        .push(compute_block_hash(
            &test_bead_8.block_header,
            PoolNetwork::Cpunet,
        ));
    test_bead_12
        .committed_metadata
        .parents
        .push(compute_block_hash(
            &test_bead_11.block_header,
            PoolNetwork::Cpunet,
        ));
    test_bead_12
        .committed_metadata
        .parents
        .push(compute_block_hash(
            &test_bead_3.block_header,
            PoolNetwork::Cpunet,
        ));
    test_braid.extend(&test_bead_12);

    assert_eq!(
        test_braid.cohorts,
        vec![
            Cohort(HashSet::from([0])),
            Cohort(HashSet::from([1])),
            Cohort(HashSet::from([2])),
            Cohort(HashSet::from([3, 4, 5, 6, 7, 8, 9, 10, 11])),
            Cohort(HashSet::from([12])),
        ]
    );

    let mut test_bead_13 = emit_bead();
    test_bead_13
        .committed_metadata
        .parents
        .push(compute_block_hash(
            &test_bead_12.block_header,
            PoolNetwork::Cpunet,
        ));
    test_braid.extend(&test_bead_13);
    assert_eq!(
        test_braid.cohorts,
        vec![
            Cohort(HashSet::from([0])),
            Cohort(HashSet::from([1])),
            Cohort(HashSet::from([2])),
            Cohort(HashSet::from([3, 4, 5, 6, 7, 8, 9, 10, 11])),
            Cohort(HashSet::from([12])),
            Cohort(HashSet::from([13])),
        ]
    );
}

#[test]
pub fn test_orphan_beads_functinality() {
    let test_bead_0 = emit_bead();

    let mut test_braid = Braid {
        beads: vec![test_bead_0.clone()],
        genesis_beads: HashSet::from([0]),
        tips: HashSet::from([0]),
        orphan_beads: OrphanPool::new(DEFAULT_MAX_ORPHAN_BEADS),
        cohorts: vec![Cohort(HashSet::from([0]))],
        cohort_tips: vec![HashSet::from([0])],
        bead_index_mapping: std::collections::HashMap::from([(
            compute_block_hash(&test_bead_0.block_header, PoolNetwork::Cpunet),
            0,
        )]),
        network: PoolNetwork::Cpunet,
    };
    assert_eq!(
        test_braid.cohorts,
        vec![Cohort(HashSet::from([0]))],
        "Initial cohort should contain only the genesis bead"
    );

    let mut test_bead_1 = emit_bead();
    let mut test_bead_2 = emit_bead();

    test_bead_1
        .committed_metadata
        .parents
        .push(compute_block_hash(
            &test_bead_2.block_header,
            PoolNetwork::Cpunet,
        ));

    test_braid.extend(&test_bead_1);
    assert_eq!(
        test_braid.cohorts,
        vec![Cohort(HashSet::from([0]))],
        "The added bead was an orphan, cohort shouldn't change."
    );

    test_bead_2
        .committed_metadata
        .parents
        .push(compute_block_hash(
            &test_bead_0.block_header,
            PoolNetwork::Cpunet,
        ));
    test_braid.extend(&test_bead_2);

    // After adding the second bead, we should have three cohorts
    assert_eq!(
        test_braid.cohorts,
        vec![
            Cohort(HashSet::from([0])),
            Cohort(HashSet::from([1])),
            Cohort(HashSet::from([2]))
        ],
        "After adding the third bead, there should be three cohorts"
    );
}

#[test]
pub fn test_genesis1() {
    let test_bead_0 = emit_bead();
    let mut test_bead_1 = emit_bead();

    let mut test_bead_2 = emit_bead();

    let mut test_bead_3 = emit_bead();

    test_bead_1
        .committed_metadata
        .parents
        .push(compute_block_hash(
            &test_bead_0.block_header,
            PoolNetwork::Cpunet,
        ));
    test_bead_2
        .committed_metadata
        .parents
        .push(compute_block_hash(
            &test_bead_1.block_header,
            PoolNetwork::Cpunet,
        ));

    test_bead_3
        .committed_metadata
        .parents
        .push(compute_block_hash(
            &test_bead_2.block_header,
            PoolNetwork::Cpunet,
        ));

    let test_braid = Braid {
        beads: vec![
            test_bead_0.clone(),
            test_bead_1.clone(),
            test_bead_2.clone(),
            test_bead_3.clone(),
        ],
        genesis_beads: HashSet::from([0]),
        tips: HashSet::from([3]),
        orphan_beads: OrphanPool::new(DEFAULT_MAX_ORPHAN_BEADS),
        cohorts: vec![Cohort(HashSet::from([0]))],
        cohort_tips: vec![HashSet::from([0])],
        bead_index_mapping: std::collections::HashMap::from([
            (
                compute_block_hash(&test_bead_0.block_header, PoolNetwork::Cpunet),
                0,
            ),
            (
                compute_block_hash(&test_bead_1.block_header, PoolNetwork::Cpunet),
                1,
            ),
            (
                compute_block_hash(&test_bead_2.block_header, PoolNetwork::Cpunet),
                2,
            ),
            (
                compute_block_hash(&test_bead_3.block_header, PoolNetwork::Cpunet),
                3,
            ),
        ]),
        network: PoolNetwork::Cpunet,
    };

    //mapping of the indices with set of indices representing its parents
    //where the key represents the ith indexed bead from self.beads which contains all the beads
    //belonging to a particular braid and mapping is a set of indices of its parents present in
    //self.beads
    let mut parents1: HashMap<usize, HashSet<usize>> = HashMap::new();
    parents1.insert(0, HashSet::from([]));
    parents1.insert(1, HashSet::from([0]));
    parents1.insert(2, HashSet::from([1]));
    parents1.insert(3, HashSet::from([2]));

    let geneses_bead_indices = genesis(&test_braid, &parents1);
    assert_eq!(geneses_bead_indices, HashSet::from([0]));
}
#[test]
pub fn test_genesis2() {
    let test_bead_0 = emit_bead();
    let test_bead_1 = emit_bead();

    let mut test_bead_2 = emit_bead();

    let mut test_bead_3 = emit_bead();

    test_bead_2
        .committed_metadata
        .parents
        .push(test_bead_1.block_header.prev_blockhash);
    test_bead_3
        .committed_metadata
        .parents
        .push(test_bead_1.block_header.prev_blockhash);
    let test_braid = Braid {
        beads: vec![
            test_bead_0.clone(),
            test_bead_1.clone(),
            test_bead_2.clone(),
            test_bead_3.clone(),
        ],
        genesis_beads: HashSet::from([0]),
        tips: HashSet::from([3]),
        orphan_beads: OrphanPool::new(DEFAULT_MAX_ORPHAN_BEADS),
        cohorts: vec![Cohort(HashSet::from([0]))],
        cohort_tips: vec![HashSet::from([0])],
        bead_index_mapping: std::collections::HashMap::from([
            (
                compute_block_hash(&test_bead_0.block_header, PoolNetwork::Cpunet),
                0,
            ),
            (
                compute_block_hash(&test_bead_1.block_header, PoolNetwork::Cpunet),
                1,
            ),
            (
                compute_block_hash(&test_bead_2.block_header, PoolNetwork::Cpunet),
                2,
            ),
            (
                compute_block_hash(&test_bead_3.block_header, PoolNetwork::Cpunet),
                3,
            ),
        ]),
        network: PoolNetwork::Cpunet,
    };
    //mapping of the indices with set of indices representing its parents
    //where the key represents the ith indexed bead from self.beads which contains all the beads
    //belonging to a particular braid and mapping is a set of indices of its parents present in
    //self.beads
    let mut parents1: HashMap<usize, HashSet<usize>> = HashMap::new();
    parents1.insert(0, HashSet::from([]));
    parents1.insert(1, HashSet::from([]));
    parents1.insert(2, HashSet::from([1]));
    parents1.insert(3, HashSet::from([1]));

    let geneses_bead_indices = genesis(&test_braid, &parents1);
    assert_eq!(geneses_bead_indices, HashSet::from([0, 1]));
}
#[test]
pub fn test_genesis3() {
    let test_bead_0 = emit_bead();
    let test_bead_1 = emit_bead();

    let test_bead_2 = emit_bead();

    let mut test_bead_3 = emit_bead();

    let mut test_bead_4 = emit_bead();
    test_bead_3
        .committed_metadata
        .parents
        .push(compute_block_hash(
            &test_bead_1.block_header,
            PoolNetwork::Cpunet,
        ));
    test_bead_4
        .committed_metadata
        .parents
        .push(compute_block_hash(
            &test_bead_0.block_header,
            PoolNetwork::Cpunet,
        ));

    let test_braid = Braid {
        beads: vec![
            test_bead_0.clone(),
            test_bead_1.clone(),
            test_bead_2.clone(),
            test_bead_3.clone(),
            test_bead_4.clone(),
        ],
        genesis_beads: HashSet::from([0, 1, 2]),
        tips: HashSet::from([3]),
        orphan_beads: OrphanPool::new(DEFAULT_MAX_ORPHAN_BEADS),
        cohorts: vec![Cohort(HashSet::from([0]))],
        cohort_tips: vec![HashSet::from([0])],
        bead_index_mapping: std::collections::HashMap::from([
            (
                compute_block_hash(&test_bead_0.block_header, PoolNetwork::Cpunet),
                0,
            ),
            (
                compute_block_hash(&test_bead_1.block_header, PoolNetwork::Cpunet),
                1,
            ),
            (
                compute_block_hash(&test_bead_2.block_header, PoolNetwork::Cpunet),
                2,
            ),
            (
                compute_block_hash(&test_bead_3.block_header, PoolNetwork::Cpunet),
                3,
            ),
            (
                compute_block_hash(&test_bead_4.block_header, PoolNetwork::Cpunet),
                4,
            ),
        ]),
        network: PoolNetwork::Cpunet,
    };
    //mapping of the indices with set of indices representing its parents
    //where the key represents the ith indexed bead from self.beads which contains all the beads
    //belonging to a particular braid and mapping is a set of indices of its parents present in
    //self.beads
    let mut parents1: HashMap<usize, HashSet<usize>> = HashMap::new();
    parents1.insert(0, HashSet::from([]));
    parents1.insert(1, HashSet::from([]));
    parents1.insert(2, HashSet::from([]));
    parents1.insert(3, HashSet::from([1]));
    parents1.insert(3, HashSet::from([0]));

    let geneses_bead_indices = genesis(&test_braid, &parents1);
    assert_eq!(geneses_bead_indices, HashSet::from([0, 1, 2]));
}

#[test]
pub fn test_genesis_files() {
    let ancestors = std::env::current_dir().unwrap();
    let ancestors_directory: Vec<&Path> = ancestors.ancestors().collect();
    let parent_directory = ancestors_directory[1];
    let test_absolute_path = parent_directory.join(BRAIDTESTDIRECTORY);
    for test_braid_file in std::fs::read_dir(test_absolute_path.as_path()).unwrap() {
        let re = test_braid_file.unwrap().file_name();
        let current_file_name = re.to_str().unwrap();
        let file_path = test_absolute_path.join(current_file_name);
        let (current_file_braid, file_braid) = loading_braid_from_file(file_path.to_str().unwrap());
        let mut current_braid_parents: HashMap<usize, HashSet<usize>> = HashMap::new();
        for beads in file_braid.parents {
            let mut current_bead_parents: HashSet<usize> = HashSet::new();
            for parent_beads in beads.1 {
                current_bead_parents.insert(parent_beads);
            }
            current_braid_parents.insert(beads.0, current_bead_parents);
        }

        let computed_genesis_indices = genesis(&current_file_braid, &current_braid_parents);
        let current_file_genesis = file_braid.geneses;
        let mut file_genesis_set: HashSet<usize> = HashSet::new();
        for genesis_idx in current_file_genesis {
            file_genesis_set.insert(genesis_idx);
        }
        assert_eq!(file_genesis_set, computed_genesis_indices);
    }
}

#[test]
pub fn test_tips1() {
    let test_bead_0 = emit_bead();
    let mut test_bead_1 = emit_bead();

    let mut test_bead_2 = emit_bead();

    let mut test_bead_3 = emit_bead();

    test_bead_1
        .committed_metadata
        .parents
        .push(compute_block_hash(
            &test_bead_0.block_header,
            PoolNetwork::Cpunet,
        ));
    test_bead_2
        .committed_metadata
        .parents
        .push(compute_block_hash(
            &test_bead_1.block_header,
            PoolNetwork::Cpunet,
        ));

    test_bead_3
        .committed_metadata
        .parents
        .push(compute_block_hash(
            &test_bead_2.block_header,
            PoolNetwork::Cpunet,
        ));

    let test_braid = Braid {
        beads: vec![
            test_bead_0.clone(),
            test_bead_1.clone(),
            test_bead_2.clone(),
            test_bead_3.clone(),
        ],
        genesis_beads: HashSet::from([0]),
        tips: HashSet::from([3]),
        orphan_beads: OrphanPool::new(DEFAULT_MAX_ORPHAN_BEADS),
        cohorts: vec![Cohort(HashSet::from([0]))],
        cohort_tips: vec![HashSet::from([0])],
        bead_index_mapping: std::collections::HashMap::from([
            (
                compute_block_hash(&test_bead_0.block_header, PoolNetwork::Cpunet),
                0,
            ),
            (
                compute_block_hash(&test_bead_1.block_header, PoolNetwork::Cpunet),
                1,
            ),
            (
                compute_block_hash(&test_bead_2.block_header, PoolNetwork::Cpunet),
                2,
            ),
            (
                compute_block_hash(&test_bead_3.block_header, PoolNetwork::Cpunet),
                3,
            ),
        ]),
        network: PoolNetwork::Cpunet,
    };

    //mapping of the indices with set of indices representing its parents
    //where the key represents the ith indexed bead from self.beads which contains all the beads
    //belonging to a particular braid and mapping is a set of indices of its parents present in
    //self.beads
    let mut parents1: HashMap<usize, HashSet<usize>> = HashMap::new();
    parents1.insert(0, HashSet::from([]));
    parents1.insert(1, HashSet::from([0]));
    parents1.insert(2, HashSet::from([1]));
    parents1.insert(3, HashSet::from([2]));
    let tips_bead_indices = tips(&test_braid, &parents1);
    assert_eq!(tips_bead_indices, HashSet::from([3]));
}

#[test]
pub fn test_tips2() {
    let test_bead_0 = emit_bead();
    let mut test_bead_1 = emit_bead();

    let mut test_bead_2 = emit_bead();

    let mut test_bead_3 = emit_bead();

    test_bead_1
        .committed_metadata
        .parents
        .push(compute_block_hash(
            &test_bead_0.block_header,
            PoolNetwork::Cpunet,
        ));
    test_bead_2
        .committed_metadata
        .parents
        .push(compute_block_hash(
            &test_bead_1.block_header,
            PoolNetwork::Cpunet,
        ));

    test_bead_3
        .committed_metadata
        .parents
        .push(compute_block_hash(
            &test_bead_1.block_header,
            PoolNetwork::Cpunet,
        ));

    let test_braid = Braid {
        beads: vec![
            test_bead_0.clone(),
            test_bead_1.clone(),
            test_bead_2.clone(),
            test_bead_3.clone(),
        ],
        genesis_beads: HashSet::from([0]),
        tips: HashSet::from([3]),
        orphan_beads: OrphanPool::new(DEFAULT_MAX_ORPHAN_BEADS),
        cohorts: vec![Cohort(HashSet::from([0]))],
        cohort_tips: vec![HashSet::from([0])],
        bead_index_mapping: std::collections::HashMap::from([
            (
                compute_block_hash(&test_bead_0.block_header, PoolNetwork::Cpunet),
                0,
            ),
            (
                compute_block_hash(&test_bead_1.block_header, PoolNetwork::Cpunet),
                1,
            ),
            (
                compute_block_hash(&test_bead_2.block_header, PoolNetwork::Cpunet),
                2,
            ),
            (
                compute_block_hash(&test_bead_3.block_header, PoolNetwork::Cpunet),
                3,
            ),
        ]),
        network: PoolNetwork::Cpunet,
    };

    //mapping of the indices with set of indices representing its parents
    //where the key represents the ith indexed bead from self.beads which contains all the beads
    //belonging to a particular braid and mapping is a set of indices of its parents present in
    //self.beads
    let mut parents1: HashMap<usize, HashSet<usize>> = HashMap::new();
    parents1.insert(0, HashSet::from([]));
    parents1.insert(1, HashSet::from([0]));
    parents1.insert(2, HashSet::from([1]));
    parents1.insert(3, HashSet::from([1]));

    let tips_bead_indices = tips(&test_braid, &parents1);
    assert_eq!(tips_bead_indices, HashSet::from([2, 3]));
}

#[test]
pub fn test_tips3() {
    let test_bead_0 = emit_bead();
    let test_bead_1 = emit_bead();

    let test_bead_2 = emit_bead();

    let mut test_bead_3 = emit_bead();

    let mut test_bead_4 = emit_bead();

    let mut test_bead_5 = emit_bead();
    test_bead_3
        .committed_metadata
        .parents
        .push(compute_block_hash(
            &test_bead_0.block_header,
            PoolNetwork::Cpunet,
        ));
    test_bead_3
        .committed_metadata
        .parents
        .push(compute_block_hash(
            &test_bead_1.block_header,
            PoolNetwork::Cpunet,
        ));
    test_bead_3
        .committed_metadata
        .parents
        .push(compute_block_hash(
            &test_bead_2.block_header,
            PoolNetwork::Cpunet,
        ));
    test_bead_4
        .committed_metadata
        .parents
        .push(compute_block_hash(
            &test_bead_0.block_header,
            PoolNetwork::Cpunet,
        ));
    test_bead_4
        .committed_metadata
        .parents
        .push(compute_block_hash(
            &test_bead_1.block_header,
            PoolNetwork::Cpunet,
        ));
    test_bead_4
        .committed_metadata
        .parents
        .push(compute_block_hash(
            &test_bead_2.block_header,
            PoolNetwork::Cpunet,
        ));
    test_bead_5
        .committed_metadata
        .parents
        .push(compute_block_hash(
            &test_bead_0.block_header,
            PoolNetwork::Cpunet,
        ));
    test_bead_5
        .committed_metadata
        .parents
        .push(compute_block_hash(
            &test_bead_1.block_header,
            PoolNetwork::Cpunet,
        ));
    test_bead_5
        .committed_metadata
        .parents
        .push(compute_block_hash(
            &test_bead_2.block_header,
            PoolNetwork::Cpunet,
        ));
    let test_braid = Braid {
        beads: vec![
            test_bead_0.clone(),
            test_bead_1.clone(),
            test_bead_2.clone(),
            test_bead_3.clone(),
            test_bead_4.clone(),
            test_bead_5.clone(),
        ],
        genesis_beads: HashSet::from([0, 1, 2]),
        tips: HashSet::from([3, 4, 5]),
        orphan_beads: OrphanPool::new(DEFAULT_MAX_ORPHAN_BEADS),
        cohorts: vec![Cohort(HashSet::from([0]))],
        cohort_tips: vec![HashSet::from([0])],
        bead_index_mapping: std::collections::HashMap::from([
            (
                compute_block_hash(&test_bead_0.block_header, PoolNetwork::Cpunet),
                0,
            ),
            (
                compute_block_hash(&test_bead_1.block_header, PoolNetwork::Cpunet),
                1,
            ),
            (
                compute_block_hash(&test_bead_2.block_header, PoolNetwork::Cpunet),
                2,
            ),
            (
                compute_block_hash(&test_bead_3.block_header, PoolNetwork::Cpunet),
                3,
            ),
            (
                compute_block_hash(&test_bead_4.block_header, PoolNetwork::Cpunet),
                4,
            ),
            (
                compute_block_hash(&test_bead_5.block_header, PoolNetwork::Cpunet),
                5,
            ),
        ]),
        network: PoolNetwork::Cpunet,
    };
    //mapping of the indices with set of indices representing its parents
    //where the key represents the ith indexed bead from self.beads which contains all the beads
    //belonging to a particular braid and mapping is a set of indices of its parents present in
    //self.beads
    let mut parents1: HashMap<usize, HashSet<usize>> = HashMap::new();
    parents1.insert(0, HashSet::from([]));
    parents1.insert(1, HashSet::from([]));
    parents1.insert(2, HashSet::from([]));
    parents1.insert(3, HashSet::from([0, 1, 2]));
    parents1.insert(4, HashSet::from([0, 1, 2]));

    parents1.insert(5, HashSet::from([0, 1, 2]));

    let tips_bead_indices = tips(&test_braid, &parents1);
    assert_eq!(tips_bead_indices, HashSet::from([3, 4, 5]));
}
#[test]

pub fn test_reverse() {
    let test_bead_0 = emit_bead();
    let test_bead_1 = emit_bead();

    let test_bead_2 = emit_bead();

    let mut test_bead_3 = emit_bead();

    let mut test_bead_4 = emit_bead();

    let mut test_bead_5 = emit_bead();
    test_bead_3
        .committed_metadata
        .parents
        .push(compute_block_hash(
            &test_bead_0.block_header,
            PoolNetwork::Cpunet,
        ));
    test_bead_3
        .committed_metadata
        .parents
        .push(compute_block_hash(
            &test_bead_1.block_header,
            PoolNetwork::Cpunet,
        ));
    test_bead_3
        .committed_metadata
        .parents
        .push(compute_block_hash(
            &test_bead_2.block_header,
            PoolNetwork::Cpunet,
        ));
    test_bead_4
        .committed_metadata
        .parents
        .push(compute_block_hash(
            &test_bead_0.block_header,
            PoolNetwork::Cpunet,
        ));
    test_bead_4
        .committed_metadata
        .parents
        .push(compute_block_hash(
            &test_bead_1.block_header,
            PoolNetwork::Cpunet,
        ));
    test_bead_4
        .committed_metadata
        .parents
        .push(compute_block_hash(
            &test_bead_2.block_header,
            PoolNetwork::Cpunet,
        ));
    test_bead_5
        .committed_metadata
        .parents
        .push(compute_block_hash(
            &test_bead_0.block_header,
            PoolNetwork::Cpunet,
        ));
    test_bead_5
        .committed_metadata
        .parents
        .push(compute_block_hash(
            &test_bead_1.block_header,
            PoolNetwork::Cpunet,
        ));
    test_bead_5
        .committed_metadata
        .parents
        .push(compute_block_hash(
            &test_bead_2.block_header,
            PoolNetwork::Cpunet,
        ));
    let test_braid = Braid {
        beads: vec![
            test_bead_0.clone(),
            test_bead_1.clone(),
            test_bead_2.clone(),
            test_bead_3.clone(),
            test_bead_4.clone(),
            test_bead_5.clone(),
        ],
        genesis_beads: HashSet::from([0, 1, 2]),
        tips: HashSet::from([3, 4, 5]),
        orphan_beads: OrphanPool::new(DEFAULT_MAX_ORPHAN_BEADS),
        cohorts: vec![Cohort(HashSet::from([0]))],
        cohort_tips: vec![HashSet::from([0])],
        bead_index_mapping: std::collections::HashMap::from([
            (
                compute_block_hash(&test_bead_0.block_header, PoolNetwork::Cpunet),
                0,
            ),
            (
                compute_block_hash(&test_bead_1.block_header, PoolNetwork::Cpunet),
                1,
            ),
            (
                compute_block_hash(&test_bead_2.block_header, PoolNetwork::Cpunet),
                2,
            ),
            (
                compute_block_hash(&test_bead_3.block_header, PoolNetwork::Cpunet),
                3,
            ),
            (
                compute_block_hash(&test_bead_4.block_header, PoolNetwork::Cpunet),
                4,
            ),
            (
                compute_block_hash(&test_bead_5.block_header, PoolNetwork::Cpunet),
                5,
            ),
        ]),
        network: PoolNetwork::Cpunet,
    };
    //mapping of the indices with set of indices representing its parents
    //where the key represents the ith indexed bead from self.beads which contains all the beads
    //belonging to a particular braid and mapping is a set of indices of its parents present in
    //self.beads
    let mut parents1: HashMap<usize, HashSet<usize>> = HashMap::new();
    parents1.insert(0, HashSet::from([]));
    parents1.insert(1, HashSet::from([]));
    parents1.insert(2, HashSet::from([]));
    parents1.insert(3, HashSet::from([0, 1, 2]));
    parents1.insert(4, HashSet::from([0, 1, 2]));

    parents1.insert(5, HashSet::from([0, 1, 2]));
    let reverse_children_mapping = reverse(&test_braid, &parents1);
    let mut actual_children_mapping: HashMap<usize, HashSet<usize>> = HashMap::new();
    actual_children_mapping.insert(0, HashSet::from([3, 4, 5]));
    actual_children_mapping.insert(1, HashSet::from([3, 4, 5]));

    actual_children_mapping.insert(2, HashSet::from([3, 4, 5]));
    actual_children_mapping.insert(3, HashSet::new());
    actual_children_mapping.insert(4, HashSet::new());
    actual_children_mapping.insert(5, HashSet::new());
    assert_eq!(reverse_children_mapping, actual_children_mapping);
}
#[test]
pub fn test_all_ancestors() {
    let ancestors = std::env::current_dir().unwrap();
    let ancestors_directory: Vec<&Path> = ancestors.ancestors().collect();
    let parent_directory = ancestors_directory[1];
    let test_absolute_path = parent_directory.join(BRAIDTESTDIRECTORY);
    for test_braid_file in std::fs::read_dir(test_absolute_path.as_path()).unwrap() {
        let re = test_braid_file.unwrap().file_name();
        let current_file_name = re.to_str().unwrap();
        let file_path = test_absolute_path.join(current_file_name);
        let (current_file_braid, file_braid) = loading_braid_from_file(file_path.to_str().unwrap());
        let mut current_braid_parents: HashMap<usize, HashSet<usize>> = HashMap::new();
        for beads in file_braid.parents {
            let mut current_bead_parents: HashSet<usize> = HashSet::new();
            for parent_beads in beads.1 {
                current_bead_parents.insert(parent_beads);
            }
            current_braid_parents.insert(beads.0, current_bead_parents);
        }
        for bead_index in current_braid_parents.clone() {
            let current_bead_hash = compute_block_hash(
                &current_file_braid.beads[bead_index.0].block_header,
                PoolNetwork::Cpunet,
            );
            let mut d1_compute: HashMap<usize, HashSet<usize>> = HashMap::new();
            get_all_ancestors(
                &current_file_braid,
                current_bead_hash,
                &mut d1_compute,
                &current_braid_parents,
            );
            let mut d2_compute: HashMap<usize, HashSet<usize>> = HashMap::new();

            updating_ancestors(
                &current_file_braid,
                current_bead_hash,
                &mut d2_compute,
                &current_braid_parents,
            );
            assert_eq!(d1_compute, d2_compute);
        }
    }
}
#[test]

pub fn test_cohorts_parents_1() {
    let test_bead_0 = emit_bead();
    let mut test_bead_1 = emit_bead();

    let mut test_bead_2 = emit_bead();

    let mut test_bead_3 = emit_bead();

    test_bead_1
        .committed_metadata
        .parents
        .push(compute_block_hash(
            &test_bead_0.block_header,
            PoolNetwork::Cpunet,
        ));
    test_bead_2
        .committed_metadata
        .parents
        .push(compute_block_hash(
            &test_bead_1.block_header,
            PoolNetwork::Cpunet,
        ));

    test_bead_3
        .committed_metadata
        .parents
        .push(compute_block_hash(
            &test_bead_2.block_header,
            PoolNetwork::Cpunet,
        ));

    let test_braid = Braid {
        beads: vec![
            test_bead_0.clone(),
            test_bead_1.clone(),
            test_bead_2.clone(),
            test_bead_3.clone(),
        ],
        genesis_beads: HashSet::from([0]),
        tips: HashSet::from([3]),
        orphan_beads: OrphanPool::new(DEFAULT_MAX_ORPHAN_BEADS),
        cohorts: vec![Cohort(HashSet::from([0]))],
        cohort_tips: vec![HashSet::from([0])],
        bead_index_mapping: std::collections::HashMap::from([
            (
                compute_block_hash(&test_bead_0.block_header, PoolNetwork::Cpunet),
                0,
            ),
            (
                compute_block_hash(&test_bead_1.block_header, PoolNetwork::Cpunet),
                1,
            ),
            (
                compute_block_hash(&test_bead_2.block_header, PoolNetwork::Cpunet),
                2,
            ),
            (
                compute_block_hash(&test_bead_3.block_header, PoolNetwork::Cpunet),
                3,
            ),
        ]),
        network: PoolNetwork::Cpunet,
    };

    //mapping of the indices with set of indices representing its parents
    //where the key represents the ith indexed bead from self.beads which contains all the beads
    //belonging to a particular braid and mapping is a set of indices of its parents present in
    //self.beads
    let mut parents1: HashMap<usize, HashSet<usize>> = HashMap::new();
    parents1.insert(0, HashSet::from([]));
    parents1.insert(1, HashSet::from([0]));
    parents1.insert(2, HashSet::from([1]));
    parents1.insert(3, HashSet::from([2]));

    let cohort_indices = cohort(&test_braid, &parents1, None, None);
    assert_eq!(
        cohort_indices,
        vec![
            HashSet::from([0]),
            HashSet::from([1]),
            HashSet::from([2]),
            HashSet::from([3])
        ]
    );
}

#[test]
pub fn test_cohorts_braid_testcases() {
    let ancestors = std::env::current_dir().unwrap();
    let ancestors_directory: Vec<&Path> = ancestors.ancestors().collect();
    let parent_directory = ancestors_directory[1];
    let test_absolute_path = parent_directory.join(BRAIDTESTDIRECTORY);
    for test_braid_file in std::fs::read_dir(test_absolute_path.as_path()).unwrap() {
        let re = test_braid_file.unwrap().file_name();
        let current_file_name = re.to_str().unwrap();
        let file_path = test_absolute_path.join(current_file_name);
        let (current_file_braid, file_braid) = loading_braid_from_file(file_path.to_str().unwrap());
        let mut current_braid_parents: HashMap<usize, HashSet<usize>> = HashMap::new();
        for beads in file_braid.parents {
            let mut current_bead_parents: HashSet<usize> = HashSet::new();
            for parent_beads in beads.1 {
                current_bead_parents.insert(parent_beads);
            }
            current_braid_parents.insert(beads.0, current_bead_parents);
        }

        let cohort_indices = cohort(&current_file_braid, &current_braid_parents, None, None);

        let mut computed_cohorts: Vec<HashSet<usize>> = Vec::new();
        for cohort in cohort_indices {
            let mut current_cohort_beads: HashSet<usize> = HashSet::new();
            for bead in cohort {
                current_cohort_beads.insert(bead);
            }
            computed_cohorts.push(current_cohort_beads);
        }
        let current_file_cohorts = file_braid.cohorts;
        let mut current_file_cohorts_set_vec: Vec<HashSet<usize>> = Vec::new();
        for cohort in current_file_cohorts {
            let mut current_cohort: HashSet<usize> = HashSet::new();
            for cohort_bead in cohort {
                current_cohort.insert(cohort_bead);
            }
            current_file_cohorts_set_vec.push(current_cohort);
        }
        assert_eq!(computed_cohorts, current_file_cohorts_set_vec);
    }
}

#[test]
pub fn reverse_cohorts_testcases() {
    let test_absolute_path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .join(BRAIDTESTDIRECTORY);
    for test_braid_file in std::fs::read_dir(test_absolute_path.as_path()).unwrap() {
        let re = test_braid_file.unwrap().file_name();
        let current_file_name = re.to_str().unwrap();
        let file_path = test_absolute_path.join(current_file_name);
        let (current_file_braid, file_braid) = loading_braid_from_file(file_path.to_str().unwrap());
        let mut current_braid_parents: HashMap<usize, HashSet<usize>> = HashMap::new();
        for beads in file_braid.parents {
            let mut current_bead_parents: HashSet<usize> = HashSet::new();
            for parent_beads in beads.1 {
                current_bead_parents.insert(parent_beads);
            }
            current_braid_parents.insert(beads.0, current_bead_parents);
        }
        let reversed_beads = reverse(&current_file_braid, &current_braid_parents);

        let computed_val = cohort(&current_file_braid, &reversed_beads, None, None);

        let mut file_cohorts: Vec<HashSet<usize>> = file_braid
            .cohorts
            .iter()
            .map(|c| c.iter().copied().collect())
            .collect();
        file_cohorts.reverse();
        assert_eq!(
            computed_val, file_cohorts,
            "Reversed cohorts do not match for file: {}",
            current_file_name
        );
    }
}
#[test]
pub fn test_highest_work_path_1() {
    let test_bead_0 = emit_bead();
    let mut test_bead_1 = emit_bead();

    let mut test_bead_2 = emit_bead();

    let mut test_bead_3 = emit_bead();

    test_bead_1
        .committed_metadata
        .parents
        .push(compute_block_hash(
            &test_bead_0.block_header,
            PoolNetwork::Cpunet,
        ));
    test_bead_2
        .committed_metadata
        .parents
        .push(compute_block_hash(
            &test_bead_1.block_header,
            PoolNetwork::Cpunet,
        ));

    test_bead_3
        .committed_metadata
        .parents
        .push(compute_block_hash(
            &test_bead_2.block_header,
            PoolNetwork::Cpunet,
        ));

    let test_braid = Braid {
        beads: vec![
            test_bead_0.clone(),
            test_bead_1.clone(),
            test_bead_2.clone(),
            test_bead_3.clone(),
        ],
        genesis_beads: HashSet::from([0]),
        tips: HashSet::from([3]),
        orphan_beads: OrphanPool::new(DEFAULT_MAX_ORPHAN_BEADS),
        cohorts: vec![Cohort(HashSet::from([0]))],
        cohort_tips: vec![HashSet::from([0])],
        bead_index_mapping: std::collections::HashMap::from([
            (
                compute_block_hash(&test_bead_0.block_header, PoolNetwork::Cpunet),
                0,
            ),
            (
                compute_block_hash(&test_bead_1.block_header, PoolNetwork::Cpunet),
                1,
            ),
            (
                compute_block_hash(&test_bead_2.block_header, PoolNetwork::Cpunet),
                2,
            ),
            (
                compute_block_hash(&test_bead_3.block_header, PoolNetwork::Cpunet),
                3,
            ),
        ]),
        network: PoolNetwork::Cpunet,
    };

    //mapping of the indices with set of indices representing its parents
    //where the key represents the ith indexed bead from self.beads which contains all the beads
    //belonging to a particular braid and mapping is a set of indices of its parents present in
    //self.beads
    let mut parents1: HashMap<usize, HashSet<usize>> = HashMap::new();
    parents1.insert(0, HashSet::from([]));
    parents1.insert(1, HashSet::from([0]));
    parents1.insert(2, HashSet::from([1]));
    parents1.insert(3, HashSet::from([2]));
    let test_braid_child_beads = reverse(&test_braid, &parents1);
    let highest_work_path_bead_indices =
        highest_work_path(&test_braid, &parents1, Some(&test_braid_child_beads), None).unwrap();
    assert_eq!(highest_work_path_bead_indices, Vec::from([0, 1, 2, 3]));
}
#[test]
pub fn test_diamond_path_highest_work() {
    let test_bead_0 = emit_bead();
    let mut test_bead_1 = emit_bead();

    let mut test_bead_2 = emit_bead();

    let mut test_bead_3 = emit_bead();

    let mut test_bead_4 = emit_bead();

    test_bead_1
        .committed_metadata
        .parents
        .push(compute_block_hash(
            &test_bead_0.block_header,
            PoolNetwork::Cpunet,
        ));
    test_bead_2
        .committed_metadata
        .parents
        .push(compute_block_hash(
            &test_bead_0.block_header,
            PoolNetwork::Cpunet,
        ));
    test_bead_3
        .committed_metadata
        .parents
        .push(compute_block_hash(
            &test_bead_1.block_header,
            PoolNetwork::Cpunet,
        ));
    test_bead_3
        .committed_metadata
        .parents
        .push(compute_block_hash(
            &test_bead_2.block_header,
            PoolNetwork::Cpunet,
        ));
    test_bead_4
        .committed_metadata
        .parents
        .push(compute_block_hash(
            &test_bead_3.block_header,
            PoolNetwork::Cpunet,
        ));

    let test_braid = Braid {
        beads: vec![
            test_bead_0.clone(),
            test_bead_1.clone(),
            test_bead_2.clone(),
            test_bead_3.clone(),
            test_bead_4.clone(),
        ],
        genesis_beads: HashSet::from([0]),
        tips: HashSet::from([3]),
        orphan_beads: OrphanPool::new(DEFAULT_MAX_ORPHAN_BEADS),
        cohorts: vec![Cohort(HashSet::from([0]))],
        cohort_tips: vec![HashSet::from([0])],
        bead_index_mapping: std::collections::HashMap::from([
            (
                compute_block_hash(&test_bead_0.block_header, PoolNetwork::Cpunet),
                0,
            ),
            (
                compute_block_hash(&test_bead_1.block_header, PoolNetwork::Cpunet),
                1,
            ),
            (
                compute_block_hash(&test_bead_2.block_header, PoolNetwork::Cpunet),
                2,
            ),
            (
                compute_block_hash(&test_bead_3.block_header, PoolNetwork::Cpunet),
                3,
            ),
            (
                compute_block_hash(&test_bead_4.block_header, PoolNetwork::Cpunet),
                4,
            ),
        ]),
        network: PoolNetwork::Cpunet,
    };
    //mapping of the indices with set of indices representing its parents
    //where the key represents the ith indexed bead from self.beads which contains all the beads
    //belonging to a particular braid and mapping is a set of indices of its parents present in
    //self.beads
    let mut parents1: HashMap<usize, HashSet<usize>> = HashMap::new();
    parents1.insert(0, HashSet::from([]));
    parents1.insert(1, HashSet::from([0]));
    parents1.insert(2, HashSet::from([0]));
    parents1.insert(3, HashSet::from([1, 2]));
    parents1.insert(4, HashSet::from([3]));
    let test_braid_child_mapping = reverse(&test_braid, &parents1);
    let highest_work_path = highest_work_path(
        &test_braid,
        &parents1,
        Some(&test_braid_child_mapping),
        None,
    )
    .unwrap();

    assert_eq!(highest_work_path, Vec::from([0, 1, 3, 4]));
}

#[test]
pub fn highest_work_path_testcases_directory() {
    let ancestors = std::env::current_dir().unwrap();
    let ancestors_directory: Vec<&Path> = ancestors.ancestors().collect();
    let parent_directory = ancestors_directory[1];
    let test_absolute_path = parent_directory.join(BRAIDTESTDIRECTORY);
    for test_braid_file in std::fs::read_dir(test_absolute_path.as_path()).unwrap() {
        let re = test_braid_file.unwrap().file_name();
        let current_file_name = re.to_str().unwrap();
        let file_path = test_absolute_path.join(current_file_name);
        let (current_file_braid, file_braid) = loading_braid_from_file(file_path.to_str().unwrap());
        let mut current_braid_parents: HashMap<usize, HashSet<usize>> = HashMap::new();
        for beads in file_braid.parents {
            let mut current_bead_parents: HashSet<usize> = HashSet::new();
            for parent_beads in beads.1 {
                current_bead_parents.insert(parent_beads);
            }
            current_braid_parents.insert(beads.0, current_bead_parents);
        }
        let current_braid_children_mapping = reverse(&current_file_braid, &current_braid_parents);
        let highest_work_path = highest_work_path(
            &current_file_braid,
            &current_braid_parents,
            Some(&current_braid_children_mapping),
            None,
        )
        .unwrap();
        assert_eq!(highest_work_path, file_braid.highest_work_path);
    }
}

#[test]
pub fn test_check_cohort_files() {
    let ancestors = std::env::current_dir().unwrap();
    let ancestors_directory: Vec<&Path> = ancestors.ancestors().collect();
    let parent_directory = ancestors_directory[1];
    let test_absolute_path = parent_directory.join(BRAIDTESTDIRECTORY);
    for test_braid_file in std::fs::read_dir(test_absolute_path.as_path()).unwrap() {
        let re = test_braid_file.unwrap().file_name();
        let current_file_name = re.to_str().unwrap();
        let file_path = test_absolute_path.join(current_file_name);

        let (current_file_braid, file_braid) = loading_braid_from_file(file_path.to_str().unwrap());
        let mut current_braid_parents: HashMap<usize, HashSet<usize>> = HashMap::new();
        for beads in file_braid.parents {
            let mut current_bead_parents: HashSet<usize> = HashSet::new();
            for parent_beads in beads.1 {
                current_bead_parents.insert(parent_beads);
            }
            current_braid_parents.insert(beads.0, current_bead_parents);
        }
        let current_braid_children_mapping = reverse(&current_file_braid, &current_braid_parents);
        let current_braid_cohorts = file_braid.cohorts;
        for cohort in current_braid_cohorts {
            let mut cohort_set: HashSet<usize> = HashSet::new();
            for bead in cohort.clone() {
                cohort_set.insert(bead);
            }
            let result = check_cohort(
                &current_file_braid,
                &cohort_set,
                &current_braid_parents,
                Some(&current_braid_children_mapping),
            );
            assert_eq!(result, true);
        }
    }
}
#[test]
pub fn test_sub_braids() {
    let ancestors = std::env::current_dir().unwrap();
    let ancestors_directory: Vec<&Path> = ancestors.ancestors().collect();
    let parent_directory = ancestors_directory[1];
    let test_absolute_path = parent_directory.join(BRAIDTESTDIRECTORY);
    for test_braid_file in std::fs::read_dir(test_absolute_path.as_path()).unwrap() {
        let re = test_braid_file.unwrap().file_name();
        let current_file_name = re.to_str().unwrap();
        let file_path = test_absolute_path.join(current_file_name);

        let (current_file_braid, file_braid) = loading_braid_from_file(file_path.to_str().unwrap());
        let mut current_braid_parents: HashMap<usize, HashSet<usize>> = HashMap::new();
        for beads in file_braid.parents {
            let mut current_bead_parents: HashSet<usize> = HashSet::new();
            for parent_beads in beads.1 {
                current_bead_parents.insert(parent_beads);
            }
            current_braid_parents.insert(beads.0, current_bead_parents);
        }
        let current_braid_children_mapping = reverse(&current_file_braid, &current_braid_parents);
        let current_braid_cohorts = file_braid.cohorts;
        for cohort in current_braid_cohorts {
            let mut cohort_set: HashSet<usize> = HashSet::new();
            for bead in cohort.clone() {
                cohort_set.insert(bead);
            }
            let sub_braid = get_sub_braid(&current_file_braid, &cohort_set, &current_braid_parents);
            let gen = genesis(&current_file_braid, &sub_braid);
            let curr_cohort_head = cohort_head(
                &current_file_braid,
                &cohort_set,
                &current_braid_parents,
                Some(&current_braid_children_mapping),
            );
            assert_eq!(gen, curr_cohort_head);

            let curr_cohort_tips = tips(&current_file_braid, &sub_braid);
            let curr_cohort_tail = cohort_tail(
                &current_file_braid,
                &cohort_set,
                &current_braid_parents,
                Some(current_braid_children_mapping.clone()),
            );
            assert_eq!(curr_cohort_tail, curr_cohort_tips);
        }
    }
}
#[test]
pub fn test_cohort_tail_braids() {
    let ancestors = std::env::current_dir().unwrap();
    let ancestors_directory: Vec<&Path> = ancestors.ancestors().collect();
    let parent_directory = ancestors_directory[1];
    let test_absolute_path = parent_directory.join(BRAIDTESTDIRECTORY);
    for test_braid_file in std::fs::read_dir(test_absolute_path.as_path()).unwrap() {
        let re = test_braid_file.unwrap().file_name();
        let current_file_name = re.to_str().unwrap();
        let file_path = test_absolute_path.join(current_file_name);

        let (current_file_braid, file_braid) = loading_braid_from_file(file_path.to_str().unwrap());
        let mut current_braid_parents: HashMap<usize, HashSet<usize>> = HashMap::new();
        for beads in file_braid.parents {
            let mut current_bead_parents: HashSet<usize> = HashSet::new();
            for parent_beads in beads.1 {
                current_bead_parents.insert(parent_beads);
            }
            current_braid_parents.insert(beads.0, current_bead_parents);
        }
        let current_braid_children_mapping = reverse(&current_file_braid, &current_braid_parents);
        let current_braid_cohorts = file_braid.cohorts;
        for cohort in current_braid_cohorts {
            let mut cohort_set: HashSet<usize> = HashSet::new();
            for bead in cohort.clone() {
                cohort_set.insert(bead);
            }
            let a = cohort_tail(
                &current_file_braid,
                &cohort_set,
                &current_braid_parents,
                Some(current_braid_children_mapping.clone()),
            );
            let b = get_sub_braid(&current_file_braid, &cohort_set, &current_braid_parents);

            let c = tips(&current_file_braid, &b);
            assert_eq!(a, c);
        }
    }
}
#[test]
pub fn test_cohort_head_braids() {
    let ancestors = std::env::current_dir().unwrap();
    let ancestors_directory: Vec<&Path> = ancestors.ancestors().collect();
    let parent_directory = ancestors_directory[1];
    let test_absolute_path = parent_directory.join(BRAIDTESTDIRECTORY);
    for test_braid_file in std::fs::read_dir(test_absolute_path.as_path()).unwrap() {
        let re = test_braid_file.unwrap().file_name();
        let current_file_name = re.to_str().unwrap();
        let file_path = test_absolute_path.join(current_file_name);

        let (current_file_braid, file_braid) = loading_braid_from_file(file_path.to_str().unwrap());
        let mut current_braid_parents: HashMap<usize, HashSet<usize>> = HashMap::new();
        for beads in file_braid.parents {
            let mut current_bead_parents: HashSet<usize> = HashSet::new();
            for parent_beads in beads.1 {
                current_bead_parents.insert(parent_beads);
            }
            current_braid_parents.insert(beads.0, current_bead_parents);
        }
        let current_braid_children_mapping = reverse(&current_file_braid, &current_braid_parents);
        let current_braid_cohorts = file_braid.cohorts;
        for cohort in current_braid_cohorts {
            let mut cohort_set: HashSet<usize> = HashSet::new();
            for bead in cohort.clone() {
                cohort_set.insert(bead);
            }
            let c = cohort_head(
                &current_file_braid,
                &cohort_set,
                &current_braid_parents,
                Some(&current_braid_children_mapping),
            );
            let d = get_sub_braid(&current_file_braid, &cohort_set, &current_braid_parents);
            let e = genesis(&current_file_braid, &d);
            assert_eq!(e, c);
        }
    }
}
#[test]
pub fn test_check_work_files() {
    let ancestors = std::env::current_dir().unwrap();
    let ancestors_directory: Vec<&Path> = ancestors.ancestors().collect();
    let parent_directory = ancestors_directory[1];
    let test_absolute_path = parent_directory.join(BRAIDTESTDIRECTORY);
    for test_braid_file in std::fs::read_dir(test_absolute_path.as_path()).unwrap() {
        let re = test_braid_file.unwrap().file_name();
        let current_file_name = re.to_str().unwrap();
        let file_path = test_absolute_path.join(current_file_name);

        let (current_file_braid, file_braid) = loading_braid_from_file(file_path.to_str().unwrap());
        let mut current_braid_parents: HashMap<usize, HashSet<usize>> = HashMap::new();
        for beads in file_braid.parents {
            let mut current_bead_parents: HashSet<usize> = HashSet::new();
            for parent_beads in beads.1 {
                current_bead_parents.insert(parent_beads);
            }
            current_braid_parents.insert(beads.0, current_bead_parents);
        }
        let current_braid_children_mapping = reverse(&current_file_braid, &current_braid_parents);
        let current_braid_cohorts = file_braid.cohorts;
        let current_dag_braid_work_u32 = file_braid.work.clone();
        let mut current_dag_braid_work = HashMap::new();
        for (idx, work) in current_dag_braid_work_u32 {
            current_dag_braid_work.insert(idx, BigUint::from(work));
        }
        for cohort in current_braid_cohorts {
            let mut cohort_set: HashSet<usize> = HashSet::new();
            for bead in cohort.clone() {
                cohort_set.insert(bead);
            }
            let current_file_braid_bead_work_u32 = file_braid.bead_work.clone();
            let mut current_file_braid_bead_work = HashMap::new();

            for (idx, work) in current_file_braid_bead_work_u32 {
                current_file_braid_bead_work.insert(idx, BigUint::from(work));
            }
            let current_cohort_descendant_work = descendant_work(
                &current_file_braid,
                &current_braid_parents,
                Some(&current_braid_children_mapping),
                Some(&current_file_braid_bead_work),
                None,
            );
            assert_eq!(current_cohort_descendant_work, current_dag_braid_work);
        }
    }
}

#[test]
fn test_extend_function() {
    let ancestors = std::env::current_dir().unwrap();
    let ancestors_directory: Vec<&Path> = ancestors.ancestors().collect();
    let parent_directory = ancestors_directory[1];
    let test_absolute_path = parent_directory.join(BRAIDTESTDIRECTORY);

    for test_braid_file in std::fs::read_dir(test_absolute_path.as_path()).unwrap() {
        let re = test_braid_file.unwrap().file_name();
        let current_file_name = re.to_str().unwrap();
        let file_path = test_absolute_path.join(current_file_name);
        let (_, file_braid) = loading_braid_from_file(file_path.to_str().unwrap());

        let mut current_braid_parents: HashMap<usize, HashSet<usize>> = HashMap::new();
        for beads in file_braid.parents {
            let mut current_bead_parents: HashSet<usize> = HashSet::new();
            for parent_beads in beads.1 {
                current_bead_parents.insert(parent_beads);
            }
            current_braid_parents.insert(beads.0, current_bead_parents);
        }

        let mut index_to_bead: HashMap<usize, Bead> = HashMap::new();
        let mut max_index = 0;

        // First generate all beads
        for &index in current_braid_parents.keys() {
            let bead = emit_bead();
            index_to_bead.insert(index, bead);
            max_index = max_index.max(index);
        }

        let mut parent_hashes: HashMap<usize, Vec<bitcoin::BlockHash>> = HashMap::new();
        for (index, parents) in &current_braid_parents {
            let mut hashes = Vec::new();
            for &parent_idx in parents {
                if let Some(parent_bead) = index_to_bead.get(&parent_idx) {
                    hashes.push(compute_block_hash(
                        &parent_bead.block_header,
                        PoolNetwork::Cpunet,
                    ));
                }
            }
            parent_hashes.insert(*index, hashes);
        }

        // Now set up parent relationships in committed metadata
        for (index, hashes) in parent_hashes {
            if let Some(bead) = index_to_bead.get_mut(&index) {
                for hash in hashes {
                    bead.committed_metadata.parents.push(hash);
                }
            }
        }

        let genesis_indices: HashSet<usize> = current_braid_parents
            .iter()
            .filter(|(_, parents)| parents.is_empty())
            .map(|(&idx, _)| idx)
            .collect();

        assert_eq!(genesis_indices, HashSet::from([0]));

        // Create initial braid with genesis beads
        let mut genesis_beads = Vec::new();
        let mut genesis_set = HashSet::new();
        let mut bead_index_mapping = HashMap::new();

        for &idx in &genesis_indices {
            if let Some(bead) = index_to_bead.get(&idx) {
                genesis_beads.push(bead.clone());
                genesis_set.insert(idx);
                bead_index_mapping.insert(
                    compute_block_hash(&bead.block_header, PoolNetwork::Cpunet),
                    idx,
                );
            }
        }

        let mut test_braid = Braid {
            beads: genesis_beads,
            tips: genesis_set.clone(),
            cohorts: vec![Cohort(genesis_set.clone())],
            cohort_tips: vec![genesis_set.clone()],
            orphan_beads: OrphanPool::new(DEFAULT_MAX_ORPHAN_BEADS),
            genesis_beads: genesis_set,
            bead_index_mapping,
            network: PoolNetwork::Cpunet,
        };

        // Extend braid with remaining beads in order of index
        for index in 0..=max_index {
            if !genesis_indices.contains(&index) {
                if let Some(bead) = index_to_bead.get(&index) {
                    test_braid.extend(bead);
                }
            }
        }
        assert_eq!(test_braid.beads.len(), current_braid_parents.len());

        let mut computed_cohorts_by_hash: Vec<HashSet<bitcoin::BlockHash>> = Vec::new();
        for cohort in &test_braid.cohorts {
            let mut cohort_hashes = HashSet::new();
            for &bead_idx in &cohort.0 {
                let bead_hash = test_braid.compute_bead_hash(&test_braid.beads[bead_idx]);
                cohort_hashes.insert(bead_hash);
            }
            computed_cohorts_by_hash.push(cohort_hashes);
        }

        let mut file_cohorts_by_hash: Vec<HashSet<bitcoin::BlockHash>> = Vec::new();
        for cohort in &file_braid.cohorts {
            let mut cohort_hashes = HashSet::new();
            for &bead_idx in cohort {
                if let Some(bead) = index_to_bead.get(&bead_idx) {
                    let bead_hash = compute_block_hash(&bead.block_header, PoolNetwork::Cpunet);
                    cohort_hashes.insert(bead_hash);
                }
            }
            file_cohorts_by_hash.push(cohort_hashes);
        }

        assert_eq!(computed_cohorts_by_hash, file_cohorts_by_hash);
    }
}

#[test]
fn test_get_beads_after() {
    // Test Case 1: Simple linear chain
    // Genesis -> Bead1 -> Bead2 -> Bead3
    // Test getting beads after genesis, after bead1, etc.

    let mut beads = Vec::new();
    let mut parent_relationships = HashMap::new();

    // Create 4 beads for a linear chain
    for _i in 0..4 {
        beads.push(emit_bead());
    }

    // Set up parent relationships for linear chain
    parent_relationships.insert(0, HashSet::new()); // Genesis has no parents
    parent_relationships.insert(1, HashSet::from([0])); // Bead1 -> Genesis
    parent_relationships.insert(2, HashSet::from([1])); // Bead2 -> Bead1
    parent_relationships.insert(3, HashSet::from([2])); // Bead3 -> Bead2

    // Collect parent hashes first to avoid borrowing issues
    let mut parent_hashes: HashMap<usize, Vec<bitcoin::BlockHash>> = HashMap::new();
    for (index, parents) in &parent_relationships {
        let mut hashes = Vec::new();
        for &parent_idx in parents {
            hashes.push(compute_block_hash(
                &beads[parent_idx].block_header,
                PoolNetwork::Cpunet,
            ));
        }
        parent_hashes.insert(*index, hashes);
    }

    // Update parent hashes in committed metadata
    for (index, hashes) in parent_hashes {
        for hash in hashes {
            beads[index].committed_metadata.parents.push(hash);
        }
    }

    // Create braid with genesis
    let genesis_set = HashSet::from([0]);
    let mut bead_index_mapping = HashMap::new();
    bead_index_mapping.insert(
        compute_block_hash(&beads[0].block_header, PoolNetwork::Cpunet),
        0,
    );

    let mut test_braid = Braid {
        beads: vec![beads[0].clone()],
        tips: genesis_set.clone(),
        cohorts: vec![Cohort(genesis_set.clone())],
        cohort_tips: vec![genesis_set.clone()],
        orphan_beads: OrphanPool::new(DEFAULT_MAX_ORPHAN_BEADS),
        genesis_beads: genesis_set,
        bead_index_mapping,
        network: PoolNetwork::Cpunet,
    };

    // Extend braid with remaining beads
    for i in 1..4 {
        test_braid.extend(&beads[i]);
    }

    // Test 1: Get beads after genesis (should return beads 1, 2, 3)
    let genesis_hash = compute_block_hash(&beads[0].block_header, PoolNetwork::Cpunet);
    let result = test_braid.get_beads_after(vec![genesis_hash]);
    assert!(result.is_some());
    let returned_beads = result.unwrap();

    // Should return beads from cohort containing genesis onwards
    // In a linear chain, each bead is in its own cohort after genesis
    assert!(
        returned_beads.len() >= 3,
        "Should return at least 3 beads after genesis"
    );

    // Verify the returned beads contain the expected hashes
    let returned_hashes: HashSet<_> = returned_beads
        .iter()
        .map(|b| compute_block_hash(&b.block_header, PoolNetwork::Cpunet))
        .collect();
    assert!(returned_hashes.contains(&compute_block_hash(
        &beads[1].block_header,
        PoolNetwork::Cpunet
    )));
    assert!(returned_hashes.contains(&compute_block_hash(
        &beads[2].block_header,
        PoolNetwork::Cpunet
    )));
    assert!(returned_hashes.contains(&compute_block_hash(
        &beads[3].block_header,
        PoolNetwork::Cpunet
    )));

    // Test 2: Get beads after bead1 (should return beads 2, 3)
    let bead1_hash = compute_block_hash(&beads[1].block_header, PoolNetwork::Cpunet);
    let result = test_braid.get_beads_after(vec![bead1_hash]);
    assert!(result.is_some());
    let returned_beads = result.unwrap();

    let returned_hashes: HashSet<_> = returned_beads
        .iter()
        .map(|b| compute_block_hash(&b.block_header, PoolNetwork::Cpunet))
        .collect();
    assert!(returned_hashes.contains(&compute_block_hash(
        &beads[2].block_header,
        PoolNetwork::Cpunet
    )));
    assert!(returned_hashes.contains(&compute_block_hash(
        &beads[3].block_header,
        PoolNetwork::Cpunet
    )));

    // Test 3: Get beads after the last bead (should return empty or just that bead)
    let last_hash = compute_block_hash(&beads[3].block_header, PoolNetwork::Cpunet);
    let result = test_braid.get_beads_after(vec![last_hash]);
    assert!(result.is_none());

    println!("Linear chain tests passed");
}

#[test]
fn test_get_beads_after_diamond_structure() {
    // Test Case 2: Diamond structure
    //     Genesis (0)
    //    /           \
    //   Bead1(1)    Bead2(2)
    //    \           /
    //     Bead3(3)

    let mut beads = Vec::new();
    let mut parent_relationships = HashMap::new();

    // Create 4 beads for diamond structure
    for _i in 0..4 {
        beads.push(emit_bead());
    }

    // Set up parent relationships for diamond
    parent_relationships.insert(0, HashSet::new()); // Genesis
    parent_relationships.insert(1, HashSet::from([0])); // Bead1 -> Genesis
    parent_relationships.insert(2, HashSet::from([0])); // Bead2 -> Genesis
    parent_relationships.insert(3, HashSet::from([1, 2])); // Bead3 -> Bead1, Bead2

    // Collect parent hashes first to avoid borrowing issues
    let mut parent_hashes: HashMap<usize, Vec<bitcoin::BlockHash>> = HashMap::new();
    for (index, parents) in &parent_relationships {
        let mut hashes = Vec::new();
        for &parent_idx in parents {
            hashes.push(compute_block_hash(
                &beads[parent_idx].block_header,
                PoolNetwork::Cpunet,
            ));
        }
        parent_hashes.insert(*index, hashes);
    }

    // Update parent hashes in committed metadata
    for (index, hashes) in parent_hashes {
        for hash in hashes {
            beads[index].committed_metadata.parents.push(hash);
        }
    }

    // Create braid with genesis
    let genesis_set = HashSet::from([0]);
    let mut bead_index_mapping = HashMap::new();
    bead_index_mapping.insert(
        compute_block_hash(&beads[0].block_header, PoolNetwork::Cpunet),
        0,
    );

    let mut test_braid = Braid {
        beads: vec![beads[0].clone()],
        tips: genesis_set.clone(),
        cohorts: vec![Cohort(genesis_set.clone())],
        cohort_tips: vec![genesis_set.clone()],
        orphan_beads: OrphanPool::new(DEFAULT_MAX_ORPHAN_BEADS),
        genesis_beads: genesis_set,
        bead_index_mapping,
        network: PoolNetwork::Cpunet,
    };

    // Extend braid with remaining beads
    for i in 1..4 {
        test_braid.extend(&beads[i]);
    }

    // Test 1: Get beads after genesis
    let genesis_hash = compute_block_hash(&beads[0].block_header, PoolNetwork::Cpunet);
    let result = test_braid.get_beads_after(vec![genesis_hash]);
    assert!(result.is_some());
    let returned_beads = result.unwrap();

    // Should include all beads after genesis
    let returned_hashes: HashSet<_> = returned_beads
        .iter()
        .map(|b| compute_block_hash(&b.block_header, PoolNetwork::Cpunet))
        .collect();
    assert!(returned_hashes.contains(&compute_block_hash(
        &beads[1].block_header,
        PoolNetwork::Cpunet
    )));
    assert!(returned_hashes.contains(&compute_block_hash(
        &beads[2].block_header,
        PoolNetwork::Cpunet
    )));
    assert!(returned_hashes.contains(&compute_block_hash(
        &beads[3].block_header,
        PoolNetwork::Cpunet
    )));

    // Test 2: Get beads after both middle beads (should return bead3)
    let bead1_hash = compute_block_hash(&beads[1].block_header, PoolNetwork::Cpunet);
    let bead2_hash = compute_block_hash(&beads[2].block_header, PoolNetwork::Cpunet);
    let result = test_braid.get_beads_after(vec![bead1_hash, bead2_hash]);
    assert!(result.is_some());
    let returned_beads = result.unwrap();

    let returned_hashes: HashSet<_> = returned_beads
        .iter()
        .map(|b| compute_block_hash(&b.block_header, PoolNetwork::Cpunet))
        .collect();
    assert!(returned_hashes.contains(&compute_block_hash(
        &beads[3].block_header,
        PoolNetwork::Cpunet
    )));

    println!("Diamond structure tests passed");
}

#[test]
fn test_get_beads_after_complex_braid() {
    // Test Case 3: More complex braid structure
    //     Genesis(0)
    //    /     |     \
    //   B1(1)  B2(2)  B3(3)
    //   |      |      |
    //   B4(4)  B5(5)  B6(6)
    //    \     |     /
    //      B7(7)

    let mut beads = Vec::new();
    let mut parent_relationships = HashMap::new();

    // Create 8 beads
    for _i in 0..8 {
        beads.push(emit_bead());
    }

    // Set up parent relationships
    parent_relationships.insert(0, HashSet::new()); // Genesis
    parent_relationships.insert(1, HashSet::from([0])); // B1 -> Genesis
    parent_relationships.insert(2, HashSet::from([0])); // B2 -> Genesis
    parent_relationships.insert(3, HashSet::from([0])); // B3 -> Genesis
    parent_relationships.insert(4, HashSet::from([1])); // B4 -> B1
    parent_relationships.insert(5, HashSet::from([2])); // B5 -> B2
    parent_relationships.insert(6, HashSet::from([3])); // B6 -> B3
    parent_relationships.insert(7, HashSet::from([4, 5, 6])); // B7 -> B4, B5, B6

    // Collect parent hashes first to avoid borrowing issues
    let mut parent_hashes: HashMap<usize, Vec<bitcoin::BlockHash>> = HashMap::new();
    for (index, parents) in &parent_relationships {
        let mut hashes = Vec::new();
        for &parent_idx in parents {
            hashes.push(compute_block_hash(
                &beads[parent_idx].block_header,
                PoolNetwork::Cpunet,
            ));
        }
        parent_hashes.insert(*index, hashes);
    }

    // Update parent hashes in committed metadata
    for (index, hashes) in parent_hashes {
        for hash in hashes {
            beads[index].committed_metadata.parents.push(hash);
        }
    }

    // Create braid with genesis
    let genesis_set = HashSet::from([0]);
    let mut bead_index_mapping = HashMap::new();
    bead_index_mapping.insert(
        compute_block_hash(&beads[0].block_header, PoolNetwork::Cpunet),
        0,
    );

    let mut test_braid = Braid {
        beads: vec![beads[0].clone()],
        tips: genesis_set.clone(),
        cohorts: vec![Cohort(genesis_set.clone())],
        cohort_tips: vec![genesis_set.clone()],
        orphan_beads: OrphanPool::new(DEFAULT_MAX_ORPHAN_BEADS),
        genesis_beads: genesis_set,
        bead_index_mapping,
        network: PoolNetwork::Cpunet,
    };

    // Extend braid with remaining beads
    for i in 1..8 {
        test_braid.extend(&beads[i]);
    }

    // Test 1: Get beads after genesis (should return all other beads)
    let genesis_hash = compute_block_hash(&beads[0].block_header, PoolNetwork::Cpunet);
    let result = test_braid.get_beads_after(vec![genesis_hash]);
    assert!(result.is_some());
    let returned_beads = result.unwrap();
    assert!(
        returned_beads.len() >= 7,
        "Should return at least 7 beads after genesis"
    );

    // Test 2: Get beads after first cohort (B1, B2, B3)
    let b1_hash = compute_block_hash(&beads[1].block_header, PoolNetwork::Cpunet);
    let result = test_braid.get_beads_after(vec![b1_hash]);
    assert!(result.is_some());
    let returned_beads = result.unwrap();

    let returned_hashes: HashSet<_> = returned_beads
        .iter()
        .map(|b| compute_block_hash(&b.block_header, PoolNetwork::Cpunet))
        .collect();

    // Should include beads from the cohort containing B1 onwards
    assert!(
        returned_hashes.contains(&compute_block_hash(
            &beads[4].block_header,
            PoolNetwork::Cpunet
        )) || returned_hashes.contains(&compute_block_hash(
            &beads[5].block_header,
            PoolNetwork::Cpunet
        )) || returned_hashes.contains(&compute_block_hash(
            &beads[6].block_header,
            PoolNetwork::Cpunet
        )) || returned_hashes.contains(&compute_block_hash(
            &beads[7].block_header,
            PoolNetwork::Cpunet
        ))
    );

    // Test 3: Get beads after multiple tips from second level
    let b4_hash = compute_block_hash(&beads[4].block_header, PoolNetwork::Cpunet);
    let b5_hash = compute_block_hash(&beads[5].block_header, PoolNetwork::Cpunet);
    let result = test_braid.get_beads_after(vec![b4_hash, b5_hash]);
    assert!(result.is_some());
    let returned_beads = result.unwrap();

    let returned_hashes: HashSet<_> = returned_beads
        .iter()
        .map(|b| compute_block_hash(&b.block_header, PoolNetwork::Cpunet))
        .collect();
    assert!(returned_hashes.contains(&compute_block_hash(
        &beads[7].block_header,
        PoolNetwork::Cpunet
    )));

    println!("Complex braid tests passed");
}

#[test]
fn test_get_beads_after_edge_cases() {
    // Test Case 4: Edge cases
    pub type BeadHash = BlockHash;
    // Create a simple braid for edge case testing
    let mut beads = Vec::new();
    for _i in 0..3 {
        beads.push(emit_bead());
    }

    // Simple chain: Genesis -> Bead1 -> Bead2
    // Collect parent hashes first to avoid borrowing issues
    let parent0_hash = compute_block_hash(&beads[0].block_header, PoolNetwork::Cpunet);
    let parent1_hash = compute_block_hash(&beads[1].block_header, PoolNetwork::Cpunet);
    beads[1].committed_metadata.parents.push(parent0_hash);
    beads[2].committed_metadata.parents.push(parent1_hash);

    let genesis_set = HashSet::from([0]);
    let mut bead_index_mapping = HashMap::new();
    bead_index_mapping.insert(
        compute_block_hash(&beads[0].block_header, PoolNetwork::Cpunet),
        0,
    );

    let mut test_braid = Braid {
        beads: vec![beads[0].clone()],
        tips: genesis_set.clone(),
        cohorts: vec![Cohort(genesis_set.clone())],
        cohort_tips: vec![genesis_set.clone()],
        orphan_beads: OrphanPool::new(DEFAULT_MAX_ORPHAN_BEADS),
        genesis_beads: genesis_set,
        bead_index_mapping,
        network: PoolNetwork::Cpunet,
    };

    test_braid.extend(&beads[1]);
    test_braid.extend(&beads[2]);

    // Test 1: Empty input vector
    let _result = test_braid.get_beads_after(vec![]);
    // Function should handle empty input gracefully

    // Test 2: Non-existent hash
    let fake_hash =
        BeadHash::from_str("0000000000000000000000000000000000000000000000000000000000000001")
            .unwrap();
    let _result = test_braid.get_beads_after(vec![fake_hash]);
    // Should handle non-existent hash gracefully

    // Test 3: Mix of valid and invalid hashes
    let genesis_hash = compute_block_hash(&beads[0].block_header, PoolNetwork::Cpunet);
    let result = test_braid.get_beads_after(vec![genesis_hash, fake_hash]);
    assert!(result.is_some());
    let returned_beads = result.unwrap();

    // Should still work with valid hash and ignore invalid one
    let returned_hashes: HashSet<_> = returned_beads
        .iter()
        .map(|b| compute_block_hash(&b.block_header, PoolNetwork::Cpunet))
        .collect();
    assert!(
        returned_hashes.contains(&compute_block_hash(
            &beads[1].block_header,
            PoolNetwork::Cpunet
        )) || returned_hashes.contains(&compute_block_hash(
            &beads[2].block_header,
            PoolNetwork::Cpunet
        ))
    );

    // Test 4: Get beads after the tip (last bead)
    let tip_hash = compute_block_hash(&beads[2].block_header, PoolNetwork::Cpunet);
    let result = test_braid.get_beads_after(vec![tip_hash]);
    assert!(result.is_none());
    // Should return at least the tip bead itself or beads from its cohort
}

#[test]
fn test_get_beads_after_multiple_tips() {
    // Test Case 5: Multiple tips scenario
    // Test with multiple valid tips to ensure function finds smallest index correctly

    let mut beads = Vec::new();
    for _i in 0..6 {
        beads.push(emit_bead());
    }

    // Create a structure:
    //   Genesis(0)
    //   /        \
    //  B1(1)    B2(2)
    //  |        |
    //  B3(3)    B4(4)
    //           |
    //           B5(5)

    let mut parent_relationships = HashMap::new();
    parent_relationships.insert(0, HashSet::new());
    parent_relationships.insert(1, HashSet::from([0]));
    parent_relationships.insert(2, HashSet::from([0]));
    parent_relationships.insert(3, HashSet::from([1]));
    parent_relationships.insert(4, HashSet::from([2]));
    parent_relationships.insert(5, HashSet::from([4]));

    // Collect parent hashes first to avoid borrowing issues
    let mut parent_hashes: HashMap<usize, Vec<bitcoin::BlockHash>> = HashMap::new();
    for (index, parents) in &parent_relationships {
        let mut hashes = Vec::new();
        for &parent_idx in parents {
            hashes.push(compute_block_hash(
                &beads[parent_idx].block_header,
                PoolNetwork::Cpunet,
            ));
        }
        parent_hashes.insert(*index, hashes);
    }

    // Update parent hashes in committed metadata
    for (index, hashes) in parent_hashes {
        for hash in hashes {
            beads[index].committed_metadata.parents.push(hash);
        }
    }

    // Create and build braid
    let genesis_set = HashSet::from([0]);
    let mut bead_index_mapping = HashMap::new();
    bead_index_mapping.insert(
        compute_block_hash(&beads[0].block_header, PoolNetwork::Cpunet),
        0,
    );

    let mut test_braid = Braid {
        beads: vec![beads[0].clone()],
        tips: genesis_set.clone(),
        cohorts: vec![Cohort(genesis_set.clone())],
        cohort_tips: vec![genesis_set.clone()],
        orphan_beads: OrphanPool::new(DEFAULT_MAX_ORPHAN_BEADS),
        genesis_beads: genesis_set,
        bead_index_mapping,
        network: PoolNetwork::Cpunet,
    };

    for i in 1..6 {
        test_braid.extend(&beads[i]);
    }

    // Test: Get beads after multiple tips with different indices
    let b3_hash = compute_block_hash(&beads[3].block_header, PoolNetwork::Cpunet); // Index 3
    let b5_hash = compute_block_hash(&beads[5].block_header, PoolNetwork::Cpunet); // Index 5

    let result = test_braid.get_beads_after(vec![b3_hash, b5_hash]);
    assert!(result.is_some());
    let returned_beads = result.unwrap();

    // Should start from the cohort containing the smallest index (B3 at index 3)
    // and return beads from that cohort onwards
    assert!(!returned_beads.is_empty(), "Should return some beads");

    // Test with tips in reverse order (larger index first)
    let result2 = test_braid.get_beads_after(vec![b5_hash, b3_hash]);
    assert!(result2.is_some());
    let returned_beads2 = result2.unwrap();

    // Should return the same result regardless of order
    assert_eq!(
        returned_beads.len(),
        returned_beads2.len(),
        "Order of input tips should not affect result"
    );
}

/// A bead added with no parked orphans depending on it should report an empty
/// `promoted_orphans` set.
#[test]
fn test_extend_without_orphans_promotes_nothing() {
    let genesis = emit_bead();
    let mut braid = Braid::new(vec![genesis.clone()], PoolNetwork::Cpunet);

    let mut child = emit_bead();
    child
        .committed_metadata
        .parents
        .push(compute_block_hash(&genesis.block_header, braid.network));

    match braid.extend(&child) {
        AddBeadStatus::BeadAdded { promoted_orphans } => {
            assert!(
                promoted_orphans.is_empty(),
                "no orphans were waiting, so none should be promoted"
            );
        }
        other => panic!("expected BeadAdded, got {:?}", other),
    }
}

/// An orphan that arrives before its parent is parked; when the parent arrives
/// the orphan is promoted and reported back through `BeadAdded`.
#[test]
fn test_extend_reports_promoted_orphan() {
    let genesis = emit_bead();
    let mut braid = Braid::new(vec![genesis.clone()], PoolNetwork::Cpunet);

    let mut child = emit_bead();
    child
        .committed_metadata
        .parents
        .push(compute_block_hash(&genesis.block_header, braid.network));

    let mut grandchild = emit_bead();
    grandchild
        .committed_metadata
        .parents
        .push(compute_block_hash(&child.block_header, braid.network));

    // Grandchild arrives before its parent `child` -> parked as an orphan.
    assert!(
        matches!(
            braid.extend(&grandchild),
            AddBeadStatus::ParentsNotYetReceived
        ),
        "grandchild should be parked while its parent is missing"
    );
    assert_eq!(braid.orphan_beads.len(), 1);

    // The parent arrives: `child` is added and `grandchild` becomes connectable.
    match braid.extend(&child) {
        AddBeadStatus::BeadAdded { promoted_orphans } => {
            assert_eq!(promoted_orphans.len(), 1, "grandchild should be promoted");
            assert_eq!(
                compute_block_hash(&promoted_orphans[0].block_header, braid.network),
                compute_block_hash(&grandchild.block_header, braid.network)
            );
        }
        other => panic!("expected BeadAdded, got {:?}", other),
    }
    assert!(
        braid.orphan_beads.is_empty(),
        "the orphan set should be drained once the parent arrives"
    );
}

/// A chain of orphans (each depending on the previous) that arrive before their
/// common ancestor should all be promoted transitively in a single `extend`.
#[test]
fn test_extend_promotes_transitive_orphan_chain() {
    let genesis = emit_bead();
    let mut braid = Braid::new(vec![genesis.clone()], PoolNetwork::Cpunet);

    let mut a = emit_bead();
    a.committed_metadata
        .parents
        .push(compute_block_hash(&genesis.block_header, braid.network));
    let mut b = emit_bead();
    b.committed_metadata
        .parents
        .push(compute_block_hash(&a.block_header, braid.network));
    let mut c = emit_bead();
    c.committed_metadata
        .parents
        .push(compute_block_hash(&b.block_header, braid.network));

    // `c` and `b` arrive before `a`; both are parked.
    assert!(matches!(
        braid.extend(&c),
        AddBeadStatus::ParentsNotYetReceived
    ));
    assert!(matches!(
        braid.extend(&b),
        AddBeadStatus::ParentsNotYetReceived
    ));
    assert_eq!(braid.orphan_beads.len(), 2);

    // `a` connects the whole chain: `b` then `c` are promoted transitively.
    match braid.extend(&a) {
        AddBeadStatus::BeadAdded { promoted_orphans } => {
            assert_eq!(
                promoted_orphans.len(),
                2,
                "both b and c should be promoted, got {:?}",
                promoted_orphans.len()
            );
            let promoted_hashes: HashSet<_> = promoted_orphans
                .iter()
                .map(|bead| compute_block_hash(&bead.block_header, braid.network))
                .collect();
            assert!(promoted_hashes.contains(&compute_block_hash(&b.block_header, braid.network)));
            assert!(promoted_hashes.contains(&compute_block_hash(&c.block_header, braid.network)));
        }
        other => panic!("expected BeadAdded, got {:?}", other),
    }
    assert!(
        braid.orphan_beads.is_empty(),
        "all transitively-connectable orphans should be drained"
    );
}

/// A long chain of orphans that arrive child-first must be promoted without
/// exhausting the stack. `extend` and `process_orphan_beads` used to call each
/// other once per promoted bead, so a chain of ~1500 beads aborted the process
/// with a stack overflow. Regression test for #532.
#[test]
fn test_extend_deep_orphan_chain_does_not_overflow_stack() {
    const CHAIN_LEN: usize = 2000;

    let genesis = emit_bead();
    let mut braid = Braid::new(vec![genesis.clone()], PoolNetwork::Cpunet);

    // Build genesis <- b0 <- b1 <- ... <- b(CHAIN_LEN - 1).
    let mut chain: Vec<Bead> = Vec::with_capacity(CHAIN_LEN);
    let mut parent_hash = compute_block_hash(&genesis.block_header, braid.network);
    for _ in 0..CHAIN_LEN {
        let mut bead = emit_bead();
        bead.committed_metadata.parents.push(parent_hash);
        parent_hash = compute_block_hash(&bead.block_header, braid.network);
        chain.push(bead);
    }

    // Deliver child-first: chain[N-1] down to chain[1] are parked because each
    // waits on the bead one step closer to the genesis. chain[0] is the only bead
    // whose parent (the genesis) is already present.
    for bead in chain.iter().rev().take(CHAIN_LEN - 1) {
        assert!(
            matches!(braid.extend(bead), AddBeadStatus::ParentsNotYetReceived),
            "bead should be parked while its parent is missing"
        );
    }
    assert_eq!(braid.orphan_beads.len(), CHAIN_LEN - 1);

    // chain[0] connects the whole chain at once.
    let root = &chain[0];
    // Everything in the braid before `root` is inserted, plus `root` itself once
    // `extend` accepts it. Each promoted bead must only depend on beads in this
    // set, and is added to it after the check, so the assertion actually verifies
    // the parent-before-child order of the returned vector.
    let mut visible: HashSet<BeadHash> = braid.bead_index_mapping.keys().copied().collect();
    visible.insert(braid.compute_bead_hash(root));
    match braid.extend(root) {
        AddBeadStatus::BeadAdded { promoted_orphans } => {
            assert_eq!(
                promoted_orphans.len(),
                CHAIN_LEN - 1,
                "the whole chain should be promoted"
            );
            // Parents must be reported before the children that depend on them,
            // because the promoted beads are persisted in this order.
            for bead in &promoted_orphans {
                let bead_hash = braid.compute_bead_hash(bead);
                for parent in &bead.committed_metadata.parents {
                    assert!(
                        visible.contains(parent),
                        "parent {parent} must be reported before its child {bead_hash}"
                    );
                }
                assert!(
                    visible.insert(bead_hash),
                    "each orphan must be promoted exactly once"
                );
            }
        }
        other => panic!("expected BeadAdded, got {other:?}"),
    }
    assert_eq!(braid.beads.len(), CHAIN_LEN + 1);
    assert!(
        braid.orphan_beads.is_empty(),
        "the orphan set should be drained once the chain connects"
    );
}

/// Re-sending the same orphan must not accumulate copies of it. The
/// already-seen check used to run after the missing-parent branch, so a peer
/// could grow `orphan_beads` without bound by replaying one bead.
#[test]
fn test_extend_deduplicates_orphans() {
    let genesis = emit_bead();
    let mut braid = Braid::new(vec![genesis.clone()], PoolNetwork::Cpunet);

    let mut child = emit_bead();
    child
        .committed_metadata
        .parents
        .push(compute_block_hash(&genesis.block_header, braid.network));

    let mut orphan = emit_bead();
    orphan
        .committed_metadata
        .parents
        .push(compute_block_hash(&child.block_header, braid.network));

    for i in 0..1000 {
        let status = braid.extend(&orphan);
        if i == 0 {
            assert!(
                matches!(status, AddBeadStatus::ParentsNotYetReceived),
                "first sighting of an orphan should be parked"
            );
        } else {
            // A replay is recognised as already parked rather than parked again.
            // It must not be reported as part of the braid: during IBD that would
            // clear the sync lock even though the bead is still missing parents.
            assert!(
                matches!(status, AddBeadStatus::OrphanAlreadyParked),
                "a replayed orphan should be reported as already parked"
            );
        }
    }

    assert_eq!(
        braid.orphan_beads.len(),
        1,
        "replaying the same orphan must not park duplicate copies"
    );

    match braid.extend(&child) {
        AddBeadStatus::BeadAdded { promoted_orphans } => {
            assert_eq!(
                promoted_orphans.len(),
                1,
                "the orphan should be promoted exactly once"
            );
        }
        other => panic!("expected BeadAdded, got {other:?}"),
    }
    assert!(braid.orphan_beads.is_empty());
}

/// The orphan pool must stay bounded so a peer cannot grow it without limit by
/// naming parents that never arrive. At capacity it evicts the oldest parked
/// bead, so the pool keeps accepting recent orphans instead of locking up.
#[test]
fn test_orphan_pool_evicts_oldest_at_capacity() {
    let genesis = emit_bead();

    let mut pool = OrphanPool::new(2);
    assert_eq!(pool.capacity(), 2);

    let park_one = |pool: &mut OrphanPool, parent: BeadHash| -> BeadHash {
        let mut orphan = emit_bead();
        orphan.committed_metadata.parents.push(parent);
        let hash = compute_block_hash(&orphan.block_header, PoolNetwork::Cpunet);
        assert!(pool.park(hash, orphan, &[parent]), "parking must succeed");
        hash
    };

    let missing = compute_block_hash(&emit_bead().block_header, PoolNetwork::Cpunet);
    let first = park_one(&mut pool, missing);
    let second = park_one(&mut pool, missing);
    assert_eq!(pool.len(), 2);
    let third = park_one(&mut pool, missing);
    assert_eq!(pool.len(), 2, "eviction must keep the pool at capacity");
    assert!(!pool.contains(&first), "the oldest bead must be evicted");
    assert!(pool.contains(&second) && pool.contains(&third));

    // Eviction must also drop the bead from the waiting-on index, otherwise the
    // index would leak hashes of beads that are no longer parked.
    let waiting = pool.take_waiting_on(&missing);
    assert_eq!(waiting.len(), 2);
    assert!(waiting.contains(&second) && waiting.contains(&third));
    assert!(!waiting.contains(&first));

    // A capacity of zero is clamped to one, and still evicts rather than reject.
    let mut one = OrphanPool::new(0);
    assert_eq!(one.capacity(), 1);
    let first = park_one(&mut one, missing);
    let second = park_one(&mut one, missing);
    assert!(!one.contains(&first), "the single slot is reused");
    assert!(one.contains(&second));

    // The braid surfaces eviction as a normal "parked" result: both beads are
    // waiting for parents, the older one has simply been dropped.
    let mut small = Braid::new(vec![genesis.clone()], PoolNetwork::Cpunet);
    small.orphan_beads = OrphanPool::new(1);
    let mut first_bead = emit_bead();
    first_bead.committed_metadata.parents.push(missing);
    let mut second_bead = emit_bead();
    second_bead.committed_metadata.parents.push(missing);
    let first_hash = small.compute_bead_hash(&first_bead);
    let second_hash = small.compute_bead_hash(&second_bead);

    assert!(matches!(
        small.extend(&first_bead),
        AddBeadStatus::ParentsNotYetReceived
    ));
    assert!(matches!(
        small.extend(&second_bead),
        AddBeadStatus::ParentsNotYetReceived
    ));
    assert_eq!(small.orphan_beads.len(), 1);
    assert!(!small.orphan_beads.contains(&first_hash));
    assert!(small.orphan_beads.contains(&second_hash));
}

/// An orphan waiting on two missing parents must stay parked when the first one
/// arrives, and be promoted exactly once when the second arrives. This exercises
/// the re-park path in the promotion worklist, where a half-satisfied orphan is
/// put back without losing its remaining index entry.
#[test]
fn test_orphan_with_two_missing_parents_promoted_once() {
    let genesis = emit_bead();
    let mut braid = Braid::new(vec![genesis.clone()], PoolNetwork::Cpunet);
    let genesis_hash = compute_block_hash(&genesis.block_header, braid.network);

    let mut parent_a = emit_bead();
    parent_a.committed_metadata.parents.push(genesis_hash);
    let mut parent_b = emit_bead();
    parent_b.committed_metadata.parents.push(genesis_hash);

    let hash_a = compute_block_hash(&parent_a.block_header, braid.network);
    let hash_b = compute_block_hash(&parent_b.block_header, braid.network);

    let mut orphan = emit_bead();
    orphan.committed_metadata.parents.push(hash_a);
    orphan.committed_metadata.parents.push(hash_b);
    let orphan_hash = compute_block_hash(&orphan.block_header, braid.network);

    assert!(matches!(
        braid.extend(&orphan),
        AddBeadStatus::ParentsNotYetReceived
    ));
    assert_eq!(braid.orphan_beads.len(), 1);

    // First parent arrives: the orphan is still missing one parent.
    match braid.extend(&parent_a) {
        AddBeadStatus::BeadAdded { promoted_orphans } => {
            assert!(
                promoted_orphans.is_empty(),
                "orphan must wait for its second parent"
            );
        }
        other => panic!("expected BeadAdded, got {other:?}"),
    }
    assert_eq!(
        braid.orphan_beads.len(),
        1,
        "half-satisfied orphan must be re-parked"
    );

    // Second parent arrives: the orphan is promoted exactly once.
    match braid.extend(&parent_b) {
        AddBeadStatus::BeadAdded { promoted_orphans } => {
            assert_eq!(promoted_orphans.len(), 1);
            assert_eq!(
                braid.compute_bead_hash(&promoted_orphans[0]),
                orphan_hash,
                "the promoted bead should be the parked orphan"
            );
        }
        other => panic!("expected BeadAdded, got {other:?}"),
    }
    assert!(braid.orphan_beads.is_empty());
    // genesis + parent_a + parent_b + orphan
    assert_eq!(braid.beads.len(), 4);
    assert!(braid.bead_index_mapping.contains_key(&orphan_hash));
}
