use super::Bead;
use super::Braid;
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
use crate::utils::test_utils::test_utility_functions::loading_braid_from_file;
use crate::utils::test_utils::test_utility_functions::*;
use num::BigUint;
use std::collections::HashMap;
use std::collections::HashSet;
use std::path::Path;
#[test]
pub fn test_extend_functionality() {
    // Create a braid with one bead.
    let test_bead_0 = emit_bead();

    let mut test_braid = Braid {
        beads: vec![test_bead_0.clone()],
        genesis_beads: HashSet::from([0]),
        tips: HashSet::from([0]),
        orphan_beads: Vec::new(),
        cohorts: vec![Cohort(HashSet::from([0]))],
        cohort_tips: vec![HashSet::from([0])],
        bead_index_mapping: std::collections::HashMap::from([(
            test_bead_0.block_header.block_hash(),
            0,
        )]),
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
        .insert(test_bead_0.block_header.block_hash());

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
        .insert(test_bead_1.block_header.block_hash());
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
        .insert(test_bead_2.block_header.block_hash());
    test_braid.extend(&test_bead_3);

    // Create bead 4 with parent 2
    let mut test_bead_4 = emit_bead();
    test_bead_4
        .committed_metadata
        .parents
        .insert(test_bead_2.block_header.block_hash());
    test_braid.extend(&test_bead_4);

    // Create bead 5 with parent 2
    let mut test_bead_5 = emit_bead();
    test_bead_5
        .committed_metadata
        .parents
        .insert(test_bead_2.block_header.block_hash());
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
        .insert(test_bead_4.block_header.block_hash());
    test_braid.extend(&test_bead_6);

    let mut test_bead_7 = emit_bead();
    test_bead_7
        .committed_metadata
        .parents
        .insert(test_bead_6.block_header.block_hash());
    test_braid.extend(&test_bead_7);

    let mut test_bead_8 = emit_bead();
    test_bead_8
        .committed_metadata
        .parents
        .insert(test_bead_7.block_header.block_hash());
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
        .insert(test_bead_5.block_header.block_hash());
    test_braid.extend(&test_bead_9);

    let mut test_bead_10 = emit_bead();
    test_bead_10
        .committed_metadata
        .parents
        .insert(test_bead_9.block_header.block_hash());
    test_braid.extend(&test_bead_10);

    let mut test_bead_11 = emit_bead();
    test_bead_11
        .committed_metadata
        .parents
        .insert(test_bead_10.block_header.block_hash());
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
        .insert(test_bead_8.block_header.block_hash());
    test_bead_12
        .committed_metadata
        .parents
        .insert(test_bead_11.block_header.block_hash());
    test_bead_12
        .committed_metadata
        .parents
        .insert(test_bead_3.block_header.block_hash());
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
        .insert(test_bead_12.block_header.block_hash());
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
        orphan_beads: Vec::new(),
        cohorts: vec![Cohort(HashSet::from([0]))],
        cohort_tips: vec![HashSet::from([0])],
        bead_index_mapping: std::collections::HashMap::from([(
            test_bead_0.block_header.block_hash(),
            0,
        )]),
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
        .insert(test_bead_2.block_header.block_hash());

    test_braid.extend(&test_bead_1);
    assert_eq!(
        test_braid.cohorts,
        vec![Cohort(HashSet::from([0]))],
        "The added bead was an orphan, cohort shouldn't change."
    );

    test_bead_2
        .committed_metadata
        .parents
        .insert(test_bead_0.block_header.block_hash());
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
        .insert(test_bead_0.block_header.block_hash());
    test_bead_2
        .committed_metadata
        .parents
        .insert(test_bead_1.block_header.block_hash());

    test_bead_3
        .committed_metadata
        .parents
        .insert(test_bead_2.block_header.block_hash());

    let test_braid = Braid {
        beads: vec![
            test_bead_0.clone(),
            test_bead_1.clone(),
            test_bead_2.clone(),
            test_bead_3.clone(),
        ],
        genesis_beads: HashSet::from([0]),
        tips: HashSet::from([3]),
        orphan_beads: Vec::new(),
        cohorts: vec![Cohort(HashSet::from([0]))],
        cohort_tips: vec![HashSet::from([0])],
        bead_index_mapping: std::collections::HashMap::from([
            (test_bead_0.block_header.block_hash(), 0),
            (test_bead_1.block_header.block_hash(), 1),
            (test_bead_2.block_header.block_hash(), 2),
            (test_bead_3.block_header.block_hash(), 3),
        ]),
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
        .insert(test_bead_1.block_header.prev_blockhash);
    test_bead_3
        .committed_metadata
        .parents
        .insert(test_bead_1.block_header.prev_blockhash);
    let test_braid = Braid {
        beads: vec![
            test_bead_0.clone(),
            test_bead_1.clone(),
            test_bead_2.clone(),
            test_bead_3.clone(),
        ],
        genesis_beads: HashSet::from([0]),
        tips: HashSet::from([3]),
        orphan_beads: Vec::new(),
        cohorts: vec![Cohort(HashSet::from([0]))],
        cohort_tips: vec![HashSet::from([0])],
        bead_index_mapping: std::collections::HashMap::from([
            (test_bead_0.block_header.block_hash(), 0),
            (test_bead_1.block_header.block_hash(), 1),
            (test_bead_2.block_header.block_hash(), 2),
            (test_bead_3.block_header.block_hash(), 3),
        ]),
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
        .insert(test_bead_1.block_header.block_hash());
    test_bead_4
        .committed_metadata
        .parents
        .insert(test_bead_0.block_header.block_hash());

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
        orphan_beads: Vec::new(),
        cohorts: vec![Cohort(HashSet::from([0]))],
        cohort_tips: vec![HashSet::from([0])],
        bead_index_mapping: std::collections::HashMap::from([
            (test_bead_0.block_header.block_hash(), 0),
            (test_bead_1.block_header.block_hash(), 1),
            (test_bead_2.block_header.block_hash(), 2),
            (test_bead_3.block_header.block_hash(), 3),
            (test_bead_4.block_header.block_hash(), 4),
        ]),
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
        .insert(test_bead_0.block_header.block_hash());
    test_bead_2
        .committed_metadata
        .parents
        .insert(test_bead_1.block_header.block_hash());

    test_bead_3
        .committed_metadata
        .parents
        .insert(test_bead_2.block_header.block_hash());

    let test_braid = Braid {
        beads: vec![
            test_bead_0.clone(),
            test_bead_1.clone(),
            test_bead_2.clone(),
            test_bead_3.clone(),
        ],
        genesis_beads: HashSet::from([0]),
        tips: HashSet::from([3]),
        orphan_beads: Vec::new(),
        cohorts: vec![Cohort(HashSet::from([0]))],
        cohort_tips: vec![HashSet::from([0])],
        bead_index_mapping: std::collections::HashMap::from([
            (test_bead_0.block_header.block_hash(), 0),
            (test_bead_1.block_header.block_hash(), 1),
            (test_bead_2.block_header.block_hash(), 2),
            (test_bead_3.block_header.block_hash(), 3),
        ]),
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
        .insert(test_bead_0.block_header.block_hash());
    test_bead_2
        .committed_metadata
        .parents
        .insert(test_bead_1.block_header.block_hash());

    test_bead_3
        .committed_metadata
        .parents
        .insert(test_bead_1.block_header.block_hash());

    let test_braid = Braid {
        beads: vec![
            test_bead_0.clone(),
            test_bead_1.clone(),
            test_bead_2.clone(),
            test_bead_3.clone(),
        ],
        genesis_beads: HashSet::from([0]),
        tips: HashSet::from([3]),
        orphan_beads: Vec::new(),
        cohorts: vec![Cohort(HashSet::from([0]))],
        cohort_tips: vec![HashSet::from([0])],
        bead_index_mapping: std::collections::HashMap::from([
            (test_bead_0.block_header.block_hash(), 0),
            (test_bead_1.block_header.block_hash(), 1),
            (test_bead_2.block_header.block_hash(), 2),
            (test_bead_3.block_header.block_hash(), 3),
        ]),
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
        .insert(test_bead_0.block_header.block_hash());
    test_bead_3
        .committed_metadata
        .parents
        .insert(test_bead_1.block_header.block_hash());
    test_bead_3
        .committed_metadata
        .parents
        .insert(test_bead_2.block_header.block_hash());
    test_bead_4
        .committed_metadata
        .parents
        .insert(test_bead_0.block_header.block_hash());
    test_bead_4
        .committed_metadata
        .parents
        .insert(test_bead_1.block_header.block_hash());
    test_bead_4
        .committed_metadata
        .parents
        .insert(test_bead_2.block_header.block_hash());
    test_bead_5
        .committed_metadata
        .parents
        .insert(test_bead_0.block_header.block_hash());
    test_bead_5
        .committed_metadata
        .parents
        .insert(test_bead_1.block_header.block_hash());
    test_bead_5
        .committed_metadata
        .parents
        .insert(test_bead_2.block_header.block_hash());
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
        orphan_beads: Vec::new(),
        cohorts: vec![Cohort(HashSet::from([0]))],
        cohort_tips: vec![HashSet::from([0])],
        bead_index_mapping: std::collections::HashMap::from([
            (test_bead_0.block_header.block_hash(), 0),
            (test_bead_1.block_header.block_hash(), 1),
            (test_bead_2.block_header.block_hash(), 2),
            (test_bead_3.block_header.block_hash(), 3),
            (test_bead_4.block_header.block_hash(), 4),
            (test_bead_5.block_header.block_hash(), 5),
        ]),
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
        .insert(test_bead_0.block_header.block_hash());
    test_bead_3
        .committed_metadata
        .parents
        .insert(test_bead_1.block_header.block_hash());
    test_bead_3
        .committed_metadata
        .parents
        .insert(test_bead_2.block_header.block_hash());
    test_bead_4
        .committed_metadata
        .parents
        .insert(test_bead_0.block_header.block_hash());
    test_bead_4
        .committed_metadata
        .parents
        .insert(test_bead_1.block_header.block_hash());
    test_bead_4
        .committed_metadata
        .parents
        .insert(test_bead_2.block_header.block_hash());
    test_bead_5
        .committed_metadata
        .parents
        .insert(test_bead_0.block_header.block_hash());
    test_bead_5
        .committed_metadata
        .parents
        .insert(test_bead_1.block_header.block_hash());
    test_bead_5
        .committed_metadata
        .parents
        .insert(test_bead_2.block_header.block_hash());
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
        orphan_beads: Vec::new(),
        cohorts: vec![Cohort(HashSet::from([0]))],
        cohort_tips: vec![HashSet::from([0])],
        bead_index_mapping: std::collections::HashMap::from([
            (test_bead_0.block_header.block_hash(), 0),
            (test_bead_1.block_header.block_hash(), 1),
            (test_bead_2.block_header.block_hash(), 2),
            (test_bead_3.block_header.block_hash(), 3),
            (test_bead_4.block_header.block_hash(), 4),
            (test_bead_5.block_header.block_hash(), 5),
        ]),
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
            let current_bead_hash = current_file_braid.beads[bead_index.0]
                .block_header
                .block_hash();
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
        .insert(test_bead_0.block_header.block_hash());
    test_bead_2
        .committed_metadata
        .parents
        .insert(test_bead_1.block_header.block_hash());

    test_bead_3
        .committed_metadata
        .parents
        .insert(test_bead_2.block_header.block_hash());

    let test_braid = Braid {
        beads: vec![
            test_bead_0.clone(),
            test_bead_1.clone(),
            test_bead_2.clone(),
            test_bead_3.clone(),
        ],
        genesis_beads: HashSet::from([0]),
        tips: HashSet::from([3]),
        orphan_beads: Vec::new(),
        cohorts: vec![Cohort(HashSet::from([0]))],
        cohort_tips: vec![HashSet::from([0])],
        bead_index_mapping: std::collections::HashMap::from([
            (test_bead_0.block_header.block_hash(), 0),
            (test_bead_1.block_header.block_hash(), 1),
            (test_bead_2.block_header.block_hash(), 2),
            (test_bead_3.block_header.block_hash(), 3),
        ]),
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
#[allow(unused)]
pub fn reverse_cohorts_testcases() {
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
        let reversed_beads = reverse(&current_file_braid, &current_braid_parents);
        let current_braid_cohorts = file_braid.cohorts;

        let computed_val = cohort(&current_file_braid, &reversed_beads, None, None);
        //TODO:assetion to be done
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
        .insert(test_bead_0.block_header.block_hash());
    test_bead_2
        .committed_metadata
        .parents
        .insert(test_bead_1.block_header.block_hash());

    test_bead_3
        .committed_metadata
        .parents
        .insert(test_bead_2.block_header.block_hash());

    let test_braid = Braid {
        beads: vec![
            test_bead_0.clone(),
            test_bead_1.clone(),
            test_bead_2.clone(),
            test_bead_3.clone(),
        ],
        genesis_beads: HashSet::from([0]),
        tips: HashSet::from([3]),
        orphan_beads: Vec::new(),
        cohorts: vec![Cohort(HashSet::from([0]))],
        cohort_tips: vec![HashSet::from([0])],
        bead_index_mapping: std::collections::HashMap::from([
            (test_bead_0.block_header.block_hash(), 0),
            (test_bead_1.block_header.block_hash(), 1),
            (test_bead_2.block_header.block_hash(), 2),
            (test_bead_3.block_header.block_hash(), 3),
        ]),
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
        .insert(test_bead_0.block_header.block_hash());
    test_bead_2
        .committed_metadata
        .parents
        .insert(test_bead_0.block_header.block_hash());
    test_bead_3
        .committed_metadata
        .parents
        .insert(test_bead_1.block_header.block_hash());
    test_bead_3
        .committed_metadata
        .parents
        .insert(test_bead_2.block_header.block_hash());
    test_bead_4
        .committed_metadata
        .parents
        .insert(test_bead_3.block_header.block_hash());

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
        orphan_beads: Vec::new(),
        cohorts: vec![Cohort(HashSet::from([0]))],
        cohort_tips: vec![HashSet::from([0])],
        bead_index_mapping: std::collections::HashMap::from([
            (test_bead_0.block_header.block_hash(), 0),
            (test_bead_1.block_header.block_hash(), 1),
            (test_bead_2.block_header.block_hash(), 2),
            (test_bead_3.block_header.block_hash(), 3),
            (test_bead_4.block_header.block_hash(), 4),
        ]),
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
                    hashes.push(parent_bead.block_header.block_hash());
                }
            }
            parent_hashes.insert(*index, hashes);
        }

        // Now set up parent relationships in committed metadata
        for (index, hashes) in parent_hashes {
            if let Some(bead) = index_to_bead.get_mut(&index) {
                for hash in hashes {
                    bead.committed_metadata.parents.insert(hash);
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
                bead_index_mapping.insert(bead.block_header.block_hash(), idx);
            }
        }

        let mut test_braid = Braid {
            beads: genesis_beads,
            tips: genesis_set.clone(),
            cohorts: vec![Cohort(genesis_set.clone())],
            cohort_tips: vec![genesis_set.clone()],
            orphan_beads: Vec::new(),
            genesis_beads: genesis_set,
            bead_index_mapping,
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
                let bead_hash = test_braid.beads[bead_idx].block_header.block_hash();
                cohort_hashes.insert(bead_hash);
            }
            computed_cohorts_by_hash.push(cohort_hashes);
        }

        let mut file_cohorts_by_hash: Vec<HashSet<bitcoin::BlockHash>> = Vec::new();
        for cohort in &file_braid.cohorts {
            let mut cohort_hashes = HashSet::new();
            for &bead_idx in cohort {
                if let Some(bead) = index_to_bead.get(&bead_idx) {
                    let bead_hash = bead.block_header.block_hash();
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
            hashes.push(beads[parent_idx].block_header.block_hash());
        }
        parent_hashes.insert(*index, hashes);
    }

    // Update parent hashes in committed metadata
    for (index, hashes) in parent_hashes {
        for hash in hashes {
            beads[index].committed_metadata.parents.insert(hash);
        }
    }

    // Create braid with genesis
    let genesis_set = HashSet::from([0]);
    let mut bead_index_mapping = HashMap::new();
    bead_index_mapping.insert(beads[0].block_header.block_hash(), 0);

    let mut test_braid = Braid {
        beads: vec![beads[0].clone()],
        tips: genesis_set.clone(),
        cohorts: vec![Cohort(genesis_set.clone())],
        cohort_tips: vec![genesis_set.clone()],
        orphan_beads: Vec::new(),
        genesis_beads: genesis_set,
        bead_index_mapping,
    };

    // Extend braid with remaining beads
    for i in 1..4 {
        test_braid.extend(&beads[i]);
    }

    // Test 1: Get beads after genesis (should return beads 1, 2, 3)
    let genesis_hash = beads[0].block_header.block_hash();
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
        .map(|b| b.block_header.block_hash())
        .collect();
    assert!(returned_hashes.contains(&beads[1].block_header.block_hash()));
    assert!(returned_hashes.contains(&beads[2].block_header.block_hash()));
    assert!(returned_hashes.contains(&beads[3].block_header.block_hash()));

    // Test 2: Get beads after bead1 (should return beads 2, 3)
    let bead1_hash = beads[1].block_header.block_hash();
    let result = test_braid.get_beads_after(vec![bead1_hash]);
    assert!(result.is_some());
    let returned_beads = result.unwrap();

    let returned_hashes: HashSet<_> = returned_beads
        .iter()
        .map(|b| b.block_header.block_hash())
        .collect();
    assert!(returned_hashes.contains(&beads[2].block_header.block_hash()));
    assert!(returned_hashes.contains(&beads[3].block_header.block_hash()));

    // Test 3: Get beads after the last bead (should return empty or just that bead)
    let last_hash = beads[3].block_header.block_hash();
    let result = test_braid.get_beads_after(vec![last_hash]);
    assert!(result.is_some());

    println!("✅ Linear chain tests passed");
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
            hashes.push(beads[parent_idx].block_header.block_hash());
        }
        parent_hashes.insert(*index, hashes);
    }

    // Update parent hashes in committed metadata
    for (index, hashes) in parent_hashes {
        for hash in hashes {
            beads[index].committed_metadata.parents.insert(hash);
        }
    }

    // Create braid with genesis
    let genesis_set = HashSet::from([0]);
    let mut bead_index_mapping = HashMap::new();
    bead_index_mapping.insert(beads[0].block_header.block_hash(), 0);

    let mut test_braid = Braid {
        beads: vec![beads[0].clone()],
        tips: genesis_set.clone(),
        cohorts: vec![Cohort(genesis_set.clone())],
        cohort_tips: vec![genesis_set.clone()],
        orphan_beads: Vec::new(),
        genesis_beads: genesis_set,
        bead_index_mapping,
    };

    // Extend braid with remaining beads
    for i in 1..4 {
        test_braid.extend(&beads[i]);
    }

    // Test 1: Get beads after genesis
    let genesis_hash = beads[0].block_header.block_hash();
    let result = test_braid.get_beads_after(vec![genesis_hash]);
    assert!(result.is_some());
    let returned_beads = result.unwrap();

    // Should include all beads after genesis
    let returned_hashes: HashSet<_> = returned_beads
        .iter()
        .map(|b| b.block_header.block_hash())
        .collect();
    assert!(returned_hashes.contains(&beads[1].block_header.block_hash()));
    assert!(returned_hashes.contains(&beads[2].block_header.block_hash()));
    assert!(returned_hashes.contains(&beads[3].block_header.block_hash()));

    // Test 2: Get beads after both middle beads (should return bead3)
    let bead1_hash = beads[1].block_header.block_hash();
    let bead2_hash = beads[2].block_header.block_hash();
    let result = test_braid.get_beads_after(vec![bead1_hash, bead2_hash]);
    assert!(result.is_some());
    let returned_beads = result.unwrap();

    let returned_hashes: HashSet<_> = returned_beads
        .iter()
        .map(|b| b.block_header.block_hash())
        .collect();
    assert!(returned_hashes.contains(&beads[3].block_header.block_hash()));

    println!("✅ Diamond structure tests passed");
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
            hashes.push(beads[parent_idx].block_header.block_hash());
        }
        parent_hashes.insert(*index, hashes);
    }

    // Update parent hashes in committed metadata
    for (index, hashes) in parent_hashes {
        for hash in hashes {
            beads[index].committed_metadata.parents.insert(hash);
        }
    }

    // Create braid with genesis
    let genesis_set = HashSet::from([0]);
    let mut bead_index_mapping = HashMap::new();
    bead_index_mapping.insert(beads[0].block_header.block_hash(), 0);

    let mut test_braid = Braid {
        beads: vec![beads[0].clone()],
        tips: genesis_set.clone(),
        cohorts: vec![Cohort(genesis_set.clone())],
        cohort_tips: vec![genesis_set.clone()],
        orphan_beads: Vec::new(),
        genesis_beads: genesis_set,
        bead_index_mapping,
    };

    // Extend braid with remaining beads
    for i in 1..8 {
        test_braid.extend(&beads[i]);
    }

    // Test 1: Get beads after genesis (should return all other beads)
    let genesis_hash = beads[0].block_header.block_hash();
    let result = test_braid.get_beads_after(vec![genesis_hash]);
    assert!(result.is_some());
    let returned_beads = result.unwrap();
    assert!(
        returned_beads.len() >= 7,
        "Should return at least 7 beads after genesis"
    );

    // Test 2: Get beads after first cohort (B1, B2, B3)
    let b1_hash = beads[1].block_header.block_hash();
    let result = test_braid.get_beads_after(vec![b1_hash]);
    assert!(result.is_some());
    let returned_beads = result.unwrap();

    let returned_hashes: HashSet<_> = returned_beads
        .iter()
        .map(|b| b.block_header.block_hash())
        .collect();

    // Should include beads from the cohort containing B1 onwards
    assert!(
        returned_hashes.contains(&beads[4].block_header.block_hash())
            || returned_hashes.contains(&beads[5].block_header.block_hash())
            || returned_hashes.contains(&beads[6].block_header.block_hash())
            || returned_hashes.contains(&beads[7].block_header.block_hash())
    );

    // Test 3: Get beads after multiple tips from second level
    let b4_hash = beads[4].block_header.block_hash();
    let b5_hash = beads[5].block_header.block_hash();
    let result = test_braid.get_beads_after(vec![b4_hash, b5_hash]);
    assert!(result.is_some());
    let returned_beads = result.unwrap();

    let returned_hashes: HashSet<_> = returned_beads
        .iter()
        .map(|b| b.block_header.block_hash())
        .collect();
    assert!(returned_hashes.contains(&beads[7].block_header.block_hash()));

    println!("✅ Complex braid tests passed");
}

#[test]
fn test_get_beads_after_edge_cases() {
    // Test Case 4: Edge cases

    // Create a simple braid for edge case testing
    let mut beads = Vec::new();
    for _i in 0..3 {
        beads.push(emit_bead());
    }

    // Simple chain: Genesis -> Bead1 -> Bead2
    // Collect parent hashes first to avoid borrowing issues
    let parent0_hash = beads[0].block_header.block_hash();
    let parent1_hash = beads[1].block_header.block_hash();
    beads[1].committed_metadata.parents.insert(parent0_hash);
    beads[2].committed_metadata.parents.insert(parent1_hash);

    let genesis_set = HashSet::from([0]);
    let mut bead_index_mapping = HashMap::new();
    bead_index_mapping.insert(beads[0].block_header.block_hash(), 0);

    let mut test_braid = Braid {
        beads: vec![beads[0].clone()],
        tips: genesis_set.clone(),
        cohorts: vec![Cohort(genesis_set.clone())],
        cohort_tips: vec![genesis_set.clone()],
        orphan_beads: Vec::new(),
        genesis_beads: genesis_set,
        bead_index_mapping,
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
    let genesis_hash = beads[0].block_header.block_hash();
    let result = test_braid.get_beads_after(vec![genesis_hash, fake_hash]);
    assert!(result.is_some());
    let returned_beads = result.unwrap();

    // Should still work with valid hash and ignore invalid one
    let returned_hashes: HashSet<_> = returned_beads
        .iter()
        .map(|b| b.block_header.block_hash())
        .collect();
    assert!(
        returned_hashes.contains(&beads[1].block_header.block_hash())
            || returned_hashes.contains(&beads[2].block_header.block_hash())
    );

    // Test 4: Get beads after the tip (last bead)
    let tip_hash = beads[2].block_header.block_hash();
    let result = test_braid.get_beads_after(vec![tip_hash]);
    assert!(result.is_some());
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
            hashes.push(beads[parent_idx].block_header.block_hash());
        }
        parent_hashes.insert(*index, hashes);
    }

    // Update parent hashes in committed metadata
    for (index, hashes) in parent_hashes {
        for hash in hashes {
            beads[index].committed_metadata.parents.insert(hash);
        }
    }

    // Create and build braid
    let genesis_set = HashSet::from([0]);
    let mut bead_index_mapping = HashMap::new();
    bead_index_mapping.insert(beads[0].block_header.block_hash(), 0);

    let mut test_braid = Braid {
        beads: vec![beads[0].clone()],
        tips: genesis_set.clone(),
        cohorts: vec![Cohort(genesis_set.clone())],
        cohort_tips: vec![genesis_set.clone()],
        orphan_beads: Vec::new(),
        genesis_beads: genesis_set,
        bead_index_mapping,
    };

    for i in 1..6 {
        test_braid.extend(&beads[i]);
    }

    // Test: Get beads after multiple tips with different indices
    let b3_hash = beads[3].block_header.block_hash(); // Index 3
    let b5_hash = beads[5].block_header.block_hash(); // Index 5

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
