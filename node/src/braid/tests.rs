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
