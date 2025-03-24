use std::collections::{HashMap, HashSet};
use std::fs;
use num::BigUint;
use braidpool::braid::{self, Parents};

const TEST_CASE_DIR: &str = "tests/braids/";

fn main() {
    println!("Running braid tests");
    test_geneses1();
    test_geneses2();
    test_geneses3();
    test_tips1();
    test_tips2();
    test_tips3();
    test_reverse();
    test_cohorts();
    test_highest_work_path();
    test_all_ancestors();
    test_save_load_braid();
    println!("All tests passed!");
}

fn test_geneses1() {
    let parents1: Parents = [
        (BigUint::from(0u64), HashSet::new()),
        (BigUint::from(1u64), [BigUint::from(0u64)].iter().cloned().collect()),
        (BigUint::from(2u64), [BigUint::from(1u64)].iter().cloned().collect()),
        (BigUint::from(3u64), [BigUint::from(2u64)].iter().cloned().collect()),
    ].iter().cloned().collect();

    assert_eq!(braid::geneses(&parents1), [BigUint::from(0u64)].iter().cloned().collect::<HashSet<_>>());
}

fn test_geneses2() {
    let parents2: Parents = [
        (BigUint::from(0u64), HashSet::new()),
        (BigUint::from(1u64), HashSet::new()),
        (BigUint::from(2u64), [BigUint::from(1u64)].iter().cloned().collect()),
        (BigUint::from(3u64), [BigUint::from(1u64)].iter().cloned().collect()),
    ].iter().cloned().collect();

    assert_eq!(braid::geneses(&parents2), [BigUint::from(0u64), BigUint::from(1u64)].iter().cloned().collect::<HashSet<_>>());
}

fn test_geneses3() {
    let parents3: Parents = [
        (BigUint::from(0u64), HashSet::new()),
        (BigUint::from(1u64), HashSet::new()),
        (BigUint::from(2u64), HashSet::new()),
        (BigUint::from(3u64), [BigUint::from(1u64)].iter().cloned().collect()),
        (BigUint::from(4u64), [BigUint::from(0u64)].iter().cloned().collect()),
    ].iter().cloned().collect();

    assert_eq!(braid::geneses(&parents3), [BigUint::from(0u64), BigUint::from(1u64), BigUint::from(2u64)].iter().cloned().collect::<HashSet<_>>());
}

fn test_geneses_files() {
    for entry in fs::read_dir(TEST_CASE_DIR).unwrap() {
        let entry = entry.unwrap();
        let path = entry.path();

        if path.extension().map_or(false, |ext| ext == "json") {
            let dag = braid::load_braid(&path).unwrap();
            assert_eq!(braid::geneses(&dag.parents), [BigUint::from(0u64)].iter().cloned().collect::<HashSet<_>>());
        }
    }
}

fn test_tips1() {
    let parents1: Parents = [
        (BigUint::from(0u64), HashSet::new()),
        (BigUint::from(1u64), [BigUint::from(0u64)].iter().cloned().collect()),
        (BigUint::from(2u64), [BigUint::from(1u64)].iter().cloned().collect()),
        (BigUint::from(3u64), [BigUint::from(2u64)].iter().cloned().collect()),
    ].iter().cloned().collect();

    assert_eq!(braid::tips(&parents1, None), [BigUint::from(3u64)].iter().cloned().collect::<HashSet<_>>());
}

fn test_tips2() {
    let parents2: Parents = [
        (BigUint::from(0u64), HashSet::new()),
        (BigUint::from(1u64), [BigUint::from(0u64)].iter().cloned().collect()),
        (BigUint::from(2u64), [BigUint::from(1u64)].iter().cloned().collect()),
        (BigUint::from(3u64), [BigUint::from(1u64)].iter().cloned().collect()),
    ].iter().cloned().collect();

    assert_eq!(braid::tips(&parents2, None), [BigUint::from(2u64), BigUint::from(3u64)].iter().cloned().collect::<HashSet<_>>());
}

fn test_tips3() {
    let parents3: Parents = [
        (BigUint::from(0u64), HashSet::new()),
        (BigUint::from(1u64), HashSet::new()),
        (BigUint::from(2u64), HashSet::new()),
        (BigUint::from(3u64), [BigUint::from(0u64), BigUint::from(1u64), BigUint::from(2u64)].iter().cloned().collect()),
        (BigUint::from(4u64), [BigUint::from(0u64), BigUint::from(1u64), BigUint::from(2u64)].iter().cloned().collect()),
        (BigUint::from(5u64), [BigUint::from(0u64), BigUint::from(1u64), BigUint::from(2u64)].iter().cloned().collect()),
    ].iter().cloned().collect();

    assert_eq!(braid::tips(&parents3, None), [BigUint::from(3u64), BigUint::from(4u64), BigUint::from(5u64)].iter().cloned().collect::<HashSet<_>>());
}

fn test_reverse() {
    let parents: Parents = [
        (BigUint::from(0u64), HashSet::new()),
        (BigUint::from(1u64), HashSet::new()),
        (BigUint::from(2u64), HashSet::new()),
        (BigUint::from(3u64), [BigUint::from(0u64), BigUint::from(1u64), BigUint::from(2u64)].iter().cloned().collect()),
        (BigUint::from(4u64), [BigUint::from(0u64), BigUint::from(1u64), BigUint::from(2u64)].iter().cloned().collect()),
        (BigUint::from(5u64), [BigUint::from(0u64), BigUint::from(1u64), BigUint::from(2u64)].iter().cloned().collect()),
    ].iter().cloned().collect();

    let children = braid::reverse(&parents);

    // Verify that each parent has the correct children
    assert!(children.contains_key(&BigUint::from(0u64)));
    assert!(children.contains_key(&BigUint::from(1u64)));
    assert!(children.contains_key(&BigUint::from(2u64)));
    assert!(children.contains_key(&BigUint::from(3u64)));
    assert!(children.contains_key(&BigUint::from(4u64)));
    assert!(children.contains_key(&BigUint::from(5u64)));

    // Check that beads 0, 1, 2 have beads 3, 4, 5 as children
    for parent in 0..3u64 {
        let parent_biguint = BigUint::from(parent);
        let children_set = children.get(&parent_biguint).unwrap();
        assert_eq!(children_set.len(), 3);
        assert!(children_set.contains(&BigUint::from(3u64)));
        assert!(children_set.contains(&BigUint::from(4u64)));
        assert!(children_set.contains(&BigUint::from(5u64)));
    }

    // Check that beads 3, 4, 5 have no children
    for bead in 3..6u64 {
        let bead_biguint = BigUint::from(bead);
        let children_set = children.get(&bead_biguint).unwrap();
        assert!(children_set.is_empty());
    }
}

fn test_cohorts() {
    let parents1: Parents = [
        (BigUint::from(0u64), HashSet::new()),
        (BigUint::from(1u64), [BigUint::from(0u64)].iter().cloned().collect()),
        (BigUint::from(2u64), [BigUint::from(1u64)].iter().cloned().collect()),
        (BigUint::from(3u64), [BigUint::from(2u64)].iter().cloned().collect()),
    ].iter().cloned().collect();

    let expected = vec![
        [BigUint::from(0u64)].iter().cloned().collect::<HashSet<_>>(),
        [BigUint::from(1u64)].iter().cloned().collect::<HashSet<_>>(),
        [BigUint::from(2u64)].iter().cloned().collect::<HashSet<_>>(),
        [BigUint::from(3u64)].iter().cloned().collect::<HashSet<_>>(),
    ];

    assert_eq!(braid::cohorts(&parents1, None, None), expected);
}

fn test_cohorts_files() {
    for entry in fs::read_dir(TEST_CASE_DIR).unwrap() {
        let entry = entry.unwrap();
        let path = entry.path();

        if path.extension().map_or(false, |ext| ext == "json") {
            let dag = braid::load_braid(&path).unwrap();
            assert_eq!(braid::cohorts(&dag.parents, None, None), dag.cohorts);
        }
    }
}

fn test_cohorts_reversed_files() {
    for entry in fs::read_dir(TEST_CASE_DIR).unwrap() {
        let entry = entry.unwrap();
        let path = entry.path();

        if path.extension().map_or(false, |ext| ext == "json") {
            let dag = braid::load_braid(&path).unwrap();
            let p = braid::reverse(&dag.parents);
            let mut c = dag.cohorts.clone();
            c.reverse();
            assert_eq!(braid::cohorts(&p, None, None), c);
        }
    }
}

fn test_highest_work_path() {
    let parents1: Parents = [
        (BigUint::from(0u64), HashSet::new()),
        (BigUint::from(1u64), [BigUint::from(0u64)].iter().cloned().collect()),
        (BigUint::from(2u64), [BigUint::from(1u64)].iter().cloned().collect()),
        (BigUint::from(3u64), [BigUint::from(2u64)].iter().cloned().collect()),
    ].iter().cloned().collect();

    let children1 = braid::reverse(&parents1);

    let expected = vec![
        BigUint::from(0u64),
        BigUint::from(1u64),
        BigUint::from(2u64),
        BigUint::from(3u64),
    ];

    assert_eq!(braid::highest_work_path(&parents1, Some(&children1), None, None), expected);
}

fn test_highest_work_path_files() {
    for entry in fs::read_dir(TEST_CASE_DIR).unwrap() {
        let entry = entry.unwrap();
        let path = entry.path();

        if path.extension().map_or(false, |ext| ext == "json") {
            let dag = braid::load_braid(&path).unwrap();
            assert_eq!(
                braid::highest_work_path(&dag.parents, Some(&dag.children), Some(&dag.work), None),
                dag.highest_work_path
            );
        }
    }
}

fn test_check_cohort_files() {
    for entry in fs::read_dir(TEST_CASE_DIR).unwrap() {
        let entry = entry.unwrap();
        let path = entry.path();

        if path.extension().map_or(false, |ext| ext == "json") {
            let dag = braid::load_braid(&path).unwrap();
            for c in &dag.cohorts {
                assert!(braid::check_cohort(c, &dag.parents, Some(&dag.children)));
            }
        }
    }
}

fn test_check_work_files() {
    for entry in fs::read_dir(TEST_CASE_DIR).unwrap() {
        let entry = entry.unwrap();
        let path = entry.path();

        if path.extension().map_or(false, |ext| ext == "json") {
            let dag = braid::load_braid(&path).unwrap();
            assert_eq!(
                dag.work,
                braid::descendant_work(&dag.parents, Some(&dag.children), Some(&dag.bead_work), None)
            );
        }
    }
}

fn test_sub_braid_files() {
    for entry in fs::read_dir(TEST_CASE_DIR).unwrap() {
        let entry = entry.unwrap();
        let path = entry.path();

        if path.extension().map_or(false, |ext| ext == "json") {
            let dag = braid::load_braid(&path).unwrap();
            for c in &dag.cohorts {
                assert_eq!(
                    braid::geneses(&braid::sub_braid(c, &dag.parents)),
                    braid::cohort_head(c, &dag.parents, Some(&dag.children))
                );

                assert_eq!(
                    braid::tips(&braid::sub_braid(c, &dag.parents), None),
                    braid::cohort_tail(c, &dag.parents, Some(&dag.children))
                );

                assert_eq!(
                    braid::cohorts(&braid::sub_braid(c, &dag.parents), None, None),
                    vec![c.clone()]
                );
            }
        }
    }
}

fn test_head_tail_files() {
    for entry in fs::read_dir(TEST_CASE_DIR).unwrap() {
        let entry = entry.unwrap();
        let path = entry.path();

        if path.extension().map_or(false, |ext| ext == "json") {
            let dag = braid::load_braid(&path).unwrap();
            for c in &dag.cohorts {
                assert_eq!(
                    braid::cohort_head(c, &dag.parents, Some(&dag.children)),
                    braid::geneses(&braid::sub_braid(c, &dag.parents))
                );

                assert_eq!(
                    braid::cohort_tail(c, &dag.parents, Some(&dag.children)),
                    braid::tips(&braid::sub_braid(c, &dag.parents), None)
                );
            }
        }
    }
}

fn test_all_ancestors() {
    let parents: Parents = [
        (BigUint::from(0u64), HashSet::new()),
        (BigUint::from(1u64), [BigUint::from(0u64)].iter().cloned().collect()),
        (BigUint::from(2u64), [BigUint::from(1u64)].iter().cloned().collect()),
        (BigUint::from(3u64), [BigUint::from(2u64)].iter().cloned().collect()),
    ].iter().cloned().collect();

    let mut ancestors = HashMap::new();
    braid::all_ancestors(&BigUint::from(3u64), &parents, &mut ancestors);

    let expected_ancestors: HashMap<BigUint, HashSet<BigUint>> = [
        (BigUint::from(3u64), [BigUint::from(0u64), BigUint::from(1u64), BigUint::from(2u64)].iter().cloned().collect()),
        (BigUint::from(2u64), [BigUint::from(0u64), BigUint::from(1u64)].iter().cloned().collect()),
        (BigUint::from(1u64), [BigUint::from(0u64)].iter().cloned().collect()),
        (BigUint::from(0u64), HashSet::new()),
    ].iter().cloned().collect();

    assert_eq!(ancestors, expected_ancestors);
}

fn test_save_load_braid() {
    let parents: Parents = [
        (BigUint::from(0u64), HashSet::new()),
        (BigUint::from(1u64), [BigUint::from(0u64)].iter().cloned().collect()),
        (BigUint::from(2u64), [BigUint::from(1u64)].iter().cloned().collect()),
        (BigUint::from(3u64), [BigUint::from(2u64)].iter().cloned().collect()),
    ].iter().cloned().collect();

    let temp_file = "tests/temp_braid_test.json";
    let description = "Test braid";

    // Save the braid
    let dag = braid::save_braid(&parents, temp_file, Some(description)).unwrap();

    // Load the braid
    let loaded_dag = braid::load_braid(temp_file).unwrap();

    // Compare the original and loaded DAGs
    assert_eq!(loaded_dag.description.unwrap(), description);
    assert_eq!(loaded_dag.parents, dag.parents);
    assert_eq!(loaded_dag.children, dag.children);
    assert_eq!(loaded_dag.geneses, dag.geneses);
    assert_eq!(loaded_dag.tips, dag.tips);
    assert_eq!(loaded_dag.cohorts, dag.cohorts);
    assert_eq!(loaded_dag.bead_work, dag.bead_work);
    assert_eq!(loaded_dag.work, dag.work);
    assert_eq!(loaded_dag.highest_work_path, dag.highest_work_path);

    // Clean up
    fs::remove_file(temp_file).unwrap();
}
