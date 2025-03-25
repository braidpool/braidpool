use std::{collections::{HashMap, HashSet}, fs, path::Path};

use braidpool::braid::{self, *};
use braidpool::braid::io_json::{check_cohort, load_braid, save_braid};

const TEST_CASE_DIR: &str = "tests/braids/";

#[test]
fn test_geneses1() {
    let parents1: Relatives = [
        (BeadHash::from(0u64), HashSet::new()),
        (
            BeadHash::from(1u64),
            [BeadHash::from(0u64)].iter().cloned().collect(),
        ),
        (
            BeadHash::from(2u64),
            [BeadHash::from(1u64)].iter().cloned().collect(),
        ),
        (
            BeadHash::from(3u64),
            [BeadHash::from(2u64)].iter().cloned().collect(),
        ),
    ]
    .iter()
    .cloned()
    .collect();

    assert_eq!(
        braid::geneses(&parents1),
        [BeadHash::from(0u64)]
            .iter()
            .cloned()
            .collect::<HashSet<_>>()
    );
}

#[test]
fn test_geneses2() {
    let parents2: Relatives = [
        (BeadHash::from(0u64), HashSet::new()),
        (BeadHash::from(1u64), HashSet::new()),
        (
            BeadHash::from(2u64),
            [BeadHash::from(1u64)].iter().cloned().collect(),
        ),
        (
            BeadHash::from(3u64),
            [BeadHash::from(1u64)].iter().cloned().collect(),
        ),
    ]
    .iter()
    .cloned()
    .collect();

    assert_eq!(
        braid::geneses(&parents2),
        [BeadHash::from(0u64), BeadHash::from(1u64)]
            .iter()
            .cloned()
            .collect::<HashSet<_>>()
    );
}

#[test]
fn test_geneses3() {
    let parents3: Relatives = [
        (BeadHash::from(0u64), HashSet::new()),
        (BeadHash::from(1u64), HashSet::new()),
        (BeadHash::from(2u64), HashSet::new()),
        (
            BeadHash::from(3u64),
            [BeadHash::from(1u64)].iter().cloned().collect(),
        ),
        (
            BeadHash::from(4u64),
            [BeadHash::from(0u64)].iter().cloned().collect(),
        ),
    ]
    .iter()
    .cloned()
    .collect();

    assert_eq!(
        braid::geneses(&parents3),
        [
            BeadHash::from(0u64),
            BeadHash::from(1u64),
            BeadHash::from(2u64)
        ]
        .iter()
        .cloned()
        .collect::<HashSet<_>>()
    );
}

#[test]
fn test_geneses_files() {
    // Create directory if it doesn't exist
    if !Path::new(TEST_CASE_DIR).exists() {
        fs::create_dir_all(TEST_CASE_DIR).unwrap();
    }

    // Skip if directory is empty
    let entries = fs::read_dir(TEST_CASE_DIR).unwrap();
    let has_json_files = entries
        .filter_map(Result::ok)
        .any(|e| e.path().extension().map_or(false, |ext| ext == "json"));

    if !has_json_files {
        return; // Skip test if no JSON files
    }

    for entry in fs::read_dir(TEST_CASE_DIR).unwrap() {
        let entry = entry.unwrap();
        let path = entry.path();

        if path.extension().map_or(false, |ext| ext == "json") {
            let path_str = path.to_string_lossy();
            let dag = load_braid(&path).unwrap();
            assert_eq!(
                braid::geneses(&dag.parents),
                [BeadHash::from(0u64)]
                    .iter()
                    .cloned()
                    .collect::<HashSet<_>>(),
                "Failed on file: {}",
                path_str
            );
        }
    }
}

#[test]
fn test_tips1() {
    let parents1: Relatives = [
        (BeadHash::from(0u64), HashSet::new()),
        (
            BeadHash::from(1u64),
            [BeadHash::from(0u64)].iter().cloned().collect(),
        ),
        (
            BeadHash::from(2u64),
            [BeadHash::from(1u64)].iter().cloned().collect(),
        ),
        (
            BeadHash::from(3u64),
            [BeadHash::from(2u64)].iter().cloned().collect(),
        ),
    ]
    .iter()
    .cloned()
    .collect();

    assert_eq!(
        braid::tips(&parents1, None),
        [BeadHash::from(3u64)]
            .iter()
            .cloned()
            .collect::<HashSet<_>>()
    );
}

#[test]
fn test_tips2() {
    let parents2: Relatives = [
        (BeadHash::from(0u64), HashSet::new()),
        (
            BeadHash::from(1u64),
            [BeadHash::from(0u64)].iter().cloned().collect(),
        ),
        (
            BeadHash::from(2u64),
            [BeadHash::from(1u64)].iter().cloned().collect(),
        ),
        (
            BeadHash::from(3u64),
            [BeadHash::from(1u64)].iter().cloned().collect(),
        ),
    ]
    .iter()
    .cloned()
    .collect();

    assert_eq!(
        braid::tips(&parents2, None),
        [BeadHash::from(2u64), BeadHash::from(3u64)]
            .iter()
            .cloned()
            .collect::<HashSet<_>>()
    );
}

#[test]
fn test_tips3() {
    let parents3: Relatives = [
        (BeadHash::from(0u64), HashSet::new()),
        (BeadHash::from(1u64), HashSet::new()),
        (BeadHash::from(2u64), HashSet::new()),
        (
            BeadHash::from(3u64),
            [
                BeadHash::from(0u64),
                BeadHash::from(1u64),
                BeadHash::from(2u64),
            ]
            .iter()
            .cloned()
            .collect(),
        ),
        (
            BeadHash::from(4u64),
            [
                BeadHash::from(0u64),
                BeadHash::from(1u64),
                BeadHash::from(2u64),
            ]
            .iter()
            .cloned()
            .collect(),
        ),
        (
            BeadHash::from(5u64),
            [
                BeadHash::from(0u64),
                BeadHash::from(1u64),
                BeadHash::from(2u64),
            ]
            .iter()
            .cloned()
            .collect(),
        ),
    ]
    .iter()
    .cloned()
    .collect();

    assert_eq!(
        braid::tips(&parents3, None),
        [
            BeadHash::from(3u64),
            BeadHash::from(4u64),
            BeadHash::from(5u64)
        ]
        .iter()
        .cloned()
        .collect::<HashSet<_>>()
    );
}

#[test]
fn test_reverse() {
    let parents: Relatives = [
        (BeadHash::from(0u64), HashSet::new()),
        (BeadHash::from(1u64), HashSet::new()),
        (BeadHash::from(2u64), HashSet::new()),
        (
            BeadHash::from(3u64),
            [
                BeadHash::from(0u64),
                BeadHash::from(1u64),
                BeadHash::from(2u64),
            ]
            .iter()
            .cloned()
            .collect(),
        ),
        (
            BeadHash::from(4u64),
            [
                BeadHash::from(0u64),
                BeadHash::from(1u64),
                BeadHash::from(2u64),
            ]
            .iter()
            .cloned()
            .collect(),
        ),
        (
            BeadHash::from(5u64),
            [
                BeadHash::from(0u64),
                BeadHash::from(1u64),
                BeadHash::from(2u64),
            ]
            .iter()
            .cloned()
            .collect(),
        ),
    ]
    .iter()
    .cloned()
    .collect();

    let expected: HashMap<BeadHash, HashSet<BeadHash>> = [
        (
            BeadHash::from(0u64),
            [
                BeadHash::from(3u64),
                BeadHash::from(4u64),
                BeadHash::from(5u64),
            ]
            .iter()
            .cloned()
            .collect(),
        ),
        (
            BeadHash::from(1u64),
            [
                BeadHash::from(3u64),
                BeadHash::from(4u64),
                BeadHash::from(5u64),
            ]
            .iter()
            .cloned()
            .collect(),
        ),
        (
            BeadHash::from(2u64),
            [
                BeadHash::from(3u64),
                BeadHash::from(4u64),
                BeadHash::from(5u64),
            ]
            .iter()
            .cloned()
            .collect(),
        ),
        (BeadHash::from(3u64), HashSet::new()),
        (BeadHash::from(4u64), HashSet::new()),
        (BeadHash::from(5u64), HashSet::new()),
    ]
    .iter()
    .cloned()
    .collect();

    assert_eq!(braid::reverse(&parents), expected);
}

#[test]
fn test_cohorts() {
    let parents1: Relatives = [
        (BeadHash::from(0u64), HashSet::new()),
        (
            BeadHash::from(1u64),
            [BeadHash::from(0u64)].iter().cloned().collect(),
        ),
        (
            BeadHash::from(2u64),
            [BeadHash::from(1u64)].iter().cloned().collect(),
        ),
        (
            BeadHash::from(3u64),
            [BeadHash::from(2u64)].iter().cloned().collect(),
        ),
    ]
    .iter()
    .cloned()
    .collect();

    let expected = vec![
        [BeadHash::from(0u64)]
            .iter()
            .cloned()
            .collect::<HashSet<_>>(),
        [BeadHash::from(1u64)]
            .iter()
            .cloned()
            .collect::<HashSet<_>>(),
        [BeadHash::from(2u64)]
            .iter()
            .cloned()
            .collect::<HashSet<_>>(),
        [BeadHash::from(3u64)]
            .iter()
            .cloned()
            .collect::<HashSet<_>>(),
    ];

    assert_eq!(braid::cohorts(&parents1, None, None), expected);
}

#[test]
fn test_cohorts_files() {
    for entry in fs::read_dir(TEST_CASE_DIR).unwrap() {
        let entry = entry.unwrap();
        let path = entry.path();

        if path.extension().map_or(false, |ext| ext == "json") {
            let path_str = path.to_string_lossy();
            let dag = load_braid(&path).unwrap();
            assert_eq!(
                braid::cohorts(&dag.parents, None, None),
                dag.cohorts,
                "Failed on file: {}",
                path_str
            );
        }
    }
}

#[test]
fn test_cohorts_reversed_files() {
    // Skip if directory is empty
    let entries = fs::read_dir(TEST_CASE_DIR).unwrap();
    let has_json_files = entries
        .filter_map(Result::ok)
        .any(|e| e.path().extension().map_or(false, |ext| ext == "json"));

    if !has_json_files {
        return; // Skip test if no JSON files
    }

    for entry in fs::read_dir(TEST_CASE_DIR).unwrap() {
        let entry = entry.unwrap();
        let path = entry.path();

        if path.extension().map_or(false, |ext| ext == "json") {
            let path_str = path.to_string_lossy();
            let dag = load_braid(&path).unwrap();
            let p = braid::reverse(&dag.parents);
            let mut c = dag.cohorts.clone();
            c.reverse();
            assert_eq!(
                braid::cohorts(&p, None, None),
                c,
                "Failed on file: {}",
                path_str
            );
        }
    }
}

#[test]
fn test_highest_work_path() {
    let parents1: Relatives = [
        (BeadHash::from(0u64), HashSet::new()),
        (
            BeadHash::from(1u64),
            [BeadHash::from(0u64)].iter().cloned().collect(),
        ),
        (
            BeadHash::from(2u64),
            [BeadHash::from(1u64)].iter().cloned().collect(),
        ),
        (
            BeadHash::from(3u64),
            [BeadHash::from(2u64)].iter().cloned().collect(),
        ),
    ]
    .iter()
    .cloned()
    .collect();

    let children1 = braid::reverse(&parents1);

    let expected = vec![
        BeadHash::from(0u64),
        BeadHash::from(1u64),
        BeadHash::from(2u64),
        BeadHash::from(3u64),
    ];

    let bead_work: HashMap<BeadHash, Work> = parents1
        .keys()
        .map(|b| (b.clone(), Work::from(1u32)))
        .collect();
    assert_eq!(
        braid::highest_work_path(&parents1, Some(&children1), &bead_work),
        expected
    );
}

#[test]
fn test_highest_work_path_files() {
    // Skip if directory is empty
    let entries = fs::read_dir(TEST_CASE_DIR).unwrap();
    let has_json_files = entries
        .filter_map(Result::ok)
        .any(|e| e.path().extension().map_or(false, |ext| ext == "json"));

    if !has_json_files {
        return; // Skip test if no JSON files
    }

    for entry in fs::read_dir(TEST_CASE_DIR).unwrap() {
        let entry = entry.unwrap();
        let path = entry.path();

        if path.extension().map_or(false, |ext| ext == "json") {
            let path_str = path.to_string_lossy();
            let dag = load_braid(&path).unwrap();
            assert_eq!(
                braid::highest_work_path(&dag.parents, Some(&dag.children), &dag.bead_work),
                dag.highest_work_path,
                "Failed on file: {}",
                path_str
            );
        }
    }
}

#[test]
fn test_check_cohort_files() {
    // Skip if directory is empty
    let entries = fs::read_dir(TEST_CASE_DIR).unwrap();
    let has_json_files = entries
        .filter_map(Result::ok)
        .any(|e| e.path().extension().map_or(false, |ext| ext == "json"));

    if !has_json_files {
        return; // Skip test if no JSON files
    }

    for entry in fs::read_dir(TEST_CASE_DIR).unwrap() {
        let entry = entry.unwrap();
        let path = entry.path();

        if path.extension().map_or(false, |ext| ext == "json") {
            let path_str = path.to_string_lossy();
            let dag = load_braid(&path).unwrap();
            for (i, c) in dag.cohorts.iter().enumerate() {
                assert!(
                    check_cohort(c, &dag.parents, Some(&dag.children)),
                    "Failed on file: {}, cohort index: {}",
                    path_str,
                    i
                );
            }
        }
    }
}

#[test]
fn test_check_work_files() {
    // Skip if directory is empty
    let entries = fs::read_dir(TEST_CASE_DIR).unwrap();
    let has_json_files = entries
        .filter_map(Result::ok)
        .any(|e| e.path().extension().map_or(false, |ext| ext == "json"));

    if !has_json_files {
        return; // Skip test if no JSON files
    }

    for entry in fs::read_dir(TEST_CASE_DIR).unwrap() {
        let entry = entry.unwrap();
        let path = entry.path();

        if path.extension().map_or(false, |ext| ext == "json") {
            let path_str = path.to_string_lossy();
            let dag = load_braid(&path).unwrap();
            assert_eq!(
                dag.work,
                braid::descendant_work(&dag.parents, Some(&dag.children), &dag.bead_work, None),
                "Failed on file: {}",
                path_str
            );
        }
    }
}

#[test]
fn test_sub_braid_files() {
    // Skip if directory is empty
    let entries = fs::read_dir(TEST_CASE_DIR).unwrap();
    let has_json_files = entries
        .filter_map(Result::ok)
        .any(|e| e.path().extension().map_or(false, |ext| ext == "json"));

    if !has_json_files {
        return; // Skip test if no JSON files
    }

    for entry in fs::read_dir(TEST_CASE_DIR).unwrap() {
        let entry = entry.unwrap();
        let path = entry.path();

        if path.extension().map_or(false, |ext| ext == "json") {
            let path_str = path.to_string_lossy();
            let dag = load_braid(&path).unwrap();
            for (i, c) in dag.cohorts.iter().enumerate() {
                assert_eq!(
                    braid::geneses(&braid::sub_braid(c, &dag.parents)),
                    braid::cohort_head(c, &dag.parents, Some(&dag.children)),
                    "Failed on file: {}, cohort index: {}, geneses check",
                    path_str,
                    i
                );

                assert_eq!(
                    braid::tips(&braid::sub_braid(c, &dag.parents), None),
                    braid::cohort_tail(c, &dag.parents, Some(&dag.children)),
                    "Failed on file: {}, cohort index: {}, tips check",
                    path_str,
                    i
                );

                assert_eq!(
                    braid::cohorts(&braid::sub_braid(c, &dag.parents), None, None),
                    vec![c.clone()],
                    "Failed on file: {}, cohort index: {}, cohorts check",
                    path_str,
                    i
                );
            }
        }
    }
}

#[test]
fn test_head_tail_files() {
    // Skip if directory is empty
    let entries = fs::read_dir(TEST_CASE_DIR).unwrap();
    let has_json_files = entries
        .filter_map(Result::ok)
        .any(|e| e.path().extension().map_or(false, |ext| ext == "json"));

    if !has_json_files {
        return; // Skip test if no JSON files
    }

    for entry in fs::read_dir(TEST_CASE_DIR).unwrap() {
        let entry = entry.unwrap();
        let path = entry.path();

        if path.extension().map_or(false, |ext| ext == "json") {
            let path_str = path.to_string_lossy();
            let dag = load_braid(&path).unwrap();
            for (i, c) in dag.cohorts.iter().enumerate() {
                assert_eq!(
                    braid::cohort_head(c, &dag.parents, Some(&dag.children)),
                    braid::geneses(&braid::sub_braid(c, &dag.parents)),
                    "Failed on file: {}, cohort index: {}, head check",
                    path_str,
                    i
                );

                assert_eq!(
                    braid::cohort_tail(c, &dag.parents, Some(&dag.children)),
                    braid::tips(&braid::sub_braid(c, &dag.parents), None),
                    "Failed on file: {}, cohort index: {}, tail check",
                    path_str,
                    i
                );
            }
        }
    }
}

#[test]
fn test_all_ancestors() {
    let parents = [
        (BeadHash::from(0u64), HashSet::new()),
        (
            BeadHash::from(1u64),
            [BeadHash::from(0u64)].iter().cloned().collect(),
        ),
        (
            BeadHash::from(2u64),
            [BeadHash::from(1u64)].iter().cloned().collect(),
        ),
        (
            BeadHash::from(3u64),
            [BeadHash::from(2u64)].iter().cloned().collect(),
        ),
    ]
    .iter()
    .cloned()
    .collect();

    let mut ancestors = std::collections::HashMap::new();
    braid::all_ancestors(&BeadHash::from(3u64), &parents, &mut ancestors);

    let expected_ancestors = [
        (
            BeadHash::from(3u64),
            [
                BeadHash::from(0u64),
                BeadHash::from(1u64),
                BeadHash::from(2u64),
            ]
            .iter()
            .cloned()
            .collect(),
        ),
        (
            BeadHash::from(2u64),
            [BeadHash::from(0u64), BeadHash::from(1u64)]
                .iter()
                .cloned()
                .collect(),
        ),
        (
            BeadHash::from(1u64),
            [BeadHash::from(0u64)].iter().cloned().collect(),
        ),
        (BeadHash::from(0u64), HashSet::new()),
    ]
    .iter()
    .cloned()
    .collect();

    assert_eq!(ancestors, expected_ancestors);
}

#[test]
fn test_save_load_braid() {
    let parents = [
        (BeadHash::from(0u64), HashSet::new()),
        (
            BeadHash::from(1u64),
            [BeadHash::from(0u64)].iter().cloned().collect(),
        ),
        (
            BeadHash::from(2u64),
            [BeadHash::from(1u64)].iter().cloned().collect(),
        ),
        (
            BeadHash::from(3u64),
            [BeadHash::from(2u64)].iter().cloned().collect(),
        ),
    ]
    .iter()
    .cloned()
    .collect();

    let temp_file = "tests/temp_braid_test.json";
    let description = "Test braid";

    // Save the braid
    let dag = save_braid(&parents, temp_file, Some(description)).unwrap();

    // Load the braid
    let loaded_dag = load_braid(temp_file).unwrap();

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
    std::fs::remove_file(temp_file).unwrap();
}
