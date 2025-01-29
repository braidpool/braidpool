use braidpool::cohorts::*;
use std::collections::{HashMap, HashSet, VecDeque};
use std::fs;
use std::path::Path;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_cohorts_simple() {
        let mut parents = Parents::new();
        parents.insert(0, HashSet::new());
        parents.insert(1, [0].iter().copied().collect());
        parents.insert(2, [1].iter().copied().collect());
        parents.insert(3, [2].iter().copied().collect());

        let cohorts: Vec<HashSet<Bead>> = get_cohorts(&parents).collect();
        let expected: Vec<HashSet<Bead>> = vec![
            [0].iter().copied().collect(),
            [1].iter().copied().collect(),
            [2].iter().copied().collect(),
            [3].iter().copied().collect(),
        ];

        assert_eq!(cohorts, expected);
    }

    #[test]
    fn test_cohorts_diamond() {
        let mut parents = Parents::new();
        parents.insert(0, HashSet::new());
        parents.insert(1, [0].iter().copied().collect());
        parents.insert(2, [0].iter().copied().collect());
        parents.insert(3, [1, 2].iter().copied().collect());
        parents.insert(4, [3].iter().copied().collect());

        let cohorts: Vec<HashSet<Bead>> = get_cohorts(&parents).collect();
        let expected: Vec<HashSet<Bead>> = vec![
            [0].iter().copied().collect(),
            [1, 2].iter().copied().collect(),
            [3].iter().copied().collect(),
            [4].iter().copied().collect(),
        ];

        assert_eq!(cohorts, expected);
    }

    #[test]
    fn test_cohorts_parallel() {
        let mut parents = Parents::new();
        parents.insert(0, HashSet::new());
        parents.insert(1, HashSet::new());
        parents.insert(2, [0, 1].iter().copied().collect());

        let cohorts: Vec<HashSet<Bead>> = get_cohorts(&parents).collect();
        let expected: Vec<HashSet<Bead>> = vec![
            [0, 1].iter().copied().collect(),
            [2].iter().copied().collect(),
        ];

        assert_eq!(cohorts, expected);
    }

    fn setup_test_parents() -> (Parents, Parents, Parents, Parents, Parents) {
        let mut parents1 = Parents::new();
        parents1.insert(0, HashSet::new());
        parents1.insert(1, [0].iter().copied().collect());
        parents1.insert(2, [1].iter().copied().collect());
        parents1.insert(3, [2].iter().copied().collect());

        let mut parents2 = Parents::new();
        parents2.insert(0, HashSet::new());
        parents2.insert(1, HashSet::new());
        parents2.insert(2, [1].iter().copied().collect());
        parents2.insert(3, [1].iter().copied().collect());

        let mut parents3 = Parents::new();
        parents3.insert(0, HashSet::new());
        parents3.insert(1, HashSet::new());
        parents3.insert(2, HashSet::new());
        parents3.insert(3, [1].iter().copied().collect());
        parents3.insert(4, [0].iter().copied().collect());

        let mut parents4 = Parents::new();
        parents4.insert(0, HashSet::new());
        parents4.insert(1, HashSet::new());
        parents4.insert(2, HashSet::new());
        parents4.insert(3, [0, 1, 2].iter().copied().collect());
        parents4.insert(4, [0, 1, 2].iter().copied().collect());
        parents4.insert(5, [0, 1, 2].iter().copied().collect());

        let mut diamond = Parents::new();
        diamond.insert(0, HashSet::new());
        diamond.insert(1, [0].iter().copied().collect());
        diamond.insert(2, [0].iter().copied().collect());
        diamond.insert(3, [1, 2].iter().copied().collect());
        diamond.insert(4, [3].iter().copied().collect());

        (parents1, parents2, parents3, parents4, diamond)
    }

    #[test]
    fn test_geneses() {
        let (parents1, parents2, parents3, _, _) = setup_test_parents();

        assert_eq!(get_geneses(&parents1), [0].iter().copied().collect());
        assert_eq!(get_geneses(&parents2), [0, 1].iter().copied().collect());
        assert_eq!(get_geneses(&parents3), [0, 1, 2].iter().copied().collect());
    }

    #[test]
    fn test_tips() {
        let mut parents1 = Parents::new();
        parents1.insert(0, HashSet::new());
        parents1.insert(1, [0].iter().copied().collect());
        parents1.insert(2, [1].iter().copied().collect());
        parents1.insert(3, [2].iter().copied().collect());
        assert_eq!(get_tips(&parents1), [3].iter().copied().collect());

        let mut parents2 = Parents::new();
        parents2.insert(0, HashSet::new());
        parents2.insert(1, [0].iter().copied().collect());
        parents2.insert(2, [1].iter().copied().collect());
        parents2.insert(3, [1].iter().copied().collect());
        assert_eq!(get_tips(&parents2), [2, 3].iter().copied().collect());

        let mut parents3 = Parents::new();
        parents3.insert(0, HashSet::new());
        parents3.insert(1, HashSet::new());
        parents3.insert(2, HashSet::new());
        parents3.insert(3, [0, 1, 2].iter().copied().collect());
        parents3.insert(4, [0, 1, 2].iter().copied().collect());
        parents3.insert(5, [0, 1, 2].iter().copied().collect());
        assert_eq!(get_tips(&parents3), [3, 4, 5].iter().copied().collect());
    }

    #[test]
    fn test_highest_work_path() {
        let mut parents = Parents::new();
        parents.insert(0, HashSet::new());
        parents.insert(1, [0].iter().copied().collect());
        parents.insert(2, [1].iter().copied().collect());
        parents.insert(3, [2].iter().copied().collect());

        let expected = vec![0, 1, 2, 3];
        let result = highest_work_path(&parents, &reverse(&parents));
        assert_eq!(
            result, expected,
            "\nExpected: {:?}\nGot: {:?}",
            expected, result
        );
    }

    #[test]
    fn test_reverse() {
        let (_, _, _, parents4, _) = setup_test_parents();
        let expected: Children = [
            (0, [3, 4, 5].iter().copied().collect()),
            (1, [3, 4, 5].iter().copied().collect()),
            (2, [3, 4, 5].iter().copied().collect()),
            (3, HashSet::new()),
            (4, HashSet::new()),
            (5, HashSet::new()),
        ]
        .iter()
        .cloned()
        .collect();

        assert_eq!(reverse(&parents4), expected);
    }

    #[test]
    fn test_braid_files() {
        // Get all .braid files in the current directory
        let test_files: Vec<_> = fs::read_dir(".")
            .unwrap()
            .filter_map(|entry| {
                let entry = entry.unwrap();
                let path = entry.path();
                if path.extension().and_then(|s| s.to_str()) == Some("braid") {
                    Some(path)
                } else {
                    None
                }
            })
            .collect();

        assert!(
            !test_files.is_empty(),
            "No .braid files found in current directory"
        );

        for path in test_files {
            println!("Testing file: {:?}", path);

            // Load the test case
            let dag =
                Dag::load(&path).unwrap_or_else(|e| panic!("Failed to load {:?}: {}", path, e));

            // Test geneses
            assert_eq!(
                get_geneses(&dag.parents),
                dag.geneses,
                "Genesis mismatch in {:?}",
                path
            );

            // Test cohorts
            let computed_cohorts: Vec<_> = get_cohorts(&dag.parents).collect();
            assert_eq!(
                computed_cohorts, dag.cohorts,
                "Cohorts mismatch in {:?}",
                path
            );

            // Test highest work path
            let computed_hwp = highest_work_path(&dag.parents, &dag.children);
            assert_eq!(
                computed_hwp, dag.highest_work_path,
                "Highest work path mismatch in {:?}",
                path
            );
        }
    }

    #[test]
    fn test_braid_roundtrip() {
        // Create a simple test DAG
        let mut parents = Parents::new();
        parents.insert(0, Default::default());
        parents.insert(1, [0].iter().copied().collect());
        parents.insert(2, [1].iter().copied().collect());

        let dag = Dag::new(parents, Some("Test DAG".to_string()));

        // Save and reload
        let temp_path = Path::new("test_roundtrip.braid");
        dag.save(&temp_path).expect("Failed to save DAG");

        let loaded_dag = Dag::load(&temp_path).expect("Failed to load DAG");
        assert_eq!(dag, loaded_dag, "DAG changed during save/load roundtrip");

        // Cleanup
        fs::remove_file(temp_path).expect("Failed to cleanup test file");
    }

    #[test]
    fn test_highest_work_path_from_braid_files() {
        // Get all .braid files in the current directory
        let test_files: Vec<_> = fs::read_dir(".")
            .expect("Failed to read current directory")
            .filter_map(|entry| {
                let entry = entry.unwrap();
                let path = entry.path();
                if path.extension().and_then(|s| s.to_str()) == Some("braid") {
                    Some(path)
                } else {
                    None
                }
            })
            .collect();

        assert!(
            !test_files.is_empty(),
            "No .braid files found in current directory"
        );

        for path in test_files {
            println!("Testing highest_work_path in file: {:?}", path);

            // Load the test case
            let dag =
                Dag::load(&path).unwrap_or_else(|e| panic!("Failed to load {:?}: {}", path, e));

            // Compute highest work path
            let computed_hwp = highest_work_path(&dag.parents, &dag.children);

            // Compare with expected result
            assert_eq!(
                computed_hwp, dag.highest_work_path,
                "\nFile: {:?}\nComputed highest_work_path: {:?}\nExpected: {:?}",
                path, computed_hwp, dag.highest_work_path
            );

            // Additional validation checks
            if !computed_hwp.is_empty() {
                // Check that the path starts with a genesis
                assert!(
                    dag.geneses.contains(&computed_hwp[0]),
                    "\nFile: {:?}\nPath {:?} doesn't start with a genesis bead. Genesis beads: {:?}",
                    path,
                    computed_hwp,
                    dag.geneses
                );

                // Check that the path ends with a tip
                assert!(
                    dag.tips.contains(computed_hwp.last().unwrap()),
                    "\nFile: {:?}\nPath {:?} doesn't end with a tip bead. Tip beads: {:?}",
                    path,
                    computed_hwp,
                    dag.tips
                );

                // Verify path continuity
                for window in computed_hwp.windows(2) {
                    let (current, next) = (window[0], window[1]);
                    assert!(
                        dag.children
                            .get(&current)
                            .map_or(false, |children| children.contains(&next)),
                        "\nFile: {:?}\nDiscontinuous path at {} -> {}\nPath: {:?}",
                        path,
                        current,
                        next,
                        computed_hwp
                    );
                }
            }
        }
    }

    // Add a helper function to print the DAG structure for debugging
    fn print_dag_structure(path: &Path, dag: &Dag) {
        println!("\nDAG Structure for {:?}:", path);
        println!("Genesis beads: {:?}", dag.geneses);
        println!("Tip beads: {:?}", dag.tips);
        println!("Parents map:");
        for (bead, parents) in &dag.parents {
            println!("  {}: {:?}", bead, parents);
        }
        println!("Expected highest work path: {:?}", dag.highest_work_path);
    }
}
