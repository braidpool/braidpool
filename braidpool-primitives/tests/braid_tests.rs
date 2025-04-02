use ::bitcoin::absolute::Time;
use braidpool_primitives::braid::Braid;
use braidpool_primitives::utils::BeadHash;
use braidpool_primitives::utils::test_utils::create_test_bead;
use std::collections::HashSet;

#[test]
fn add_bead_test() {
    let mut genesis_beads: HashSet<BeadHash> = HashSet::new();
    let test_dag_bead_1 = create_test_bead(
        2,
        [0x00; 32],
        [
            0xf3, 0xb8, 0x76, 0x2e, 0x7c, 0x1b, 0xd6, 0x47, 0xf1, 0xf6, 0x9d, 0x2a, 0x7f, 0x9c,
            0x85, 0xf0, 0xb2, 0x5e, 0x64, 0x69, 0xf1, 0x07, 0xd2, 0x31, 0xdf, 0xf4, 0x5c, 0x47,
            0x1f, 0x88, 0x94, 0x58,
        ],
        1653195600,
        486604799,
        0,
        [0x00; 32],
        [0xbb; 32],
        [0xbb; 32],
        4040404,
        vec![
            (
                BeadHash::from_byte_array([0x01; 32]),
                Time::from_consensus(1690000000).expect("invalid time value"),
            ),
            (
                BeadHash::from_byte_array([0x02; 32]),
                Time::from_consensus(1690001000).expect("invalid time value"),
            ),
            (
                BeadHash::from_byte_array([0x03; 32]),
                Time::from_consensus(1690002000).expect("invalid time value"),
            ),
        ],
        vec![[0x11; 32], [0x22; 32], [0x33; 32], [0x44; 32]],
        436864982,
        [0x00; 32],
        1653195600,
    );
    genesis_beads.insert(test_dag_bead_1.bead_hash);
    let mut test_braid = Braid::new(genesis_beads);
    test_braid.add_bead(test_dag_bead_1);

    // assert!(test_braid.);
}
