// Integration tests for public functions!
use braidpool_primitives::bead::Bead;
use braidpool_primitives::utils::test_utils::create_test_bead;
#[test]
fn test_valid_bead() {
    let prev_block_bytes_str_1 = "00000000000000000000efc4be188e9d2053681791a5c53b07ecfe8ba00f8464";
    let mut prev_bytes_1 = [0u8; 32];
    let result = hex::decode_to_slice(prev_block_bytes_str_1, &mut prev_bytes_1 as &mut [u8]);
    match result {
        Ok(val) => {
            println!("Successfully decoded {:?}", val);
        }
        Err(e) => {
            println!(
                "{:?} this error occurred while decoding the corresponding bytes",
                e
            );
        }
    }
    let payout_txin_1 = "450c309b70fb3f71b63b10ce60af17499bd21b1db39aa47b19bf22166ee67144";
    let mut payout_tx_bytes_1 = [0u8; 32];
    let result = hex::decode_to_slice(payout_txin_1, &mut payout_tx_bytes_1);
    match result {
        Ok(val) => {
            println!("Successfully decoded {:?}", val);
        }
        Err(e) => {
            println!(
                "{:?} this error occurred while decoding the corresponding bytes",
                e
            );
        }
    }

    let mut tx_included_in_bead_1: Vec<[u8; 32]> = Vec::new();
    let txs_1 = [
        "c8f0a4e7b3d5c1f9a6c2d5f9e7b4d1c7f3a5e9b2d6c8f0a4e7b3d5c1f9a6c2d5",
        "f3a5e9b2d6c8f0a4e7b3d5c1f9a6c2d5f9e7b4d1c7f3a5e9b2d6c8f0a4e7b3d5",
    ];

    for tx in txs_1 {
        let mut curr_bytes_1 = [0u8; 32];
        let result = hex::decode_to_slice(tx, &mut curr_bytes_1);
        match result {
            Ok(val) => {
                println!("Successfully decoded {:?}", val);
                tx_included_in_bead_1.push(curr_bytes_1);
            }
            Err(e) => {
                println!(
                    "{:?} this error occurred while decoding the corresponding bytes",
                    e
                );
            }
        }
    }

    let test_dag_bead: Bead = create_test_bead(
        2,
        prev_bytes_1,
        1653195601,
        486604790,
        1,
        payout_tx_bytes_1,
        123455,
        vec![],
        tx_included_in_bead_1,
        223456,
        123456,
    );
    assert_eq!(test_dag_bead.is_valid_bead(), true);
}
