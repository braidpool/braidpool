#![no_main]

use arbitrary::Unstructured;
use bitcoin::{TxMerkleNode, Txid};
use braidpool_primitives::utils::bitcoin::MerklePathProof;
use libfuzzer_sys::fuzz_target;

// Cap the reconstructed path length so the fuzzer spends its budget exploring
// logic, not allocating huge vectors. Well past any realistic proof depth.
const MAX_MERKLE_PATH: usize = 64;

// Build an arbitrary `MerklePathProof` from raw fuzz bytes and run the merkle
// root computation on it. The point is to exercise the path-shaping logic on
// inputs a real node could receive over the wire, especially the empty and
// single-element paths and both `is_right_leaf` branches, which are the shapes
// most likely to hit an unchecked index.
fuzz_target!(|data: &[u8]| {
    let mut u = Unstructured::new(data);

    let Ok(tx_bytes) = u.arbitrary::<[u8; 32]>() else {
        return;
    };
    let transaction_hash = Txid::from_byte_array(tx_bytes);

    let Ok(is_right_leaf) = u.arbitrary::<bool>() else {
        return;
    };

    let Ok(mut len) = u.arbitrary_len::<[u8; 32]>() else {
        return;
    };
    len = len.min(MAX_MERKLE_PATH);

    let mut merkle_path = Vec::with_capacity(len);
    for _ in 0..len {
        let Ok(node_bytes) = u.arbitrary::<[u8; 32]>() else {
            break;
        };
        merkle_path.push(TxMerkleNode::from_byte_array(node_bytes));
    }

    let proof = MerklePathProof {
        transaction_hash,
        is_right_leaf,
        merkle_path,
    };

    let _ = proof.calculate_corresponding_merkle_root();
});
