use super::*;
use bitcoin::hashes::Sha256d;

fn hash_pair(left: &[u8; 32], right: &[u8; 32]) -> [u8; 32] {
    let mut concatenated: Vec<u8> = Vec::with_capacity(64);
    concatenated.extend_from_slice(left);
    concatenated.extend_from_slice(right);
    Sha256d::hash(&concatenated).to_byte_array()
}

fn leaf(seed: u8) -> [u8; 32] {
    Sha256d::hash(&[seed]).to_byte_array()
}

#[test]
fn merkle_root_from_single_transaction() {
    // A block with one transaction: the merkle root is the txid itself.
    let txid = Txid::from_byte_array(leaf(1));
    let proof = MerklePathProof {
        transaction_hash: txid,
        transaction_index: 0u32,
        merkle_path: vec![],
    };
    assert_eq!(
        proof.calculate_corresponding_merkle_root(),
        TxMerkleNode::from_byte_array(leaf(1))
    );
}

#[test]
fn merkle_root_from_four_transactions_all_positions() {
    // Manually constructed 4-leaf tree:
    //        root
    //       /    \
    //     h01    h23
    //     / \    / \
    //    h0 h1  h2 h3
    let leaves = [leaf(0), leaf(1), leaf(2), leaf(3)];
    let h01 = hash_pair(&leaves[0], &leaves[1]);
    let h23 = hash_pair(&leaves[2], &leaves[3]);
    let root = TxMerkleNode::from_byte_array(hash_pair(&h01, &h23));

    // (index, sibling path bottom-up)
    let proofs = [
        (0, vec![leaves[1], h23]),
        (1, vec![leaves[0], h23]),
        (2, vec![leaves[3], h01]),
        (3, vec![leaves[2], h01]),
    ];

    for (index, path) in proofs {
        let proof = MerklePathProof {
            transaction_hash: Txid::from_byte_array(leaves[index]),
            transaction_index: index as u32,
            merkle_path: path
                .into_iter()
                .map(TxMerkleNode::from_byte_array)
                .collect(),
        };
        assert_eq!(
            proof.calculate_corresponding_merkle_root(),
            root,
            "proof failed for transaction index {}",
            index
        );
    }
}

#[test]
fn merkle_root_rejects_wrong_sibling() {
    let leaves = [leaf(0), leaf(1)];
    let root = TxMerkleNode::from_byte_array(hash_pair(&leaves[0], &leaves[1]));

    let proof = MerklePathProof {
        transaction_hash: Txid::from_byte_array(leaves[0]),
        transaction_index: 0u32,
        merkle_path: vec![TxMerkleNode::from_byte_array(leaf(9))],
    };
    assert_ne!(proof.calculate_corresponding_merkle_root(), root);
}
