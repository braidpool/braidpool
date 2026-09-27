use bitcoin::{TxMerkleNode, Txid};

use super::MerklePathProof;

#[test]
fn test_empty_merkle_path_proof_is_right_leaf() {
    let txid = Txid::from_byte_array([1u8; 32]);
    let proof = MerklePathProof {
        transaction_hash: txid,
        is_right_leaf: true,
        merkle_path: vec![],
    };

    let calculated_root = proof.calculate_corresponding_merkle_root();
    assert_eq!(
        calculated_root,
        TxMerkleNode::from_byte_array(txid.to_byte_array())
    );
}

#[test]
fn test_empty_merkle_path_proof_is_left_leaf() {
    let txid = Txid::from_byte_array([1u8; 32]);
    let proof = MerklePathProof {
        transaction_hash: txid,
        is_right_leaf: false,
        merkle_path: vec![],
    };

    let calculated_root = proof.calculate_corresponding_merkle_root();
    assert_eq!(
        calculated_root,
        TxMerkleNode::from_byte_array(txid.to_byte_array())
    );
}

#[test]
fn test_single_element_merkle_path_proof() {
    let txid = Txid::from_byte_array([1u8; 32]);
    let sibling = TxMerkleNode::from_byte_array([2u8; 32]);
    let proof = MerklePathProof {
        transaction_hash: txid,
        is_right_leaf: false,
        merkle_path: vec![sibling],
    };

    let calculated_root = proof.calculate_corresponding_merkle_root();
    assert_ne!(
        calculated_root,
        TxMerkleNode::from_byte_array(txid.to_byte_array())
    );
}
