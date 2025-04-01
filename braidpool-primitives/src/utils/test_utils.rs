#![allow(unused)]
use crate::beads::{Bead, TransactionWithMerklePath};
use crate::utils::bitcoin::MerklePathProof;
use crate::utils::BeadHash;
use ::bitcoin::absolute::LockTime;
use ::bitcoin::absolute::Time;
use ::bitcoin::hex::FromHex;
use ::bitcoin::{Amount, Txid};
use ::bitcoin::{
    BlockHash, BlockHeader, BlockTime, BlockVersion, CompactTarget, OutPoint, ScriptBuf, Sequence,
    Transaction, TransactionVersion, TxIn, TxMerkleNode, TxOut, Witness,
};
use std::collections::HashSet;
pub fn create_block_header(
    version: i32,
    prev_blockhash_bytes: [u8; 32],
    merkle_root_bytes: [u8; 32],
    time: u32,
    bits: u32,
    nonce: u32,
) -> BlockHeader {
    BlockHeader {
        version: BlockVersion::from_consensus(version),
        prev_blockhash: BlockHash::from_byte_array(prev_blockhash_bytes),
        merkle_root: TxMerkleNode::from_byte_array(merkle_root_bytes),
        time: BlockTime::from_u32(time),
        bits: CompactTarget::from_consensus(bits),
        nonce,
    }
}

pub fn create_dummy_transaction(
    bytes: [u8; 32],
    vout: u32,
    sequence: u32,
    witness_items: Vec<Vec<u8>>,
    value: u64,
) -> Transaction {
    Transaction {
        version: TransactionVersion::TWO,
        lock_time: LockTime::ZERO,
        input: vec![TxIn {
            previous_output: OutPoint {
                txid: Txid::from_byte_array(bytes),
                vout,
            },
            script_sig: ScriptBuf::new(),
            sequence: Sequence(sequence),
            witness: Witness::from_slice(&witness_items),
        }],
        output: vec![TxOut {
            value: Amount::from_sat(value).unwrap(),
            script_pubkey: ScriptBuf::new(),
        }],
    }
}
pub fn create_dummy_merkle_path_proof(bytes: [u8; 32]) -> MerklePathProof {
    MerklePathProof {
        transaction_hash: Txid::from_byte_array(bytes),
        merkle_path: vec![],
    }
}
pub fn create_parents_set(parents_vec: Vec<(BeadHash, Time)>) -> HashSet<(BeadHash, Time)> {
    parents_vec.into_iter().collect()
}
pub fn create_test_bead(
    block_version: i32,
    prev_blockhash_bytes: [u8; 32],
    merkle_root_bytes: [u8; 32],
    timestamp: u32,
    difficulty_bits: u32,
    nonce: u32,
    bead_hash_bytes: [u8; 32],
    coinbase_tx_bytes: [u8; 32],
    payout_tx_bytes: [u8; 32],
    lesser_difficulty_target: u32,
    parent_hashes: Vec<(BeadHash, Time)>,
    transactions_bytes: Vec<[u8; 32]>,
    bits: u32,
    bead_bytes: [u8; 32],
    observed_time_at_node: u32,
) -> Bead {
    let target: CompactTarget = CompactTarget::from_consensus(lesser_difficulty_target);
    let bytes: [u8; 32] = bead_bytes;
    let beadhash: BeadHash = BlockHash::from_byte_array(bytes);
    let blockheader: BlockHeader = create_block_header(
        block_version,
        prev_blockhash_bytes,
        merkle_root_bytes,
        timestamp,
        bits,
        nonce,
    );

    let coinbase_transaction: TransactionWithMerklePath = (
        create_dummy_transaction(
            coinbase_tx_bytes,
            2,
            0xFFFFFFFF,
            vec![
                hex::decode("03d2e15674941bad4a996372cb87e1856d3652606d98562fe39c5e9e7e413f2105")
                    .unwrap(),
                hex::decode("000000").unwrap(),
            ],
            10_000_000,
        ),
        create_dummy_merkle_path_proof(coinbase_tx_bytes),
    );

    let parents: HashSet<(BeadHash, Time)> = create_parents_set(parent_hashes);

    let mut transactions_of_bead: Vec<Transaction> = Vec::new();

    for transaction in transactions_bytes.iter() {
        transactions_of_bead.push(create_dummy_transaction(
            *transaction,
            2,
            0xFFFFFFFF,
            vec![
                hex::decode("03d2e15674941bad4a996372cb87e1856d3652606d98562fe39c5e9e7e413f2105")
                    .unwrap(),
                hex::decode("000000").unwrap(),
            ],
            10_000_000,
        ));
    }
    let payout_transaction: TransactionWithMerklePath = (
        create_dummy_transaction(
            payout_tx_bytes,
            2,
            0xFFFFFFFF,
            vec![
                hex::decode("03d2e15674941bad4a996372cb87e1856d3652606d98562fe39c5e9e7e413f2105")
                    .unwrap(),
                hex::decode("000000").unwrap(),
            ],
            10_000_000,
        ),
        create_dummy_merkle_path_proof(payout_tx_bytes),
    );
    return Bead {
        block_header: blockheader,
        bead_hash: beadhash,
        coinbase_transaction: coinbase_transaction,
        payout_update_transaction: payout_transaction,
        lesser_difficulty_target: target,
        parents: parents,
        transactions: transactions_of_bead,
        observed_time_at_node: Time::from_consensus(1234567).unwrap(),
    };
}
