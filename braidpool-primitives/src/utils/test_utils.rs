#![allow(unused)]
use crate::bead::{Bead, TransactionWithMerklePath};
use crate::utils::BeadHash;
use crate::utils::bitcoin::MerklePathProof;
use ::bitcoin::absolute::LockTime;
use ::bitcoin::absolute::Time;
use ::bitcoin::hex::FromHex;
use ::bitcoin::{Amount, Txid};
use ::bitcoin::{
    BlockHash, BlockHeader, BlockTime, BlockVersion, CompactTarget, OutPoint, ScriptBuf, Sequence,
    Transaction, TransactionVersion, TxIn, TxMerkleNode, TxOut, Witness,
};
use bitcoin::hashes::sha256d::hash;
use bitcoin::hex::DisplayHex;
use bitcoin::merkle_tree::MerkleNode;
use bitcoin::transaction;
use sha2::{Digest, Sha256};
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
        version: BlockVersion::TWO,
        prev_blockhash: BlockHash::from_byte_array(prev_blockhash_bytes),
        merkle_root: TxMerkleNode::from_byte_array(merkle_root_bytes),
        time: BlockTime::from_u32(time),
        bits: CompactTarget::from_consensus(bits),
        nonce,
    }
}
pub fn create_dummy_coinbase_transaction(
    vout: u32,
    sequence: u32,
    witness_items: Vec<Vec<u8>>,
    value: u64,
) -> Transaction {
    Transaction {
        version: TransactionVersion::TWO,
        lock_time: LockTime::ZERO,
        input: vec![TxIn {
            previous_output: OutPoint::COINBASE_PREVOUT,
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
pub fn hash_data(data: &String) -> String {
    let bytes = hex::decode(data).expect("Invalid hex string");

    let mut hasher = Sha256::new();
    hasher.update(&bytes);
    let result = hasher.finalize();
    let first_hash = result.to_hex_string(bitcoin::hex::Case::Lower);
    let mut hasher_2 = Sha256::new();
    let bytes_2 = hex::decode(first_hash).expect("sadfgh");
    hasher_2.update(bytes_2);
    let final_result = hasher_2.finalize();
    final_result.to_hex_string(bitcoin::hex::Case::Lower)
}
pub fn reverse_hex_byte_order(hex_str: &str) -> String {
    hex_str
        .as_bytes()
        .chunks(2)
        .map(|pair| std::str::from_utf8(pair).unwrap())
        .collect::<Vec<_>>()
        .into_iter()
        .rev()
        .collect::<String>()
}
fn merkle_tree(leaves: Vec<String>) -> String {
    //reversing the bytes even though not needed as sample txids are taken from explorer hence are reversed in nature
    let mut layer: Vec<String> = leaves
        .iter()
        .map(|str| reverse_hex_byte_order(str))
        .collect();
    // let mut layer = leaves;
    while layer.len() > 1 {
        if layer.len() % 2 != 0 {
            layer.push(layer.last().unwrap().clone());
        }

        let mut new_layer: Vec<String> = Vec::new();
        for i in (0..layer.len()).step_by(2) {
            let combined = format!("{}{}", layer[i], layer[i + 1]);
            new_layer.push(hash_data(&combined));
        }

        layer = new_layer;
    }

    layer[0].clone()
}
pub fn create_dummy_merkle_path_proof(
    transaction_id: Txid,
    siblings: Vec<[u8; 32]>,
) -> MerklePathProof {
    let mut converted_vector: Vec<TxMerkleNode> = Vec::new();
    for sibling in 0..siblings.len() {
        converted_vector.push(TxMerkleNode::from_byte_array(siblings[sibling]));
    }
    MerklePathProof {
        transaction_hash: transaction_id,
        merkle_path: converted_vector,
    }
}
pub fn create_parents_set(parents_vec: Vec<(BeadHash, Time)>) -> HashSet<(BeadHash, Time)> {
    parents_vec.into_iter().collect()
}
pub fn create_test_bead(
    block_version: i32,
    prev_blockhash_bytes: [u8; 32],
    timestamp: u32,
    difficulty_bits: u32,
    nonce: u32,
    payout_txin_bytes: [u8; 32],
    lesser_difficulty_target: u32,
    parent_hashes: Vec<(BeadHash, Time)>,
    transactions_bytes: Vec<[u8; 32]>,
    bits: u32,
    observed_time_at_node: u32,
) -> Bead {
    let target: CompactTarget = CompactTarget::from_consensus(lesser_difficulty_target);
    let payout_transaction =
        create_dummy_transaction(payout_txin_bytes, 2, 0xFFFFFFFF, vec![], 10_000_000);
    let payout_txid = payout_transaction.compute_txid().to_string();
    let mut payout_transaction_bytes = [0u8; 32];
    let mut coinbase_transaction_bytes = [0u8; 32];
    let result = hex::decode_to_slice(
        payout_txid.to_string(),
        &mut payout_transaction_bytes as &mut [u8],
    );
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
    let coinbase_transaction = create_dummy_coinbase_transaction(2, 0xFFFFFFFF, vec![], 10_000_000);
    let result = hex::decode_to_slice(
        coinbase_transaction.compute_txid().to_string(),
        &mut coinbase_transaction_bytes,
    );
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
    let payout_tx_reference = payout_transaction.clone();
    let payout_tx_id = payout_tx_reference.compute_txid();
    let parents: HashSet<(BeadHash, Time)> = create_parents_set(parent_hashes);
    //the input param of transaction bytes will be of txid paying to the transaction used in
    //dummy transaction construction
    let mut transactions_of_bead = Vec::new();
    for transaction in transactions_bytes.iter() {
        transactions_of_bead.push(create_dummy_transaction(
            *transaction,
            2,
            0xFFFFFFFF,
            vec![],
            10_000_000,
        ));
    }

    let transaction_of_beads_reference = transactions_of_bead.clone();
    let mut beads_txs: Vec<[u8; 32]> = Vec::new();
    for bead_tx in transaction_of_beads_reference {
        let curr_txid = bead_tx.compute_txid();
        let mut curr_tx_bytes = [0u8; 32];
        let result = hex::decode_to_slice(curr_txid.to_string(), &mut curr_tx_bytes);
        match result {
            Ok(val) => {
                beads_txs.push(curr_tx_bytes);
            }
            Err(e) => {
                println!(
                    "{:?} this error occurred while decoding the corresponding bytes",
                    e
                );
            }
        }
    }
    let iter_ref = beads_txs.clone();
    let mut payout_siblings = Vec::new();
    payout_siblings.push(coinbase_transaction_bytes);
    payout_siblings.extend(iter_ref.iter());
    let mut coinbase_siblings = Vec::new();
    coinbase_siblings.push(payout_transaction_bytes);
    coinbase_siblings.extend(iter_ref.iter());

    let payout_transaction_with_merkel_path: TransactionWithMerklePath = (
        payout_tx_reference,
        create_dummy_merkle_path_proof(payout_tx_id, payout_siblings),
    );
    let coinbase_txid = coinbase_transaction.compute_txid();
    let coinbase_transaction_with_merkel_path: TransactionWithMerklePath = (
        coinbase_transaction,
        create_dummy_merkle_path_proof(coinbase_txid, coinbase_siblings),
    );

    let mut total_txs = Vec::new();

    total_txs.push(coinbase_txid.to_string());
    total_txs.push(payout_txid.to_string());

    for txs in beads_txs {
        total_txs.push(txs.to_hex_string(bitcoin::hex::Case::Lower));
    }

    let merkel_node = merkle_tree(total_txs);
    let mut merkel_node_bytes = [0u8; 32];
    let result = hex::decode_to_slice(merkel_node, &mut merkel_node_bytes);
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

    let time = Time::from_consensus(1653195600).expect("Invalid time");
    let blockheader: BlockHeader = create_block_header(
        block_version,
        prev_blockhash_bytes,
        merkel_node_bytes,
        timestamp,
        bits,
        nonce,
    );
    //bead hash value taking random 32 byte hash but same as that of the block header bytes

    let beadhash = blockheader.block_hash();
    return Bead {
        block_header: blockheader,
        bead_hash: beadhash,
        coinbase_transaction: coinbase_transaction_with_merkel_path,
        payout_update_transaction: payout_transaction_with_merkel_path,
        lesser_difficulty_target: target,
        parents: parents,
        transactions: transactions_of_bead,
        observed_time_at_node: time,
    };
}
