use std::collections::{HashMap, HashSet};

use bitcoin::{OutPoint, Transaction, Txid};
use sha2::{Digest, Sha256};

fn make_prng_seed(parent_block_hash: &[u8; 32], extranonce: &[u8]) -> u64 {
    let mut hasher = Sha256::new();
    hasher.update(parent_block_hash);
    hasher.update(extranonce);
    let digest = hasher.finalize();

    let mut seed_bytes = [0u8; 8];
    seed_bytes.copy_from_slice(&digest[..8]);
    let seed = u64::from_le_bytes(seed_bytes);
    if seed == 0 { 1 } else { seed }
}

fn xorshift64(state: &mut u64) -> u64 {
    let mut x = *state;
    x ^= x << 13;
    x ^= x >> 7;
    x ^= x << 17;
    *state = x;
    x
}

fn shuffle<T>(vec: &mut Vec<T>, rng: &mut u64) {
    let n = vec.len();
    for i in (1..n).rev() {
        let j = (xorshift64(rng) as usize) % (i + 1);
        vec.swap(i, j);
    }
}

fn txid_to_index(txs: &[Transaction]) -> HashMap<Txid, usize> {
    txs.iter()
        .enumerate()
        .map(|(i, tx)| (tx.compute_txid(), i))
        .collect()
}

fn compute_intra_block_deps(txs: &[Transaction], index_map: &HashMap<Txid, usize>) -> Vec<HashSet<usize>> {
    let mut deps = vec![HashSet::new(); txs.len()];
    for (i, tx) in txs.iter().enumerate() {
        for input in &tx.input {
            let OutPoint { txid, .. } = input.previous_output;
            if let Some(&dep_idx) = index_map.get(&txid) {
                deps[i].insert(dep_idx);
            }
        }
    }
    deps
}

fn randomised_topological_sort(txs: &[Transaction], deps: &[HashSet<usize>], rng: &mut u64) -> Vec<usize> {
    let n = txs.len();
    if n == 0 {
        return vec![];
    }

    let mut in_degree: Vec<usize> = deps.iter().map(|d| d.len()).collect();

    let mut dependents: Vec<Vec<usize>> = vec![vec![]; n];
    for (i, dep_set) in deps.iter().enumerate() {
        for &dep in dep_set {
            dependents[dep].push(i);
        }
    }

    let mut result = Vec::with_capacity(n);
    result.push(0);
    for &dep in &dependents[0] {
        in_degree[dep] = in_degree[dep].saturating_sub(1);
    }

    let mut ready: Vec<usize> = (1..n).filter(|&i| in_degree[i] == 0).collect();

    while !ready.is_empty() {
        shuffle(&mut ready, rng);
        let batch: Vec<usize> = ready.drain(..).collect();
        for &idx in &batch {
            result.push(idx);
            for &dep in &dependents[idx] {
                in_degree[dep] = in_degree[dep].saturating_sub(1);
                if in_degree[dep] == 0 {
                    ready.push(dep);
                }
            }
        }
    }

    result
}

pub fn randomize_block_template(
    transactions: Vec<Transaction>,
    parent_block_hash: &[u8; 32],
    extranonce: &[u8],
) -> Vec<Transaction> {
    if transactions.len() <= 1 {
        return transactions;
    }

    let index_map = txid_to_index(&transactions);
    let deps = compute_intra_block_deps(&transactions, &index_map);

    let mut rng = make_prng_seed(parent_block_hash, extranonce);
    let order = randomised_topological_sort(&transactions, &deps, &mut rng);

    order.into_iter().map(|i| transactions[i].clone()).collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use bitcoin::{absolute::LockTime, transaction::Version, Transaction, TxIn, TxOut};

    fn coinbase_tx() -> Transaction {
        Transaction {
            version: Version::ONE,
            lock_time: LockTime::ZERO,
            input: vec![TxIn::default()],
            output: vec![],
        }
    }

    fn simple_tx(prevout_txid: Option<Txid>) -> Transaction {
        let input = match prevout_txid {
            Some(txid) => TxIn {
                previous_output: OutPoint { txid, vout: 0 },
                ..Default::default()
            },
            None => TxIn::default(),
        };
        Transaction {
            version: Version::ONE,
            lock_time: LockTime::ZERO,
            input: vec![input],
            output: vec![TxOut {
                value: bitcoin::Amount::from_sat(1000),
                script_pubkey: bitcoin::ScriptBuf::new(),
            }],
        }
    }

    #[test]
    fn test_prng_seed_nonzero() {
        let seed = make_prng_seed(&[0u8; 32], &[0u8; 4]);
        assert_ne!(seed, 0);
    }

    #[test]
    fn test_prng_seed_deterministic() {
        let s1 = make_prng_seed(&[1u8; 32], &[2u8; 4]);
        let s2 = make_prng_seed(&[1u8; 32], &[2u8; 4]);
        assert_eq!(s1, s2);
    }

    #[test]
    fn test_prng_seed_differs_by_extranonce() {
        let s1 = make_prng_seed(&[0u8; 32], &[0u8]);
        let s2 = make_prng_seed(&[0u8; 32], &[1u8]);
        assert_ne!(s1, s2);
    }

    #[test]
    fn test_xorshift64_changes_state() {
        let mut state = 42u64;
        let v1 = xorshift64(&mut state);
        let v2 = xorshift64(&mut state);
        assert_ne!(v1, v2);
    }

    #[test]
    fn test_shuffle_preserves_elements() {
        let mut v = vec![1, 2, 3, 4, 5];
        let original: HashSet<i32> = v.iter().cloned().collect();
        let mut rng = 123u64;
        shuffle(&mut v, &mut rng);
        let shuffled: HashSet<i32> = v.iter().cloned().collect();
        assert_eq!(original, shuffled);
    }

    #[test]
    fn test_empty_template_unchanged() {
        let result = randomize_block_template(vec![], &[0u8; 32], &[]);
        assert!(result.is_empty());
    }

    #[test]
    fn test_coinbase_only_unchanged() {
        let txs = vec![coinbase_tx()];
        let result = randomize_block_template(txs.clone(), &[0u8; 32], &[]);
        assert_eq!(result.len(), 1);
    }

    #[test]
    fn test_coinbase_always_first() {
        let coinbase = coinbase_tx();
        let tx_a = simple_tx(None);
        let tx_a_id = tx_a.compute_txid();
        let tx_b = simple_tx(Some(tx_a_id));

        let txs = vec![coinbase, tx_a, tx_b];
        let result = randomize_block_template(txs, &[0u8; 32], &[]);
        assert_eq!(result[0].input[0].previous_output, OutPoint::default());
    }

    #[test]
    fn test_dependency_order_respected() {
        let coinbase = coinbase_tx();
        let tx_a = simple_tx(None);
        let tx_a_id = tx_a.compute_txid();
        let tx_b = simple_tx(Some(tx_a_id));
        let tx_b_id = tx_b.compute_txid();

        let txs = vec![coinbase, tx_a, tx_b];
        let result = randomize_block_template(txs, &[42u8; 32], &[1, 2, 3]);

        let pos_a = result.iter().position(|tx| tx.compute_txid() == tx_a_id).unwrap();
        let pos_b = result.iter().position(|tx| tx.compute_txid() == tx_b_id).unwrap();
        assert!(pos_a < pos_b);
    }

    #[test]
    fn test_deterministic_given_same_seed() {
        let coinbase = coinbase_tx();
        let txs = vec![coinbase, simple_tx(None), simple_tx(None), simple_tx(None)];
        let r1 = randomize_block_template(txs.clone(), &[7u8; 32], &[0, 0, 0, 1]);
        let r2 = randomize_block_template(txs, &[7u8; 32], &[0, 0, 0, 1]);

        let ids1: Vec<_> = r1.iter().map(|t| t.compute_txid()).collect();
        let ids2: Vec<_> = r2.iter().map(|t| t.compute_txid()).collect();
        assert_eq!(ids1, ids2);
    }

    #[test]
    fn test_different_extranonce_different_order() {
        let coinbase = coinbase_tx();
        let indep: Vec<Transaction> = (0..8).map(|_| simple_tx(None)).collect();
        let mut txs = vec![coinbase];
        txs.extend(indep);

        let r1 = randomize_block_template(txs.clone(), &[0u8; 32], &[1]);
        let r2 = randomize_block_template(txs, &[0u8; 32], &[2]);

        let ids1: Vec<_> = r1.iter().skip(1).map(|t| t.compute_txid()).collect();
        let ids2: Vec<_> = r2.iter().skip(1).map(|t| t.compute_txid()).collect();
        assert_ne!(ids1, ids2);
    }
}
