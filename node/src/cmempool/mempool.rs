use std::collections::{HashMap, HashSet};

use bitcoin::Txid;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MempoolTx {
    pub txid: Txid,
    pub raw_tx: Vec<u8>,
    pub fee_sat: u64,
    pub weight: u64,
    pub fee_rate: f64,
    pub first_seen_in_bead: [u8; 32],
}

impl MempoolTx {
    pub fn new(txid: Txid, raw_tx: Vec<u8>, fee_sat: u64, weight: u64, first_seen_in_bead: [u8; 32]) -> Self {
        let fee_rate = if weight == 0 { 0.0 } else { fee_sat as f64 / weight as f64 };
        MempoolTx { txid, raw_tx, fee_sat, weight, fee_rate, first_seen_in_bead }
    }
}

#[derive(Debug, Clone, Default)]
pub struct BeadMempool {
    txs: HashMap<Txid, MempoolTx>,
}

impl BeadMempool {
    pub fn new() -> Self {
        BeadMempool { txs: HashMap::new() }
    }

    pub fn insert(&mut self, tx: MempoolTx) {
        self.txs.insert(tx.txid, tx);
    }

    pub fn remove(&mut self, txid: &Txid) {
        self.txs.remove(txid);
    }

    pub fn contains(&self, txid: &Txid) -> bool {
        self.txs.contains_key(txid)
    }

    pub fn len(&self) -> usize {
        self.txs.len()
    }

    pub fn is_empty(&self) -> bool {
        self.txs.is_empty()
    }

    pub fn iter(&self) -> impl Iterator<Item = &MempoolTx> {
        self.txs.values()
    }

    pub fn total_weight(&self) -> u64 {
        self.txs.values().map(|tx| tx.weight).sum()
    }

    pub fn merge(
        parent_mempools: &[&BeadMempool],
        confirmed_txids: &HashSet<Txid>,
        hwp_bead_hashes: &HashSet<[u8; 32]>,
    ) -> BeadMempool {
        let mut merged: HashMap<Txid, MempoolTx> = HashMap::new();
        for mp in parent_mempools {
            for tx in mp.txs.values() {
                merged.entry(tx.txid).or_insert_with(|| tx.clone());
            }
        }
        for txid in confirmed_txids {
            merged.remove(txid);
        }
        BeadMempool { txs: merged }
    }

    pub fn txs_sorted(&self, hwp_bead_hashes: &HashSet<[u8; 32]>) -> Vec<&MempoolTx> {
        let mut sorted: Vec<&MempoolTx> = self.txs.values().collect();
        sorted.sort_by(|a, b| {
            let a_on_hwp = hwp_bead_hashes.contains(&a.first_seen_in_bead);
            let b_on_hwp = hwp_bead_hashes.contains(&b.first_seen_in_bead);
            match (a_on_hwp, b_on_hwp) {
                (true, false) => std::cmp::Ordering::Less,
                (false, true) => std::cmp::Ordering::Greater,
                _ => b.fee_rate.partial_cmp(&a.fee_rate).unwrap_or(std::cmp::Ordering::Equal),
            }
        });
        sorted
    }

    pub fn reserved_weight_for_bead_txs(bead_tx_weights: impl Iterator<Item = u64>) -> u64 {
        bead_tx_weights.sum()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::str::FromStr;

    fn dummy_txid(n: u8) -> Txid {
        let mut bytes = [0u8; 32];
        bytes[0] = n;
        Txid::from_str(&format!("{:064x}", n)).unwrap_or_else(|_| {
            use bitcoin::hashes::Hash;
            Txid::from_raw_hash(bitcoin::hashes::sha256d::Hash::from_byte_array(bytes))
        })
    }

    fn make_tx(n: u8, fee_sat: u64, weight: u64) -> MempoolTx {
        MempoolTx::new(dummy_txid(n), vec![n; 100], fee_sat, weight, [n; 32])
    }

    #[test]
    fn test_insert_and_len() {
        let mut mp = BeadMempool::new();
        assert_eq!(mp.len(), 0);
        mp.insert(make_tx(1, 1000, 400));
        assert_eq!(mp.len(), 1);
        mp.insert(make_tx(2, 500, 200));
        assert_eq!(mp.len(), 2);
    }

    #[test]
    fn test_remove() {
        let mut mp = BeadMempool::new();
        let tx = make_tx(1, 1000, 400);
        let txid = tx.txid;
        mp.insert(tx);
        assert!(mp.contains(&txid));
        mp.remove(&txid);
        assert!(!mp.contains(&txid));
    }

    #[test]
    fn test_total_weight() {
        let mut mp = BeadMempool::new();
        mp.insert(make_tx(1, 1000, 400));
        mp.insert(make_tx(2, 500, 200));
        assert_eq!(mp.total_weight(), 600);
    }

    #[test]
    fn test_merge_deduplicates() {
        let mut mp1 = BeadMempool::new();
        let mut mp2 = BeadMempool::new();
        mp1.insert(make_tx(1, 1000, 400));
        mp1.insert(make_tx(2, 500, 200));
        mp2.insert(make_tx(1, 1000, 400));
        mp2.insert(make_tx(3, 800, 300));

        let merged = BeadMempool::merge(&[&mp1, &mp2], &HashSet::new(), &HashSet::new());
        assert_eq!(merged.len(), 3);
    }

    #[test]
    fn test_merge_removes_confirmed() {
        let mut mp1 = BeadMempool::new();
        mp1.insert(make_tx(1, 1000, 400));
        mp1.insert(make_tx(2, 500, 200));

        let mut confirmed = HashSet::new();
        confirmed.insert(dummy_txid(1));

        let merged = BeadMempool::merge(&[&mp1], &confirmed, &HashSet::new());
        assert_eq!(merged.len(), 1);
        assert!(!merged.contains(&dummy_txid(1)));
        assert!(merged.contains(&dummy_txid(2)));
    }

    #[test]
    fn test_txs_sorted_hwp_first() {
        let mut mp = BeadMempool::new();
        mp.insert(make_tx(1, 1000, 400));
        mp.insert(make_tx(2, 100, 200));

        let hwp: HashSet<[u8; 32]> = std::iter::once([2u8; 32]).collect();
        let sorted = mp.txs_sorted(&hwp);
        assert_eq!(sorted[0].txid, dummy_txid(2));
        assert_eq!(sorted[1].txid, dummy_txid(1));
    }

    #[test]
    fn test_txs_sorted_by_fee_rate_within_group() {
        let mut mp = BeadMempool::new();
        mp.insert(MempoolTx::new(dummy_txid(1), vec![1; 100], 1000, 200, [1; 32]));
        mp.insert(MempoolTx::new(dummy_txid(2), vec![2; 100], 400, 400, [2; 32]));

        let sorted = mp.txs_sorted(&HashSet::new());
        assert_eq!(sorted[0].txid, dummy_txid(1));
        assert_eq!(sorted[1].txid, dummy_txid(2));
    }

    #[test]
    fn test_reserved_weight_for_bead_txs() {
        let weights = vec![400u64, 200, 300];
        assert_eq!(BeadMempool::reserved_weight_for_bead_txs(weights.into_iter()), 900);
    }

    #[test]
    fn test_fee_rate_computation() {
        let tx = make_tx(1, 1000, 400);
        assert!((tx.fee_rate - 2.5).abs() < 1e-9);
    }

    #[test]
    fn test_fee_rate_zero_weight() {
        let tx = MempoolTx::new(dummy_txid(1), vec![], 100, 0, [0; 32]);
        assert_eq!(tx.fee_rate, 0.0);
    }
}
