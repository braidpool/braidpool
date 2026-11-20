use crate::bead::Bead;
use crate::committed_metadata::TxIdVec;
use bitcoin::consensus::encode::Encodable;
use bitcoin::hashes::Hash;
use bitcoin::io;
use bitcoin::{Transaction, Txid};

/// Size in bytes of a consensus-encoded [`Txid`].
const TXID_SIZE: usize = 32;
/// Rough size of everything in an encoded [`Bead`] other than its txid list: header,
/// length prefixes, strings, keys and the uncommitted metadata. Only used to size the
/// output buffer so it normally never reallocates.
const ENCODED_BEAD_OVERHEAD_ESTIMATE: usize = 512;

/// The part of a bead that is fixed once a block template is known.
///
/// A bead commits to the ids of every transaction in the block. For a given template
/// those ids never change: only the coinbase differs per share, because it carries the
/// miner's extranonces. Hashing every transaction and encoding the id list on each
/// `mining.submit` is therefore wasted work on the hot path, and it happens while the
/// braid write lock is held.
///
/// A `PreBead` is built once per template, when the job is constructed, and shared by
/// every share submitted against that job. At submit time the txid list is assembled
/// with [`PreBead::transaction_ids`] and the final bead bytes with
/// [`PreBead::encode`], neither of which hashes a transaction.
#[derive(Clone, Debug)]
pub struct PreBead {
    /// Ids of the template's transactions, excluding the coinbase, in block order.
    tx_ids: Box<[Txid]>,
    /// Consensus encoding of `tx_ids`, without a length prefix.
    tx_ids_encoded: Box<[u8]>,
}

impl PreBead {
    /// Builds the pre-bead from the template's transactions, **excluding the coinbase**.
    pub fn new(non_coinbase_transactions: &[Transaction]) -> Self {
        let tx_ids: Box<[Txid]> = non_coinbase_transactions
            .iter()
            .map(Transaction::compute_txid)
            .collect();
        let mut tx_ids_encoded = Vec::with_capacity(tx_ids.len() * TXID_SIZE);
        for txid in tx_ids.iter() {
            tx_ids_encoded.extend_from_slice(txid.as_byte_array());
        }
        Self {
            tx_ids,
            tx_ids_encoded: tx_ids_encoded.into_boxed_slice(),
        }
    }

    /// Number of non-coinbase transactions in the template.
    pub fn transaction_count(&self) -> usize {
        self.tx_ids.len()
    }

    /// The bead's transaction id list: the share's coinbase txid followed by the
    /// template's ids. This is a plain copy, no transaction is hashed.
    pub fn transaction_ids(&self, coinbase_txid: Txid) -> TxIdVec {
        let mut ids = Vec::with_capacity(self.tx_ids.len() + 1);
        ids.push(coinbase_txid);
        ids.extend_from_slice(&self.tx_ids);
        TxIdVec(ids)
    }

    /// Consensus-encodes `bead`, reusing the pre-encoded txid list.
    ///
    /// The output is byte-for-byte identical to [`bitcoin::consensus::serialize`] of
    /// the same bead. `bead` should carry the list returned by
    /// [`PreBead::transaction_ids`]; if its list has a different length the bead is
    /// serialized the ordinary way instead.
    pub fn encode(&self, bead: &Bead) -> Vec<u8> {
        self.try_encode(bead)
            .unwrap_or_else(|_| bitcoin::consensus::serialize(bead))
    }

    fn try_encode(&self, bead: &Bead) -> Result<Vec<u8>, io::Error> {
        let ids = &bead.committed_metadata.transaction_ids.0;
        let Some((coinbase_txid, template_ids)) = ids.split_first() else {
            return Ok(bitcoin::consensus::serialize(bead));
        };
        if template_ids.len() != self.tx_ids.len() {
            return Ok(bitcoin::consensus::serialize(bead));
        }
        debug_assert_eq!(template_ids, &*self.tx_ids);

        let mut out = Vec::with_capacity(ids.len() * TXID_SIZE + ENCODED_BEAD_OVERHEAD_ESTIMATE);
        bead.block_header.consensus_encode(&mut out)?;
        // `committed_metadata` starts with the txid list: a u64 length, then the ids.
        (ids.len() as u64).consensus_encode(&mut out)?;
        coinbase_txid.consensus_encode(&mut out)?;
        out.extend_from_slice(&self.tx_ids_encoded);
        bead.committed_metadata
            .consensus_encode_after_transaction_ids(&mut out)?;
        bead.uncommitted_metadata.consensus_encode(&mut out)?;
        Ok(out)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use bitcoin::absolute::LockTime;
    use bitcoin::transaction::Version;
    use bitcoin::{Amount, OutPoint, ScriptBuf, Sequence, TxIn, TxOut, Witness};

    fn tx(seed: u32) -> Transaction {
        Transaction {
            version: Version::TWO,
            lock_time: LockTime::from_consensus(seed),
            input: vec![TxIn {
                previous_output: OutPoint::null(),
                script_sig: ScriptBuf::new(),
                sequence: Sequence::MAX,
                witness: Witness::new(),
            }],
            output: vec![TxOut {
                value: Amount::from_sat(1_000 + seed as u64),
                script_pubkey: ScriptBuf::new(),
            }],
        }
    }

    fn txs(n: u32) -> Vec<Transaction> {
        (0..n).map(tx).collect()
    }

    fn bead_with(ids: TxIdVec) -> Bead {
        let mut bead = Bead::default();
        bead.committed_metadata.transaction_ids = ids;
        bead.committed_metadata.payout_address = "bc1qpayout".to_string();
        bead.committed_metadata.miner_ip = "10.1.2.3:3333".to_string();
        bead.block_header.nonce = 0xdead_beef;
        bead.uncommitted_metadata.extra_nonce_1 = 7;
        bead.uncommitted_metadata.extra_nonce_2 = 42;
        bead
    }

    #[test]
    fn transaction_ids_are_coinbase_then_template_in_order() {
        let template = txs(5);
        let pre = PreBead::new(&template);
        let coinbase_txid = tx(999).compute_txid();

        let ids = pre.transaction_ids(coinbase_txid).0;

        let mut expected = vec![coinbase_txid];
        expected.extend(template.iter().map(Transaction::compute_txid));
        assert_eq!(ids, expected);
        assert_eq!(pre.transaction_count(), 5);
    }

    #[test]
    fn encode_matches_consensus_serialize() {
        for count in [0, 1, 2, 57, 1000] {
            let pre = PreBead::new(&txs(count));
            let bead = bead_with(pre.transaction_ids(tx(10_000).compute_txid()));

            assert_eq!(
                pre.encode(&bead),
                bitcoin::consensus::serialize(&bead),
                "encoding differs with {count} template transactions"
            );
        }
    }

    #[test]
    fn encoded_bead_round_trips() {
        let pre = PreBead::new(&txs(20));
        let bead = bead_with(pre.transaction_ids(tx(10_000).compute_txid()));

        let decoded: Bead = bitcoin::consensus::deserialize(&pre.encode(&bead)).unwrap();

        assert_eq!(decoded, bead);
    }

    #[test]
    fn encode_reflects_per_share_fields() {
        let pre = PreBead::new(&txs(10));
        let mut bead = bead_with(pre.transaction_ids(tx(10_000).compute_txid()));
        bead.committed_metadata.parents = vec![bead_hash(1), bead_hash(2)];

        assert_eq!(pre.encode(&bead), bitcoin::consensus::serialize(&bead));
    }

    #[test]
    fn encode_falls_back_when_txid_list_does_not_match() {
        let pre = PreBead::new(&txs(10));
        // A list built for a different template has a different length.
        let other = PreBead::new(&txs(3));
        let bead = bead_with(other.transaction_ids(tx(10_000).compute_txid()));

        assert_eq!(pre.encode(&bead), bitcoin::consensus::serialize(&bead));
    }

    /// Distinct, deterministic bead hashes for the parents field.
    fn bead_hash(seed: u8) -> crate::utils::BeadHash {
        crate::utils::BeadHash::from_byte_array([seed; 32])
    }
}
