use crate::utils::BeadHash;
use bitcoin::absolute::Time;
use bitcoin::consensus::encode::Decodable;
use bitcoin::consensus::encode::Encodable;
use bitcoin::consensus::encode::Error;
use bitcoin::io::{self, Read, Write};
use bitcoin::CompactTarget;
use bitcoin::PublicKey;
use bitcoin::Transaction;
use bitcoin::Txid;
use serde::Deserialize;
use serde::Serialize;
use std::collections::HashSet;
use std::str::FromStr;

/// Most transactions a bead may propose for the committed mempool.
pub const MAX_TO_BE_ADDED_TXS: usize = 5;

/// Most non-coinbase transactions a block template can hold: the block weight
/// limit divided by the weight of the smallest possible transaction.
pub const MAX_COMMITTED_TXS: usize = 4_000_000 / 240;

/// Largest allocation a decoder makes before it has read any element, so a
/// declared length alone cannot reserve memory.
const MAX_DECODE_PREALLOCATION: usize = 1024;

/// Builds the decode error for malformed committed metadata.
fn invalid_data(reason: &'static str) -> Error {
    Error::from(io::Error::new(io::ErrorKind::InvalidData, reason))
}

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq, Default)]
pub struct TimeVec(pub Vec<Time>);

impl Encodable for TimeVec {
    fn consensus_encode<W: Write + ?Sized>(&self, w: &mut W) -> Result<usize, io::Error> {
        let mut len = 0;
        len += (self.0.len() as u64).consensus_encode(w)?;
        for time in &self.0 {
            len += time.to_consensus_u32().consensus_encode(w)?;
        }
        Ok(len)
    }
}

impl Decodable for TimeVec {
    fn consensus_decode<R: Read + ?Sized>(r: &mut R) -> Result<Self, Error> {
        let len = u64::consensus_decode(r)?;
        let mut vec = Vec::with_capacity((len as usize).min(MAX_DECODE_PREALLOCATION));
        for _ in 0..len {
            let time_u32 = u32::consensus_decode(r)?;
            let time = Time::from_consensus(time_u32)
                .map_err(|_| invalid_data("invalid parent bead timestamp in TimeVec"))?;
            vec.push(time);
        }
        Ok(TimeVec(vec))
    }
}
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq, Default)]
pub struct TxIdVec(pub Vec<Txid>);
impl Encodable for TxIdVec {
    fn consensus_encode<W: Write + ?Sized>(&self, w: &mut W) -> Result<usize, io::Error> {
        let mut len = 0;
        len += (self.0.len() as u64).consensus_encode(w)?;
        for txid in &self.0 {
            len += txid.consensus_encode(w)?;
        }
        Ok(len)
    }
}
impl TxIdVec {
    /// Decodes a txid list holding at most `max_len` distinct entries.
    pub fn consensus_decode_bounded<R: Read + ?Sized>(
        r: &mut R,
        max_len: usize,
    ) -> Result<Self, Error> {
        let len = u64::consensus_decode(r)?;
        if len > max_len as u64 {
            return Err(invalid_data("txid list longer than its limit"));
        }
        let len = len as usize;
        let mut vec = Vec::with_capacity(len.min(MAX_DECODE_PREALLOCATION));
        let mut seen = HashSet::with_capacity(len.min(MAX_DECODE_PREALLOCATION));
        for _ in 0..len {
            let txid = Txid::consensus_decode(r)?;
            if !seen.insert(txid) {
                return Err(invalid_data("duplicate txid in txid list"));
            }
            vec.push(txid);
        }
        Ok(Self(vec))
    }
}
impl Decodable for TxIdVec {
    fn consensus_decode<R: Read + ?Sized>(r: &mut R) -> Result<Self, Error> {
        Self::consensus_decode_bounded(r, MAX_COMMITTED_TXS)
    }
}

/// Returns the stand-in coinbase used where no template coinbase exists: one
/// null input and no outputs.
pub fn placeholder_coinbase() -> Transaction {
    Transaction {
        version: bitcoin::transaction::Version::TWO,
        lock_time: bitcoin::absolute::LockTime::ZERO,
        input: vec![bitcoin::TxIn::default()],
        output: Vec::new(),
    }
}

//Changing the existing atrributes type mapping for inherit implementation of serializable and
//deserializable trait
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct CommittedMetadata {
    /// The coinbase transaction this bead was mined with.
    pub coinbase_transaction: Transaction,
    /// Txids of the template's transactions, coinbase excluded, in template
    /// order. This is the committed-mempool state the bead was mined on.
    pub committed_txs: TxIdVec,
    /// Txids this bead proposes for the committed mempool. They are not part
    /// of this bead's own block and count only for its descendants.
    pub to_be_added: TxIdVec,
    pub parents: Vec<BeadHash>,
    pub parent_bead_timestamps: TimeVec,
    pub payout_address: String,
    pub start_timestamp: Time,
    pub comm_pub_key: PublicKey,
    //minimum possible target > which will be the weak target
    pub min_target: CompactTarget,
    //the weaker target locally apart from mainnet target ranging between the mainnet target and
    //minimum possible target
    pub weak_target: CompactTarget,
    pub miner_ip: String,
    /// Total transaction fees, in satoshis, in the block template this bead
    /// was mined on.
    #[serde(default)]
    pub fee_total_sats: u64,
}
impl Default for CommittedMetadata {
    fn default() -> Self {
        Self {
            coinbase_transaction: placeholder_coinbase(),
            committed_txs: TxIdVec(Vec::new()),
            to_be_added: TxIdVec(Vec::new()),
            parents: Vec::new(),
            parent_bead_timestamps: TimeVec(Vec::new()),
            payout_address: "bc1".to_string(),
            start_timestamp: Time::MIN,
            comm_pub_key: PublicKey::from_str(
                "020202020202020202020202020202020202020202020202020202020202020202",
            )
            .unwrap(),
            min_target: CompactTarget::from_consensus(486604799),
            weak_target: CompactTarget::from_consensus(486604799),
            miner_ip: "127.0.0.1".to_string(),
            fee_total_sats: 0,
        }
    }
}
impl Encodable for CommittedMetadata {
    fn consensus_encode<W: Write + ?Sized>(&self, w: &mut W) -> Result<usize, io::Error> {
        let mut len = 0;
        len += self.coinbase_transaction.consensus_encode(w)?;
        len += self.committed_txs.consensus_encode(w)?;
        len += self.to_be_added.consensus_encode(w)?;
        len += self.parents.consensus_encode(w)?;
        len += self.parent_bead_timestamps.consensus_encode(w)?;
        len += self.payout_address.consensus_encode(w)?;
        len += self
            .start_timestamp
            .to_consensus_u32()
            .consensus_encode(w)?;
        let pubkey_bytes = self.comm_pub_key.to_bytes();
        len += pubkey_bytes.consensus_encode(w)?;
        len += self.min_target.consensus_encode(w)?;
        len += self.weak_target.consensus_encode(w)?;
        len += self.miner_ip.consensus_encode(w)?;
        len += self.fee_total_sats.consensus_encode(w)?;
        Ok(len)
    }
}

impl Decodable for CommittedMetadata {
    fn consensus_decode<R: Read + ?Sized>(r: &mut R) -> Result<Self, Error> {
        let coinbase_transaction = Transaction::consensus_decode(r)?;
        let committed_txs = TxIdVec::consensus_decode_bounded(r, MAX_COMMITTED_TXS)?;
        let to_be_added = TxIdVec::consensus_decode_bounded(r, MAX_TO_BE_ADDED_TXS)?;
        let parents = Vec::<BeadHash>::consensus_decode(r)?;
        let parent_bead_timestamps = TimeVec::consensus_decode(r)?;
        let payout_address = String::consensus_decode(r)?;
        let start_timestamp = Time::from_consensus(u32::consensus_decode(r)?).map_err(|_| {
            Error::from(io::Error::new(
                io::ErrorKind::InvalidData,
                "invalid start_timestamp in CommittedMetadata",
            ))
        })?;
        let comm_pub_key =
            PublicKey::from_slice(&Vec::<u8>::consensus_decode(r)?).map_err(|_| {
                Error::from(io::Error::new(
                    io::ErrorKind::InvalidData,
                    "invalid comm_pub_key in CommittedMetadata",
                ))
            })?;
        let min_target = CompactTarget::consensus_decode(r)?;
        let weak_target = CompactTarget::consensus_decode(r)?;
        let miner_ip = String::consensus_decode(r)?;
        let fee_total_sats = u64::consensus_decode(r)?;
        // A template cannot carry more fees than can ever exist.
        if fee_total_sats > bitcoin::Amount::MAX_MONEY.to_sat() {
            return Err(Error::from(io::Error::new(
                io::ErrorKind::InvalidData,
                "fee_total_sats in CommittedMetadata exceeds MAX_MONEY",
            )));
        }
        Ok(CommittedMetadata {
            coinbase_transaction,
            committed_txs,
            to_be_added,
            parents,
            parent_bead_timestamps,
            payout_address,
            start_timestamp,
            comm_pub_key,
            min_target,
            weak_target,
            miner_ip,
            fee_total_sats,
        })
    }
}

#[cfg(test)]
mod tests;
