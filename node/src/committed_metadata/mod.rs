use crate::utils::{hashset_to_vec_deterministic, vec_to_hashset, BeadHash};
use bitcoin::absolute::Time;
use bitcoin::consensus::encode::Decodable;
use bitcoin::consensus::encode::Encodable;
use bitcoin::consensus::Error;
use bitcoin::io::{self, BufRead, Write};
use bitcoin::CompactTarget;
use bitcoin::PublicKey;
use bitcoin::Transaction;
use serde::Deserialize;
use serde::Serialize;
use std::collections::HashSet;

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq, Default)]
pub struct TimeVec(pub Vec<Time>);

impl Encodable for TimeVec {
    fn consensus_encode<W: Write + ?Sized>(&self, w: &mut W) -> Result<usize, io::Error> {
        let mut len = 0;
        // Encode the length for deterministic encoding
        len += (self.0.len() as u64).consensus_encode(w)?;
        for time in &self.0 {
            len += time.to_consensus_u32().consensus_encode(w)?;
        }
        Ok(len)
    }
}

impl Decodable for TimeVec {
    fn consensus_decode<R: BufRead + ?Sized>(r: &mut R) -> Result<Self, Error> {
        let len = u64::consensus_decode(r)?;
        let mut vec = Vec::with_capacity(len as usize);
        for _ in 0..len {
            let time_u32 = u32::consensus_decode(r)?;
            let time = Time::from_consensus(time_u32).unwrap();
            vec.push(time);
        }
        Ok(TimeVec(vec))
    }
}
//Changing the existing atrributes type mapping for inherit implementation of serializable and
//deserializable trait
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct CommittedMetadata {
    pub transactions: Vec<Transaction>,
    pub parents: HashSet<BeadHash>,
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
}

impl Encodable for CommittedMetadata {
    fn consensus_encode<W: Write + ?Sized>(&self, w: &mut W) -> Result<usize, io::Error> {
        let mut len = 0;
        len += self.transactions.consensus_encode(w)?;
        len += hashset_to_vec_deterministic(&self.parents).consensus_encode(w)?;
        len += self.parent_bead_timestamps.consensus_encode(w)?;
        len += self.payout_address.consensus_encode(w)?;
        len += self
            .start_timestamp
            .to_consensus_u32()
            .consensus_encode(w)?;
        let pubkey_bytes = self.comm_pub_key.to_vec();
        len += pubkey_bytes.consensus_encode(w)?;
        len += self.min_target.consensus_encode(w)?;
        len += self.weak_target.consensus_encode(w)?;
        len += self.miner_ip.consensus_encode(w)?;
        Ok(len)
    }
}

impl Decodable for CommittedMetadata {
    fn consensus_decode<R: BufRead + ?Sized>(r: &mut R) -> Result<Self, Error> {
        let transactions = Vec::<Transaction>::consensus_decode(r)?;
        let parents = vec_to_hashset(Vec::<BeadHash>::consensus_decode(r)?);
        let parent_bead_timestamps = TimeVec::consensus_decode(r)?;
        let payout_address = String::consensus_decode(r)?;
        let start_timestamp = Time::from_consensus(u32::consensus_decode(r).unwrap()).unwrap();
        let comm_pub_key = PublicKey::from_slice(&Vec::<u8>::consensus_decode(r).unwrap()).unwrap();
        let min_target = CompactTarget::consensus_decode(r).unwrap();
        let weak_target = CompactTarget::consensus_decode(r).unwrap();
        let miner_ip = String::consensus_decode(r)?;
        Ok(CommittedMetadata {
            transactions,
            parents,
            parent_bead_timestamps,
            payout_address,
            start_timestamp,
            comm_pub_key,
            min_target,
            weak_target,
            miner_ip,
        })
    }
}
