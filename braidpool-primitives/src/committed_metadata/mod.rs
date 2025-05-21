use crate::utils::{BeadHash, hashset_to_vec_deterministic, vec_to_hashset};
use bitcoin::CompactTarget;
use bitcoin::PublicKey;
use bitcoin::Transaction;
use bitcoin::absolute::Time;
use bitcoin::consensus::Error;
use bitcoin::consensus::encode::Decodable;
use bitcoin::consensus::encode::Encodable;
use bitcoin::io::{self, BufRead, Write};
use bitcoin::p2p::Address as P2P_Address;
use bitcoin::p2p::address::AddrV2;
use std::collections::HashSet;

#[derive(Clone, Debug, PartialEq)]
pub struct CommittedMetadata {
    pub transaction_cnt: u32,
    pub transactions: Vec<Transaction>,
    pub parents: HashSet<BeadHash>,
    pub payout_address: P2P_Address,
    pub start_timestamp: Time,
    pub comm_pub_key: PublicKey,
    //minimum possible target > which will be the weak target
    pub min_target: CompactTarget,
    //the weaker target locallay apart from mainnet target ranging between the mainnet target and
    //minimum possible target
    pub weak_target: CompactTarget,
    pub miner_ip: AddrV2,
}

impl Encodable for CommittedMetadata {
    fn consensus_encode<W: Write + ?Sized>(&self, w: &mut W) -> Result<usize, io::Error> {
        let mut len = 0;
        len += self.transaction_cnt.consensus_encode(w)?;
        len += self.transactions.consensus_encode(w)?;
        len += hashset_to_vec_deterministic(&self.parents).consensus_encode(w)?;
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
        let transaction_cnt = u32::consensus_decode(r)?;
        let transactions = Vec::<Transaction>::consensus_decode(r)?;
        let parents = vec_to_hashset(Vec::<BeadHash>::consensus_decode(r)?);
        let payout_address = P2P_Address::consensus_decode(r)?;
        let start_timestamp = Time::from_consensus(u32::consensus_decode(r).unwrap()).unwrap();
        let comm_pub_key = PublicKey::from_slice(&Vec::<u8>::consensus_decode(r).unwrap()).unwrap();
        let min_target = CompactTarget::consensus_decode(r).unwrap();
        let weak_target = CompactTarget::consensus_decode(r).unwrap();
        let miner_ip = AddrV2::consensus_decode(r)?;
        Ok(CommittedMetadata {
            transaction_cnt,
            transactions,
            parents,
            payout_address,
            start_timestamp,
            comm_pub_key,
            min_target,
            weak_target,
            miner_ip,
        })
    }
}
