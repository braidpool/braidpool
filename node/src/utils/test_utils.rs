#[cfg(test)]
use super::BeadHash;
#[cfg(test)]
use crate::bead::Bead;
#[cfg(test)]
use crate::committed_metadata::CommittedMetadata;
#[cfg(test)]
pub use crate::committed_metadata::TimeVec;
#[cfg(test)]
use crate::uncommitted_metadata::UnCommittedMetadata;
#[cfg(test)]
pub use bitcoin::ecdsa::Signature;
#[cfg(test)]
use bitcoin::p2p::Address as P2P_Address;
#[cfg(test)]
use bitcoin::BlockHeader;
#[cfg(test)]
pub use bitcoin::{absolute::Time, p2p::address::AddrV2, PublicKey, Transaction};
#[cfg(test)]
pub mod test_utility_functions {
    use std::collections::HashSet;

    use bitcoin::CompactTarget;

    pub use super::*;
    pub struct TestUnCommittedMetadataBuilder {
        extra_nonce: i32,
        broadcast_timestamp: Option<Time>,
        signature: Option<Signature>,
    }

    #[cfg(test)]
    impl TestUnCommittedMetadataBuilder {
        pub fn new() -> Self {
            Self {
                extra_nonce: 0,
                broadcast_timestamp: None,
                signature: None,
            }
        }

        pub fn extra_nonce(mut self, nonce: i32) -> Self {
            self.extra_nonce = nonce;
            self
        }

        pub fn broadcast_timestamp(mut self, time: Time) -> Self {
            self.broadcast_timestamp = Some(time);
            self
        }

        pub fn signature(mut self, sig: Signature) -> Self {
            self.signature = Some(sig);
            self
        }

        pub fn build(self) -> UnCommittedMetadata {
            UnCommittedMetadata {
                extra_nonce: self.extra_nonce,
                broadcast_timestamp: self
                    .broadcast_timestamp
                    .expect("broadcast_timestamp is required"),
                signature: self.signature.expect("signature is required"),
            }
        }
    }
    #[cfg(test)]
    pub struct TestCommittedMetadataBuilder {
        transactions: Vec<Transaction>,
        parents: std::collections::HashSet<BeadHash>,
        parent_bead_timestamps: Option<TimeVec>,
        payout_address: Option<String>,
        start_timestamp: Option<Time>,
        comm_pub_key: Option<PublicKey>,
        min_target: Option<CompactTarget>,
        weak_target: Option<CompactTarget>,
        miner_ip: Option<String>,
    }

    #[cfg(test)]
    impl TestCommittedMetadataBuilder {
        pub fn new() -> Self {
            Self {
                transactions: Vec::new(),
                parents: HashSet::new(),
                parent_bead_timestamps: None,
                payout_address: None,
                start_timestamp: None,
                comm_pub_key: None,
                min_target: None,
                weak_target: None,
                miner_ip: None,
            }
        }

        pub fn transactions(mut self, txs: Vec<Transaction>) -> Self {
            self.transactions = txs;
            self
        }

        pub fn parents(mut self, parents: HashSet<BeadHash>) -> Self {
            self.parents = parents;
            self
        }

        pub fn parent_bead_timestamps(mut self, times: TimeVec) -> Self {
            self.parent_bead_timestamps = Some(times);
            self
        }

        pub fn payout_address(mut self, address: String) -> Self {
            self.payout_address = Some(address);
            self
        }

        pub fn start_timestamp(mut self, time: Time) -> Self {
            self.start_timestamp = Some(time);
            self
        }

        pub fn comm_pub_key(mut self, key: PublicKey) -> Self {
            self.comm_pub_key = Some(key);
            self
        }

        pub fn miner_ip(mut self, ip: String) -> Self {
            self.miner_ip = Some(ip);
            self
        }
        pub fn min_target(mut self, min_target: CompactTarget) -> Self {
            self.min_target = Some(min_target);
            self
        }
        pub fn weak_target(mut self, weak_target: CompactTarget) -> Self {
            self.weak_target = Some(weak_target);
            self
        }
        pub fn build(self) -> CommittedMetadata {
            CommittedMetadata {
                transactions: self.transactions,
                parents: self.parents,
                parent_bead_timestamps: self
                    .parent_bead_timestamps
                    .expect("parent_bead_timestamps is required"),
                payout_address: self.payout_address.expect("payout_address is required"),
                start_timestamp: self
                    .start_timestamp
                    .expect("observed_time_at_node is required"),
                comm_pub_key: self.comm_pub_key.expect("comm_pub_key is required"),
                min_target: self.min_target.expect("min_target is required"),
                weak_target: self.weak_target.expect("weak_target is required"),
                miner_ip: self.miner_ip.expect("miner_ip is required"),
            }
        }
    }
    #[cfg(test)]
    pub struct TestBeadBuilder {
        block_header: Option<BlockHeader>,
        committed_metadata: Option<CommittedMetadata>,
        uncommitted_metadata: Option<UnCommittedMetadata>,
    }

    #[cfg(test)]
    impl TestBeadBuilder {
        pub fn new() -> Self {
            Self {
                block_header: None,
                committed_metadata: None,
                uncommitted_metadata: None,
            }
        }

        pub fn block_header(mut self, block_header: BlockHeader) -> Self {
            self.block_header = Some(block_header);
            self
        }

        pub fn committed_metadata(mut self, committed_metadata: CommittedMetadata) -> Self {
            self.committed_metadata = Some(committed_metadata);
            self
        }

        pub fn uncommitted_metadata(mut self, uncommitted_metadata: UnCommittedMetadata) -> Self {
            self.uncommitted_metadata = Some(uncommitted_metadata);
            self
        }

        pub fn build(self) -> Bead {
            Bead {
                block_header: self.block_header.expect("BlockHeader is required"),
                committed_metadata: self
                    .committed_metadata
                    .expect("CommittedMetadata is required"),
                uncommitted_metadata: self
                    .uncommitted_metadata
                    .expect("UnCommittedMetadata is required"),
            }
        }
    }
}
