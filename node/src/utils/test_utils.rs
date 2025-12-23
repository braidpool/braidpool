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
use bitcoin::BlockHeader;
#[cfg(test)]
pub use bitcoin::{absolute::Time, p2p::address::AddrV2, PublicKey, Transaction};
#[cfg(test)]
pub mod test_utility_functions {
    use std::{
        collections::{HashMap, HashSet},
        str::FromStr,
    };

    #[cfg(test)]
    use bitcoin::Txid;
    use bitcoin::{
        pow::CompactTargetExt, BlockHash, BlockTime, BlockVersion, CompactTarget, EcdsaSighashType,
        TxMerkleNode,
    };
    use rand::{rngs::OsRng, thread_rng, RngCore};
    use secp256k1::{Message, Secp256k1, SecretKey};
    use serde::{Deserialize, Serialize};

    #[cfg(test)]
    use crate::braid::Braid;

    pub use super::*;
    #[derive(Clone, Debug, Serialize, Deserialize)]
    pub struct FileBraid {
        pub description: String,
        pub parents: HashMap<usize, Vec<usize>>,
        pub children: HashMap<usize, Vec<usize>>,
        pub geneses: Vec<usize>,
        pub tips: Vec<usize>,
        pub cohorts: Vec<Vec<usize>>,
        pub bead_work: HashMap<usize, u32>,
        pub work: HashMap<usize, u32>,
        pub highest_work_path: Vec<usize>,
    }

    pub const BRAIDTESTDIRECTORY: &str = "tests/braids";
    #[cfg(test)]
    pub fn loading_braid_from_file(file_path: &str) -> (Braid, FileBraid) {
        use std::collections::HashMap;

        use num::range;

        use crate::braid::{Braid, Cohort};

        let current_file_path = file_path;
        let file_content = std::fs::read_to_string(current_file_path).unwrap();
        let file_braid: FileBraid = serde_json::from_str(&file_content).unwrap();
        let mut beads_to_idx: HashMap<usize, Bead> = HashMap::new();
        let mut test_braid_vector_bead_mapping: HashMap<BeadHash, usize> = HashMap::new();
        for bead_idx in file_braid.clone().parents {
            let random_test_bead = emit_bead();
            test_braid_vector_bead_mapping.insert(
                random_test_bead.clone().block_header.block_hash(),
                bead_idx.0,
            );
            beads_to_idx.insert(bead_idx.0, random_test_bead.clone());
        }
        let mut test_braid_parents_map: HashMap<usize, HashSet<usize>> = HashMap::new();
        for (idx, bead) in beads_to_idx.clone() {
            let mut current_bead = bead;
            let mut parent_idx_set: HashSet<usize> = HashSet::new();
            if let Some(current_bead_parents) = file_braid.parents.get(&idx) {
                for parent_bead_idx in current_bead_parents {
                    let parent_bead_block_hash =
                        beads_to_idx[parent_bead_idx].block_header.block_hash();
                    current_bead
                        .committed_metadata
                        .parents
                        .insert(parent_bead_block_hash);

                    parent_idx_set.insert(*parent_bead_idx);
                }
            }
            test_braid_parents_map.insert(idx, parent_idx_set);
            beads_to_idx.insert(idx, current_bead);
        }
        let mut beads_vector: Vec<Bead> = Vec::new();
        for bead_index_number in range(0, file_braid.parents.len()) {
            beads_vector.push(beads_to_idx[&bead_index_number].clone());
        }
        let mut current_braid_genesis: HashSet<usize> = HashSet::new();
        let mut current_braid_tips: HashSet<usize> = HashSet::new();
        let mut current_bead_cohorots: Vec<Cohort> = Vec::new();
        for genesis_bead_idx in file_braid.geneses.clone() {
            current_braid_genesis.insert(genesis_bead_idx);
        }
        for tips_bead_idx in file_braid.tips.clone() {
            current_braid_tips.insert(tips_bead_idx);
        }
        for cohort in file_braid.cohorts.clone() {
            use crate::braid::Cohort;

            let mut current_cohort_indices: HashSet<usize> = HashSet::new();
            for cohort_bead_idx in cohort {
                current_cohort_indices.insert(cohort_bead_idx);
            }
            current_bead_cohorots.push(Cohort(current_cohort_indices));
        }
        //constructing actual braid object from file-braid object
        (
            Braid {
                beads: beads_vector,
                bead_index_mapping: test_braid_vector_bead_mapping,
                tips: current_braid_tips,
                genesis_beads: current_braid_genesis,
                cohorts: current_bead_cohorots,
                cohort_tips: vec![HashSet::new()], // Cohorts tips are only used in extend(), so we can skip them here.
                orphan_beads: Vec::new(),
            },
            file_braid.clone(),
        )
    }

    pub struct TestUnCommittedMetadataBuilder {
        extra_nonce_1: u32,
        extra_nonce_2: u32,
        broadcast_timestamp: Option<Time>,
        signature: Option<Signature>,
    }

    #[cfg(test)]
    impl TestUnCommittedMetadataBuilder {
        pub fn new() -> Self {
            Self {
                extra_nonce_1: 0,
                extra_nonce_2: 0,
                broadcast_timestamp: None,
                signature: None,
            }
        }

        pub fn extra_nonce(mut self, nonce_1: u32, nonce_2: u32) -> Self {
            self.extra_nonce_1 = nonce_1;
            self.extra_nonce_2 = nonce_2;
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
                extra_nonce_1: self.extra_nonce_1,
                extra_nonce_2: self.extra_nonce_2,
                broadcast_timestamp: self
                    .broadcast_timestamp
                    .expect("broadcast_timestamp is required"),
                signature: self.signature.expect("signature is required"),
            }
        }
    }
    #[cfg(test)]
    pub struct TestCommittedMetadataBuilder {
        transaction_ids: Vec<Txid>,
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
                transaction_ids: Vec::new(),
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

        pub fn transactions(mut self, txs: Vec<Txid>) -> Self {
            self.transaction_ids = txs;
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
            use crate::committed_metadata::TxIdVec;

            CommittedMetadata {
                transaction_ids: TxIdVec(self.transaction_ids),
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
    fn generate_random_public_key_string() -> String {
        let secp = Secp256k1::new();
        let mut rng = thread_rng();
        let secret_key = SecretKey::new(&mut rng);
        let public_key = PublicKey::new(secret_key.public_key(&secp));
        public_key.to_string()
    }

    pub fn emit_bead() -> Bead {
        // This function creates a random bead for testing purposes.

        let random_public_key = generate_random_public_key_string()
            .parse::<bitcoin::PublicKey>()
            .unwrap();
        // Generate a reasonable timestamp (between 2020-01-01 and now)
        let now = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_secs() as u32;
        let current_time = bitcoin::absolute::Time::from_consensus(now).unwrap();

        let _address = String::from("127.0.0.1:8888");
        let public_key = random_public_key;
        let socket: String = String::from("127.0.0.1");
        let time_hash_set = TimeVec(Vec::new());
        let parent_hash_set: HashSet<BlockHash> = HashSet::new();
        let weak_target = CompactTarget::from_unprefixed_hex("1d00ffff").unwrap();
        let min_target = CompactTarget::from_unprefixed_hex("1d00ffff").unwrap();
        let time_val = current_time;

        let committed_metadata = TestCommittedMetadataBuilder::new()
            .comm_pub_key(public_key)
            .miner_ip(socket)
            .start_timestamp(time_val)
            .parents(parent_hash_set)
            .parent_bead_timestamps(time_hash_set)
            .payout_address(_address)
            .min_target(min_target)
            .weak_target(weak_target)
            .transactions(vec![])
            .build();

        let extra_nonce_1 = rand::random::<u32>();
        let extra_nonce_2 = rand::random::<u32>();

        let secp = Secp256k1::new();

        // Generate random secret key
        let mut rng = OsRng::default();
        let (secret_key, _) = secp.generate_keypair(&mut rng);

        // Create random 32-byte message
        let mut msg_bytes = [0u8; 32];
        rng.fill_bytes(&mut msg_bytes);
        let msg = Message::from_digest(msg_bytes);

        // Sign the message
        let signature = secp.sign_ecdsa(&msg, &secret_key);

        // DER encode the signature and get hex
        let der_sig = signature.serialize_der();
        let hex = hex::encode(der_sig);

        let sig = Signature {
            signature: secp256k1::ecdsa::Signature::from_str(&hex).unwrap(),
            sighash_type: EcdsaSighashType::All,
        };

        let uncommitted_metadata = TestUnCommittedMetadataBuilder::new()
            .broadcast_timestamp(time_val)
            .extra_nonce(extra_nonce_1, extra_nonce_2)
            .signature(sig)
            .build();
        let bytes: [u8; 32] = [0u8; 32];

        let test_block_header = BlockHeader {
            version: BlockVersion::TWO,
            prev_blockhash: BlockHash::from_byte_array(bytes),
            bits: CompactTarget::from_consensus(486604799),
            nonce: rand::random::<u32>(),
            time: BlockTime::from_u32(0),
            merkle_root: TxMerkleNode::from_byte_array(bytes),
        };

        let test_bead = TestBeadBuilder::new()
            .block_header(test_block_header)
            .committed_metadata(committed_metadata)
            .uncommitted_metadata(uncommitted_metadata)
            .build();
        test_bead
    }
}
