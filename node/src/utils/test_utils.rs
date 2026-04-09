#[cfg(test)]
use crate::bead::Bead;
#[cfg(test)]
pub use crate::braid::{BeadIdx, BeadSet, BeadWork, Cohort, CohortIdx, Relatives};
#[cfg(test)]
use crate::utils::BeadHash;

// A macro for making parents and children relationships for testing like:
// parents: relatives!(0 => [], 1 => [0])
#[macro_export]
macro_rules! relatives {
    () => {
        std::collections::HashMap::new()
    };
    ($($k:expr => [$($v:expr),*]),* $(,)?) => {
        std::collections::HashMap::from([$(($k, [$($v),*].into_iter().collect()),)*])
    };
}

// A macro for making a BeadSet for testing like:
// my_beadset = beadset![0,1,2]
#[cfg(test)]
#[macro_export]
macro_rules! beadset {
    ($($x:expr),* $(,)?) => {{
        use crate::braid::BeadSet;
        BeadSet::from([$($x),*])
    }};
}

// A macro for making a list of cohorts for testing like:
// my_cohorts = cohorts!([0], [1,2], [3])
#[cfg(test)]
#[macro_export]
macro_rules! cohorts {
    ($($set:expr),* $(,)?) => {{
        use crate::braid::BeadSet;
        vec![$(BeadSet::from($set)),*]
    }};
}

// A macro for creating test braids like:
// let braid = make_test_braid!(0 => [], 1 => [0], 2 => [0, 1]);
#[cfg(test)]
#[macro_export]
macro_rules! make_test_braid {
    ($($k:expr => [$($v:expr),*]),* $(,)?) => {{
        use std::collections::{HashMap, VecDeque};
        use crate::braid::{Bead, BeadIdx, BeadSet, Relatives};

        // Build parent mapping using Relatives type
        let parents: Relatives = Relatives::from([
            $(($k, [$($v),*].into_iter().collect::<BeadSet>()),)*
        ]);

        // Create beads in topological order
        let mut beads_to_idx: HashMap<BeadIdx, Bead> = HashMap::new();
        let mut remaining: BeadSet = parents.keys().copied().collect();
        let mut queue: VecDeque<BeadIdx> = VecDeque::new();

        // Start with genesis beads (no parents)
        for (&idx, parent_indices) in &parents {
            if parent_indices.is_empty() {
                queue.push_back(idx);
            }
        }

        // Process beads in topological order
        while let Some(idx) = queue.pop_front() {
            if !remaining.contains(&idx) {
                continue;
            }

            let parent_indices = &parents[&idx];

            // Check if all parents have been created
            let all_parents_ready = parent_indices.iter().all(|p| beads_to_idx.contains_key(p));

            if all_parents_ready {
                // Create bead with parent references
                let parent_refs: Vec<&Bead> = parent_indices
                    .iter()
                    .map(|parent_idx| &beads_to_idx[parent_idx])
                    .collect();
                beads_to_idx.insert(idx, crate::utils::test_utils::emit_Bead(&parent_refs));
                remaining.remove(&idx);

                // Add children to queue
                for (&child_idx, child_parents) in &parents {
                    if remaining.contains(&child_idx) && child_parents.contains(&idx) {
                        queue.push_back(child_idx);
                    }
                }
            } else {
                // Re-queue if parents aren't ready yet
                queue.push_back(idx);
            }
        }

        // Create beads vector in order (0, 1, 2, ...)
        let max_idx = parents.keys().copied().max().unwrap_or(0 as BeadIdx);
        let beads_vector: Vec<Bead> = (0..=max_idx)
            .map(|i| beads_to_idx[&i].clone())
            .collect();

        // Create and return the braid
        crate::braid::Braid::new(beads_vector)
    }};
}
#[cfg(test)]
use crate::committed_metadata::CommittedMetadata;
#[cfg(test)]
pub use crate::committed_metadata::TimeVec;
#[cfg(test)]
use crate::uncommitted_metadata::UnCommittedMetadata;
#[cfg(test)]
pub use crate::utils::Time;
#[cfg(test)]
pub use bitcoin::ecdsa::Signature;
#[cfg(test)]
// pub use crate::utils::Time; // Already imported through other means
#[cfg(test)]
use bitcoin::BlockHeader;
#[cfg(test)]
pub use bitcoin::{absolute::Time as OtherTime, p2p::address::AddrV2, Transaction};
#[cfg(test)]
use std::{
    collections::{HashMap, HashSet},
    str::FromStr,
};

#[cfg(test)]
use bitcoin::Txid;
use serde::Deserialize;

#[cfg(test)]
use crate::braid::Braid;

// JSONBraid structure for loading test data from JSON files with HashSet for algorithm compatibility
#[derive(Clone, Debug, Deserialize)]
pub struct JSONBraid {
    pub description: String,
    pub parents: crate::braid::Relatives,
    pub children: crate::braid::Relatives,
    pub geneses: crate::braid::BeadSet,
    pub tips: crate::braid::BeadSet,
    pub cohorts: Vec<crate::braid::Cohort>,
    // this is populated in the test files but always 1. TODO: improve tests with different work
    // per bead to further exercise hwpath and descendant_work
    #[allow(unused)]
    pub bead_work: std::collections::HashMap<crate::braid::BeadIdx, u32>, // FIXME Work
    pub work: std::collections::HashMap<crate::braid::BeadIdx, u32>, // FIXME Work
    pub highest_work_path: Vec<crate::braid::BeadIdx>,
}

#[cfg(test)]
impl JSONBraid {
    /// Load and convert from JSON file to HashSet format
    /// Panics if the file cannot be loaded, with a clear error message including the filename
    pub fn load(file_path: &str) -> Self {
        let file_content = std::fs::read_to_string(file_path)
            .unwrap_or_else(|e| panic!("Failed to read test file '{}': {}", file_path, e));
        serde_json::from_str(&file_content)
            .unwrap_or_else(|e| panic!("Failed to parse JSON in test file '{}': {}", file_path, e))
    }

    /// Returns an iterator over all JSONBraids in the test directory
    pub fn tests() -> Box<dyn Iterator<Item = (JSONBraid, String)>> {
        // Get the project root directory from Cargo's environment variable
        let project_root = env!("CARGO_MANIFEST_DIR");
        let test_dir = format!("{}/../{}", project_root, BRAID_TEST_DIR);

        let dir_entries = std::fs::read_dir(&test_dir)
            .unwrap_or_else(|e| panic!("Failed to read test directory '{}': {}", test_dir, e));

        // Collect all JSON test files first
        let test_files: Vec<(JSONBraid, String)> = dir_entries
            .filter_map(|entry| {
                let entry = entry.unwrap_or_else(|e| panic!("Failed to read directory: {:?}", e));
                let path = entry.path();

                // Only include JSON files
                if path.extension().and_then(|s| s.to_str()) == Some("json") {
                    let file_path = path
                        .to_str()
                        .expect("Cannot stringify file path (Invalid UTF-8?)");
                    let filename = path
                        .file_name()
                        .unwrap_or_default()
                        .to_string_lossy()
                        .to_string();
                    Some((JSONBraid::load(file_path), filename))
                } else {
                    None
                }
            })
            .collect();

        // Panic if no test files were found
        if test_files.is_empty() {
            panic!("No JSON test files found in directory '{}'", test_dir);
        }

        Box::new(test_files.into_iter())
    }

    /// Create a Braid object from this JSONBraid data structure
    #[cfg(test)]
    #[allow(non_snake_case)] // the upper case Braid name is intentional because that's the
                             // class returned.
    pub fn make_Braid(&self) -> Braid {
        use crate::braid::Braid;
        use std::collections::VecDeque;

        // Create beads in topological order to ensure parent hashes are consistent
        let mut beads_to_idx: HashMap<crate::braid::BeadIdx, Bead> = HashMap::new();
        let mut remaining: std::collections::HashSet<crate::braid::BeadIdx> =
            self.parents.keys().copied().collect();
        let mut queue: VecDeque<crate::braid::BeadIdx> = VecDeque::new();

        // Start with genesis beads (no parents)
        for (&idx, parents) in &self.parents {
            if parents.is_empty() {
                queue.push_back(idx);
            }
        }

        // Process beads in topological order
        while let Some(idx) = queue.pop_front() {
            if !remaining.contains(&idx) {
                continue;
            }

            let parent_indices = &self.parents[&idx];

            // Check if all parents have been created
            let all_parents_ready = parent_indices.iter().all(|p| beads_to_idx.contains_key(p));

            if all_parents_ready {
                // Create bead with parent references
                let parent_refs: Vec<&Bead> = parent_indices
                    .iter()
                    .map(|parent_idx| &beads_to_idx[parent_idx])
                    .collect();
                beads_to_idx.insert(idx, emit_Bead(&parent_refs));
                remaining.remove(&idx);

                // Add children to queue
                for (&child_idx, child_parents) in &self.parents {
                    if remaining.contains(&child_idx) && child_parents.contains(&idx) {
                        queue.push_back(child_idx);
                    }
                }
            } else {
                // Re-queue if parents aren't ready yet
                queue.push_back(idx);
            }
        }

        // Create beads vector in order
        let beads_vector: Vec<Bead> = (0..self.parents.len())
            .map(|i| beads_to_idx[&i].clone())
            .collect();

        // Let Braid::new handle all the complex parent/children mapping,
        // tip/genesis detection, and cohort computation
        Braid::new(beads_vector)
    }
}

/// Directory containing braid test files (relative to project root)
#[cfg(test)]
pub const BRAID_TEST_DIR: &str = "tests/braids";
#[cfg(test)]
use crate::utils::MicrosecondTimestamp;

#[cfg(test)]
pub struct TestUnCommittedMetadataBuilder {
    extra_nonce_1: u32,
    extra_nonce_2: u32,
    broadcast_timestamp: Option<crate::utils::timestamp::MicrosecondTimestamp>,
    signature: Option<bitcoin::ecdsa::Signature>,
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

    pub fn broadcast_timestamp(mut self, time: MicrosecondTimestamp) -> Self {
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
    start_timestamp: Option<crate::utils::timestamp::MicrosecondTimestamp>,
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

    pub fn start_timestamp(mut self, time: MicrosecondTimestamp) -> Self {
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

#[cfg(test)]
use rand::{thread_rng, RngCore};
#[cfg(test)]
fn generate_random_public_key_string() -> String {
    let secp = Secp256k1::new();
    let mut rng = thread_rng();
    let secret_key = SecretKey::new(&mut rng);
    let public_key = PublicKey::new(secret_key.public_key(&secp));
    public_key.to_string()
}

#[cfg(test)]
use std::sync::atomic::{AtomicU32, Ordering};
// Static counter for unique nonce generation across all beads
#[cfg(test)]
static NONCE_COUNTER: AtomicU32 = AtomicU32::new(1);

#[cfg(test)]
use bitcoin::{
    pow::CompactTargetExt, BlockHash, BlockTime, BlockVersion, CompactTarget, EcdsaSighashType,
    PublicKey, TxMerkleNode,
};
#[cfg(test)]
use rand::rngs::OsRng;
#[cfg(test)]
use secp256k1::{Message, Secp256k1, SecretKey};
#[cfg(test)]
#[allow(non_snake_case)]
pub fn emit_Bead(parents: &[&crate::bead::Bead]) -> crate::bead::Bead {
    // This function creates a random bead for testing purposes with the provided parents.

    let random_public_key = generate_random_public_key_string()
        .parse::<bitcoin::PublicKey>()
        .unwrap();
    // Generate a reasonable timestamp (between 2020-01-01 and now)
    let now = std::time::SystemTime::now();
    let current_time = crate::utils::timestamp::MicrosecondTimestamp::from_system_time(now)
        .expect("SystemTime should be after Unix epoch");

    let _address = String::from("127.0.0.1:8888");
    let public_key = random_public_key;
    let socket: String = String::from("127.0.0.1");
    let time_hash_set = TimeVec(Vec::new());

    // Convert parents slice to HashSet of hashes
    let parent_hash_set: HashSet<BlockHash> = parents.iter().map(|&bead| bead.hash()).collect();

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
        nonce: NONCE_COUNTER.fetch_add(1, Ordering::SeqCst),
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
