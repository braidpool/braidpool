use super::Bead;
use super::Braid;
use crate::braid::Cohort;
use crate::committed_metadata::TimeVec;
use crate::utils::test_utils::test_utility_functions::*;
use bitcoin::block::BlockHash as BeadHash;
use bitcoin::{
    absolute::Time,
    ecdsa::Signature,
    p2p::{Address as P2P_Address, ServiceFlags},
    BlockHash, BlockHeader, BlockTime, BlockVersion, CompactTarget, EcdsaSighashType, PublicKey,
    TxMerkleNode,
};
use core::net::SocketAddr;
use num::range;
use rand::{rngs::OsRng, thread_rng, RngCore};
use secp256k1::{Message, Secp256k1, SecretKey};
use serde::{Deserialize, Serialize};
use serde_json;
use std::collections::HashMap;
use std::collections::HashSet;
use std::net::{IpAddr, Ipv4Addr};
use std::path::Path;
use std::str::FromStr;

#[derive(Clone, Debug, Serialize, Deserialize)]
struct FileBraid {
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

pub const test_directory: &str = "tests/braids";

fn generate_random_public_key_string() -> String {
    let secp = Secp256k1::new();
    let mut rng = thread_rng();
    let secret_key = SecretKey::new(&mut rng);
    let public_key = PublicKey::new(secret_key.public_key(&secp));
    public_key.to_string()
}

fn emit_bead() -> Bead {
    // This function creates a random bead for testing purposes.

    let random_public_key = generate_random_public_key_string()
        .parse::<bitcoin::PublicKey>()
        .unwrap();
    // Generate a reasonable timestamp (between 2020-01-01 and now)
    let now = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_secs() as u32;
    let current_time = Time::from_consensus(now).unwrap();

    let test_sock_add = SocketAddr::new(IpAddr::V4(Ipv4Addr::new(127, 0, 0, 1)), 8888);
    let _address = P2P_Address::new(&test_sock_add.clone(), ServiceFlags::NONE);
    let public_key = random_public_key;
    let socket = bitcoin::p2p::address::AddrV2::Ipv4(Ipv4Addr::new(127, 0, 0, 1));
    let time_hash_set = TimeVec(Vec::new());
    let parent_hash_set: HashSet<BlockHash> = HashSet::new();
    let weak_target = CompactTarget::from_consensus(32);
    let min_target = CompactTarget::from_consensus(1);
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

    let extra_nonce = rand::random::<i32>();
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
        .extra_nonce(extra_nonce)
        .signature(sig)
        .build();
    let bytes: [u8; 32] = [0u8; 32];

    let test_block_header = BlockHeader {
        version: BlockVersion::TWO,
        prev_blockhash: BlockHash::from_byte_array(bytes),
        bits: CompactTarget::from_consensus(32),
        nonce: rand::random::<u32>(),
        time: BlockTime::from_u32(rand::random::<u32>()),
        merkle_root: TxMerkleNode::from_byte_array(bytes),
    };

    let test_bead = TestBeadBuilder::new()
        .block_header(test_block_header)
        .committed_metadata(committed_metadata)
        .uncommitted_metadata(uncommitted_metadata)
        .build();
    test_bead
}

fn loading_braid_from_file(file_path: &str) -> (Braid, FileBraid) {
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
            orphan_beads: Vec::new(),
        },
        file_braid.clone(),
    )
}
#[test]
pub fn test_extend_functionality() {
    // Create a braid with one bead.
    let test_bead_0 = emit_bead();

    let mut test_braid = Braid {
        beads: vec![test_bead_0.clone()],
        genesis_beads: HashSet::from([0]),
        tips: HashSet::from([0]),
        orphan_beads: Vec::new(),
        cohorts: vec![Cohort(HashSet::from([0]))],
        bead_index_mapping: std::collections::HashMap::from([(
            test_bead_0.block_header.block_hash(),
            0,
        )]),
    };
    assert_eq!(
        test_braid.cohorts,
        vec![Cohort(HashSet::from([0]))],
        "Initial cohort should contain only the genesis bead"
    );

    // Let's add two beads to create a chain structure.

    let mut test_bead_1 = emit_bead();
    test_bead_1
        .committed_metadata
        .parents
        .insert(test_bead_0.block_header.block_hash());

    test_braid.extend(&test_bead_1);
    // After adding a new bead that extends the zeroth one, we should have two cohorts
    assert_eq!(
        test_braid.cohorts,
        vec![Cohort(HashSet::from([0])), Cohort(HashSet::from([1]))],
        "After adding the second bead, there should be two cohorts"
    );

    let mut test_bead_2 = emit_bead();
    test_bead_2
        .committed_metadata
        .parents
        .insert(test_bead_1.block_header.block_hash());
    test_braid.extend(&test_bead_2);

    // After adding the second bead, we should have three cohorts
    assert_eq!(
        test_braid.cohorts,
        vec![
            Cohort(HashSet::from([0])),
            Cohort(HashSet::from([1])),
            Cohort(HashSet::from([2]))
        ],
        "After adding the third bead, there should be three cohorts"
    );

    // Let's add a few more beads to create a more complex braid structure

    // Structure will be:
    // - Bead(s) 3-5 will branch from bead 2
    // - Bead(s) 6-8 will branch from bead 4
    // - Bead(s) 9-11 will branch from bead 5
    // - Bead(s) 12 will merge all the tips.

    // This will create a structure like:
    //           /-- 3 --------------------\
    // 0 -- 1 -- 2 -- 4 -- 6 -- 7 -- 8 --  12 -- 13
    //           \-- 5 -- 9 -- 10 -- 11 -- /

    // Create bead 3 with parent 2
    let mut test_bead_3 = emit_bead();
    test_bead_3
        .committed_metadata
        .parents
        .insert(test_bead_2.block_header.block_hash());
    test_braid.extend(&test_bead_3);

    // Create bead 4 with parent 2
    let mut test_bead_4 = emit_bead();
    test_bead_4
        .committed_metadata
        .parents
        .insert(test_bead_2.block_header.block_hash());
    test_braid.extend(&test_bead_4);

    // Create bead 5 with parent 2
    let mut test_bead_5 = emit_bead();
    test_bead_5
        .committed_metadata
        .parents
        .insert(test_bead_2.block_header.block_hash());
    test_braid.extend(&test_bead_5);

    assert_eq!(
        test_braid.cohorts,
        vec![
            Cohort(HashSet::from([0])),
            Cohort(HashSet::from([1])),
            Cohort(HashSet::from([2])),
            Cohort(HashSet::from([3, 4, 5])),
        ],
        "After adding the sixth bead, there should be four cohorts"
    );

    // Create beads 6-8 with chain from bead 4
    let mut test_bead_6 = emit_bead();
    test_bead_6
        .committed_metadata
        .parents
        .insert(test_bead_4.block_header.block_hash());
    test_braid.extend(&test_bead_6);

    let mut test_bead_7 = emit_bead();
    test_bead_7
        .committed_metadata
        .parents
        .insert(test_bead_6.block_header.block_hash());
    test_braid.extend(&test_bead_7);

    let mut test_bead_8 = emit_bead();
    test_bead_8
        .committed_metadata
        .parents
        .insert(test_bead_7.block_header.block_hash());
    test_braid.extend(&test_bead_8);

    assert_eq!(
        test_braid.cohorts,
        vec![
            Cohort(HashSet::from([0])),
            Cohort(HashSet::from([1])),
            Cohort(HashSet::from([2])),
            Cohort(HashSet::from([3, 4, 5, 6, 7, 8])),
        ]
    );

    // Create beads 9-11 with chain from bead 5
    let mut test_bead_9 = emit_bead();
    test_bead_9
        .committed_metadata
        .parents
        .insert(test_bead_5.block_header.block_hash());
    test_braid.extend(&test_bead_9);

    let mut test_bead_10 = emit_bead();
    test_bead_10
        .committed_metadata
        .parents
        .insert(test_bead_9.block_header.block_hash());
    test_braid.extend(&test_bead_10);

    let mut test_bead_11 = emit_bead();
    test_bead_11
        .committed_metadata
        .parents
        .insert(test_bead_10.block_header.block_hash());
    test_braid.extend(&test_bead_11);

    assert_eq!(
        test_braid.cohorts,
        vec![
            Cohort(HashSet::from([0])),
            Cohort(HashSet::from([1])),
            Cohort(HashSet::from([2])),
            Cohort(HashSet::from([3, 4, 5, 6, 7, 8, 9, 10, 11])),
        ]
    );

    let mut test_bead_12 = emit_bead();
    test_bead_12
        .committed_metadata
        .parents
        .insert(test_bead_8.block_header.block_hash());
    test_bead_12
        .committed_metadata
        .parents
        .insert(test_bead_11.block_header.block_hash());
    test_bead_12
        .committed_metadata
        .parents
        .insert(test_bead_3.block_header.block_hash());
    test_braid.extend(&test_bead_12);

    assert_eq!(
        test_braid.cohorts,
        vec![
            Cohort(HashSet::from([0])),
            Cohort(HashSet::from([1])),
            Cohort(HashSet::from([2])),
            Cohort(HashSet::from([3, 4, 5, 6, 7, 8, 9, 10, 11])),
            Cohort(HashSet::from([12])),
        ]
    );

    let mut test_bead_13 = emit_bead();
    test_bead_13
        .committed_metadata
        .parents
        .insert(test_bead_12.block_header.block_hash());
    test_braid.extend(&test_bead_13);

    assert_eq!(
        test_braid.cohorts,
        vec![
            Cohort(HashSet::from([0])),
            Cohort(HashSet::from([1])),
            Cohort(HashSet::from([2])),
            Cohort(HashSet::from([3, 4, 5, 6, 7, 8, 9, 10, 11])),
            Cohort(HashSet::from([12])),
            Cohort(HashSet::from([13])),
        ]
    );
}
#[test]
pub fn test_genesis1() {
    let test_bead_0 = emit_bead();
    let mut test_bead_1 = emit_bead();

    let mut test_bead_2 = emit_bead();

    let mut test_bead_3 = emit_bead();

    test_bead_1
        .committed_metadata
        .parents
        .insert(test_bead_0.block_header.block_hash());
    test_bead_2
        .committed_metadata
        .parents
        .insert(test_bead_1.block_header.block_hash());

    test_bead_3
        .committed_metadata
        .parents
        .insert(test_bead_2.block_header.block_hash());

    let mut test_braid = Braid {
        beads: vec![
            test_bead_0.clone(),
            test_bead_1.clone(),
            test_bead_2.clone(),
            test_bead_3.clone(),
        ],
        genesis_beads: HashSet::from([0]),
        tips: HashSet::from([3]),
        orphan_beads: Vec::new(),
        cohorts: vec![Cohort(HashSet::from([0]))],
        bead_index_mapping: std::collections::HashMap::from([
            (test_bead_0.block_header.block_hash(), 0),
            (test_bead_1.block_header.block_hash(), 1),
            (test_bead_2.block_header.block_hash(), 2),
            (test_bead_3.block_header.block_hash(), 3),
        ]),
    };

    //mapping of the indices with set of indices representing its parents
    //where the key represents the ith indexed bead from self.beads which contains all the beads
    //belonging to a particular braid and mapping is a set of indices of its parents present in
    //self.beads
    let mut parents1: HashMap<usize, HashSet<usize>> = HashMap::new();
    parents1.insert(0, HashSet::from([]));
    parents1.insert(1, HashSet::from([0]));
    parents1.insert(2, HashSet::from([1]));
    parents1.insert(3, HashSet::from([2]));

    let geneses_bead_indices = test_braid.genesis(parents1);
    assert_eq!(geneses_bead_indices, HashSet::from([0]));
}
#[test]
pub fn test_genesis2() {
    let test_bead_0 = emit_bead();
    let test_bead_1 = emit_bead();

    let mut test_bead_2 = emit_bead();

    let mut test_bead_3 = emit_bead();

    test_bead_2
        .committed_metadata
        .parents
        .insert(test_bead_1.block_header.prev_blockhash);
    test_bead_3
        .committed_metadata
        .parents
        .insert(test_bead_1.block_header.prev_blockhash);
    let mut test_braid = Braid {
        beads: vec![
            test_bead_0.clone(),
            test_bead_1.clone(),
            test_bead_2.clone(),
            test_bead_3.clone(),
        ],
        genesis_beads: HashSet::from([0]),
        tips: HashSet::from([3]),
        orphan_beads: Vec::new(),
        cohorts: vec![Cohort(HashSet::from([0]))],
        bead_index_mapping: std::collections::HashMap::from([
            (test_bead_0.block_header.block_hash(), 0),
            (test_bead_1.block_header.block_hash(), 1),
            (test_bead_2.block_header.block_hash(), 2),
            (test_bead_3.block_header.block_hash(), 3),
        ]),
    };
    //mapping of the indices with set of indices representing its parents
    //where the key represents the ith indexed bead from self.beads which contains all the beads
    //belonging to a particular braid and mapping is a set of indices of its parents present in
    //self.beads
    let mut parents1: HashMap<usize, HashSet<usize>> = HashMap::new();
    parents1.insert(0, HashSet::from([]));
    parents1.insert(1, HashSet::from([]));
    parents1.insert(2, HashSet::from([1]));
    parents1.insert(3, HashSet::from([1]));

    let geneses_bead_indices = test_braid.genesis(parents1);

    assert_eq!(geneses_bead_indices, HashSet::from([0, 1]));
}
#[test]
pub fn test_genesis3() {
    let test_bead_0 = emit_bead();
    let test_bead_1 = emit_bead();

    let test_bead_2 = emit_bead();

    let mut test_bead_3 = emit_bead();

    let mut test_bead_4 = emit_bead();
    test_bead_3
        .committed_metadata
        .parents
        .insert(test_bead_1.block_header.block_hash());
    test_bead_4
        .committed_metadata
        .parents
        .insert(test_bead_0.block_header.block_hash());

    let mut test_braid = Braid {
        beads: vec![
            test_bead_0.clone(),
            test_bead_1.clone(),
            test_bead_2.clone(),
            test_bead_3.clone(),
            test_bead_4.clone(),
        ],
        genesis_beads: HashSet::from([0, 1, 2]),
        tips: HashSet::from([3]),
        orphan_beads: Vec::new(),
        cohorts: vec![Cohort(HashSet::from([0]))],
        bead_index_mapping: std::collections::HashMap::from([
            (test_bead_0.block_header.block_hash(), 0),
            (test_bead_1.block_header.block_hash(), 1),
            (test_bead_2.block_header.block_hash(), 2),
            (test_bead_3.block_header.block_hash(), 3),
            (test_bead_4.block_header.block_hash(), 4),
        ]),
    };
    //mapping of the indices with set of indices representing its parents
    //where the key represents the ith indexed bead from self.beads which contains all the beads
    //belonging to a particular braid and mapping is a set of indices of its parents present in
    //self.beads
    let mut parents1: HashMap<usize, HashSet<usize>> = HashMap::new();
    parents1.insert(0, HashSet::from([]));
    parents1.insert(1, HashSet::from([]));
    parents1.insert(2, HashSet::from([]));
    parents1.insert(3, HashSet::from([1]));
    parents1.insert(3, HashSet::from([0]));

    let geneses_bead_indices = test_braid.genesis(parents1);
    assert_eq!(geneses_bead_indices, HashSet::from([0, 1, 2]));
}

#[test]
pub fn test_geneses_files() {
    let ancestors = std::env::current_dir().unwrap();
    let ancestors_directory: Vec<&Path> = ancestors.ancestors().collect();
    let parent_directory = ancestors_directory[1];
    let test_absolute_path = parent_directory.join(test_directory);
    for test_braid_file in std::fs::read_dir(test_absolute_path.as_path()).unwrap() {
        let re = test_braid_file.unwrap().file_name();
        let current_file_name = re.to_str().unwrap();
        let file_path = test_absolute_path.join(current_file_name);
        let (mut current_file_braid, file_braid) =
            loading_braid_from_file(file_path.to_str().unwrap());
        let mut current_braid_parents: HashMap<usize, HashSet<usize>> = HashMap::new();
        for beads in file_braid.parents {
            let mut current_bead_parents: HashSet<usize> = HashSet::new();
            for parent_beads in beads.1 {
                current_bead_parents.insert(parent_beads);
            }
            current_braid_parents.insert(beads.0, current_bead_parents);
        }

        let computed_genesis_indices = current_file_braid.genesis(current_braid_parents);
        let current_file_genesis = file_braid.geneses;
        let mut file_genesis_set: HashSet<usize> = HashSet::new();
        for genesis_idx in current_file_genesis {
            file_genesis_set.insert(genesis_idx);
        }
        assert_eq!(file_genesis_set, computed_genesis_indices);
    }
}

#[test]
pub fn tips1() {
    let test_bead_0 = emit_bead();
    let mut test_bead_1 = emit_bead();

    let mut test_bead_2 = emit_bead();

    let mut test_bead_3 = emit_bead();

    test_bead_1
        .committed_metadata
        .parents
        .insert(test_bead_0.block_header.block_hash());
    test_bead_2
        .committed_metadata
        .parents
        .insert(test_bead_1.block_header.block_hash());

    test_bead_3
        .committed_metadata
        .parents
        .insert(test_bead_2.block_header.block_hash());

    let mut test_braid = Braid {
        beads: vec![
            test_bead_0.clone(),
            test_bead_1.clone(),
            test_bead_2.clone(),
            test_bead_3.clone(),
        ],
        genesis_beads: HashSet::from([0]),
        tips: HashSet::from([3]),
        orphan_beads: Vec::new(),
        cohorts: vec![Cohort(HashSet::from([0]))],
        bead_index_mapping: std::collections::HashMap::from([
            (test_bead_0.block_header.block_hash(), 0),
            (test_bead_1.block_header.block_hash(), 1),
            (test_bead_2.block_header.block_hash(), 2),
            (test_bead_3.block_header.block_hash(), 3),
        ]),
    };

    //mapping of the indices with set of indices representing its parents
    //where the key represents the ith indexed bead from self.beads which contains all the beads
    //belonging to a particular braid and mapping is a set of indices of its parents present in
    //self.beads
    let mut parents1: HashMap<usize, HashSet<usize>> = HashMap::new();
    parents1.insert(0, HashSet::from([]));
    parents1.insert(1, HashSet::from([0]));
    parents1.insert(2, HashSet::from([1]));
    parents1.insert(3, HashSet::from([2]));
    let tips_bead_indices = test_braid.tips(parents1);
    assert_eq!(tips_bead_indices, HashSet::from([3]));
}

#[test]
pub fn tips2() {
    let test_bead_0 = emit_bead();
    let mut test_bead_1 = emit_bead();

    let mut test_bead_2 = emit_bead();

    let mut test_bead_3 = emit_bead();

    test_bead_1
        .committed_metadata
        .parents
        .insert(test_bead_0.block_header.block_hash());
    test_bead_2
        .committed_metadata
        .parents
        .insert(test_bead_1.block_header.block_hash());

    test_bead_3
        .committed_metadata
        .parents
        .insert(test_bead_1.block_header.block_hash());

    let mut test_braid = Braid {
        beads: vec![
            test_bead_0.clone(),
            test_bead_1.clone(),
            test_bead_2.clone(),
            test_bead_3.clone(),
        ],
        genesis_beads: HashSet::from([0]),
        tips: HashSet::from([3]),
        orphan_beads: Vec::new(),
        cohorts: vec![Cohort(HashSet::from([0]))],
        bead_index_mapping: std::collections::HashMap::from([
            (test_bead_0.block_header.block_hash(), 0),
            (test_bead_1.block_header.block_hash(), 1),
            (test_bead_2.block_header.block_hash(), 2),
            (test_bead_3.block_header.block_hash(), 3),
        ]),
    };

    //mapping of the indices with set of indices representing its parents
    //where the key represents the ith indexed bead from self.beads which contains all the beads
    //belonging to a particular braid and mapping is a set of indices of its parents present in
    //self.beads
    let mut parents1: HashMap<usize, HashSet<usize>> = HashMap::new();
    parents1.insert(0, HashSet::from([]));
    parents1.insert(1, HashSet::from([0]));
    parents1.insert(2, HashSet::from([1]));
    parents1.insert(3, HashSet::from([1]));

    let tips_bead_indices = test_braid.tips(parents1);
    assert_eq!(tips_bead_indices, HashSet::from([2, 3]));
}

#[test]
pub fn tips3() {
    let test_bead_0 = emit_bead();
    let test_bead_1 = emit_bead();

    let test_bead_2 = emit_bead();

    let mut test_bead_3 = emit_bead();

    let mut test_bead_4 = emit_bead();

    let mut test_bead_5 = emit_bead();
    test_bead_3
        .committed_metadata
        .parents
        .insert(test_bead_0.block_header.block_hash());
    test_bead_3
        .committed_metadata
        .parents
        .insert(test_bead_1.block_header.block_hash());
    test_bead_3
        .committed_metadata
        .parents
        .insert(test_bead_2.block_header.block_hash());
    test_bead_4
        .committed_metadata
        .parents
        .insert(test_bead_0.block_header.block_hash());
    test_bead_4
        .committed_metadata
        .parents
        .insert(test_bead_1.block_header.block_hash());
    test_bead_4
        .committed_metadata
        .parents
        .insert(test_bead_2.block_header.block_hash());
    test_bead_5
        .committed_metadata
        .parents
        .insert(test_bead_0.block_header.block_hash());
    test_bead_5
        .committed_metadata
        .parents
        .insert(test_bead_1.block_header.block_hash());
    test_bead_5
        .committed_metadata
        .parents
        .insert(test_bead_2.block_header.block_hash());
    let mut test_braid = Braid {
        beads: vec![
            test_bead_0.clone(),
            test_bead_1.clone(),
            test_bead_2.clone(),
            test_bead_3.clone(),
            test_bead_4.clone(),
            test_bead_5.clone(),
        ],
        genesis_beads: HashSet::from([0, 1, 2]),
        tips: HashSet::from([3, 4, 5]),
        orphan_beads: Vec::new(),
        cohorts: vec![Cohort(HashSet::from([0]))],
        bead_index_mapping: std::collections::HashMap::from([
            (test_bead_0.block_header.block_hash(), 0),
            (test_bead_1.block_header.block_hash(), 1),
            (test_bead_2.block_header.block_hash(), 2),
            (test_bead_3.block_header.block_hash(), 3),
            (test_bead_4.block_header.block_hash(), 4),
            (test_bead_5.block_header.block_hash(), 5),
        ]),
    };
    //mapping of the indices with set of indices representing its parents
    //where the key represents the ith indexed bead from self.beads which contains all the beads
    //belonging to a particular braid and mapping is a set of indices of its parents present in
    //self.beads
    let mut parents1: HashMap<usize, HashSet<usize>> = HashMap::new();
    parents1.insert(0, HashSet::from([]));
    parents1.insert(1, HashSet::from([]));
    parents1.insert(2, HashSet::from([]));
    parents1.insert(3, HashSet::from([0, 1, 2]));
    parents1.insert(4, HashSet::from([0, 1, 2]));

    parents1.insert(5, HashSet::from([0, 1, 2]));

    let tips_bead_indices = test_braid.tips(parents1);
    assert_eq!(tips_bead_indices, HashSet::from([3, 4, 5]));
}
#[test]

pub fn test_reverse() {
    let test_bead_0 = emit_bead();
    let test_bead_1 = emit_bead();

    let test_bead_2 = emit_bead();

    let mut test_bead_3 = emit_bead();

    let mut test_bead_4 = emit_bead();

    let mut test_bead_5 = emit_bead();
    test_bead_3
        .committed_metadata
        .parents
        .insert(test_bead_0.block_header.block_hash());
    test_bead_3
        .committed_metadata
        .parents
        .insert(test_bead_1.block_header.block_hash());
    test_bead_3
        .committed_metadata
        .parents
        .insert(test_bead_2.block_header.block_hash());
    test_bead_4
        .committed_metadata
        .parents
        .insert(test_bead_0.block_header.block_hash());
    test_bead_4
        .committed_metadata
        .parents
        .insert(test_bead_1.block_header.block_hash());
    test_bead_4
        .committed_metadata
        .parents
        .insert(test_bead_2.block_header.block_hash());
    test_bead_5
        .committed_metadata
        .parents
        .insert(test_bead_0.block_header.block_hash());
    test_bead_5
        .committed_metadata
        .parents
        .insert(test_bead_1.block_header.block_hash());
    test_bead_5
        .committed_metadata
        .parents
        .insert(test_bead_2.block_header.block_hash());
    let mut test_braid = Braid {
        beads: vec![
            test_bead_0.clone(),
            test_bead_1.clone(),
            test_bead_2.clone(),
            test_bead_3.clone(),
            test_bead_4.clone(),
            test_bead_5.clone(),
        ],
        genesis_beads: HashSet::from([0, 1, 2]),
        tips: HashSet::from([3, 4, 5]),
        orphan_beads: Vec::new(),
        cohorts: vec![Cohort(HashSet::from([0]))],
        bead_index_mapping: std::collections::HashMap::from([
            (test_bead_0.block_header.block_hash(), 0),
            (test_bead_1.block_header.block_hash(), 1),
            (test_bead_2.block_header.block_hash(), 2),
            (test_bead_3.block_header.block_hash(), 3),
            (test_bead_4.block_header.block_hash(), 4),
            (test_bead_5.block_header.block_hash(), 5),
        ]),
    };
    //mapping of the indices with set of indices representing its parents
    //where the key represents the ith indexed bead from self.beads which contains all the beads
    //belonging to a particular braid and mapping is a set of indices of its parents present in
    //self.beads
    let mut parents1: HashMap<usize, HashSet<usize>> = HashMap::new();
    parents1.insert(0, HashSet::from([]));
    parents1.insert(1, HashSet::from([]));
    parents1.insert(2, HashSet::from([]));
    parents1.insert(3, HashSet::from([0, 1, 2]));
    parents1.insert(4, HashSet::from([0, 1, 2]));

    parents1.insert(5, HashSet::from([0, 1, 2]));
    let reverse_children_mapping = test_braid.reverse(parents1);
    let mut actual_children_mapping: HashMap<usize, HashSet<usize>> = HashMap::new();
    actual_children_mapping.insert(0, HashSet::from([3, 4, 5]));
    actual_children_mapping.insert(1, HashSet::from([3, 4, 5]));

    actual_children_mapping.insert(2, HashSet::from([3, 4, 5]));
    actual_children_mapping.insert(3, HashSet::new());
    actual_children_mapping.insert(4, HashSet::new());
    actual_children_mapping.insert(5, HashSet::new());

    assert_eq!(reverse_children_mapping, actual_children_mapping);
}
#[test]
pub fn test_all_ancestors() {
    let ancestors = std::env::current_dir().unwrap();
    let ancestors_directory: Vec<&Path> = ancestors.ancestors().collect();
    let parent_directory = ancestors_directory[1];
    let test_absolute_path = parent_directory.join(test_directory);
    for test_braid_file in std::fs::read_dir(test_absolute_path.as_path()).unwrap() {
        let re = test_braid_file.unwrap().file_name();
        let current_file_name = re.to_str().unwrap();
        let file_path = test_absolute_path.join(current_file_name);
        let (current_file_braid, file_braid) = loading_braid_from_file(file_path.to_str().unwrap());
        let mut current_braid_parents: HashMap<usize, HashSet<usize>> = HashMap::new();
        for beads in file_braid.parents {
            let mut current_bead_parents: HashSet<usize> = HashSet::new();
            for parent_beads in beads.1 {
                current_bead_parents.insert(parent_beads);
            }
            current_braid_parents.insert(beads.0, current_bead_parents);
        }
        for bead_index in current_braid_parents.clone() {
            let current_bead_hash = current_file_braid.beads[bead_index.0]
                .block_header
                .block_hash();
            let mut d1: HashMap<usize, HashSet<usize>> = HashMap::new();
            let ancestor_mapping = current_file_braid.clone().get_all_ancestors(
                current_bead_hash,
                &mut d1,
                current_braid_parents.clone(),
            );
            let mut d2: HashMap<usize, HashSet<usize>> = HashMap::new();

            let ancestor_mapping_dfs = current_file_braid.clone().updating_ancestors(
                current_bead_hash,
                &mut d2,
                current_braid_parents.clone(),
            );
            assert_eq!(d1, d2);
        }
    }
}
#[test]

pub fn test_cohorts_parents_1() {
    let test_bead_0 = emit_bead();
    let mut test_bead_1 = emit_bead();

    let mut test_bead_2 = emit_bead();

    let mut test_bead_3 = emit_bead();

    test_bead_1
        .committed_metadata
        .parents
        .insert(test_bead_0.block_header.block_hash());
    test_bead_2
        .committed_metadata
        .parents
        .insert(test_bead_1.block_header.block_hash());

    test_bead_3
        .committed_metadata
        .parents
        .insert(test_bead_2.block_header.block_hash());

    let mut test_braid = Braid {
        beads: vec![
            test_bead_0.clone(),
            test_bead_1.clone(),
            test_bead_2.clone(),
            test_bead_3.clone(),
        ],
        genesis_beads: HashSet::from([0]),
        tips: HashSet::from([3]),
        orphan_beads: Vec::new(),
        cohorts: vec![Cohort(HashSet::from([0]))],
        bead_index_mapping: std::collections::HashMap::from([
            (test_bead_0.block_header.block_hash(), 0),
            (test_bead_1.block_header.block_hash(), 1),
            (test_bead_2.block_header.block_hash(), 2),
            (test_bead_3.block_header.block_hash(), 3),
        ]),
    };

    //mapping of the indices with set of indices representing its parents
    //where the key represents the ith indexed bead from self.beads which contains all the beads
    //belonging to a particular braid and mapping is a set of indices of its parents present in
    //self.beads
    let mut parents1: HashMap<usize, HashSet<usize>> = HashMap::new();
    parents1.insert(0, HashSet::from([]));
    parents1.insert(1, HashSet::from([0]));
    parents1.insert(2, HashSet::from([1]));
    parents1.insert(3, HashSet::from([2]));

    let cohort_indices = test_braid.cohort(parents1, None, None);
    assert_eq!(
        cohort_indices,
        vec![
            HashSet::from([0]),
            HashSet::from([1]),
            HashSet::from([2]),
            HashSet::from([3])
        ]
    );
}

#[test]
pub fn test_cohorts_braid_testcases() {
    let ancestors = std::env::current_dir().unwrap();
    let ancestors_directory: Vec<&Path> = ancestors.ancestors().collect();
    let parent_directory = ancestors_directory[1];
    let test_absolute_path = parent_directory.join(test_directory);
    for test_braid_file in std::fs::read_dir(test_absolute_path.as_path()).unwrap() {
        let re = test_braid_file.unwrap().file_name();
        let current_file_name = re.to_str().unwrap();
        let file_path = test_absolute_path.join(current_file_name);
        let (current_file_braid, file_braid) = loading_braid_from_file(file_path.to_str().unwrap());
        let mut current_braid_parents: HashMap<usize, HashSet<usize>> = HashMap::new();
        for beads in file_braid.parents {
            let mut current_bead_parents: HashSet<usize> = HashSet::new();
            for parent_beads in beads.1 {
                current_bead_parents.insert(parent_beads);
            }
            current_braid_parents.insert(beads.0, current_bead_parents);
        }

        let cohort_indices = current_file_braid
            .clone()
            .cohort(current_braid_parents, None, None);

        let mut computed_cohorts: Vec<HashSet<usize>> = Vec::new();
        for cohort in cohort_indices {
            let mut current_cohort_beads: HashSet<usize> = HashSet::new();
            for bead in cohort {
                current_cohort_beads.insert(bead);
            }
            computed_cohorts.push(current_cohort_beads);
        }
        let current_file_cohorts = file_braid.cohorts;
        let mut current_file_cohorts_set_vec: Vec<HashSet<usize>> = Vec::new();
        for cohort in current_file_cohorts {
            let mut current_cohort: HashSet<usize> = HashSet::new();
            for cohort_bead in cohort {
                current_cohort.insert(cohort_bead);
            }
            current_file_cohorts_set_vec.push(current_cohort);
        }
        assert_eq!(computed_cohorts, current_file_cohorts_set_vec);
    }
}
#[test]
pub fn reverse_cohorts_testcases() {
    let ancestors = std::env::current_dir().unwrap();
    let ancestors_directory: Vec<&Path> = ancestors.ancestors().collect();
    let parent_directory = ancestors_directory[1];
    let test_absolute_path = parent_directory.join(test_directory);
    for test_braid_file in std::fs::read_dir(test_absolute_path.as_path()).unwrap() {
        let re = test_braid_file.unwrap().file_name();
        let current_file_name = re.to_str().unwrap();
        let file_path = test_absolute_path.join(current_file_name);
        let (mut current_file_braid, file_braid) =
            loading_braid_from_file(file_path.to_str().unwrap());
        let mut current_braid_parents: HashMap<usize, HashSet<usize>> = HashMap::new();
        for beads in file_braid.parents {
            let mut current_bead_parents: HashSet<usize> = HashSet::new();
            for parent_beads in beads.1 {
                current_bead_parents.insert(parent_beads);
            }
            current_braid_parents.insert(beads.0, current_bead_parents);
        }
        let reversed_beads = current_file_braid.reverse(current_braid_parents.clone());
        let current_braid_cohorts = file_braid.cohorts;

        let computed_val = current_file_braid.cohort(reversed_beads, None, None);
        //TODO:assetion to be done
    }
}
#[test]
pub fn test_highest_work_path_1() {
    let test_bead_0 = emit_bead();
    let mut test_bead_1 = emit_bead();

    let mut test_bead_2 = emit_bead();

    let mut test_bead_3 = emit_bead();

    test_bead_1
        .committed_metadata
        .parents
        .insert(test_bead_0.block_header.block_hash());
    test_bead_2
        .committed_metadata
        .parents
        .insert(test_bead_1.block_header.block_hash());

    test_bead_3
        .committed_metadata
        .parents
        .insert(test_bead_2.block_header.block_hash());

    let mut test_braid = Braid {
        beads: vec![
            test_bead_0.clone(),
            test_bead_1.clone(),
            test_bead_2.clone(),
            test_bead_3.clone(),
        ],
        genesis_beads: HashSet::from([0]),
        tips: HashSet::from([3]),
        orphan_beads: Vec::new(),
        cohorts: vec![Cohort(HashSet::from([0]))],
        bead_index_mapping: std::collections::HashMap::from([
            (test_bead_0.block_header.block_hash(), 0),
            (test_bead_1.block_header.block_hash(), 1),
            (test_bead_2.block_header.block_hash(), 2),
            (test_bead_3.block_header.block_hash(), 3),
        ]),
    };

    //mapping of the indices with set of indices representing its parents
    //where the key represents the ith indexed bead from self.beads which contains all the beads
    //belonging to a particular braid and mapping is a set of indices of its parents present in
    //self.beads
    let mut parents1: HashMap<usize, HashSet<usize>> = HashMap::new();
    parents1.insert(0, HashSet::from([]));
    parents1.insert(1, HashSet::from([0]));
    parents1.insert(2, HashSet::from([1]));
    parents1.insert(3, HashSet::from([2]));
    let test_braid_child_beads = test_braid.reverse(parents1.clone());
    let highest_work_path_bead_indices =
        test_braid.highest_work_path(parents1.clone(), Some(test_braid_child_beads), None);

    assert_eq!(highest_work_path_bead_indices, Vec::from([0, 1, 2, 3]));
}
#[test]
pub fn test_diamond_path_highest_work() {
    let test_bead_0 = emit_bead();
    let mut test_bead_1 = emit_bead();

    let mut test_bead_2 = emit_bead();

    let mut test_bead_3 = emit_bead();

    let mut test_bead_4 = emit_bead();

    test_bead_1
        .committed_metadata
        .parents
        .insert(test_bead_0.block_header.block_hash());
    test_bead_2
        .committed_metadata
        .parents
        .insert(test_bead_0.block_header.block_hash());
    test_bead_3
        .committed_metadata
        .parents
        .insert(test_bead_1.block_header.block_hash());
    test_bead_3
        .committed_metadata
        .parents
        .insert(test_bead_2.block_header.block_hash());
    test_bead_4
        .committed_metadata
        .parents
        .insert(test_bead_3.block_header.block_hash());

    let mut test_braid = Braid {
        beads: vec![
            test_bead_0.clone(),
            test_bead_1.clone(),
            test_bead_2.clone(),
            test_bead_3.clone(),
            test_bead_4.clone(),
        ],
        genesis_beads: HashSet::from([0]),
        tips: HashSet::from([3]),
        orphan_beads: Vec::new(),
        cohorts: vec![Cohort(HashSet::from([0]))],
        bead_index_mapping: std::collections::HashMap::from([
            (test_bead_0.block_header.block_hash(), 0),
            (test_bead_1.block_header.block_hash(), 1),
            (test_bead_2.block_header.block_hash(), 2),
            (test_bead_3.block_header.block_hash(), 3),
            (test_bead_4.block_header.block_hash(), 4),
        ]),
    };
    //mapping of the indices with set of indices representing its parents
    //where the key represents the ith indexed bead from self.beads which contains all the beads
    //belonging to a particular braid and mapping is a set of indices of its parents present in
    //self.beads
    let mut parents1: HashMap<usize, HashSet<usize>> = HashMap::new();
    parents1.insert(0, HashSet::from([]));
    parents1.insert(1, HashSet::from([0]));
    parents1.insert(2, HashSet::from([0]));
    parents1.insert(3, HashSet::from([1, 2]));
    parents1.insert(4, HashSet::from([3]));
    let test_braid_child_mapping = test_braid.reverse(parents1.clone());
    let highest_work_path =
        test_braid.highest_work_path(parents1, Some(test_braid_child_mapping), None);

    assert_eq!(highest_work_path, Vec::from([0, 1, 3, 4]));
}

#[test]
pub fn highest_work_path_testcases_directory() {
    let ancestors = std::env::current_dir().unwrap();
    let ancestors_directory: Vec<&Path> = ancestors.ancestors().collect();
    let parent_directory = ancestors_directory[1];
    let test_absolute_path = parent_directory.join(test_directory);
    for test_braid_file in std::fs::read_dir(test_absolute_path.as_path()).unwrap() {
        let re = test_braid_file.unwrap().file_name();
        let current_file_name = re.to_str().unwrap();
        let file_path = test_absolute_path.join(current_file_name);
        let (mut current_file_braid, file_braid) =
            loading_braid_from_file(file_path.to_str().unwrap());
        let mut current_braid_parents: HashMap<usize, HashSet<usize>> = HashMap::new();
        for beads in file_braid.parents {
            let mut current_bead_parents: HashSet<usize> = HashSet::new();
            for parent_beads in beads.1 {
                current_bead_parents.insert(parent_beads);
            }
            current_braid_parents.insert(beads.0, current_bead_parents);
        }
        let current_braid_children_mapping =
            current_file_braid.reverse(current_braid_parents.clone());
        let highest_work_path = current_file_braid.highest_work_path(
            current_braid_parents,
            Some(current_braid_children_mapping),
            None,
        );
        assert_eq!(highest_work_path, file_braid.highest_work_path);
    }
}

#[test]
pub fn test_check_cohort_files() {
    let ancestors = std::env::current_dir().unwrap();
    let ancestors_directory: Vec<&Path> = ancestors.ancestors().collect();
    let parent_directory = ancestors_directory[1];
    let test_absolute_path = parent_directory.join(test_directory);
    for test_braid_file in std::fs::read_dir(test_absolute_path.as_path()).unwrap() {
        let re = test_braid_file.unwrap().file_name();
        let current_file_name = re.to_str().unwrap();
        let file_path = test_absolute_path.join(current_file_name);

        let (mut current_file_braid, file_braid) =
            loading_braid_from_file(file_path.to_str().unwrap());
        let mut current_braid_parents: HashMap<usize, HashSet<usize>> = HashMap::new();
        for beads in file_braid.parents {
            let mut current_bead_parents: HashSet<usize> = HashSet::new();
            for parent_beads in beads.1 {
                current_bead_parents.insert(parent_beads);
            }
            current_braid_parents.insert(beads.0, current_bead_parents);
        }
        let current_braid_children_mapping =
            current_file_braid.reverse(current_braid_parents.clone());
        let current_braid_cohorts = file_braid.cohorts;
        for cohort in current_braid_cohorts {
            let mut cohort_set: HashSet<usize> = HashSet::new();
            for bead in cohort.clone() {
                cohort_set.insert(bead);
            }
            let result = current_file_braid.check_cohort(
                cohort_set,
                current_braid_parents.clone(),
                Some(current_braid_children_mapping.clone()),
            );
            assert_eq!(result, true);
        }
    }
}
#[test]
pub fn test_sub_braids() {
    let ancestors = std::env::current_dir().unwrap();
    let ancestors_directory: Vec<&Path> = ancestors.ancestors().collect();
    let parent_directory = ancestors_directory[1];
    let test_absolute_path = parent_directory.join(test_directory);
    for test_braid_file in std::fs::read_dir(test_absolute_path.as_path()).unwrap() {
        let re = test_braid_file.unwrap().file_name();
        let current_file_name = re.to_str().unwrap();
        let file_path = test_absolute_path.join(current_file_name);

        let (mut current_file_braid, file_braid) =
            loading_braid_from_file(file_path.to_str().unwrap());
        let mut current_braid_parents: HashMap<usize, HashSet<usize>> = HashMap::new();
        for beads in file_braid.parents {
            let mut current_bead_parents: HashSet<usize> = HashSet::new();
            for parent_beads in beads.1 {
                current_bead_parents.insert(parent_beads);
            }
            current_braid_parents.insert(beads.0, current_bead_parents);
        }
        let current_braid_children_mapping =
            current_file_braid.reverse(current_braid_parents.clone());
        let current_braid_cohorts = file_braid.cohorts;
        for cohort in current_braid_cohorts {
            let mut cohort_set: HashSet<usize> = HashSet::new();
            for bead in cohort.clone() {
                cohort_set.insert(bead);
            }
            let sub_braid =
                current_file_braid.get_sub_braid(cohort_set.clone(), current_braid_parents.clone());
            let gen = current_file_braid.genesis(sub_braid.clone());
            let curr_cohort_head = current_file_braid.cohort_head(
                cohort_set.clone(),
                current_braid_parents.clone(),
                Some(current_braid_children_mapping.clone()),
            );
            assert_eq!(gen, curr_cohort_head);

            let curr_cohort_tips = current_file_braid.tips(sub_braid.clone());
            let curr_cohort_tail = current_file_braid.cohort_tail(
                cohort_set,
                current_braid_parents.clone(),
                Some(current_braid_children_mapping.clone()),
            );
            assert_eq!(curr_cohort_tail, curr_cohort_tips);
        }
    }
}
#[test]
pub fn test_cohort_tail_braids() {
    let ancestors = std::env::current_dir().unwrap();
    let ancestors_directory: Vec<&Path> = ancestors.ancestors().collect();
    let parent_directory = ancestors_directory[1];
    let test_absolute_path = parent_directory.join(test_directory);
    for test_braid_file in std::fs::read_dir(test_absolute_path.as_path()).unwrap() {
        let re = test_braid_file.unwrap().file_name();
        let current_file_name = re.to_str().unwrap();
        let file_path = test_absolute_path.join(current_file_name);

        let (mut current_file_braid, file_braid) =
            loading_braid_from_file(file_path.to_str().unwrap());
        let mut current_braid_parents: HashMap<usize, HashSet<usize>> = HashMap::new();
        for beads in file_braid.parents {
            let mut current_bead_parents: HashSet<usize> = HashSet::new();
            for parent_beads in beads.1 {
                current_bead_parents.insert(parent_beads);
            }
            current_braid_parents.insert(beads.0, current_bead_parents);
        }
        let current_braid_children_mapping =
            current_file_braid.reverse(current_braid_parents.clone());
        let current_braid_cohorts = file_braid.cohorts;
        for cohort in current_braid_cohorts {
            let mut cohort_set: HashSet<usize> = HashSet::new();
            for bead in cohort.clone() {
                cohort_set.insert(bead);
            }
            let a = current_file_braid.cohort_tail(
                cohort_set.clone(),
                current_braid_parents.clone(),
                Some(current_braid_children_mapping.clone()),
            );
            let b =
                current_file_braid.get_sub_braid(cohort_set.clone(), current_braid_parents.clone());

            let c = current_file_braid.tips(b);
            assert_eq!(a, c);
        }
    }
}
#[test]
pub fn test_cohort_head_braids() {
    let ancestors = std::env::current_dir().unwrap();
    let ancestors_directory: Vec<&Path> = ancestors.ancestors().collect();
    let parent_directory = ancestors_directory[1];
    let test_absolute_path = parent_directory.join(test_directory);
    for test_braid_file in std::fs::read_dir(test_absolute_path.as_path()).unwrap() {
        let re = test_braid_file.unwrap().file_name();
        let current_file_name = re.to_str().unwrap();
        let file_path = test_absolute_path.join(current_file_name);

        let (mut current_file_braid, file_braid) =
            loading_braid_from_file(file_path.to_str().unwrap());
        let mut current_braid_parents: HashMap<usize, HashSet<usize>> = HashMap::new();
        for beads in file_braid.parents {
            let mut current_bead_parents: HashSet<usize> = HashSet::new();
            for parent_beads in beads.1 {
                current_bead_parents.insert(parent_beads);
            }
            current_braid_parents.insert(beads.0, current_bead_parents);
        }
        let current_braid_children_mapping =
            current_file_braid.reverse(current_braid_parents.clone());
        let current_braid_cohorts = file_braid.cohorts;
        for cohort in current_braid_cohorts {
            let mut cohort_set: HashSet<usize> = HashSet::new();
            for bead in cohort.clone() {
                cohort_set.insert(bead);
            }
            let c = current_file_braid.cohort_head(
                cohort_set.clone(),
                current_braid_parents.clone(),
                Some(current_braid_children_mapping.clone()),
            );
            let d =
                current_file_braid.get_sub_braid(cohort_set.clone(), current_braid_parents.clone());
            let e = current_file_braid.genesis(d);
            assert_eq!(e, c);
        }
    }
}
#[test]
pub fn test_check_work_files() {
    let ancestors = std::env::current_dir().unwrap();
    let ancestors_directory: Vec<&Path> = ancestors.ancestors().collect();
    let parent_directory = ancestors_directory[1];
    let test_absolute_path = parent_directory.join(test_directory);
    for test_braid_file in std::fs::read_dir(test_absolute_path.as_path()).unwrap() {
        let re = test_braid_file.unwrap().file_name();
        let current_file_name = re.to_str().unwrap();
        let file_path = test_absolute_path.join(current_file_name);

        let (mut current_file_braid, file_braid) =
            loading_braid_from_file(file_path.to_str().unwrap());
        let mut current_braid_parents: HashMap<usize, HashSet<usize>> = HashMap::new();
        for beads in file_braid.parents {
            let mut current_bead_parents: HashSet<usize> = HashSet::new();
            for parent_beads in beads.1 {
                current_bead_parents.insert(parent_beads);
            }
            current_braid_parents.insert(beads.0, current_bead_parents);
        }
        let current_braid_children_mapping =
            current_file_braid.reverse(current_braid_parents.clone());
        let current_braid_cohorts = file_braid.cohorts;
        let current_dag_braid_work = file_braid.work.clone();
        for cohort in current_braid_cohorts {
            let mut cohort_set: HashSet<usize> = HashSet::new();
            for bead in cohort.clone() {
                cohort_set.insert(bead);
            }
            let current_file_braid_bead_work = file_braid.bead_work.clone();
            let current_cohort_descendant_work = current_file_braid.descendant_work(
                current_braid_parents.clone(),
                Some(current_braid_children_mapping.clone()),
                Some(current_file_braid_bead_work),
                None,
            );
            assert_eq!(current_cohort_descendant_work, current_dag_braid_work);
        }
    }
}
