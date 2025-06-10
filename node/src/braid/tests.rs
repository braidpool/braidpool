use super::Bead;
use super::Braid;
use crate::braid::Cohort;
use crate::committed_metadata::TimeVec;
use crate::utils::test_utils::test_utility_functions::*;
use bitcoin::{
    absolute::Time,
    ecdsa::Signature,
    p2p::{Address as P2P_Address, ServiceFlags},
    BlockHash, BlockHeader, BlockTime, BlockVersion, CompactTarget, EcdsaSighashType, PublicKey,
    TxMerkleNode,
};
use core::net::SocketAddr;
use rand::{rngs::OsRng, thread_rng, RngCore};
use secp256k1::{Message, Secp256k1, SecretKey};
use std::collections::HashSet;
use std::net::{IpAddr, Ipv4Addr};
use std::str::FromStr;

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
