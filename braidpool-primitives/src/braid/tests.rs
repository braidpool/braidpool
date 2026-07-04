use std::collections::HashSet;
use std::net::{IpAddr, Ipv4Addr, SocketAddr};
use std::str::FromStr;

use bitcoin::absolute::Time;
use bitcoin::address::NetworkChecked;
use bitcoin::ecdsa::Signature;
use bitcoin::secp256k1::PublicKey;
use bitcoin::{
    Address, BlockHash, BlockHeader, BlockTime, BlockVersion, CompactTarget, EcdsaSighashType,
    Network, TxMerkleNode,
};
use secp256k1::{Secp256k1, SecretKey};

use crate::bead::{Bead, CommittedMetadata, UnCommittedMetadata};
use crate::utils::BeadHash;

use super::{AddBeadStatus, Braid};

fn create_test_bead(parents: HashSet<BeadHash>, nonce: u32) -> Bead {
    let address: Address = Address::from_str("32iVBEu4dxkUQk9dJbZUiBiQdmypcEyJRf")
        .unwrap()
        .require_network(Network::Bitcoin)
        .unwrap();
    let secp = Secp256k1::new();
    let secret_key = SecretKey::from_slice(&[0xcd; 32]).expect("32 bytes, within curve order");
    let public_key = PublicKey::from_secret_key(&secp, &secret_key);
    let socket_addr = SocketAddr::new(IpAddr::V4(Ipv4Addr::new(127, 0, 0, 1)), 8080);

    let committed = CommittedMetadata {
        transaction_cnt: 0,
        parents,
        transactions: vec![],
        payout_address: address,
        comm_pub_key: public_key,
        observed_time_at_node: Time::from_consensus(1653195600).unwrap(),
        miner_ip: socket_addr,
    };

    let sig_hex = "3046022100839c1fbc5304de944f697c9f4b1d01d1faeba32d751c0f7acb21ac8a0f436a72022100e89bd46bb3a5a62adc679f659b7ce876d83ee297c7a5587b2011c4fcc72eab45";
    let sig = Signature {
        signature: secp256k1::ecdsa::Signature::from_str(sig_hex).unwrap(),
        sighash_type: EcdsaSighashType::All,
    };

    let uncommitted = UnCommittedMetadata {
        extra_nonce: 12,
        broadcast_timestamp: Time::from_consensus(1653195600).unwrap(),
        signature: sig,
        parent_bead_timestamps: HashSet::new(),
    };

    let zero_bytes = [0u8; 32];
    Bead {
        block_header: BlockHeader {
            version: BlockVersion::TWO,
            prev_blockhash: BlockHash::from_byte_array(zero_bytes),
            bits: CompactTarget::from_consensus(32),
            nonce,
            time: BlockTime::from_u32(8328429),
            merkle_root: TxMerkleNode::from_byte_array(zero_bytes),
        },
        committed_metadata: committed,
        uncommitted_metadata: uncommitted,
    }
}

#[test]
fn test_new_braid_initializes_with_genesis_hashes() {
    let genesis_hash = BlockHash::from_byte_array([0u8; 32]);
    let mut genesis_set = HashSet::new();
    genesis_set.insert(genesis_hash);

    let braid = Braid::new(genesis_set.clone());

    assert!(
        braid.tips.contains(&genesis_hash),
        "genesis hash should be in tips"
    );
}

#[test]
fn test_add_genesis_bead_inserts_into_beads_and_tips() {
    let genesis_hash = BlockHash::from_byte_array([0u8; 32]);
    let mut genesis_set = HashSet::new();
    genesis_set.insert(genesis_hash);

    let mut braid = Braid::new(genesis_set);

    let bead = create_test_bead(HashSet::new(), 1);
    let expected_hash = bead.block_header.block_hash();

    let status = braid.add_bead(bead);

    assert!(
        matches!(status, AddBeadStatus::BeadAdded),
        "genesis bead should be added successfully"
    );
    assert!(
        braid.beads.contains(&expected_hash),
        "bead hash should be in beads set"
    );
    assert!(
        braid.tips.contains(&expected_hash),
        "bead hash should be in tips set"
    );
}

#[test]
fn test_add_child_bead_with_existing_parent() {
    let genesis_hash = BlockHash::from_byte_array([0u8; 32]);
    let mut genesis_set = HashSet::new();
    genesis_set.insert(genesis_hash);

    let mut braid = Braid::new(genesis_set);

    let genesis_bead = create_test_bead(HashSet::new(), 1);
    let genesis_bead_hash = genesis_bead.block_header.block_hash();
    braid.add_bead(genesis_bead);

    let mut child_parents = HashSet::new();
    child_parents.insert(genesis_bead_hash);
    let child_bead = create_test_bead(child_parents, 2);
    let child_bead_hash = child_bead.block_header.block_hash();

    let status = braid.add_bead(child_bead);

    assert!(
        matches!(status, AddBeadStatus::BeadAdded),
        "child bead with existing parent should be added"
    );
    assert!(
        braid.beads.contains(&child_bead_hash),
        "child bead hash should be in beads set"
    );
    assert!(
        braid.tips.contains(&child_bead_hash),
        "child bead should be a tip"
    );
    assert!(
        !braid.tips.contains(&genesis_bead_hash),
        "genesis bead should no longer be a tip after having a child"
    );
}

#[test]
fn test_add_orphan_bead_returns_parents_not_yet_received() {
    let genesis_hash = BlockHash::from_byte_array([0u8; 32]);
    let mut genesis_set = HashSet::new();
    genesis_set.insert(genesis_hash);

    let mut braid = Braid::new(genesis_set);

    let unknown_parent = BlockHash::from_byte_array([0xaa; 32]);
    let mut orphan_parents = HashSet::new();
    orphan_parents.insert(unknown_parent);
    let orphan_bead = create_test_bead(orphan_parents, 1);

    let status = braid.add_bead(orphan_bead);

    assert!(
        matches!(status, AddBeadStatus::ParentsNotYetReceived),
        "orphan bead should be rejected"
    );
}

#[test]
fn test_add_duplicate_bead_returns_dag_already_contains_bead() {
    let genesis_hash = BlockHash::from_byte_array([0u8; 32]);
    let mut genesis_set = HashSet::new();
    genesis_set.insert(genesis_hash);

    let mut braid = Braid::new(genesis_set);

    let bead = create_test_bead(HashSet::new(), 1);
    let first_status = braid.add_bead(bead);

    assert!(
        matches!(first_status, AddBeadStatus::BeadAdded),
        "first addition should succeed"
    );

    let duplicate_bead = create_test_bead(HashSet::new(), 1);
    let second_status = braid.add_bead(duplicate_bead);

    assert!(
        matches!(second_status, AddBeadStatus::DagAlreadyContainsBead),
        "duplicate bead should be rejected"
    );
}

#[test]
fn test_orphan_bead_adopted_when_parent_added() {
    let genesis_hash = BlockHash::from_byte_array([0u8; 32]);
    let mut genesis_set = HashSet::new();
    genesis_set.insert(genesis_hash);

    let mut braid = Braid::new(genesis_set);

    let genesis_bead = create_test_bead(HashSet::new(), 1);
    let genesis_bead_hash = genesis_bead.block_header.block_hash();
    braid.add_bead(genesis_bead);

    let intermediate = create_test_bead(
        {
            let mut p = HashSet::new();
            p.insert(genesis_bead_hash);
            p
        },
        2,
    );
    let intermediate_hash = intermediate.block_header.block_hash();
    braid.add_bead(intermediate);

    let mut unknown_parent = HashSet::new();
    unknown_parent.insert(BlockHash::from_byte_array([0xbb; 32]));
    let nested_orphan = create_test_bead(unknown_parent, 3);
    braid.add_bead(nested_orphan);

    let mut intermediate_parents = HashSet::new();
    intermediate_parents.insert(intermediate_hash);
    let child_of_intermediate = create_test_bead(intermediate_parents, 4);

    let status = braid.add_bead(child_of_intermediate);

    assert!(
        matches!(status, AddBeadStatus::BeadAdded),
        "child of intermediate should be added after intermediate is in braid"
    );
    assert_eq!(
        braid.orphan_beads.len(),
        1,
        "only the nested orphan should remain orphaned"
    );
}

#[test]
fn test_multiple_children_same_parent() {
    let genesis_hash = BlockHash::from_byte_array([0u8; 32]);
    let mut genesis_set = HashSet::new();
    genesis_set.insert(genesis_hash);

    let mut braid = Braid::new(genesis_set);

    let genesis_bead = create_test_bead(HashSet::new(), 1);
    let genesis_bead_hash = genesis_bead.block_header.block_hash();
    braid.add_bead(genesis_bead);

    let child1 = create_test_bead(
        {
            let mut p = HashSet::new();
            p.insert(genesis_bead_hash);
            p
        },
        2,
    );
    let child1_hash = child1.block_header.block_hash();
    braid.add_bead(child1);

    let child2 = create_test_bead(
        {
            let mut p = HashSet::new();
            p.insert(genesis_bead_hash);
            p
        },
        3,
    );
    let child2_hash = child2.block_header.block_hash();
    let status = braid.add_bead(child2);

    assert!(
        matches!(status, AddBeadStatus::BeadAdded),
        "second child of same parent should be added"
    );
    assert!(
        braid.beads.contains(&child1_hash),
        "first child should be in beads"
    );
    assert!(
        braid.beads.contains(&child2_hash),
        "second child should be in beads"
    );
    assert!(
        braid.tips.contains(&child1_hash),
        "first child should be a tip"
    );
    assert!(
        braid.tips.contains(&child2_hash),
        "second child should be a tip"
    );
    assert!(
        !braid.tips.contains(&genesis_bead_hash),
        "genesis should not be a tip after having children"
    );
}
