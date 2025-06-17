use super::BraidPoolBehaviourEvent as BraidPoolEvent;
use super::*;
use crate::bead::{Bead, BeadResponse};
use crate::utils::test_utils::test_utility_functions::{
    Signature, TestCommittedMetadataBuilder, TestUnCommittedMetadataBuilder, Time, TimeVec,
};
use bitcoin::p2p::address::Address as P2P_Address;
use bitcoin::p2p::ServiceFlags;
use bitcoin::BlockVersion;
use bitcoin::CompactTarget;
use bitcoin::{BlockHash, BlockHeader, BlockTime, EcdsaSighashType, TxMerkleNode};
use futures::StreamExt;
use libp2p::Multiaddr;
use libp2p::{identity, swarm::SwarmEvent};
use std::collections::HashSet;
use std::net::{IpAddr, Ipv4Addr, SocketAddr};
use std::str::FromStr;
use tokio::time::timeout;

// Helper function to create a test bead
fn create_test_bead() -> Bead {
    let test_sock_add = SocketAddr::new(IpAddr::V4(Ipv4Addr::new(127, 0, 0, 1)), 8888);
    let _address = P2P_Address::new(&test_sock_add.clone(), ServiceFlags::NONE);
    let public_key = "020202020202020202020202020202020202020202020202020202020202020202"
        .parse::<bitcoin::PublicKey>()
        .unwrap();
    let socket = bitcoin::p2p::address::AddrV2::Ipv4(Ipv4Addr::new(127, 0, 0, 1));
    let time_hash_set = TimeVec(Vec::new());
    let parent_hash_set: HashSet<BlockHash> = HashSet::new();
    let weak_target = CompactTarget::from_consensus(32);
    let min_target = CompactTarget::from_consensus(1);
    let time_val = Time::from_consensus(1653195600).unwrap();
    let test_committed_metadata = TestCommittedMetadataBuilder::new()
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
    let extra_nonce = 42;
    let hex = "3046022100839c1fbc5304de944f697c9f4b1d01d1faeba32d751c0f7acb21ac8a0f436a72022100e89bd46bb3a5a62adc679f659b7ce876d83ee297c7a5587b2011c4fcc72eab45";
    let sig = Signature {
        signature: secp256k1::ecdsa::Signature::from_str(hex).unwrap(),
        sighash_type: EcdsaSighashType::All,
    };
    let test_uncommitted_metadata = TestUnCommittedMetadataBuilder::new()
        .broadcast_timestamp(time_val)
        .extra_nonce(extra_nonce)
        .signature(sig)
        .build();
    let test_bytes: [u8; 32] = [0u8; 32];
    let test_block_header = BlockHeader {
        version: BlockVersion::TWO,
        prev_blockhash: BlockHash::from_byte_array(test_bytes),
        bits: CompactTarget::from_consensus(32),
        nonce: 1,
        time: BlockTime::from_u32(8328429),
        merkle_root: TxMerkleNode::from_byte_array(test_bytes),
    };
    Bead {
        block_header: test_block_header,
        committed_metadata: test_committed_metadata,
        uncommitted_metadata: test_uncommitted_metadata,
    }
}

#[tokio::test]
async fn test_bead_request_handling() {
    // Create two nodes with different keypairs
    let key1 = identity::Keypair::generate_ed25519();
    let key2 = identity::Keypair::generate_ed25519();

    let mut swarm1 = libp2p::SwarmBuilder::with_existing_identity(key1.clone())
        .with_tokio()
        .with_quic()
        .with_behaviour(|_| BraidPoolBehaviour::new(&key1).unwrap())
        .unwrap()
        .build();

    let mut swarm2 = libp2p::SwarmBuilder::with_existing_identity(key2.clone())
        .with_tokio()
        .with_quic()
        .with_behaviour(|_| BraidPoolBehaviour::new(&key2).unwrap())
        .unwrap()
        .build();

    // Listen on random ports
    swarm1
        .listen_on("/ip4/127.0.0.1/udp/5000/quic-v1".parse().unwrap())
        .unwrap();
    swarm2
        .listen_on("/ip4/127.0.0.1/udp/6000/quic-v1".parse().unwrap())
        .unwrap();

    // Wait for swarm1 to start listening
    let mut addr = Multiaddr::empty();
    let timeout_duration = Duration::from_secs(5);
    let mut listening_established = false;
    while !listening_established {
        match timeout(timeout_duration, swarm1.next()).await {
            Ok(Some(SwarmEvent::NewListenAddr { address, .. })) => {
                addr = address;
                listening_established = true;
            }
            Ok(Some(_)) => {} // Ignore other events
            Ok(None) => break,
            Err(_) => panic!("Test timed out waiting for swarm1 to listen"),
        }
    }

    // Wait for swarm2 to start listening
    let mut swarm2_listening = false;
    while !swarm2_listening {
        match timeout(timeout_duration, swarm2.next()).await {
            Ok(Some(SwarmEvent::NewListenAddr { address: _, .. })) => {
                swarm2_listening = true;
            }
            Ok(Some(_)) => {} // Ignore other events
            Ok(None) => break,
            Err(_) => panic!("Test timed out waiting for swarm2 to listen"),
        }
    }

    println!("Swarm1 listening on: {}", addr);
    println!(
        "Swarm2 listening on: {}",
        swarm2.listeners().next().unwrap()
    );
    println!("Swarm1 local peer ID: {}", swarm1.local_peer_id());
    let local_peer_id = swarm1.local_peer_id().clone();
    // Connect swarm2 to swarm1
    let test_bead = create_test_bead();
    let bead_hash = test_bead.block_header.block_hash();
    swarm2.dial(addr.clone()).unwrap();
    // wait for connection to be established

    println!("Swarm2 dialed swarm1 at: {}", addr);
    // Process events until we get a response or timeout
    println!("Swarm2: Requesting beads with hashes: {:?}", bead_hash);

    // swarm1 event loop
    let swarm1_handle = tokio::spawn(async move {
        let mut swarm = swarm1;
        loop {
            match swarm.next().await {
                Some(SwarmEvent::ConnectionEstablished { peer_id, .. }) => {
                    println!("Swarm1: Connection established with {}", peer_id);
                }
                Some(SwarmEvent::IncomingConnection { .. }) => {
                    println!("Swarm1: Incoming connection");
                }
                Some(SwarmEvent::Behaviour(BraidPoolEvent::BeadSync(event))) => {
                    println!("Swarm1: BeadSync event received: {:?}", event);
                    match event {
                        request_response::Event::Message {
                            peer,
                            connection_id: _,
                            message,
                        } => {
                            if let request_response::Message::Request {
                                request_id: _,
                                request,
                                channel,
                            } = message
                            {
                                if let BeadRequest::GetBeads(hashes) = request {
                                    println!(
                                        "Swarm1: Received bead request from {} with hashes: {:?}",
                                        peer, hashes
                                    );
                                    assert_eq!(hashes.len(), 1);
                                    assert_eq!(hashes.iter().next().unwrap(), &bead_hash);
                                    // Respond with an error for now
                                    swarm
                                        .behaviour_mut()
                                        .bead_sync
                                        .send_response(
                                            channel,
                                            BeadResponse::Error(
                                                "Bead retrieval not implemented yet".to_string(),
                                            ),
                                        )
                                        .unwrap();
                                }
                            }
                        }
                        other => {
                            println!("Swarm1: Other event: {:?}", other);
                        }
                    }
                }
                Some(_) => {} // Ignore other events
                None => break,
            }
        }
        swarm
    });

    // swarm2 event loop
    let swarm2_handle = tokio::spawn(async move {
        let mut swarm = swarm2;
        loop {
            match swarm.next().await {
                Some(SwarmEvent::ConnectionEstablished { peer_id, .. }) => {
                    println!("Swarm2: Connection established with {}", peer_id);
                    let mut hashes = HashSet::new();
                    hashes.insert(bead_hash);
                    swarm.behaviour_mut().request_beads(local_peer_id, hashes);
                }
                Some(SwarmEvent::IncomingConnection { .. }) => {
                    println!("Swarm2: Incoming connection");
                }
                Some(SwarmEvent::Behaviour(BraidPoolEvent::BeadSync(event))) => {
                    println!("Swarm2: BeadSync event received: {:?}", event);
                    match event {
                        request_response::Event::Message {
                            peer,
                            connection_id: _,
                            message,
                        } => {
                            match message {
                                // Handle bead request
                                request_response::Message::Request {
                                    request_id: _,
                                    request,
                                    channel,
                                } => {
                                    if let BeadRequest::GetBeads(hashes) = request {
                                        println!("Swarm2: Received bead request from {} with hashes: {:?}", peer, hashes);
                                        // Respond with an error for now
                                        swarm
                                            .behaviour_mut()
                                            .bead_sync
                                            .send_response(
                                                channel,
                                                BeadResponse::Error(
                                                    "Bead retrieval not implemented yet"
                                                        .to_string(),
                                                ),
                                            )
                                            .unwrap();
                                    }
                                }
                                // Handle bead response
                                request_response::Message::Response {
                                    request_id: _,
                                    response,
                                } => {
                                    if let BeadResponse::Error(error) = response {
                                        println!("Swarm2: Received error response: {}", error);
                                        assert_eq!(error, "Bead retrieval not implemented yet");
                                        break;
                                    } else if let BeadResponse::Beads(beads) = response {
                                        println!("Swarm2: Received beads: {:?}", beads);
                                        assert_eq!(beads.len(), 1);
                                        assert_eq!(beads[0].block_header.block_hash(), bead_hash);
                                    }
                                }
                            }
                        }
                        other => {
                            println!("Swarm2: Other event: {:?}", other);
                        }
                    }
                }
                Some(_) => {} // Ignore other events
                None => break,
            }
        }
        swarm
    });

    _ = tokio::time::timeout(
        tokio::time::Duration::from_secs(10),
        futures::future::join_all(vec![swarm1_handle, swarm2_handle]),
    )
    .await;
}
