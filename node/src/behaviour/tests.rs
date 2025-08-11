use super::BraidPoolBehaviourEvent as BraidPoolEvent;
use super::*;
use crate::bead::{Bead, BeadResponse};
use crate::utils::test_utils::test_utility_functions::{
    Signature, TestCommittedMetadataBuilder, TestUnCommittedMetadataBuilder, Time, TimeVec,
};
use bitcoin::consensus::encode::deserialize;
use bitcoin::consensus::serialize;
use bitcoin::BlockVersion;
use bitcoin::CompactTarget;
use bitcoin::{BlockHash, BlockHeader, BlockTime, EcdsaSighashType, TxMerkleNode};
use futures::StreamExt;
use libp2p::floodsub::Topic;
use libp2p::swarm::SwarmEvent;
use libp2p::{Multiaddr, Swarm, SwarmBuilder};
use std::collections::HashSet;
use std::str::FromStr;
use tokio::time::timeout;

// Helper function to create a test bead
fn create_test_bead() -> Bead {
    let _address = String::from("127.0.0.1:8888");
    let public_key = "020202020202020202020202020202020202020202020202020202020202020202"
        .parse::<bitcoin::PublicKey>()
        .unwrap();
    let socket = String::from("127.0.0.1");
    let time_hash_set = TimeVec(Vec::new());
    let parent_hash_set: HashSet<BlockHash> = HashSet::new();
    let weak_target = CompactTarget::from_consensus(486604799);
    let min_target = CompactTarget::from_consensus(486604799);
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
    let extra_nonce_1 = 42;
    let extra_nonce_2 = 42;

    let hex = "3046022100839c1fbc5304de944f697c9f4b1d01d1faeba32d751c0f7acb21ac8a0f436a72022100e89bd46bb3a5a62adc679f659b7ce876d83ee297c7a5587b2011c4fcc72eab45";
    let sig = Signature {
        signature: secp256k1::ecdsa::Signature::from_str(hex).unwrap(),
        sighash_type: EcdsaSighashType::All,
    };
    let test_uncommitted_metadata = TestUnCommittedMetadataBuilder::new()
        .broadcast_timestamp(time_val)
        .extra_nonce(extra_nonce_1, extra_nonce_2)
        .signature(sig)
        .build();
    let test_bytes: [u8; 32] = [0u8; 32];
    let test_block_header = BlockHeader {
        version: BlockVersion::TWO,
        prev_blockhash: BlockHash::from_byte_array(test_bytes),
        bits: CompactTarget::from_consensus(486604799),
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
fn build_swarm() -> (Swarm<BraidPoolBehaviour>, PeerId) {
    let key = Keypair::generate_ed25519();
    let peer_id = PeerId::from(key.public());
    let swarm = SwarmBuilder::with_existing_identity(key)
        .with_tokio()
        .with_quic()
        .with_dns()
        .unwrap()
        .with_behaviour(|local_key| BraidPoolBehaviour::new(local_key).unwrap())
        .unwrap()
        .build();
    (swarm, peer_id)
}

#[tokio::test]
async fn test_bead_request_handling() {
    let mut swarm1 = build_swarm().0;

    let mut swarm2 = build_swarm().0;

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
            Ok(Some(event)) => {
                println!("{:?}", event);
            } // Ignore other events
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
            Ok(Some(event)) => {
                println!("{:?}", event);
            } // Ignore other events
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
                                            BeadResponse::Error(BeadSyncError::Other(
                                                "Bead retrieval not implemented yet".to_string(),
                                            )),
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
                                                BeadResponse::Error(BeadSyncError::Other(
                                                    "Bead retrieval not implemented yet"
                                                        .to_string(),
                                                )),
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
                                        println!("Swarm2: Received error response: {:?}", error);
                                        assert_eq!(
                                            error,
                                            BeadSyncError::Other(String::from(
                                                "Bead retrieval not implemented yet"
                                            ))
                                        );
                                        break;
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

#[tokio::test]
async fn test_floodsub_message_propagation() {
    let mut swarm1 = build_swarm().0;

    let mut swarm2 = build_swarm().0;

    swarm1
        .listen_on("/ip4/127.0.0.1/udp/5001/quic-v1".parse().unwrap())
        .unwrap();
    swarm2
        .listen_on("/ip4/127.0.0.1/udp/6001/quic-v1".parse().unwrap())
        .unwrap();

    let mut addr = Multiaddr::empty();
    let timeout_duration = Duration::from_secs(5);
    let mut listening_established = false;
    while !listening_established {
        match timeout(timeout_duration, swarm1.next()).await {
            Ok(Some(SwarmEvent::NewListenAddr { address, .. })) => {
                addr = address;
                listening_established = true;
            }
            Ok(Some(event)) => {
                println!("{:?}", event);
            }
            Ok(None) => break,
            Err(_) => panic!("Test timed out waiting for swarm1 to listen"),
        }
    }

    let mut swarm2_listening = false;
    while !swarm2_listening {
        match timeout(timeout_duration, swarm2.next()).await {
            Ok(Some(SwarmEvent::NewListenAddr { address: _, .. })) => {
                swarm2_listening = true;
            }
            Ok(Some(event)) => {
                println!("{:?}", event);
            }
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
    // Connect swarm2 to swarm1
    let test_bead = create_test_bead();
    let test_bead_ref = test_bead.clone();
    let bead_hash = test_bead.block_header.block_hash();

    let topic = Topic::new("test");
    swarm1
        .behaviour_mut()
        .bead_announce
        .subscribe(topic.clone());
    swarm2
        .behaviour_mut()
        .bead_announce
        .subscribe(topic.clone());

    swarm2.dial(addr.clone()).unwrap();

    println!("Swarm2 dialed swarm1 at: {}", addr);
    // Process events until we get a response or timeout
    println!("Swarm2: Requesting beads with hashes: {:?}", bead_hash);
    swarm1
        .behaviour_mut()
        .bead_announce
        .add_node_to_partial_view(*swarm2.local_peer_id());
    swarm2
        .behaviour_mut()
        .bead_announce
        .add_node_to_partial_view(*swarm1.local_peer_id());
    let (tx, mut rx) = tokio::sync::mpsc::channel::<Vec<u8>>(100);
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
                Some(SwarmEvent::Behaviour(BraidPoolBehaviourEvent::BeadAnnounce(
                    floodsub::FloodsubEvent::Subscribed { peer_id, topic },
                ))) => {
                    println!("A peer {:?} subscribed to the topic {:?}", peer_id, topic);
                }
                Some(SwarmEvent::Behaviour(BraidPoolBehaviourEvent::BeadAnnounce(
                    floodsub::FloodsubEvent::Message(msg),
                ))) => {
                    println!(
                        "Bead succesfully received from a peer with peer id {:?} from topic {:?}",
                        msg.source, topic
                    );
                    let res = tx.send(msg.data.to_ascii_lowercase()).await;
                    match res {
                        Ok(_) => {
                            println!("Bead succesfully sent to the main thread reciever");
                        }
                        Err(error) => {
                            println!(
                                "An error occurred while sending bead to the main thread receiver -- {:?}",error
                            );
                        }
                    }
                }
                Some(_) => {}
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
                }
                Some(SwarmEvent::Behaviour(BraidPoolBehaviourEvent::BeadAnnounce(
                    floodsub::FloodsubEvent::Subscribed { topic, .. },
                ))) => {
                    println!("Sent bead to other peers");
                    swarm
                        .behaviour_mut()
                        .bead_announce
                        .publish(topic.clone(), serialize(&test_bead));
                }
                Some(SwarmEvent::IncomingConnection { .. }) => {
                    println!("Swarm2: Incoming connection");
                }

                Some(_) => {}
                None => break,
            }
        }
        swarm
    });

    let result = rx.recv().await.unwrap();
    let received_bead: Result<Bead, bitcoin::consensus::DeserializeError> = deserialize(&result);
    assert_eq!(
        received_bead.unwrap().block_header.block_hash(),
        test_bead_ref.clone().block_header.block_hash()
    );
    _ = tokio::time::timeout(
        tokio::time::Duration::from_secs(20),
        futures::future::join_all(vec![swarm1_handle, swarm2_handle]),
    )
    .await;
}
