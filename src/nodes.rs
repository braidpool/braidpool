// Standard Imports
use std::collections::{VecDeque, HashSet};

// Custom Imports
use crate::braid::DagBraid;
use crate::utils::bitcoin::CompactTarget;
use crate::utils::Time;
use crate::beads::{MiningBead, NetworkBead};

// Type Definitions for Rust Safety
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct NodeIdentifier(usize);

#[derive(Debug, Clone, Copy, PartialEq)]
pub struct HashRate(f64);

#[derive(Debug, Clone, Copy, PartialEq)]
pub struct NetworkLatency(f64);

#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Location {
    latitude: f64,
    longitude: f64
}

#[derive(Debug)]
pub struct Salt([u64; 4]);

pub struct PeerConnection<'node_lifetime> {
    peer: &'node_lifetime Node<'node_lifetime>,
    latency: NetworkLatency
}
pub struct Node<'node_lifetime> {
    node_identifier: NodeIdentifier,
    hash_rate: HashRate,
    dag_braid: DagBraid<'node_lifetime>,
    lower_mining_target: CompactTarget,
    location: Location,
    node_salt: Salt,
    current_bead_being_mined: MiningBead,
    incoming_network_beads: VecDeque<NetworkBead>,
    peers: Vec<PeerConnection<'node_lifetime>>,
    difficulty_adjusting_algorithm: DifficultyAdjustingAlgorithm
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum DifficultyAdjustingAlgorithm {
    Simple,
    ExponentialDamping,
    Parents,
    SimpleAsym,
    SimpleAsymDamped
}

struct NetworkBeadPacket <'network_bead_packet_lifetime, 'node_lifetime>{
    source: &'network_bead_packet_lifetime Node<'node_lifetime>,
    destinations: Vec<&'network_bead_packet_lifetime Node<'node_lifetime>>,
    bead: NetworkBead
}

pub struct Network<'network_lifetime, 'network_bead_packet_lifetime> {
    current_time: Time,
    nodes: HashSet<Node<'network_lifetime>>,
    initial_target_difficulty: CompactTarget,
    pending_broadcasts: VecDeque<NetworkBeadPacket<'network_bead_packet_lifetime, 'network_lifetime>>,
    beads_in_flight: Vec<NetworkBeadPacket<'network_bead_packet_lifetime, 'network_lifetime>>
}