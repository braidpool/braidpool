// Standard Imports
use std::collections::VecDeque;

// Custom Imports
use crate::braid::DagBraid;
use crate::utils::bitcoin::CompactTarget;
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

pub struct PeerConnection<'a> {
    peer: &'a Node<'a>,
    latency: NetworkLatency
}
pub struct Node<'a> {
    node_identifier: NodeIdentifier,
    hash_rate: HashRate,
    dag_braid: DagBraid<'a>,
    lower_mining_target: CompactTarget,
    location: Location,
    node_salt: Salt,
    current_bead_being_mined: MiningBead,
    incoming_network_beads: VecDeque<NetworkBead>,
    peers: Vec<PeerConnection<'a>>,
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