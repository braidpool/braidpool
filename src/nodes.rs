// Standard Imports
use std::collections::{VecDeque, HashSet};
use std::cell::RefCell;

// Custom Imports
use crate::braid::DagBraid;
use crate::utils::bitcoin::CompactTarget;
use crate::utils::Time;
use crate::beads::{MiningBead, NetworkBead};

// Type Definitions for Rust Safety
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct NodeIdentifier(pub usize);

#[derive(Debug, Clone, Copy, PartialEq)]
pub struct HashRate(pub f64);

#[derive(Debug, Clone, Copy, PartialEq)]
pub struct NetworkLatency(pub f64);

#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Location {
    pub latitude: f64,
    pub longitude: f64
}

#[derive(Debug)]
pub struct Salt(pub [u64; 4]);

pub struct PeerConnection<'node_lifetime> {
    peer: &'node_lifetime Node<'node_lifetime>,
    latency: NetworkLatency
}
pub struct Node<'node_lifetime> {
    node_identifier: NodeIdentifier,
    hash_rate: HashRate,
    dag_braid: DagBraid<'node_lifetime>,
    lower_mining_target: Option<CompactTarget>,
    location: Location,
    node_salt: Salt,
    current_bead_being_mined: Option<MiningBead>,
    incoming_network_beads: VecDeque<NetworkBead>,
    peers: RefCell<Vec<PeerConnection<'node_lifetime>>>,
    difficulty_adjusting_algorithm: DifficultyAdjustingAlgorithm
}

impl<'a> Node<'a> {
    pub fn new(node_identifier: NodeIdentifier, hash_rate: HashRate, location: Location, node_salt: Salt, difficulty_adjusting_algorithm: DifficultyAdjustingAlgorithm) -> Self {
        Node {
            node_identifier,
            hash_rate,
            dag_braid: DagBraid::new(),
            lower_mining_target: None,
            location,
            node_salt,
            current_bead_being_mined: None,
            incoming_network_beads: VecDeque::new(),
            peers: RefCell::new(Vec::new()),
            difficulty_adjusting_algorithm
        }
    }

    pub fn connect_with_peer(&'a self, peer: &'a Node<'a>, latency: NetworkLatency) {
        self.peers.borrow_mut().push(PeerConnection{
            peer,
            latency
        });

        peer.peers.borrow_mut().push(PeerConnection{
            peer: &self,
            latency
        });
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DifficultyAdjustingAlgorithm {
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
    pub current_time: Time,
    pub nodes: Vec<Node<'network_lifetime>>,
    pub initial_target_difficulty: CompactTarget,
    pub pending_broadcasts: VecDeque<NetworkBeadPacket<'network_bead_packet_lifetime, 'network_lifetime>>,
    pub beads_in_flight: Vec<NetworkBeadPacket<'network_bead_packet_lifetime, 'network_lifetime>>
}

impl <'a, 'b> Network<'a, 'b> {
    pub fn new(initial_target_difficulty: CompactTarget) -> Self {
        Network {
            current_time: Time(0),
            nodes: Vec::new(),
            initial_target_difficulty,
            pending_broadcasts: VecDeque::new(),
            beads_in_flight: Vec::new()
        }
    }

    pub fn add_node(&mut self, node: Node<'a>) {
        self.nodes.push(node);
    }
}