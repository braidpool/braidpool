//! Braidpool Simulator
//!
//! This code simulates a network of nodes distributed on a sphere (the Earth)
//! with realistic latency defined by the path length between them on the surface
//! of the sphere. Note that all signals are assumed to propagate at the speed
//! of light -- propagation speed in copper or global fiber optics is not simulated.

use clap::{Parser, ArgAction};
use num::{BigUint, Zero};
use serde::{Serialize, Deserialize};
use num_traits::cast::ToPrimitive;
use rand::{Rng, SeedableRng};
use rand::rngs::StdRng;
use sha2::{Sha256, Digest};
use std::collections::{HashMap, HashSet};
use std::error::Error;
use std::f64::consts::PI;
use std::time::Instant;
use std::str::FromStr;
use std::cmp::min;
use std::rc::Rc;
use std::cell::RefCell;
use regex::Regex;

// Import our braid module
use braidpool::braid::{self, Relatives, BeadWork, BeadHash, Target};
use braidpool::braid::io_json::{save_braid};

// Constants
const NETWORK_SIZE: f64 = 0.06676; // The round-trip time in seconds to traverse the network = pi*r_e/c
const TICKSIZE: f64 = 0.001; // One "tick" in seconds in which beads will be propagated and mined
const NETWORK_HASHRATE: f64 = 800000.0; // Single core hashrate in hashes/s (will be benchmarked)
const OVERHEAD_FUDGE: f64 = 1.95; // Fudge factor for processing overhead compared to pure sha256d mining
const EARTH_RADIUS: f64 = 6371000.0; // Mean radius of earth in meters
const SPEED_OF_LIGHT: f64 = 299792458.0; // speed of light in m/s

// Default target values
const TARGET_NC: usize = 7;
const TARGET_NB: usize = 17;
const TARGET_DAMPING: usize = 4 * TARGET_NB;

// Debug flag in thread-local storage for safety
thread_local! {
    static DEBUG: std::cell::Cell<bool> = std::cell::Cell::new(false);
}

// Maximum hash value (2^256-1)
lazy_static::lazy_static! {
    static ref MAX_HASH: BigUint = BigUint::from_str("115792089237316195423570985008687907853269984665640564039457584007913129639935").unwrap();
}

/// Command line arguments
#[derive(Parser, Debug)]
#[clap(author, version, about, long_about = None)]
struct Args {
    /// Base filename to which we will write the generated braid, '.json' will be added
    #[clap(short, long, default_value = "braid")]
    output_file: String,

    /// Number of nodes to simulate
    #[clap(short, long, default_value_t = 25)]
    nodes: usize,

    /// Do sha256d mining (if --no-mine we will use a geometric distribution)
    #[clap(long, action = ArgAction::SetTrue)]
    mine: bool,

    /// Target difficulty exponent t where T=2**t-1
    #[clap(short, long, default_value_t = 239)]
    target_exponent: u32,

    /// Number of beads to simulate
    #[clap(short, long, default_value_t = 50)]
    beads: usize,

    /// Number of peers per node
    #[clap(short, long, default_value_t = 4)]
    peers: usize,

    /// String description describing this simulation run
    #[clap(short, long, default_value = "No description provided")]
    description: String,

    /// Test mining vs no-mining mode
    #[clap(short = 'M', long, action = ArgAction::SetTrue)]
    test_mining: bool,

    /// Target N_B/N_C ratio
    #[clap(short = 'R', long, default_value = "17/7")]
    target_ratio: String,

    /// Random seed (to regenerate the same network)
    #[clap(short, long, default_value_t = 1)]
    random_seed: u64,

    /// Damping factor for difficulty adjustment
    #[clap(short = 'D', long, default_value_t = TARGET_DAMPING)]
    damping_factor: usize,

    /// Select the Difficulty Algorithm
    #[clap(short = 'A', long, default_value = "exp")]
    algorithm: String,

    /// Log each bead as it is found to make plots
    #[clap(short, long, action = ArgAction::SetTrue)]
    log: bool,

    /// Print extra debugging information
    #[clap(long, action = ArgAction::SetTrue)]
    debug: bool,
}

/// Compute SHA256d hash (double SHA256)
fn sha256d(msg: &[u8]) -> [u8; 32] {
    let first_hash = Sha256::digest(msg);
    let second_hash = Sha256::digest(&first_hash);
    let mut result = [0u8; 32];
    result.copy_from_slice(&second_hash);
    result
}

/// Convert bytes to BigUint
fn uint256(bytes: &[u8]) -> BigUint {
    BigUint::from_bytes_be(bytes)
}

/// Print a hash in a simplified format (first 8 hex digits)
fn print_hash_simple(hash: &BigUint) -> String {
    // Create a BigUint representing 2^(256-32)
    let shift_amount = BigUint::from(1u32) << (256 - 32);

    // Divide the hash by the shift amount to get the first 32 bits
    let shifted: BigUint = hash / &shift_amount;

    // Format as hex with leading zeros using the string representation of BigUint
    format!("{:0>8}", shifted.to_str_radix(16))
}

/// Compute the arc length on the surface of a unit sphere
fn sph_arclen(n1: &Node, n2: &Node) -> f64 {
    // phi = 90 - latitude
    let phi1 = (90.0 - n1.latitude) * PI / 180.0;
    let phi2 = (90.0 - n2.latitude) * PI / 180.0;

    // theta = longitude
    let theta1 = n1.longitude * PI / 180.0;
    let theta2 = n2.longitude * PI / 180.0;

    let c = phi1.sin() * phi2.sin() * (theta1 - theta2).cos() + phi1.cos() * phi2.cos();
    c.acos()
}

/// A Bead is a full bitcoin (weak) block that may miss Bitcoin's difficulty target
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
struct BeadImpl {
    t: f64,                  // Time when created
    hash: Option<BeadHash>,   // Hash that identifies this block
    parents: HashSet<BeadHash>, // Parent beads
    creator: usize,          // Node ID that created this bead
    target: Target,         // Target difficulty
}

impl BeadImpl {
    fn new(t: f64, parents: HashSet<BigUint>, creator: usize, target: Target) -> Self {
        Self {
            t,
            hash: None,
            parents,
            creator,
            target,
        }
    }

    fn add_pow(&mut self, hash: BigUint) {
        self.hash = Some(hash);
    }
}

/// A Braid is a Directed Acyclic Graph with no incest
#[derive(Clone, Debug)]
struct BraidImpl {
    beads: HashMap<BigUint, BeadImpl>,
    times: HashMap<BigUint, f64>,
    tips: HashSet<BigUint>,
    cohorts: Vec<HashSet<BigUint>>,
}

impl BraidImpl {
    fn new(genesis_bead: BeadImpl) -> Self {
        let genesis_hash = genesis_bead.hash.clone().unwrap();
        let mut beads = HashMap::new();
        beads.insert(genesis_hash.clone(), genesis_bead);

        let mut tips = HashSet::new();
        tips.insert(genesis_hash.clone());

        // Create a parents map for cohort calculation
        let mut parents_map = HashMap::new();
        parents_map.insert(genesis_hash.clone(), HashSet::new());

        // Calculate initial cohorts
        let cohorts = braid::cohorts(&parents_map, None, None);

        Self {
            beads,
            times: HashMap::new(),
            tips,
            cohorts,
        }
    }

    fn contains(&self, hash: &BigUint) -> bool {
        self.beads.contains_key(hash)
    }

    fn extend(&mut self, bead: BeadImpl) -> bool {
        let hash = match &bead.hash {
            Some(h) => h.clone(),
            None => return false, // Can't add a bead without a hash
        };

        // Check if we already have this bead
        if self.beads.contains_key(&hash) {
            return false;
        }

        // Check if we have all parents
        for parent in &bead.parents {
            if !self.beads.contains_key(parent) {
                return false;
            }
        }

        // Add the bead
        self.beads.insert(hash.clone(), bead.clone());
        self.times.insert(hash.clone(), bead.t);

        // Update tips
        for parent in &bead.parents {
            self.tips.remove(parent);
        }
        self.tips.insert(hash.clone());

        // Recalculate cohorts
        let parents_map = self.to_relatives();
        self.cohorts = braid::cohorts(&parents_map, None, None);

        true
    }

    fn to_relatives(&self) -> Relatives {
        let mut parents = HashMap::new();

        for (hash, bead) in &self.beads {
            let parent_set = bead.parents.clone();
            parents.insert(hash.clone(), parent_set);
        }

        parents
    }
}

/// Network abstraction containing nodes
struct Network {
    t: f64,                          // Current simulation time
    nodes: Vec<Rc<RefCell<Node>>>,   // Network nodes
    inflightdelay: HashMap<(usize, BeadHash), (Vec<u8>, f64)>, // (serialized bead, delay)
    genesis_hash: BeadHash,          // Hash of genesis block
    target: Target,                  // Initial target difficulty
    log: bool,                       // Whether to log events
    pending_broadcasts: Vec<(usize, BeadImpl, f64)>, // Queue of pending broadcasts
}

impl Network {
    fn new(
        nnodes: usize,
        hashrate: f64,
        _ticksize: f64,
        npeers: usize,
        target: Target,
        log: bool,
        rng: &mut StdRng,
    ) -> std::rc::Rc<std::cell::RefCell<Network>> {
        let t = 0.0;

        // Create genesis block
        let genesis_bytes = sha256d(&[0u8; 32]);
        let genesis_hash = uint256(&genesis_bytes);

        // Create a genesis bead
        let mut genesis_bead = BeadImpl::new(t, HashSet::new(), 0, target.clone());
        genesis_bead.add_pow(genesis_hash.clone());
        let genesis_bead = genesis_bead;

        // Create nodes
        let mut nodes = Vec::with_capacity(nnodes);
        for nodeid in 0..nnodes {
            let node = Node::new(
                genesis_bead.clone(),
                nodeid,
                hashrate / nnodes as f64 / NETWORK_SIZE,
                Some(target.clone()),
                log,
                rng,
                std::rc::Weak::new(),
            );
            nodes.push(Rc::new(RefCell::new(node)));
        }

        // Set up peer connections
        for nodeid in 0..nnodes {
            // Select random peers
            let mut peers = Vec::new();
            let mut peer_indices = Vec::new();

            // Create a list of potential peers (all nodes except self)
            let mut potential_peers: Vec<usize> = (0..nnodes).filter(|&id| id != nodeid).collect();

            // Shuffle and take the first npeers
            for _ in 0..min(npeers, potential_peers.len()) {
                let idx = rng.gen_range(0..potential_peers.len());
                let peer_id = potential_peers.remove(idx);
                peer_indices.push(peer_id);
                peers.push(nodes[peer_id].clone());
            }

            // Calculate latencies
            let latencies: Vec<f64> = peer_indices.iter()
                .map(|&peer_id| {
                    NETWORK_SIZE * sph_arclen(&nodes[nodeid].borrow(), &nodes[peer_id].borrow())
                })
                .collect();

            // Add peers to the node
            nodes[nodeid].borrow_mut().add_peers(peers, latencies);
        }

        // Reset all nodes to ensure proper initialization
        for node in &nodes {
            node.borrow_mut().reset(Some(target.clone()));
        }

        // Create the network
        let network = Self {
            t,
            nodes,
            inflightdelay: HashMap::new(),
            genesis_hash,
            target,
            log,
            pending_broadcasts: Rc::new(RefCell::new(Vec::new())),
        };

        // Set up incoming peers for each node
        for nodeid in 0..nnodes {
            let mut in_peers = Vec::new();
            let mut in_latencies = Vec::new();

            for other_id in 0..nnodes {
                if other_id == nodeid {
                    continue;
                }

                let other_node = &network.nodes[other_id];
                let peers = &other_node.borrow().peers;

                // Check if this node is a peer of the other node
                for (i, peer) in peers.iter().enumerate() {
                    if Rc::ptr_eq(peer, &network.nodes[nodeid]) {
                        in_peers.push(other_node.clone());
                        in_latencies.push(other_node.borrow().latencies[i]);
                        break;
                    }
                }
            }

            // Add incoming peers
            network.nodes[nodeid].borrow_mut().add_peers(in_peers, in_latencies);
        }

        // Wrap the network in an Rc<RefCell<>> and update each node’s network field
        let network_rc = Rc::new(RefCell::new(network));
        for node in network_rc.borrow().nodes.iter() {
            node.borrow_mut().network = Rc::downgrade(&network_rc);
        }
        return network_rc;
    }

    fn tick(&mut self, mine: bool) {
        // Find the next event time
        let next_bead_dt = self.nodes.iter()
            .map(|n| n.borrow().tremaining)
            .min_by(|a, b| a.partial_cmp(b).unwrap())
            .unwrap_or(f64::MAX);

        let next_recv_dt = self.inflightdelay.values()
            .map(|(_, delay)| *delay)
            .min_by(|a, b| a.partial_cmp(b).unwrap())
            .unwrap_or(next_bead_dt + NETWORK_SIZE);

        let dt = if mine { TICKSIZE } else { next_bead_dt.min(next_recv_dt) };
        self.t += dt;

        // Process in-flight beads
        let mut to_remove = Vec::new();
        let mut to_deliver = Vec::new();

        for ((nodeid, bead_hash), (serialized, delay)) in &mut self.inflightdelay {
            *delay -= dt;
            if *delay <= 0.0 {
                let bead = bincode::deserialize(serialized).unwrap();
                to_remove.push((*nodeid, bead_hash.clone()));
                to_deliver.push((*nodeid, bead));
            }
        }

        for key in to_remove {
            self.inflightdelay.remove(&key);
        }

        for (nodeid, bead_hash) in to_deliver {
            self.nodes[nodeid].borrow_mut().receive(bead_hash);
        }

        // Process any pending broadcasts
        let broadcasts = {
            let mut pending = self.pending_broadcasts.borrow_mut();
            let broadcasts = std::mem::take(&mut *pending);
            broadcasts
        };

        for (nodeid, bead_hash, delay) in broadcasts {
            self.broadcast(nodeid, bead_hash, delay);
        }

        // Tick all nodes
        for node in &self.nodes {
            node.borrow_mut().tick(mine, dt, self.t);
        }
    }

    fn simulate(&mut self, nbeads: usize, mine: bool) {
        while self.nodes[0].borrow().braid.beads.len() < nbeads {
            self.tick(mine);
        }
    }

    fn broadcast(&mut self, node_id: usize, bead: BeadImpl, delay: f64) {
        let bead_hash = bead.hash.clone().unwrap();
        let serialized = bincode::serialize(&bead).unwrap();
        let key = (node_id, bead_hash);
        let prev_entry = self.inflightdelay.get(&key);
        let new_delay = prev_entry.map(|(_, d)| *d).unwrap_or(NETWORK_SIZE).min(delay);
        self.inflightdelay.insert(key, (serialized, new_delay));
    }

    fn reset(&mut self, target: Option<Target>) {
        self.t = 0.0;
        self.inflightdelay.clear();
        self.pending_broadcasts.borrow_mut().clear();

        let target = target.unwrap_or_else(|| self.target.clone());

        for node in &self.nodes {
            node.borrow_mut().reset(Some(target.clone()));
        }
    }

    fn print_in_flight_delays(&self) {
        if self.inflightdelay.is_empty() {
            println!("There are no beads in flight.");
            return;
        }

        for ((node_id, bead_hash), delay) in &self.inflightdelay {
            println!("bead {} to node {} will arrive in {}s",
                     print_hash_simple(bead_hash), node_id, delay.1);
        }
    }
}

/// Node in the network
#[derive(Debug)]
struct Node {
    nodeid: usize,
    network: std::rc::Weak<RefCell<Network>>,
    peers: Vec<Rc<RefCell<Node>>>,
    latencies: Vec<f64>,
    nodesalt: BigUint,
    hashrate: f64,
    target: Target,
    log: bool,
    nonce: u64,
    tremaining: f64,
    braid: BraidImpl,
    incoming: HashMap<BigUint, BeadImpl>,
    working_bead: BeadImpl,
    latitude: f64,
    longitude: f64,
    calc_target_method: TargetMethod,
}

#[derive(Debug, Clone, Copy)]
enum TargetMethod {
    Simple,
    ExponentialDamping,
    Parents,
    SimpleAsym,
    SimpleAsymDamped,
}

impl Node {
    fn new(
        genesis_bead: BeadImpl,
        nodeid: usize,
        hashrate: f64,
        initial_target: Option<Target>,
        log: bool,
        rng: &mut StdRng,
        network: std::rc::Weak<RefCell<Network>>,
    ) -> Self {
        // Generate a random salt for this node
        let mut salt_bytes = [0u8; 32];
        rng.fill(&mut salt_bytes);
        let nodesalt = uint256(&salt_bytes);

        // Create the braid with the genesis bead
        let braid = BraidImpl::new(genesis_bead.clone());

        // Set the target
        let target = initial_target.unwrap_or_else(|| Target::from(1u32));

        // Generate random geospatial location
        let latitude = 90.0 * (0.5 - rng.gen::<f64>());
        let longitude = 180.0 * (2.0 * rng.gen::<f64>() - 1.0);

        // Create a working bead
        let mut tips = HashSet::new();
        tips.insert(genesis_bead.borrow().hash.clone().unwrap());
        let working_bead = BeadImpl::new(0.0, tips, nodeid, target.clone());

        let mut node = Self {
            nodeid,
            network,
            peers: Vec::new(),
            latencies: Vec::new(),
            nodesalt,
            hashrate,
            target,
            log,
            nonce: 0,
            tremaining: 0.0,
            braid,
            incoming: HashMap::new(),
            working_bead,
            latitude,
            longitude,
            calc_target_method: TargetMethod::ExponentialDamping,
        };

        // Calculate initial time to next bead
        node.tremaining = node.time_to_next_bead();

        node
    }

    fn reset(&mut self, initial_target: Option<Target>) {
        // Reset the braid
        let genesis_bead = self.braid.beads.values().next().unwrap().clone();
        self.braid = BraidImpl::new(genesis_bead.clone());

        // Update target if provided
        if let Some(target) = initial_target {
            self.target = target;
        }

        // Reset incoming beads
        self.incoming.clear();

        // Recalculate time to next bead
        self.tremaining = self.time_to_next_bead();

        // Create a new working bead
        let mut tips = HashSet::new();
        tips.insert(genesis_bead.borrow().hash.clone().unwrap());
        self.working_bead = BeadImpl::new(0.0, tips, self.nodeid, self.target.clone());
    }

    fn add_peers(&mut self, peers: Vec<Rc<RefCell<Node>>>, latencies: Vec<f64>) {
        self.peers.extend(peers);
        self.latencies.extend(latencies);
    }

    fn time_to_next_bead(&self) -> f64 {
        // Sample from geometric distribution
        let p = {
            let ratio = num_rational::BigRational::new(self.target.clone().into(), MAX_HASH.clone().into());
            ratio.to_f64().unwrap_or(1e-10)
        };

        // Generate random number in [0, 1)
        let r = rand::random::<f64>();

        // Calculate number of hashes needed
        let nhashes = if p < 1e-6 {
            // Use Taylor series for small p
            let taylor = p + p.powi(2)/2.0 + p.powi(3)/3.0 + p.powi(4)/4.0 + p.powi(5)/5.0;
            (-r.ln() / taylor).ceil() as u64 + 1
        } else {
            (-(1.0 - r).ln() / (1.0 - p).ln()).ceil() as u64 + 1
        };

        // Convert to time
        nhashes as f64 / self.hashrate
    }

    fn tick(&mut self, mine: bool, dt: f64, network_time: f64) {
        if !mine {
            self.tremaining -= dt;

            // If we have no incoming beads and our tips haven't changed and we're not ready to mine, return
            if self.incoming.is_empty() &&
               self.working_bead.borrow().parents == self.braid.tips &&
               self.tremaining > 0.0 {
                return;
            }
        }

        // Check if tips have changed
        let old_tips = self.braid.tips.clone();
        if old_tips != self.working_bead.borrow().parents {
            // Create a new working bead with updated parents
            self.working_bead = BeadImpl::new(network_time, old_tips.clone(), self.nodeid, self.target.clone());
        }

        if mine {
            // Try to mine a block
            let nhashes = (self.hashrate * dt).ceil() as u64;

            for _ in 0..nhashes {
                // Create nonce bytes
                let nonce_bytes = self.nonce.to_be_bytes();

                // Combine with salt
                let mut combined = self.nodesalt.to_bytes_be();
                combined.extend_from_slice(&nonce_bytes);

                // Hash
                let pow_bytes = sha256d(&combined);
                let pow = uint256(&pow_bytes);

                self.nonce += 1;

                // Check if we found a solution
                if pow < self.target {
                    // Calculate cohort size for logging
                    let nb = if self.braid.cohorts.len() >= TARGET_NC {
                        self.braid.cohorts[self.braid.cohorts.len() - TARGET_NC..].iter()
                            .map(|c| c.len())
                            .sum::<usize>()
                    } else {
                        0
                    };

                    if self.log {
                        println!("== Solution bead {} target = {:08x}... for cohort size {:2} on node {:2} at time {:.6} Nb/Nc={:.4}",
                                 print_hash_simple(&pow),
                                 (self.working_bead.target.clone() >> 224u32).to_u64().unwrap_or(0),
                                 self.braid.cohorts.last().map_or(0, |c| c.len()),
                                 self.nodeid,
                                 network_time,
                                 nb as f64 / TARGET_NC as f64);

                        DEBUG.with(|debug| {
                            if debug.get() {
                                println!("    Having parents: {:?}",
                                         self.working_bead.borrow().parents.iter()
                                             .map(|p| print_hash_simple(p))
                                             .collect::<Vec<_>>());
                            }
                        });
                    }

                    // Add PoW to the working bead
                    self.working_bead.borrow_mut().add_pow(pow);

                    // Send it to ourselves (will rebroadcast to peers)
                    self.receive(self.working_bead.clone());
                    break;
                }
            }
        } else if self.tremaining <= 0.0 {
            // Time to create a new bead
            let nb = if self.braid.cohorts.len() >= TARGET_NC {
                self.braid.cohorts[self.braid.cohorts.len() - TARGET_NC..].iter()
                    .map(|c| c.len())
                    .sum::<usize>()
            } else {
                0
            };

            self.nonce += 1;

            // Create nonce bytes
            let nonce_bytes = self.nonce.to_be_bytes();

            // Combine with salt
            let mut combined = self.nodesalt.to_bytes_be();
            combined.extend_from_slice(&nonce_bytes);

            // Hash
            let pow_bytes = sha256d(&combined);
            let pow = uint256(&pow_bytes);

            // Scale the hash to be below target
            let scaled_pow = (pow * self.target.clone()) / MAX_HASH.clone();

            self.working_bead.borrow_mut().add_pow(scaled_pow.clone());

            if self.log {
                println!("== Solution {} target = {}... for cohort size {:3} on node {:2} and at time {:.6} Nb/Nc={:.6}",
                         print_hash_simple(&scaled_pow),
                         {
                             let shift_amount = BigUint::from(1u32) << (256 - 32);
                             let shifted = self.working_bead.target.clone() / shift_amount;
                             format!("{:08x}", shifted)
                         },
                         self.braid.cohorts.last().map_or(0, |c| c.len()),
                         self.nodeid,
                         network_time,
                         nb as f64 / TARGET_NC as f64);

                DEBUG.with(|debug| {
                    if debug.get() {
                        println!("    Having parents: {:?}",
                                 self.working_bead.borrow().parents.iter()
                                     .map(|p| print_hash_simple(p))
                                     .collect::<Vec<_>>());
                    }
                });
            }

            // Send it to ourselves (will rebroadcast to peers)
            self.receive(self.working_bead.clone());

            // Calculate time to next bead
            self.tremaining = self.time_to_next_bead();
        }

        // Process any incoming beads
        self.process_incoming();

        // If tips have changed and we're not mining, reset mining timer
        if self.braid.tips != old_tips && !mine {
            self.tremaining = self.time_to_next_bead();
        }
    }

    fn receive(&mut self, bead: BeadImpl) {
        let bead_hash = match bead.hash {
            Some(ref h) => h.clone(),
            None => return, // Can't receive a bead without a hash
        };

        // If we already have this bead, ignore it
        if self.braid.contains(&bead_hash) {
            return;
        }

        // Add to incoming beads
        self.incoming.insert(bead_hash.clone(), bead.clone());

        // Try to process incoming beads
        self.process_incoming();

        // Update working bead with new tips
        let tips = self.braid.tips.clone();
        self.working_bead = Rc::new(RefCell::new(
            BeadImpl::new(0.0, tips, self.nodeid, self.target.clone())
        ));

        // Recalculate target
        self.target = self.calc_target(&self.working_bead.parents);
        self.working_bead.borrow_mut().target = self.target.clone();

        // Reset mining timer
        self.tremaining = self.time_to_next_bead();

        // Clone the hash for sending to avoid borrowing conflicts
        let bead_to_send = bead.clone();

        DEBUG.with(|debug| {
            if debug.get() {
                println!("Node {:2} received bead {} at time {:.6} we have {} tips: {:?}",
                         self.nodeid,
                         print_hash_simple(&bead_hash),
                         0.0, // network.t would go here
                         self.braid.tips.len(),
                         self.braid.tips.iter()
                             .map(|t| print_hash_simple(t))
                             .collect::<Vec<_>>());
            }
        });

        // Send to peers after we're done with all other operations
        self.send(bead_to_send);
    }

    fn process_incoming(&mut self) {
        loop {
            let old_incoming = self.incoming.clone();
            let mut processed = Vec::new();
            for (bead_hash, bead) in old_incoming.iter() {
                if self.braid.extend(bead.clone()) {
                    processed.push(bead_hash.clone());
                } else {
                    println!("    Unable to add {} to braid, missing parents",
                             print_hash_simple(bead_hash));
                }
            }
            for bead_hash in processed {
                self.incoming.remove(&bead_hash);
            }
            if self.incoming.keys().eq(old_incoming.keys()) {
                break;
            }
        }
        if !self.incoming.is_empty() {
            println!("Node {:2} has {} incoming beads", self.nodeid, self.incoming.len());
        }
    }

    fn send(&self, bead: BeadImpl) {
        // Collect all broadcast data first without any borrows
        let broadcasts: Vec<(usize, BeadImpl, f64)> = self.peers.iter()
            .zip(self.latencies.iter())
            .map(|(peer, delay)| {
                let peer_id = peer.borrow().nodeid;
                (peer_id, bead.clone(), *delay)
            })
            .collect();

        // Then do a single mutable borrow to push all messages
        if let Some(net_rc) = self.network.upgrade() {
            // Get pending_broadcasts without holding network borrow
            let pending_broadcasts = {
                let net = net_rc.borrow();
                net.pending_broadcasts.clone()
            };

            // Now borrow mutably just the pending_broadcasts
            let mut pending = pending_broadcasts.borrow_mut();
            for (peer_id, hash, delay) in broadcasts {
                pending.push((peer_id, hash, delay));
            }
        }
    }

    fn calc_target(&self, parents: &HashSet<BeadHash>) -> Target {
        match self.calc_target_method {
            TargetMethod::Simple => self.calc_target_simple(parents),
            TargetMethod::ExponentialDamping => self.calc_target_exponential_damping(parents),
            TargetMethod::Parents => self.calc_target_parents(parents),
            TargetMethod::SimpleAsym => self.calc_target_simple_asym(parents),
            TargetMethod::SimpleAsymDamped => self.calc_target_simple_asym_damped(parents),
        }
    }

    fn calc_target_parents(&self, parents: &HashSet<BeadHash>) -> Target {
        const TARGET_PARENTS: usize = 2;
        const INTERVAL: usize = 100;

        // Calculate harmonic average of parent targets
        let mut sum = BigUint::zero();
        for parent_hash in parents {
            if let Some(parent_bead) = self.braid.beads.get(parent_hash) {
                let parent_target = parent_bead.borrow().target.clone();
                sum += MAX_HASH.clone() / parent_target;
            }
        }

        if sum.is_zero() {
            return self.target.clone(); // Avoid division by zero
        }

        let htarget = (BigUint::from(parents.len() as u32) * MAX_HASH.clone()) / sum;
        if self.braid.beads.len() <= TARGET_NC {
            return htarget.clone() + htarget.clone() / BigUint::from(32u32);
        }

        // Adjust based on number of parents
        if parents.len() < TARGET_PARENTS {
            htarget.clone() + (htarget.clone() * BigUint::from((TARGET_PARENTS - parents.len()) as u32)) / BigUint::from(INTERVAL as u32)
        } else if parents.len() > TARGET_PARENTS {
            htarget.clone() - (htarget.clone() * BigUint::from((parents.len() - TARGET_PARENTS) as u32)) / BigUint::from(INTERVAL as u32)
        } else {
            htarget
        }
    }

    fn calc_target_simple(&self, parents: &HashSet<BeadHash>) -> Target {
        const DELTA_NUM: usize = 2;
        const DELTA_DENOM: usize = 128;

        // Calculate Nb (sum of beads in last TARGET_NC cohorts)
        let nb = if self.braid.cohorts.len() >= TARGET_NC {
            self.braid.cohorts[self.braid.cohorts.len() - TARGET_NC..].iter()
                .map(|c| c.len())
                .sum::<usize>()
        } else {
            0
        };

        // Calculate harmonic average of parent targets
        let mut sum = BigUint::zero();
        for parent_hash in parents {
            if let Some(parent_bead) = self.braid.beads.get(parent_hash) {
                let parent_target = parent_bead.target.clone();
                sum += MAX_HASH.clone() / parent_target;
            }
        }

        if sum.is_zero() {
            return self.target.clone(); // Avoid division by zero
        }

        let htarget = (Target::from(parents.len() as u32) * MAX_HASH.clone()) / sum;

        // Adjust based on cohort size
        if nb > TARGET_NB {
            // Make it more difficult if cohort is too large
            htarget.clone() - (htarget * BigUint::from(DELTA_NUM as u32)) / BigUint::from(DELTA_DENOM as u32)
        } else if nb < TARGET_NB {
            // Make it easier if cohort is too small
            htarget.clone() + (htarget * BigUint::from(DELTA_NUM as u32)) / BigUint::from(DELTA_DENOM as u32)
        } else {
            htarget
        }
    }

    fn calc_target_exponential_damping(&self, parents: &HashSet<BeadHash>) -> Target {
        // Calculate Nb (sum of beads in last TARGET_NC cohorts)
        let nb = if self.braid.cohorts.len() >= TARGET_NC {
            self.braid.cohorts[self.braid.cohorts.len() - TARGET_NC..].iter()
                .map(|c| c.len())
                .sum::<usize>()
        } else {
            0
        };

        let adev = nb as i64 - TARGET_NB as i64;
        let tau = TARGET_DAMPING as i64;

        // Calculate harmonic average of parent targets
        let mut sum = BigUint::zero();
        for parent_hash in parents {
            if let Some(parent_bead) = self.braid.beads.get(parent_hash) {
                let parent_target = parent_bead.target.clone();
                sum += MAX_HASH.clone() / parent_target;
            }
        }

        if sum.is_zero() {
            return self.target.clone(); // Avoid division by zero
        }

        let htarget = (Target::from(parents.len() as u32) * MAX_HASH.clone()) / sum;

        // Apply exponential damping using Taylor series
        let mut result = htarget.clone();

        // Subtract htarget * adev / tau
        if adev > 0 {
            result -= (htarget.clone() * BigUint::from(adev as u64)) / BigUint::from(tau as u64);
        } else if adev < 0 {
            result += (htarget.clone() * BigUint::from((-adev) as u64)) / BigUint::from(tau as u64);
        }

        // Add htarget * adev^2 / tau^2 / 2
        result += (htarget.clone() * BigUint::from((adev * adev) as u64)) /
                 (BigUint::from((tau * tau) as u64) * BigUint::from(2u64));

        // Subtract htarget * adev^3 / tau^3 / 6
        if adev > 0 {
            result -= (htarget.clone() * BigUint::from((adev * adev * adev) as u64)) /
                     (BigUint::from((tau * tau * tau) as u64) * BigUint::from(6u64));
        } else if adev < 0 {
            result += (htarget.clone() * BigUint::from(((-adev) * (-adev) * (-adev)) as u64)) /
                     (BigUint::from((tau * tau * tau) as u64) * BigUint::from(6u64));
        }

        // Add htarget * adev^4 / tau^4 / 24
        result += (htarget.clone() * BigUint::from((adev * adev * adev * adev) as u64)) /
                 (BigUint::from((tau * tau * tau * tau) as u64) * BigUint::from(24u64));

        // Subtract htarget * adev^5 / tau^5 / 120
        if adev > 0 {
            result -= (htarget * BigUint::from((adev * adev * adev * adev * adev) as u64)) /
                     (BigUint::from((tau * tau * tau * tau * tau) as u64) * BigUint::from(120u64));
        } else if adev < 0 {
            result += (htarget * BigUint::from(((-adev) * (-adev) * (-adev) * (-adev) * (-adev)) as u64)) /
                     (BigUint::from((tau * tau * tau * tau * tau) as u64) * BigUint::from(120u64));
        }

        result
    }

    fn calc_target_simple_asym(&self, parents: &HashSet<BigUint>) -> BigUint {
        const DELTA_NUM: usize = 2;
        const DELTA_DENOM: usize = TARGET_NC;
        const W12_NUM: u64 = 35173371124919584;
        const W12_DENOM: u64 = 100000000000000000;

        // Calculate harmonic average of parent targets
        let mut sum = BigUint::zero();
        for parent_hash in parents {
            if let Some(parent_bead) = self.braid.beads.get(parent_hash) {
                let parent_target = parent_bead.borrow().target.clone();
                sum += MAX_HASH.clone() / parent_target;
            }
        }

        if sum.is_zero() {
            return self.target.clone(); // Avoid division by zero
        }

        let htarget = (BigUint::from(parents.len() as u32) * MAX_HASH.clone()) / sum;

        // Find Nc and Nb
        let mut nc = TARGET_NC;
        let mut nb = if self.braid.cohorts.len() >= nc {
            self.braid.cohorts[self.braid.cohorts.len() - nc..].iter()
                .map(|c| c.len())
                .sum::<usize>()
        } else {
            0
        };

        // Keep expanding Nc until we have Nb != Nc
        let mut loops = 0;
        while nb <= nc {
            loops += 1;
            nc *= 2;
            if nc >= self.braid.beads.len() {
                // We started with difficulty too high
                return htarget.clone() + htarget / BigUint::from(32u32);
            }

            nb = if self.braid.cohorts.len() >= nc {
                self.braid.cohorts[self.braid.cohorts.len() - nc..].iter()
                    .map(|c| c.len())
                    .sum::<usize>()
            } else {
                0
            };
        }

        if loops > 0 {
            println!("loops = {}", loops);
        }

        let nb_nc = nb as f64 / nc as f64;

        // This is a simplified approximation of the Lambert W function calculation
        // In the Python code, it uses the actual Lambert W function
        let w_factor = if nb_nc > 1.0 {
            // Simple approximation for W(nb_nc - 1)
            (nb_nc - 1.0).ln() - (nb_nc - 1.0).ln().ln() + 0.1
        } else {
            0.1 // Default value if nb_nc <= 1
        };

        // Convert to fraction-like calculation
        let w12 = BigUint::from(W12_NUM);
        let w12_denom = BigUint::from(W12_DENOM);

        // Approximate WRm1 (W(nb_nc - 1))
        let wrm1 = BigUint::from((w_factor * 1_000_000_000.0) as u64);
        let wrm1_denom = BigUint::from(1_000_000_000u64);

        // Calculate x0 = 2 * htarget * W12 * WRm1_denom / W12_denom / WRm1
        let x0 = (BigUint::from(2u32) * htarget.clone() * w12 * wrm1_denom.clone()) /
                (w12_denom * wrm1.clone());

        // Calculate dx = x0 - htarget
        let dx = if x0 > htarget.clone() {
            x0 - htarget.clone()
        } else {
            htarget.clone() - x0
        };

        // Apply adjustment
        htarget + (dx * BigUint::from(DELTA_NUM as u32)) / BigUint::from(DELTA_DENOM as u32)
    }

    fn calc_target_simple_asym_damped(&self, parents: &HashSet<BigUint>) -> BigUint {
        // This is a placeholder implementation since the Python version notes this doesn't work
        // We'll just use the simple_asym implementation for now
        self.calc_target_simple_asym(parents)
    }
}

fn main() -> Result<(), Box<dyn Error>> {
    // Parse command line arguments
    let mut args = Args::parse();

    // Set debug flag in thread-local storage
    DEBUG.with(|debug| {
        debug.set(args.debug);
        if debug.get() {
            args.log = true;
        }
    });

    // Parse target ratio
    let re = Regex::new(r"(\d+)/(\d+)").unwrap();
    let (target_nb, target_nc) = if let Some(captures) = re.captures(&args.target_ratio) {
        (
            captures[1].parse::<usize>().unwrap_or(TARGET_NB),
            captures[2].parse::<usize>().unwrap_or(TARGET_NC)
        )
    } else {
        (TARGET_NB, TARGET_NC)
    };

    // Initialize RNG with seed
    let mut rng = StdRng::seed_from_u64(args.random_seed);

    println!("# Simulating a global network of {} nodes having {} peers each,", args.nodes, args.peers);
    println!("# targeting N_B/N_C = {}/{} and damping factor {},", target_nb, target_nc, args.damping_factor);
    println!("# with hashrate {:.4} kh/s per node, and target 2**{}-1",
             NETWORK_HASHRATE / args.nodes as f64 / NETWORK_SIZE / 1000.0,
             args.target);

    let mut network_hashrate = NETWORK_HASHRATE;

    if args.mine {
        // Benchmark hashrate
        let n_hashes = 10000;
        let start = Instant::now();

        for nonce in 0u64..n_hashes {
            sha256d(&nonce.to_be_bytes());
        }

        let elapsed = start.elapsed().as_secs_f64();
        let benchmark_hashrate = n_hashes as f64 / elapsed;

        println!("# Network hashrate (single core) benchmark: {} kh/s",
                 (benchmark_hashrate / 1000.0) as f64);

        network_hashrate = benchmark_hashrate as f64;

        let target_biguint = (BigUint::from(1u32) << args.target) - BigUint::from(1u32);
        let max_hash_f64 = MAX_HASH.to_f64().unwrap_or(f64::MAX);
        let target_f64 = target_biguint.to_f64().unwrap_or(1.0);
        let bead_time = max_hash_f64 / target_f64 / benchmark_hashrate;

        println!("# We should generate a bead roughly once every {:.6}ms", bead_time * 1000.0);
        println!("# Expected time to completion: {:.4}s to mine {} beads",
                 bead_time * OVERHEAD_FUDGE * args.beads as f64,
                 args.beads);
    } else {
        println!("# using the geometric distribution to simulate mining.");
    }

    // Create target difficulty
    let target = (BigUint::from(1u32) << args.target) - BigUint::from(1u32);

    // Create network
    let network = Network::new(
        args.nodes,
        network_hashrate,
        TICKSIZE,
        args.peers,
        target.clone(),
        args.log,
        &mut rng,
    );

    // Set algorithm for each node
    for node in &network.borrow().nodes {
        let mut node = node.borrow_mut();
        node.calc_target_method = match args.algorithm.as_str() {
            "exp" => TargetMethod::ExponentialDamping,
            "parents" => TargetMethod::Parents,
            "simple" => TargetMethod::Simple,
            "simple_asym" => TargetMethod::SimpleAsym,
            "simple_asym_damped" => TargetMethod::SimpleAsymDamped,
            _ => TargetMethod::ExponentialDamping,
        };
    }

    if args.test_mining {
        // Simulate with mining
        network.borrow_mut().simulate(args.beads, true);

        // Get the braid from the first node
        let bmine = network.borrow().nodes[0].borrow().braid.clone();

        // Convert to relatives format
        let mined_parents = bmine.to_relatives();

        // Save to file
        let filename = format!("{}-mine.json", args.output_file);
        let dag = save_braid(&mined_parents, &filename, &args.description)?;

        // Calculate statistics
        let nc = dag["cohorts"].as_array().unwrap().len();
        let nc_err = 1.0 / (nc as f64).sqrt();

        println!("\n   mined Nb/Nc = {:.4} +/- {:.4}",
                 dag["parents"].as_object().unwrap().len() as f64 / nc as f64,
                 nc_err);
        println!("Wrote {} beads to {}-mine.json.", bmine.beads.len(), args.output_file);

        // Reset network
        network.borrow_mut().reset(Some(target.clone()));

        // Simulate without mining
        network.borrow_mut().simulate(args.beads, false);

        // Get the braid from the first node
        let bnomine = network.borrow().nodes[0].borrow().braid.clone();

        // Convert to relatives format
        let nomine_parents = bnomine.to_relatives();

        // Save to file
        let filename = format!("{}-no-mine.json", args.output_file);
        let dag = save_braid(&nomine_parents, &filename, &args.description)?;

        // Calculate statistics
        let nc = dag["cohorts"].as_array().unwrap().len();
        let nc_err = 1.0 / (nc as f64).sqrt();

        println!("\nno-mined Nb/Nc = {:.4} +/- {:.4}",
                 dag["parents"].as_object().unwrap().len() as f64 / nc as f64,
                 nc_err);
        println!("Wrote {} beads to {}-no-mine.json.", bnomine.beads.len(), args.output_file);
    } else {
        // Simulate with the specified mining mode
        network.borrow_mut().simulate(args.beads, args.mine);

        // Get the braid from the first node
        let b = network.borrow().nodes[0].borrow().braid.clone();

        // Convert to relatives format
        let parents = b.to_relatives();

        // Save to file
        let filename = format!("{}.json", args.output_file);
        let dag = save_braid(&parents, &filename, &args.description)?;

        // Calculate statistics
        let nc = dag["cohorts"].as_array().unwrap().len();
        let nc_err = 1.0 / (nc as f64).sqrt();

        println!("\n# no-mined Nb/Nc = {:.4} +/- {:.4}",
                 dag["parents"].as_object().unwrap().len() as f64 / nc as f64,
                 nc_err);
        println!("# Wrote {} beads to {}.json having {} cohorts.",
                 b.beads.len(), args.output_file, nc);
    }

    Ok(())
}
