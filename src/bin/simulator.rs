//! Braidpool Simulator
//!
//! This code simulates a network of nodes distributed on a sphere (the Earth)
//! with realistic latency defined by the path length between them on the surface
//! of the sphere. Note that all signals are assumed to propagate at the speed
//! of light -- propagation speed in copper or global fiber optics is not simulated.

use clap::{Parser, ArgAction};
use num::{BigUint, Zero};
use num_traits::cast::ToPrimitive;
use rand::{Rng, SeedableRng};
use rand::rngs::StdRng;
use serde_json::{json, Value};
use sha2::{Sha256, Digest};
use std::collections::{HashMap, HashSet};
use std::error::Error;
use std::f64::consts::PI;
use std::fs::File;
use std::time::Instant;
use std::str::FromStr;
use std::cmp::min;
use std::cell::RefCell;
use bimap::BiMap;
use regex::Regex;

// Import our braid module
use braidpool::braid::{self, Relatives, BeadWork};

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

// Configuration struct to hold debug settings
#[derive(Clone, Copy, Debug)]
struct Config {
    debug: bool,
}

// Global network messages (this is a hack for the simulation)
thread_local! {
    static NETWORK_MESSAGES: RefCell<HashMap<BigUint, BeadMessage>> = RefCell::new(HashMap::new());
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
    target: u32,

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

/// Print a hash in a simplified format (first 8 hex digits) with color based on hash value
fn print_hash(hash: &BigUint) -> String {
    // Create a 64-character hex string of the hash, padded with zeros.
    let hex_string = format!("{:0>64}", hash.to_str_radix(16));
    // Use a regex to extract 6 hex digits after any leading zeros.
    let re = regex::Regex::new(r"^0*([^0].{5})").unwrap();
    let color_match = re.captures(&hex_string);
    let (r, g, b) = if let Some(cap) = color_match {
        let color_hex = &cap[1];
        let r = u8::from_str_radix(&color_hex[0..2], 16).unwrap_or(255);
        let g = u8::from_str_radix(&color_hex[2..4], 16).unwrap_or(255);
        let b = u8::from_str_radix(&color_hex[4..6], 16).unwrap_or(255);
        (r, g, b)
    } else {
        (255, 255, 255)
    };
    let ansi_color = format!("\x1b[38;2;{};{};{}m", r, g, b);
    let reset = "\x1b[0m";
    // Create a BigUint representing 2^(256-32)
    let shift_amount = BigUint::from(1u32) << (256 - 32);
    // Divide the hash by the shift amount to get the first 32 bits
    let shifted: BigUint = hash / &shift_amount;
    format!("{}{:0>8}{}", ansi_color, shifted.to_str_radix(16), reset)
}

/// Print a HashSet of BigUint values
fn print_hash_set(hashes: &HashSet<BigUint>) -> String {
    if hashes.is_empty() {
        return "{}".to_string();
    }

    let mut result = "{".to_string();
    let mut first = true;

    // Sort the hashes for consistent output
    let mut sorted_hashes: Vec<&BigUint> = hashes.iter().collect();
    sorted_hashes.sort();

    for hash in sorted_hashes {
        if !first {
            result.push_str(", ");
        }
        result.push_str(&print_hash(hash));
        first = false;
    }

    result.push('}');
    result
}

/// Print a Vec of BigUint values
fn print_hash_vec(hashes: &[BigUint]) -> String {
    if hashes.is_empty() {
        return "[]".to_string();
    }

    let mut result = "[".to_string();
    let mut first = true;

    for hash in hashes {
        if !first {
            result.push_str(", ");
        }
        result.push_str(&print_hash(hash));
        first = false;
    }

    result.push(']');
    result
}

/// Print a Vec of HashSet of BigUint values (e.g., cohorts)
fn print_hash_vec_set(vec_set: &[HashSet<BigUint>]) -> String {
    if vec_set.is_empty() {
        return "[]".to_string();
    }

    let mut result = "[\n".to_string();

    for (i, set) in vec_set.iter().enumerate() {
        result.push_str(&format!("  {}", print_hash_set(set)));
        if i < vec_set.len() - 1 {
            result.push_str(",\n");
        }
    }

    result.push_str("\n]");
    result
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
#[derive(Clone, Debug)]
struct BeadImpl {
    t: f64,                  // Time when created
    hash: BigUint,           // Hash that identifies this block
    parents: HashSet<BigUint>, // Parent beads
    creator: usize,          // Node ID that created this bead
    target: BigUint,         // Target difficulty
}

impl BeadImpl {
    fn new(t: f64, hash: BigUint, parents: HashSet<BigUint>, creator: usize, target: BigUint) -> Self {
        Self {
            t,
            hash,
            parents,
            creator,
            target,
        }
    }
}

/// A Braid is a Directed Acyclic Graph with no incest
#[derive(Clone, Debug)]
struct BraidImpl {
    beads: HashMap<BigUint, BeadImpl>,
    tips: HashSet<BigUint>,
    cohorts: Vec<HashSet<BigUint>>,
}

impl BraidImpl {
    fn new(genesis_bead: BeadImpl) -> Self {
        let genesis_hash = genesis_bead.hash.clone();
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
            tips,
            cohorts,
        }
    }

    fn contains(&self, hash: &BigUint) -> bool {
        self.beads.contains_key(hash)
    }

    fn extend(&mut self, bead: BeadImpl) -> bool {
        let hash = bead.hash.clone();

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

        // Update tips
        for parent in &bead.parents {
            self.tips.remove(parent);
        }
        self.tips.insert(hash.clone());

        // Add the bead
        self.beads.insert(hash, bead);

        // Recalculate cohorts
        let parents_map = self.to_relatives();
        self.cohorts = braid::cohorts(&parents_map, None, None);

        true
    }

    fn to_relatives(&self) -> Relatives {
        let mut parents = HashMap::new();

        for (hash, bead) in &self.beads {
            parents.insert(hash.clone(), bead.parents.clone());
        }

        parents
    }
}

/// Message sent between nodes
#[derive(Clone, Debug)]
struct BeadMessage {
    hash: BigUint,                  // Hash of the bead
    parents: HashSet<BigUint>,      // Parent beads
    creator: usize,                 // Node ID that created this bead
    target: BigUint,                // Target difficulty
    creation_time: f64,             // Time when created
}

/// Network abstraction containing nodes
struct Network {
    t: f64,                          // Current simulation time
    nodes: Vec<Node>,                // Network nodes
    inflightdelay: HashMap<(usize, BigUint), f64>, // Beads in flight with delays
    genesis_hash: BigUint,           // Hash of genesis block
    target: BigUint,                 // Initial target difficulty
    log: bool,                       // Whether to log events
    config: Config,                  // Configuration settings
}

impl Network {
    fn new(
        nnodes: usize,
        hashrate: f64,
        _ticksize: f64,
        npeers: usize,
        target: BigUint,
        log: bool,
        config: Config,
        rng: &mut StdRng,
    ) -> Self {
        let t = 0.0;

        // Create genesis block
        let genesis_bytes = sha256d(&[0u8; 32]);
        let genesis_hash = uint256(&genesis_bytes);

        // Create a genesis bead
        let genesis_bead = BeadImpl::new(t, genesis_hash.clone(), HashSet::new(), 0, target.clone());

        // Create nodes first
        let mut nodes = Vec::with_capacity(nnodes);
        for nodeid in 0..nnodes {
            let node = Node::new(
                genesis_bead.clone(),
                nodeid,
                hashrate / nnodes as f64 / NETWORK_SIZE,
                Some(target.clone()),
                log,
                config,
                rng,
                None, // We'll set the network reference later
            );
            nodes.push(node);
        }

        // Create a network instance with the nodes
        let mut network = Self {
            t,
            nodes,
            inflightdelay: HashMap::new(),
            genesis_hash: genesis_hash.clone(),
            target: target.clone(),
            log,
            config,
        };

        // Set up peer connections
        for nodeid in 0..nnodes {
            // Select random peers
            let mut peers = Vec::new();

            // Create a list of potential peers (all nodes except self)
            let mut potential_peers: Vec<usize> = (0..nnodes).filter(|&id| id != nodeid).collect();

            // Shuffle and take the first npeers
            for _ in 0..min(npeers, potential_peers.len()) {
                let idx = rng.gen_range(0..potential_peers.len());
                let peer_id = potential_peers.remove(idx);
                peers.push(peer_id);
            }

            // Calculate latencies
            let latencies: Vec<f64> = peers.iter()
                .map(|&peer_id| {
                    NETWORK_SIZE * sph_arclen(&network.nodes[nodeid], &network.nodes[peer_id])
                })
                .collect();

            // Add peers to the node
            network.nodes[nodeid].add_peers(peers, latencies);
        }

        // We no longer need to set network pointers

        if log {
            println!("# Starting network with genesis bead {} at time {:.8}",
                     print_hash(&network.genesis_hash), network.t);
        }

        network
    }

    fn tick(&mut self, mine: bool) {
        let dt = if mine {
            TICKSIZE
        } else {
            // Find the minimum time until next bead from any node
            let next_bead_dt = self.nodes.iter()
                .map(|n| n.tremaining)
                .min_by(|a, b| a.partial_cmp(b).unwrap())
                .unwrap();

            // Find minimum time until next message arrival
            let next_recv_dt = self.inflightdelay.values()
                .min_by(|a, b| a.partial_cmp(b).unwrap())
                .cloned()
                .unwrap_or(next_bead_dt + NETWORK_SIZE);

            // Take the minimum of the two
            next_bead_dt.min(next_recv_dt)
        };

        // Increment the simulation time
        self.t += dt;

        // Process in-flight beads
        let mut to_remove = Vec::new();
        let mut to_deliver = Vec::new();

        for ((nodeid, bead_hash), delay) in &mut self.inflightdelay {
            *delay -= dt;
            if *delay <= 0.0 {
                to_remove.push((*nodeid, bead_hash.clone()));
                to_deliver.push((*nodeid, bead_hash.clone()));
            }
        }

        for key in to_remove {
            self.inflightdelay.remove(&key);
        }

        for (nodeid, bead_hash) in to_deliver {
            // Find the message in the global map
            let message_opt = NETWORK_MESSAGES.with(|messages| {
                messages.borrow().get(&bead_hash).cloned()
            });

            if let Some(message) = message_opt {
                if nodeid < self.nodes.len() {
                    // Deliver the message to the node
                    self.nodes[nodeid].receive(message);
                }
            }
        }

        // Tick all nodes
        for i in 0..self.nodes.len() {
            // If logging is enabled and this node is about to create a bead, print in-flight delays
            if self.log && self.nodes[i].tremaining <= 0.0 {
                self.print_in_flight_delays();
            }

            if let Some(message) = self.nodes[i].tick(mine, dt, self.t) {
                self.send_message(i, message);
            }
        }
    }

    fn simulate(&mut self, nbeads: usize, mine: bool) {
        while self.nodes[0].braid.beads.len() < nbeads {
            self.tick(mine);
        }
    }

    // New method to handle sending messages between nodes
    fn send_message(&mut self, from_node: usize, message: BeadMessage) {
        let bead_hash = message.hash.clone();

        // Store the message in the global map
        NETWORK_MESSAGES.with(|messages| {
            messages.borrow_mut().insert(bead_hash.clone(), message.clone());
        });

        // Broadcast message to all nodes except the sender
        if from_node < self.nodes.len() {
            let sender = &self.nodes[from_node];

            for peer_id in 0..self.nodes.len() {
                if peer_id == from_node {
                    continue;
                }
                if self.nodes[peer_id].braid.contains(&bead_hash) {
                    continue;
                }

                // Calculate delay based on spherical arc length between nodes
                let delay = NETWORK_SIZE * sph_arclen(sender, &self.nodes[peer_id]);

                // Schedule delivery
                let key = (peer_id, bead_hash.clone());
                let prev_delay = self.inflightdelay.get(&key).cloned().unwrap_or(NETWORK_SIZE);
                self.inflightdelay.insert(key, prev_delay.min(delay));
            }
        }
    }

    fn reset(&mut self, target: Option<BigUint>) {
        self.t = 0.0;
        self.inflightdelay.clear();

        let target = target.unwrap_or_else(|| self.target.clone());

        for node in &mut self.nodes {
            node.reset(Some(target.clone()));
        }
    }

    fn print_in_flight_delays(&self) {
        if self.inflightdelay.is_empty() {
            println!("There are no beads in flight.");
            return;
        }

        for ((node_id, bead_hash), delay) in &self.inflightdelay {
            println!("bead {} to node {} will arrive in {}s",
                     print_hash(bead_hash), node_id, delay);
        }
    }
}

/// Node in the network
#[derive(Debug)]
struct Node {
    nodeid: usize,
    peers: Vec<usize>,               // Peer node IDs instead of references
    latencies: Vec<f64>,
    nodesalt: BigUint,
    hashrate: f64,
    target: BigUint,
    log: bool,
    nonce: u64,
    tremaining: f64,
    braid: BraidImpl,
    incoming: HashSet<BigUint>,      // Hashes of incoming beads
    working_parents: HashSet<BigUint>, // Parents for the next bead
    latitude: f64,
    longitude: f64,
    calc_target_method: TargetMethod,
    current_time: f64,
    config: Config,                  // Configuration settings
    // We'll remove the network reference entirely and handle this differently
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
        initial_target: Option<BigUint>,
        log: bool,
        config: Config,
        rng: &mut StdRng,
        network: Option<()>, // Placeholder to maintain function signature
    ) -> Self {
        // Generate a random salt for this node
        let mut salt_bytes = [0u8; 32];
        rng.fill(&mut salt_bytes);
        let nodesalt = uint256(&salt_bytes);

        // Create the braid with the genesis bead
        let braid = BraidImpl::new(genesis_bead.clone());

        // Set the target
        let target = initial_target.unwrap_or_else(|| BigUint::from(1u32));

        // Generate random geospatial location
        let latitude = 90.0 * (0.5 - rng.gen::<f64>());
        let longitude = 180.0 * (2.0 * rng.gen::<f64>() - 1.0);

        // Set up working parents (initially just the genesis hash)
        let mut working_parents = HashSet::new();
        working_parents.insert(genesis_bead.hash.clone());

        let mut node = Self {
            nodeid,
            peers: Vec::new(),
            latencies: Vec::new(),
            nodesalt,
            hashrate,
            target,
            log,
            nonce: 0,
            tremaining: 0.0, // Will be set below
            braid,
            incoming: HashSet::new(),
            working_parents,
            latitude,
            longitude,
            calc_target_method: TargetMethod::ExponentialDamping,
            current_time: 0.0,
            config
        };

        // Calculate initial time to next bead
        node.tremaining = node.time_to_next_bead();

        node
    }

    fn reset(&mut self, initial_target: Option<BigUint>) {
        // Get the genesis bead
        let genesis_bead = self.braid.beads.values().next().unwrap().clone();

        // Reset the braid
        self.braid = BraidImpl::new(genesis_bead);

        // Update target if provided
        if let Some(target) = initial_target {
            self.target = target;
        }

        // Reset incoming beads
        self.incoming.clear();

        // Reset working parents to just the genesis hash
        self.working_parents.clear();
        self.working_parents.insert(self.braid.tips.iter().next().unwrap().clone());

        // Recalculate time to next bead
        self.tremaining = self.time_to_next_bead();
    }

    fn add_peers(&mut self, peers: Vec<usize>, latencies: Vec<f64>) {
        self.peers.extend(peers);
        self.latencies.extend(latencies);
    }

    fn time_to_next_bead(&self) -> f64 {
        // Sample from geometric distribution
        // Calculate p as a floating point value directly to avoid integer division resulting in 0
        let p = self.target.to_f64().unwrap() / MAX_HASH.to_f64().unwrap();

        // Generate random number in [0, 1)
        let r = rand::random::<f64>();

        if p > 1.0 {
            panic!("target {} is larger than MAX_HASH", self.target);
        }
        // Calculate number of hashes needed
        let nhashes = if p < 1e-6 {
            // Use Taylor series for small p
            let taylor = p + p.powi(2)/2.0 + p.powi(3)/3.0 + p.powi(4)/4.0 + p.powi(5)/5.0;
            ((1.0 - r).ln() / - taylor).ceil() as u64 + 1
        } else {
            ((1.0 - r).ln() / (1.0 - p).ln()).ceil() as u64 + 1
        };

        // Convert to time (using f64 throughout to avoid overflow)
        // Match Python implementation exactly
        nhashes as f64 / self.hashrate
    }

    fn tick(&mut self, mine: bool, dt: f64, network_time: f64) -> Option<BeadMessage> {
        // Store the current network time
        self.current_time = network_time;

        if !mine {
            // Decrement the remaining time
            self.tremaining -= dt;

            // If we have no incoming beads and our tips haven't changed and we're not ready to mine, return
            if self.incoming.is_empty() &&
               self.working_parents == self.braid.tips &&
               self.tremaining > 0.0 {
                return None;
            }
        }

        // Check if tips have changed
        let old_tips = self.braid.tips.clone();
        if old_tips != self.working_parents {
            // Update working parents to match current tips
            self.working_parents = old_tips.clone();
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
                    let nb = if self.braid.cohorts.is_empty() {
                        0
                    } else {
                        // Take up to TARGET_NC cohorts from the end, similar to Python's [-TARGET_NC:]
                        let start_idx = self.braid.cohorts.len().saturating_sub(TARGET_NC);
                        self.braid.cohorts[start_idx..].iter()
                            .map(|c| c.len())
                            .sum::<usize>()
                    };

                    if self.log {
                        println!("== Solution bead {} target = {:08x}... for cohort size {:2} on node {:2} at time {:.6} Nb/Nc={:.4}",
                                 print_hash(&pow),
                                 (self.target.clone() >> 224u32).to_u64().unwrap_or(0),
                                 self.braid.cohorts.last().map_or(0, |c| c.len()),
                                 self.nodeid,
                                 network_time,
                                 nb as f64 / TARGET_NC as f64);

                        if self.config.debug {
                            println!("    Having parents: {}", print_hash_set(&self.working_parents));
                        }
                    }

                    // Create a new bead with the solution
                    let new_bead = BeadImpl::new(
                        network_time,
                        pow.clone(),
                        self.working_parents.clone(),
                        self.nodeid,
                        self.target.clone()
                    );

                    // Add the bead to our braid
                    self.braid.extend(new_bead.clone());
                    self.working_parents = self.braid.tips.clone();

                    // Create a message to send to peers using the parent's set of the new bead
                    let message = BeadMessage {
                        hash: pow,
                        parents: new_bead.parents.clone(),
                        creator: self.nodeid,
                        target: self.target.clone(),
                        creation_time: network_time,
                    };

                    // Reset tremaining for the next bead
                    self.tremaining = self.time_to_next_bead();

                    return Some(message);
                }
            }
        } else if self.tremaining <= 0.0 {
            // Time to create a new bead
            //println!("cohorts = {}", print_hash_vec_set(&self.braid.cohorts));
            //println!("tips = {}", print_hash_set(&self.braid.tips));
            let nb = if self.braid.cohorts.is_empty() {
                0
            } else {
                // Take up to TARGET_NC cohorts from the end, similar to Python's [-TARGET_NC:]
                let start_idx = self.braid.cohorts.len().saturating_sub(TARGET_NC);
                self.braid.cohorts[start_idx..].iter()
                    .map(|c| c.len())
                    .sum::<usize>()
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

            if self.log {
                println!("== Solution {} target = {}... for cohort size {:3} on node {:2} and at time {:.6} Nb={:3} Nc={:3} Nb/Nc={:.6}",
                         print_hash(&scaled_pow),
                         {
                             let shift_amount = BigUint::from(1u32) << (256 - 32);
                             let shifted = self.target.clone() / shift_amount;
                             format!("{:08x}", shifted)
                         },
                         self.braid.cohorts.last().map_or(0, |c| c.len()),
                         self.nodeid,
                         network_time,
                         nb,
                         TARGET_NC,
                         nb as f64 / TARGET_NC as f64);

                if self.config.debug {
                    println!("    Having parents: {}", print_hash_set(&self.working_parents));
                }
            }

            // Create a new bead
            let new_bead = BeadImpl::new(
                network_time,
                scaled_pow.clone(),
                self.working_parents.clone(),
                self.nodeid,
                self.target.clone()
            );

            // Add the bead to our braid
            self.braid.extend(new_bead.clone());
            self.working_parents = self.braid.tips.clone();

            // Create a message to send to peers using the parent's set from the new bead
            let message = BeadMessage {
                hash: scaled_pow,
                parents: new_bead.parents.clone(),
                creator: self.nodeid,
                target: self.target.clone(),
                creation_time: network_time,
            };

            // Reset tremaining for the next bead
            self.tremaining = self.time_to_next_bead();

            return Some(message);
        }

        // Process any incoming beads
        self.process_incoming();

        // If tips have changed and we're not mining, reset mining timer
        if self.braid.tips != old_tips && !mine {
            self.tremaining = self.time_to_next_bead();
        }
        return None;
    }

    fn receive(&mut self, message: BeadMessage) {
        let bead_hash = message.hash.clone();

        // If we already have this bead, ignore it
        if self.braid.contains(&bead_hash) {
            return;
        }

        // Add to incoming beads
        self.incoming.insert(bead_hash.clone());

        // Try to process incoming beads
        self.process_incoming();

        // Update working parents with new tips
        self.working_parents = self.braid.tips.clone();

        // Recalculate target
        self.target = self.calc_target(&self.working_parents);

        // Reset mining timer
        self.tremaining = self.time_to_next_bead();

        // Return message to be sent by Network
        self.send_message(message);

        if self.config.debug {
            println!("Node {:2} received bead {} at time {:.6} we have {} tips: {}",
                     self.nodeid,
                     print_hash(&bead_hash),
                     self.current_time,
                     self.braid.tips.len(),
                     print_hash_set(&self.braid.tips));
        }
    }

    fn process_incoming(&mut self) {
        // Process all incoming bead hashes
        let mut processed = Vec::new();

        for bead_hash in &self.incoming {
            // Try to create a bead from the message
            let message_opt = NETWORK_MESSAGES.with(|messages| {
                messages.borrow().get(bead_hash).cloned()
            });

            if let Some(message) = message_opt {
                let bead = BeadImpl::new(
                    message.creation_time,
                    message.hash.clone(),
                    message.parents.clone(),
                    message.creator,
                    message.target.clone()
                );

                // Try to add it to our braid
                if self.braid.extend(bead) {
                    processed.push(bead_hash.clone());
                }
            }
        }

        // Remove processed beads from incoming
        for bead_hash in processed {
            self.incoming.remove(&bead_hash);
        }

    }

    // This method will be called by the Network
    fn send_message(&self, _message: BeadMessage) {
        // In a real implementation, this would send the message to the network
        // For our simulation, the Network will handle this
    }

    fn calc_target(&self, parents: &HashSet<BigUint>) -> BigUint {
        match self.calc_target_method {
            TargetMethod::Simple => self.calc_target_simple(parents),
            TargetMethod::ExponentialDamping => self.calc_target_exponential_damping(parents),
            TargetMethod::Parents => self.calc_target_parents(parents),
            TargetMethod::SimpleAsym => self.calc_target_simple_asym(parents),
            TargetMethod::SimpleAsymDamped => self.calc_target_simple_asym_damped(parents),
        }
    }

    fn calc_target_parents(&self, parents: &HashSet<BigUint>) -> BigUint {
        const TARGET_PARENTS: usize = 2;
        const INTERVAL: usize = 100;

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

        let htarget = (BigUint::from(parents.len() as u32) * MAX_HASH.clone()) / sum;

        // Adjust based on number of parents
        if parents.len() < TARGET_PARENTS {
            htarget.clone() + (htarget.clone() * BigUint::from((TARGET_PARENTS - parents.len()) as u32)) / BigUint::from(INTERVAL as u32)
        } else if parents.len() > TARGET_PARENTS {
            htarget.clone() - (htarget.clone() * BigUint::from((parents.len() - TARGET_PARENTS) as u32)) / BigUint::from(INTERVAL as u32)
        } else {
            htarget
        }
    }

    fn calc_target_simple(&self, parents: &HashSet<BigUint>) -> BigUint {
        const DELTA_NUM: usize = 2;
        const DELTA_DENOM: usize = 128;

        // Calculate Nb (sum of beads in last TARGET_NC cohorts)
        let nb = if self.braid.cohorts.is_empty() {
            0
        } else {
            // Take up to TARGET_NC cohorts from the end, similar to Python's [-TARGET_NC:]
            let start_idx = self.braid.cohorts.len().saturating_sub(TARGET_NC);
            self.braid.cohorts[start_idx..].iter()
                .map(|c| c.len())
                .sum::<usize>()
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

        let htarget = (BigUint::from(parents.len() as u32) * MAX_HASH.clone()) / sum;

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

    fn calc_target_exponential_damping(&self, parents: &HashSet<BigUint>) -> BigUint {
        // Calculate Nb (sum of beads in last TARGET_NC cohorts)
        let nb = if self.braid.cohorts.is_empty() {
            0
        } else {
            // Take up to TARGET_NC cohorts from the end, similar to Python's [-TARGET_NC:]
            let start_idx = self.braid.cohorts.len().saturating_sub(TARGET_NC);
            self.braid.cohorts[start_idx..].iter()
                .map(|c| c.len())
                .sum::<usize>()
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

        let htarget = (BigUint::from(parents.len() as u32) * MAX_HASH.clone()) / sum;

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
                let parent_target = parent_bead.target.clone();
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

/// Save a braid to a JSON file
fn save_braid(
    parents: &Relatives,
    filename: &str,
    description: &str,
) -> Result<Value, Box<dyn Error>> {
    // Create a DAG using our braid module
    let children = braid::reverse(parents);
    let geneses = braid::geneses(parents);
    let tips = braid::tips(parents, Some(&children));
    let cohorts = braid::cohorts(parents, Some(&children), None);

    // Create bead_work map (all beads have work=1)
    let mut bead_work = BeadWork::new();
    for bead in parents.keys() {
        bead_work.insert(bead.clone(), BigUint::from(1u32));
    }

    // Calculate work
    let work = braid::descendant_work(parents, Some(&children), &bead_work, Some(&cohorts));

    // Calculate highest work path
    let highest_work_path = braid::highest_work_path(parents, Some(&children), &bead_work);

    // Create the JSON structure
    let mut result = json!({
        "description": description,
        "geneses": geneses.iter().map(|b| b.to_string()).collect::<Vec<_>>(),
        "tips": tips.iter().map(|b| b.to_string()).collect::<Vec<_>>(),
        "cohorts": cohorts.iter().map(|c|
            c.iter().map(|b| b.to_string()).collect::<Vec<_>>()
        ).collect::<Vec<_>>(),
        "highest_work_path": highest_work_path.iter().map(|b| b.to_string()).collect::<Vec<_>>(),
    });

    // Add parents and children as objects with string keys
    let mut parents_obj = serde_json::Map::new();
    for (bead, parent_set) in parents {
        parents_obj.insert(
            bead.to_string(),
            json!(parent_set.iter().map(|p| p.to_string()).collect::<Vec<_>>())
        );
    }
    result["parents"] = json!(parents_obj);

    let mut children_obj = serde_json::Map::new();
    for (bead, child_set) in &children {
        children_obj.insert(
            bead.to_string(),
            json!(child_set.iter().map(|c| c.to_string()).collect::<Vec<_>>())
        );
    }
    result["children"] = json!(children_obj);

    // Add bead_work as object with string keys
    let mut bead_work_obj = serde_json::Map::new();
    for (bead, work) in &bead_work {
        bead_work_obj.insert(bead.to_string(), json!(work.to_string()));
    }
    result["bead_work"] = json!(bead_work_obj);

    // Add work as object with string keys
    let mut work_obj = serde_json::Map::new();
    for (bead, w) in &work {
        work_obj.insert(bead.to_string(), json!(w.to_string()));
    }
    result["work"] = json!(work_obj);

    // Write to file
    let file = File::create(filename)?;
    serde_json::to_writer_pretty(file, &result)?;

    Ok(result)
}

/// Number the beads in a braid sequentially in topological order starting at genesis
fn number_beads(hashed_parents: &Relatives) -> Relatives {
    let mut bead_id: u64 = 0;
    let mut parents = Relatives::new();
    let mut bead_ids = BiMap::new();

    // First handle genesis beads
    for bead_hash in braid::geneses(hashed_parents) {
        bead_ids.insert(bead_hash.clone(), BigUint::from(bead_id));
        parents.insert(BigUint::from(bead_id), HashSet::new());
        bead_id += 1;
    }

    // Traverse the DAG in BFS in the descendant direction
    let hashed_children = braid::reverse(hashed_parents);
    let mut next_parents = parents.clone();

    while !next_parents.is_empty() {
        let working_parents = next_parents.clone();
        next_parents = Relatives::new();

        for (parent, _) in working_parents {
            if let Some(parent_hash) = bead_ids.get_by_right(&parent) {
                if let Some(children_set) = hashed_children.get(parent_hash) {
                    for bead_hash in children_set {
                        let this_id;

                        if let Some(id) = bead_ids.get_by_left(bead_hash) {
                            this_id = id.clone();
                        } else {
                            this_id = BigUint::from(bead_id);
                            bead_ids.insert(bead_hash.clone(), this_id.clone());
                            bead_id += 1;
                        }

                        parents
                            .entry(this_id.clone())
                            .or_insert_with(HashSet::new)
                            .insert(parent.clone());
                        next_parents
                            .entry(this_id)
                            .or_insert_with(HashSet::new)
                            .insert(parent.clone());
                    }
                }
            }
        }
    }

    parents
}

fn main() -> Result<(), Box<dyn Error>> {
    // Parse command line arguments
    let mut args = Args::parse();

    // Create configuration
    let config = Config {
        debug: args.debug,
    };

    // If debug is enabled, also enable logging
    if config.debug {
        args.log = true;
    }

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
    let mut network = Network::new(
        args.nodes,
        network_hashrate,
        TICKSIZE,
        args.peers,
        target.clone(),
        args.log,
        config,
        &mut rng,
    );

    // Set algorithm for each node
    for node in &mut network.nodes {
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
        network.simulate(args.beads, true);

        // Get the braid from the first node
        let bmine = network.nodes[0].braid.clone();

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
        network.reset(Some(target.clone()));

        // Simulate without mining
        network.simulate(args.beads, false);

        // Get the braid from the first node
        let bnomine = network.nodes[0].braid.clone();

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
        network.simulate(args.beads, args.mine);

        // Get the braid from the first node
        let b = network.nodes[0].braid.clone();

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
