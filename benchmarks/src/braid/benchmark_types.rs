use rand::prelude::*;
use std::cmp::Reverse;
use std::collections::{BinaryHeap, HashMap, HashSet};
use std::f64::consts::{PI, TAU};

pub type BeadIdx = usize;
pub type NodeId = u32;
pub type ParentMap = HashMap<BeadIdx, HashSet<BeadIdx>>;

#[derive(Debug, Clone)]
pub struct SimpleNode {
    pub id: NodeId,
    pub position: (f64, f64), // (latitude, longitude) in radians
    pub peers: Vec<(NodeId, f64)>,
    pub hashrate: f64,
    pub known_beads: ParentMap,
    pub tips: HashSet<BeadIdx>,
    pub next_mining_time: f64,
}

pub struct SimpleNetwork {
    pub nodes: Vec<SimpleNode>,
    pub current_time: f64,
    pub pending_transmissions: BinaryHeap<Reverse<Transmission>>,
    pub parents: ParentMap, // This is what we'll generate for the algorithm
    pub next_bead_id: BeadIdx,
    pub mean_latency: f64,
    mine_rate_scale: f64,
    rng: StdRng,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Transmission {
    pub bead_id: BeadIdx,
    pub bead_parents: HashSet<BeadIdx>,
    pub target_node: NodeId,
    pub arrival_time: f64,
}

impl Eq for Transmission {}

impl PartialOrd for Transmission {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.arrival_time.partial_cmp(&other.arrival_time)
    }
}

impl Ord for Transmission {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.partial_cmp(other).unwrap_or(std::cmp::Ordering::Equal)
    }
}

impl SimpleNetwork {
    pub const NETWORK_SIZE: f64 = 0.06676; // Seconds for a round trip across the network sphere.

    pub fn new(num_nodes: usize, peers_per_node: usize, seed: u64) -> Self {
        let mut rng = StdRng::seed_from_u64(seed);
        let mut nodes = Vec::new();

        // Generate nodes with random positions on the sphere.
        for i in 0..num_nodes {
            let node = SimpleNode {
                id: i as NodeId,
                position: (rng.gen_range(-PI / 2.0..PI / 2.0), rng.gen_range(0.0..TAU)),
                peers: Vec::new(),
                hashrate: 1.0 / num_nodes as f64,
                known_beads: HashMap::new(),
                tips: HashSet::new(),
                next_mining_time: 0.0,
            };
            nodes.push(node);
        }

        // Connect each node to its closest peers to mirror simulator behavior.
        let mean_latency = Self::connect_peers(&mut nodes, peers_per_node);

        let mut network = SimpleNetwork {
            nodes,
            current_time: 0.0,
            pending_transmissions: BinaryHeap::new(),
            parents: HashMap::new(),
            next_bead_id: 0,
            mean_latency,
            mine_rate_scale: 1.0,
            rng,
        };

        // Create genesis bead
        network.create_genesis_parents();
        network
    }

    fn connect_peers(nodes: &mut [SimpleNode], peers_per_node: usize) -> f64 {
        let count = nodes.len();
        let mut total_latency = 0.0;
        let mut edge_count = 0usize;
        for i in 0..count {
            let mut peers: Vec<(NodeId, f64)> = (0..count)
                .filter(|&j| j != i)
                .map(|j| {
                    let latency = Self::network_latency(nodes[i].position, nodes[j].position);
                    (j as NodeId, latency)
                })
                .collect();
            peers.sort_by(|a, b| a.1.partial_cmp(&b.1).unwrap());
            peers.truncate(peers_per_node.min(peers.len()));
            for &(_, lat) in &peers {
                total_latency += lat;
                edge_count += 1;
            }
            nodes[i].peers = peers;
        }
        if edge_count == 0 {
            0.0
        } else {
            total_latency / edge_count as f64
        }
    }

    fn network_latency(p1: (f64, f64), p2: (f64, f64)) -> f64 {
        let (lat1, lon1) = p1;
        let (lat2, lon2) = p2;
        let dlat = lat2 - lat1;
        let dlon = lon2 - lon1;
        let a = (dlat / 2.0).sin().powi(2) + lat1.cos() * lat2.cos() * (dlon / 2.0).sin().powi(2);
        let c = 2.0 * a.sqrt().atan2((1.0 - a).sqrt());
        // Scale arc length by network size (round-trip) to get one-way latency.
        0.5 * Self::NETWORK_SIZE * c / PI
    }

    fn create_genesis_parents(&mut self) {
        // Genesis bead has no parents
        self.parents.insert(0, HashSet::new());
        self.next_bead_id = 1;

        // Distribute genesis to all nodes
        for idx in 0..self.nodes.len() {
            let delay = Self::sample_geometric(
                &mut self.rng,
                self.nodes[idx].hashrate,
                self.mine_rate_scale,
            );
            let node = &mut self.nodes[idx];
            node.known_beads.insert(0, HashSet::new());
            node.tips.insert(0);
            node.next_mining_time = delay;
        }
    }

    fn sample_geometric(rng: &mut StdRng, hashrate: f64, mine_rate_scale: f64) -> f64 {
        // Exponential wait with mean tied to network size to create natural overlap.
        let rate = (hashrate * mine_rate_scale / Self::NETWORK_SIZE.max(1e-6)).max(1e-6);
        let u: f64 = f64::max(rng.gen_range(0.0..1.0), 1e-9);
        (-u.ln()) / rate
    }

    pub fn simulate_parents(
        &mut self,
        target_beads: usize,
        max_parents: usize,
        mine_rate_scale: f64,
    ) -> ParentMap {
        self.mine_rate_scale = mine_rate_scale.max(1e-3);
        // Re-seed initial mining times with the requested scale.
        for idx in 0..self.nodes.len() {
            let rate_delay = Self::sample_geometric(
                &mut self.rng,
                self.nodes[idx].hashrate,
                self.mine_rate_scale,
            );
            self.nodes[idx].next_mining_time = rate_delay;
        }
        while self.parents.len() < target_beads {
            let next_arrival = self
                .pending_transmissions
                .peek()
                .map(|t| t.0.arrival_time)
                .unwrap_or(f64::INFINITY);
            let (next_node_idx, next_mine_time) = self
                .nodes
                .iter()
                .enumerate()
                .min_by(|(_, a), (_, b)| {
                    a.next_mining_time.partial_cmp(&b.next_mining_time).unwrap()
                })
                .map(|(idx, node)| (idx, node.next_mining_time))
                .unwrap();

            let next_time = next_arrival.min(next_mine_time);
            self.current_time = next_time;

            // Process arrivals.
            while let Some(Reverse(tx)) = self.pending_transmissions.peek() {
                if tx.arrival_time > self.current_time {
                    break;
                }
                let tx = self.pending_transmissions.pop().unwrap().0;
                let node = &mut self.nodes[tx.target_node as usize];
                node.known_beads.insert(tx.bead_id, tx.bead_parents.clone());
                for parent in &tx.bead_parents {
                    node.tips.remove(parent);
                }
                node.tips.insert(tx.bead_id);
            }

            // Mine if due before the next arrival.
            if next_mine_time <= next_arrival {
                let bead_id = self.next_bead_id;
                self.next_bead_id += 1;
                let node = &mut self.nodes[next_node_idx];
                let mut parents = Self::choose_parents(&mut self.rng, node, max_parents);
                if parents.is_empty() {
                    parents.insert(0);
                }

                self.parents.insert(bead_id, parents.clone());

                // Miner learns immediately.
                for p in &parents {
                    node.tips.remove(p);
                }
                node.known_beads.insert(bead_id, parents.clone());
                node.tips.insert(bead_id);

                for &(peer_id, latency) in &node.peers {
                    self.pending_transmissions.push(Reverse(Transmission {
                        bead_id,
                        bead_parents: parents.clone(),
                        target_node: peer_id,
                        arrival_time: self.current_time + latency,
                    }));
                }

                node.next_mining_time +=
                    Self::sample_geometric(&mut self.rng, node.hashrate, self.mine_rate_scale);
            }
        }

        self.parents.clone()
    }

    fn choose_parents(rng: &mut StdRng, node: &SimpleNode, max_parents: usize) -> HashSet<BeadIdx> {
        if node.tips.is_empty() {
            return HashSet::new();
        }
        let mut tips: Vec<BeadIdx> = node.tips.iter().copied().collect();
        tips.shuffle(rng);
        tips.truncate(max_parents.max(1));
        tips.into_iter().collect()
    }

    pub fn analyze_braid_structure(parents: &ParentMap) {
        println!("\n=== Braid Structure Analysis ===");
        println!("Total beads: {}", parents.len());

        // Calculate parent statistics
        let total_parents: usize = parents.values().map(|p| p.len()).sum();
        let avg_parents = total_parents as f64 / parents.len() as f64;

        let parent_counts: Vec<usize> = parents.values().map(|p| p.len()).collect();
        let max_parents = parent_counts.iter().max().unwrap_or(&0);
        let min_parents = parent_counts.iter().min().unwrap_or(&0);

        println!("Parents per bead:");
        println!("  Average: {:.2}", avg_parents);
        println!("  Min: {}", min_parents);
        println!("  Max: {}", max_parents);

        // Count nodes with different parent counts
        let mut parent_distribution = std::collections::HashMap::new();
        for count in &parent_counts {
            *parent_distribution.entry(*count).or_insert(0) += 1;
        }

        println!("  Distribution:");
        let mut sorted_pairs: Vec<_> = parent_distribution.iter().collect();
        sorted_pairs.sort_by_key(|&(k, _)| k);
        for (count, frequency) in sorted_pairs {
            println!(
                "    {} parents: {} beads ({:.1}%)",
                count,
                frequency,
                (*frequency as f64 / parents.len() as f64) * 100.0
            );
        }

        // Count genesis and tips
        let genesis_count = parents.values().filter(|p| p.is_empty()).count();
        let mut referenced = HashSet::new();
        for parents_set in parents.values() {
            for parent in parents_set {
                referenced.insert(*parent);
            }
        }
        let all_beads: HashSet<BeadIdx> = parents.keys().copied().collect();
        let tips: HashSet<BeadIdx> = &all_beads - &referenced;

        println!("Genesis beads: {}", genesis_count);
        println!("Tips: {}", tips.len());

        // Calculate fan-in distribution (how many beads reference each parent)
        let mut fan_in_count = std::collections::HashMap::new();
        for parents_set in parents.values() {
            for parent in parents_set {
                *fan_in_count.entry(*parent).or_insert(0) += 1;
            }
        }

        if !fan_in_count.is_empty() {
            let fan_in_values: Vec<usize> = fan_in_count.values().copied().collect();
            let avg_fan_in =
                fan_in_values.iter().sum::<usize>() as f64 / fan_in_values.len() as f64;
            let max_fan_in = fan_in_values.iter().max().unwrap_or(&0);

            println!("Fan-in distribution (how many children each parent has):");
            println!("  Average: {:.2}", avg_fan_in);
            println!("  Max: {}", max_fan_in);
        }
    }
}
