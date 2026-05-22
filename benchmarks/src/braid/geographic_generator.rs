use crate::braid::benchmark_types::{SimpleNetwork, SimpleNode, Transmission, BeadIdx, NodeId, ParentMap};
use rand::prelude::*;
use std::collections::{HashMap, HashSet, VecDeque};

impl SimpleNetwork {
    pub fn new(num_nodes: usize, _peers_per_node: usize, seed: u64) -> Self {
        let mut rng = StdRng::seed_from_u64(seed);
        let mut nodes = Vec::new();

        // Generate nodes with simplified structure - we don't need geographic complexity for benchmarking
        for i in 0..num_nodes {
            let node = SimpleNode {
                id: i as NodeId,
                position: (0.0, 0.0),  // Simplified - no need for real coordinates
                peers: Vec::new(),      // Simplified - no peer connections needed
                hashrate: 1.0 / num_nodes as f64,
                known_beads: HashMap::new(),
                tips: HashSet::new(),
                next_mining_time: 0.0,
            };
            nodes.push(node);
        }

        let mut network = SimpleNetwork {
            nodes,
            current_time: 0.0,
            pending_transmissions: VecDeque::new(),
            parents: HashMap::new(),
            next_bead_id: 0,
        };

        // Create genesis bead
        network.create_genesis_parents();
        network
    }

    fn create_genesis_parents(&mut self) {
        // Genesis bead has no parents
        self.parents.insert(0, HashSet::new());
        self.next_bead_id = 1;

        // Distribute genesis to all nodes
        for node in &mut self.nodes {
            node.known_beads.insert(0, HashSet::new());
            node.tips.insert(0);
            // Set initial mining times
            node.next_mining_time = Self::sample_geometric(&mut rand::thread_rng(), node.hashrate);
        }
    }

    fn sample_geometric(rng: &mut impl Rng, hashrate: f64) -> f64 {
        // Simplified geometric distribution
        let p = hashrate;
        let u: f64 = rng.gen();
        ((1.0 - u).ln() / (1.0 - p).ln()).ceil() as f64
    }

    pub fn simulate_parents(&mut self, target_beads: usize) -> ParentMap {
        while self.parents.len() < target_beads {
            // Find the node with the earliest mining time
            let (next_node_idx, next_time) = self.nodes.iter()
                .enumerate()
                .map(|(i, node)| (i, node.next_mining_time))
                .min_by(|(_, a), (_, b)| a.partial_cmp(b).unwrap())
                .unwrap();

            // Advance time to the next mining event
            self.current_time = next_time;

            let node = &mut self.nodes[next_node_idx];

            // Use current tips as parents - NO CLONING until we need to store
            if !node.tips.is_empty() {
                let working_parents: HashSet<BeadIdx> = node.tips.iter().copied().collect();

                // Create new bead
                let bead_id = self.next_bead_id;
                self.next_bead_id += 1;

                // Add to global parents map first
                self.parents.insert(bead_id, working_parents.clone());

                // Update all nodes that know the parents (simplified - no transmission delays)
                for other_node in &mut self.nodes {
                    let parents_known = working_parents.iter()
                        .all(|parent_id| other_node.known_beads.contains_key(parent_id));

                    if parents_known {
                        // Add to node's knowledge
                        other_node.known_beads.insert(bead_id, working_parents.clone());

                        // Update tips efficiently
                        for parent in &working_parents {
                            other_node.tips.remove(parent);
                        }
                        other_node.tips.insert(bead_id);
                    }
                }

                // Update mining node's tips (we already did this in the loop above)
                // Schedule next mining time for this node
                node.next_mining_time += Self::sample_geometric(&mut rand::thread_rng(), node.hashrate);
            }
        }

        self.parents.clone()
    }
}