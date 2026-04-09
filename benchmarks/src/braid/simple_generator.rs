use crate::braid::benchmark_types::{BeadIdx, ParentMap};
use rand::prelude::*;

/// Simple, fast parent map generator that creates realistic DAG structures
/// without the overhead of network simulation
pub struct SimpleParentGenerator {
    rng: StdRng,
    next_id: BeadIdx,
    parents: ParentMap,
    tips: Vec<BeadIdx>,
    fan_out_range: (usize, usize), // min/max parents per bead
}

impl SimpleParentGenerator {
    pub fn new(seed: u64, fan_out_range: (usize, usize)) -> Self {
        let mut generator = SimpleParentGenerator {
            rng: StdRng::seed_from_u64(seed),
            next_id: 0,
            parents: ParentMap::new(),
            tips: Vec::new(),
            fan_out_range,
        };

        // Create genesis bead
        generator
            .parents
            .insert(0, std::collections::HashSet::new());
        generator.tips.push(0);
        generator.next_id = 1;
        generator
    }

    pub fn generate_parents(&mut self, target_beads: usize) -> ParentMap {
        while self.parents.len() < target_beads {
            self.add_random_bead();
        }
        self.parents.clone()
    }

    fn add_random_bead(&mut self) {
        // Select random number of parents from current tips
        let max_parents = self.fan_out_range.1.min(self.tips.len());
        let num_parents = if max_parents == 0 {
            1
        } else {
            self.rng.gen_range(self.fan_out_range.0..=max_parents)
        };

        // Randomly sample parents from tips
        let mut parents = std::collections::HashSet::new();
        let mut available_tips = self.tips.clone();

        for _ in 0..num_parents {
            if available_tips.is_empty() {
                break;
            }
            let idx = self.rng.gen_range(0..available_tips.len());
            let parent = available_tips.swap_remove(idx);
            parents.insert(parent);
        }

        if !parents.is_empty() {
            // Add new bead
            let bead_id = self.next_id;
            self.next_id += 1;

            self.parents.insert(bead_id, parents.clone());

            // Update tips - remove parents, add new bead
            self.tips.retain(|&tip| !parents.contains(&tip));
            self.tips.push(bead_id);
        }
    }

    /// Optimized bulk generator for large bead counts
    pub fn generate_parents_fast(target_beads: usize, seed: u64) -> ParentMap {
        let mut generator = Self::new(seed, (1, 3));
        generator.generate_parents(target_beads)
    }
}
