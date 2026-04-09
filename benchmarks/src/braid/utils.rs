use crate::braid::benchmark_types::{BeadIdx, ParentMap, SimpleNetwork};
use crate::braid::simple_generator::SimpleParentGenerator;
use node::braid::{algorithms, Cohort, Relatives};
use rand::prelude::*;
use std::collections::{HashMap, HashSet};
use std::f64::consts::E;
use std::str::FromStr;

#[derive(Debug, Clone, Copy)]
pub enum ParentGeneratorKind {
    Layered,
    Simple,
    Network,
}

impl ParentGeneratorKind {
    pub fn name(&self) -> &'static str {
        match self {
            ParentGeneratorKind::Layered => "layered",
            ParentGeneratorKind::Simple => "simple",
            ParentGeneratorKind::Network => "network",
        }
    }
}

impl FromStr for ParentGeneratorKind {
    type Err = String;

    fn from_str(value: &str) -> Result<Self, Self::Err> {
        match value.to_lowercase().as_str() {
            "layered" => Ok(ParentGeneratorKind::Layered),
            "simple" => Ok(ParentGeneratorKind::Simple),
            "network" => Ok(ParentGeneratorKind::Network),
            other => Err(format!("Unknown generator: {}", other)),
        }
    }
}

impl Default for ParentGeneratorKind {
    fn default() -> Self {
        ParentGeneratorKind::Layered
    }
}

/// Generate a parent map tuned to the desired average cohort width.
pub fn generate_parents_for_scenario(
    kind: ParentGeneratorKind,
    total_beads: usize,
    avg_cohort_size: f64,
    seed: u64,
) -> ParentMap {
    let width = avg_cohort_size.clamp(1.0, 500.0);
    match kind {
        ParentGeneratorKind::Layered => layered_parents(total_beads, width, seed),
        ParentGeneratorKind::Simple => simple_parents(total_beads, width.ceil() as usize, seed),
        ParentGeneratorKind::Network => network_parents(total_beads, width, seed),
    }
}

fn layered_parents(total_beads: usize, target_width: f64, seed: u64) -> ParentMap {
    let mut parents: ParentMap = HashMap::new();
    parents.insert(0, HashSet::new());
    let mut prev_layer = vec![0usize];
    let mut current_id = 1usize;
    let mut rng = StdRng::seed_from_u64(seed);
    let floor_w = target_width.floor().max(1.0) as usize;
    let ceil_w = target_width.ceil().max(1.0) as usize;
    let p_ceil = (target_width - target_width.floor()).max(0.0);

    while current_id < total_beads {
        let mut layer = Vec::new();
        let width = if rng.gen::<f64>() < p_ceil {
            ceil_w
        } else {
            floor_w
        };
        for _ in 0..width {
            if current_id >= total_beads {
                break;
            }
            let parent_set = choose_parent_subset(&prev_layer, width, &mut rng);
            parents.insert(current_id, parent_set);
            layer.push(current_id);
            current_id += 1;
        }
        if layer.is_empty() {
            break;
        }
        prev_layer = layer;
    }

    parents
}

fn choose_parent_subset(
    prev_layer: &[BeadIdx],
    max_parents: usize,
    rng: &mut StdRng,
) -> HashSet<BeadIdx> {
    let mut parents = HashSet::new();
    if prev_layer.is_empty() {
        return parents;
    }

    let count = max_parents.min(prev_layer.len()).max(1);
    let mut candidates = prev_layer.to_vec();

    for _ in 0..count {
        if candidates.is_empty() {
            break;
        }
        let idx = rng.gen_range(0..candidates.len());
        parents.insert(candidates.swap_remove(idx));
    }

    if parents.is_empty() {
        parents.insert(prev_layer[0]);
    }

    parents
}

fn simple_parents(total_beads: usize, max_parents: usize, seed: u64) -> ParentMap {
    let mut generator = SimpleParentGenerator::new(seed, (1, max_parents.max(1)));
    generator.generate_parents(total_beads)
}

fn network_parents(total_beads: usize, width: f64, seed: u64) -> ParentMap {
    // Target beads/cohort -> y = W(N-1).
    let target = width;
    let y = lambert_w_principal((target - 1.0).max(1e-9));
    // Difficulty target x (inverse difficulty); default to 1.0.
    let x: f64 = 1.0;
    let max_parents = width.ceil().max(2.0) as usize;

    // Sweep scales to find N closest to target, derive a_eff for visibility.
    let mut best: Option<(f64, ParentMap, f64)> = None; // (err, parents, scale)
    for exp in -8..=8 {
        let scale = y * SimpleNetwork::NETWORK_SIZE * 10f64.powi(exp);
        let (actual, parents) = simulate_with_scale(total_beads, max_parents, seed, scale);
        let err = (actual - target).abs();
        match best {
            None => best = Some((err, parents, scale)),
            Some((best_err, _, _)) if err < best_err => best = Some((err, parents, scale)),
            _ => {}
        }
    }

    if let Some((_, parents, scale)) = best {
        // Derive a_eff from the chosen scale: λ_total = scale / NETWORK_SIZE, y = a_eff * λ_total * x.
        let lambda_total = scale / SimpleNetwork::NETWORK_SIZE;
        let _a_eff = y / (lambda_total * x.max(1e-9));
        parents
    } else {
        let mut network = SimpleNetwork::new(20, 4, seed);
        network.simulate_parents(total_beads, max_parents, y * SimpleNetwork::NETWORK_SIZE)
    }
}

fn simulate_with_scale(
    total_beads: usize,
    max_parents: usize,
    seed: u64,
    mine_rate_scale: f64,
) -> (f64, ParentMap) {
    let mut network = SimpleNetwork::new(20, 4, seed);
    let parents = network.simulate_parents(total_beads, max_parents, mine_rate_scale);
    let children: Relatives = algorithms::reverse(&parents);
    let mut cache = Relatives::new();
    let cohorts = algorithms::cohorts(&parents, &children, &Cohort::new(), &mut cache);
    let actual = if cohorts.is_empty() {
        0.0
    } else {
        total_beads as f64 / cohorts.len() as f64
    };
    (actual, parents)
}

// Principal branch Lambert W for z >= 0 using series near 0 and Halley iteration otherwise.
fn lambert_w_principal(z: f64) -> f64 {
    if z.abs() < 1e-6 {
        // Series: W(z) ≈ z - z^2 + 3/2 z^3
        return z - z * z + 1.5 * z * z * z;
    }
    let mut w = (z + 1.0 / E).ln(); // initial guess
    for _ in 0..16 {
        let e = w.exp();
        let we = w * e;
        let f = we - z;
        let denom = e * (w + 1.0) - (w + 2.0) * f / (2.0 * (w + 1.0));
        let step = f / denom;
        w -= step;
        if step.abs() < 1e-12 {
            break;
        }
    }
    w
}
