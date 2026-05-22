use braidpool_benchmarks::braid::utils::generate_parents_for_scenario;
use braidpool_benchmarks::braid::ParentGeneratorKind;
use node::braid::{algorithms, Cohort, Relatives};

// Calibrate the network parent generator: sweep hashrate scale factors and
// report the resulting beads/cohort for the target width.
fn main() {
    let target_width = 2.42;
    let total_beads = 2_000;
    let seed = 42;
    let multipliers = [0.25, 0.5, 1.0, 2.0, 4.0, 8.0];

    // Base parents map using the network generator; we'll override the internal
    // scaling via the generator kind.
    let mut results = Vec::new();
    for &m in &multipliers {
        // ParentGeneratorKind::Network uses lambert W to choose mine_rate_scale
        // internally; we temporarily override the computed scale by adjusting
        // the target width passed in (scale target by 1/m) to emulate changing
        // a*lambda (they are degenerate here).
        let effective_target = target_width / m;
        let parents = generate_parents_for_scenario(
            ParentGeneratorKind::Network,
            total_beads,
            effective_target,
            seed,
        );
        let children: Relatives = algorithms::reverse(&parents);
        let mut cache = Relatives::new();
        let cohorts = algorithms::cohorts(&parents, &children, &Cohort::new(), &mut cache);
        let actual = if cohorts.is_empty() {
            0.0
        } else {
            total_beads as f64 / cohorts.len() as f64
        };
        results.push((m, effective_target, actual, cohorts.len()));
    }

    println!("Calibration sweep (target={}):", target_width);
    println!("multiplier | eff_target | beads/cohort | cohorts");
    for (m, eff, actual, cohorts) in results {
        println!(
            "{:10.2} | {:10.4} | {:12.4} | {:7}",
            m, eff, actual, cohorts
        );
    }
}
