use bitcoin::pow::CompactTarget;
use bitcoin::{BlockHash, BlockHeader, BlockTime, BlockVersion, TxMerkleNode};
use braidpool_benchmarks::braid::{
    fit_cubic, generate_parents_for_scenario, ParentGeneratorKind, ParentMap, TimingPoint,
    DEFAULT_SCENARIOS,
};
use criterion::{black_box, AxisScale, BatchSize, BenchmarkId, Criterion, PlotConfiguration};
use node::bead::Bead;
use node::braid::{algorithms, Braid, Cohort, ExtendStrategy, Relatives};
use node::committed_metadata::CommittedMetadata;
use node::uncommitted_metadata::UnCommittedMetadata;
use rayon::prelude::*;
use std::collections::HashMap;
use std::env;
use std::sync::Arc;
use std::time::{Duration, Instant};

const EXTEND_STRATEGIES: [ExtendStrategy; 3] = [
    ExtendStrategy::Heuristic,
    ExtendStrategy::Cached,
    ExtendStrategy::NoCache,
];

// Smaller scenarios for quick iterations; switch to the full set with --full-scenarios.
const QUICK_SCENARIOS: &[(usize, f64)] = &[
    (200, 2.0),
    (242, 2.42),
    (500, 5.0),
    (1000, 10.0),
    //    (5000, 50.0),
    //    (10000, 100.0),
];

const ITERATIONS_DEFAULT: usize = 8;

#[derive(Clone, Copy, Debug)]
enum Mode {
    Cohorts,
    Extend,
}

impl Mode {
    fn from_str(value: &str) -> Result<Self, String> {
        match value.to_lowercase().as_str() {
            "cohorts" => Ok(Mode::Cohorts),
            "extend" => Ok(Mode::Extend),
            other => Err(format!("Unknown mode: {}", other)),
        }
    }

    fn name(&self) -> &'static str {
        match self {
            Mode::Cohorts => "cohorts",
            Mode::Extend => "extend",
        }
    }
}

#[derive(Clone, Copy, Debug)]
struct BenchConfig {
    mode: Mode,
    generator: ParentGeneratorKind,
    seed: u64,
    iterations: usize,
    samples: usize,
    measurement_time_ms: u64,
    max_beads: usize,
    run_criterion: bool,
    quick_scenarios: bool,
}

impl BenchConfig {
    fn from_env() -> Self {
        let mut config = BenchConfig {
            mode: Mode::Extend,
            generator: ParentGeneratorKind::default(),
            seed: 42,
            iterations: ITERATIONS_DEFAULT,
            samples: 12,
            // Short default keeps a full run under a couple of minutes; override for deeper stats.
            measurement_time_ms: 250,
            // Filter out very large scenarios by default to keep quick iterations.
            max_beads: 20_000,
            // Skip Criterion by default; enable with --criterion for full statistics.
            run_criterion: false,
            // Use the reduced scenario set unless overridden.
            quick_scenarios: true,
        };

        let mut args = env::args().skip(1);
        while let Some(arg) = args.next() {
            if let Some(value) = arg.strip_prefix("--mode=") {
                config.mode = Mode::from_str(value).unwrap_or_else(|e| panic!("{}", e));
            } else if arg == "--mode" {
                if let Some(value) = args.next() {
                    config.mode = Mode::from_str(&value).unwrap_or_else(|e| panic!("{}", e));
                }
            } else if let Some(value) = arg.strip_prefix("--generator=") {
                config.generator = value.parse().unwrap_or_else(|e| panic!("{}", e));
            } else if arg == "--generator" {
                if let Some(value) = args.next() {
                    config.generator = value.parse().unwrap_or_else(|e| panic!("{}", e));
                }
            } else if let Some(value) = arg.strip_prefix("--seed=") {
                config.seed = value
                    .parse()
                    .unwrap_or_else(|_| panic!("invalid seed value"));
            } else if arg == "--seed" {
                if let Some(value) = args.next() {
                    config.seed = value
                        .parse()
                        .unwrap_or_else(|_| panic!("invalid seed value"));
                }
            } else if let Some(value) = arg.strip_prefix("--iterations=") {
                config.iterations = value
                    .parse()
                    .unwrap_or_else(|_| panic!("invalid iterations value"));
            } else if arg == "--iterations" {
                if let Some(value) = args.next() {
                    config.iterations = value
                        .parse()
                        .unwrap_or_else(|_| panic!("invalid iterations value"));
                }
            } else if let Some(value) = arg.strip_prefix("--samples=") {
                config.samples = value
                    .parse()
                    .unwrap_or_else(|_| panic!("invalid samples value"));
            } else if arg == "--samples" || arg == "-s" {
                if let Some(value) = args.next() {
                    config.samples = value
                        .parse()
                        .unwrap_or_else(|_| panic!("invalid samples value"));
                }
            } else if let Some(value) = arg.strip_prefix("--time-ms=") {
                config.measurement_time_ms = value
                    .parse()
                    .unwrap_or_else(|_| panic!("invalid time-ms value"));
            } else if arg == "--time-ms" {
                if let Some(value) = args.next() {
                    config.measurement_time_ms = value
                        .parse()
                        .unwrap_or_else(|_| panic!("invalid time-ms value"));
                }
            } else if let Some(value) = arg.strip_prefix("--max-beads=") {
                config.max_beads = value
                    .parse()
                    .unwrap_or_else(|_| panic!("invalid max-beads value"));
            } else if arg == "--max-beads" {
                if let Some(value) = args.next() {
                    config.max_beads = value
                        .parse()
                        .unwrap_or_else(|_| panic!("invalid max-beads value"));
                }
            } else if arg == "--criterion" || arg == "--run-criterion" {
                config.run_criterion = true;
            } else if arg == "--full-scenarios" || arg == "--full" {
                config.quick_scenarios = false;
            } else {
                // Ignore unrecognized arguments that cargo may append (`--bench`, filters, etc.)
                continue;
            }
        }

        // Criterion requires at least 10 samples for statistical estimates.
        if config.samples < 10 {
            config.samples = 10;
        }
        // Keep a floor so Criterion doesn't panic on zero-length measurements.
        if config.measurement_time_ms < 50 {
            config.measurement_time_ms = 50;
        }

        config
    }

    fn scenario_set(&self) -> &[(usize, f64)] {
        if self.quick_scenarios {
            QUICK_SCENARIOS
        } else {
            DEFAULT_SCENARIOS
        }
    }
}

fn benchmark_cohorts_performance(c: &mut Criterion, config: BenchConfig) {
    match config.mode {
        Mode::Cohorts => run_cohorts_mode(c, &config),
        Mode::Extend => run_extend_mode(c, &config),
    }
}

fn run_cohorts_mode(c: &mut Criterion, config: &BenchConfig) {
    let mut group = config.run_criterion.then(|| {
        let mut g = c.benchmark_group("cohorts_performance");
        g.plot_config(PlotConfiguration::default().summary_scale(AxisScale::Logarithmic))
            .sample_size(config.samples)
            .measurement_time(Duration::from_millis(config.measurement_time_ms));
        g
    });

    let mut timings = Vec::new();
    let scenarios: Vec<_> = config
        .scenario_set()
        .par_iter()
        .copied()
        .filter(|(total, _)| *total <= config.max_beads)
        .map(|(total, avg)| {
            let parents = generate_parents_for_scenario(
                config.generator,
                total,
                avg,
                config.seed + total as u64,
            );
            let children = algorithms::reverse(&parents);
            let mut cache = Relatives::new();
            let cohorts = algorithms::cohorts(&parents, &children, &Cohort::new(), &mut cache);
            let actual_avg = if cohorts.is_empty() {
                0.0
            } else {
                total as f64 / cohorts.len() as f64
            };
            (total, avg, actual_avg, parents, children)
        })
        .collect();

    if scenarios.is_empty() {
        println!(
            "No cohort scenarios selected (max_beads: {}). Nothing to benchmark.",
            config.max_beads
        );
        return;
    }

    let mut table_rows = Vec::new();

    for (total, avg, actual_avg, parents, children) in scenarios {
        let avg_ms = measure_cohorts(&parents, &children, config.iterations);
        timings.push(TimingPoint {
            total_beads: total as f64,
            duration_ms: avg_ms,
        });
        table_rows.push((total, avg, actual_avg, avg_ms));

        let parents_arc = Arc::new(parents);
        let children_arc = Arc::new(children);
        let bench_id = BenchmarkId::new("cohorts", format!("{}w{}", total, avg));
        if let Some(g) = group.as_mut() {
            g.bench_with_input(bench_id, &(total, avg), move |b, _| {
                let parents_clone = parents_arc.clone();
                let children_clone = children_arc.clone();
                b.iter(|| {
                    let mut cache = Relatives::new();
                    let initial = Cohort::new();
                    black_box(algorithms::cohorts(
                        &parents_clone,
                        &children_clone,
                        &initial,
                        &mut cache,
                    ))
                });
            });
        }
    }

    if let Some(g) = group {
        g.finish();
    } else {
        println!("(Criterion runs skipped; summary-only mode)");
    }

    print_cohorts_summary(&table_rows, &timings, config);
}

fn measure_cohorts(parents: &ParentMap, children: &Relatives, iterations: usize) -> f64 {
    let mut total_duration = Duration::new(0, 0);
    for _ in 0..iterations {
        let start = Instant::now();
        let mut cache = Relatives::new();
        let initial = Cohort::new();
        black_box(algorithms::cohorts(parents, children, &initial, &mut cache));
        total_duration += start.elapsed();
    }
    total_duration.as_secs_f64() * 1000.0 / iterations as f64
}

fn print_cohorts_summary(
    rows: &[(usize, f64, f64, f64)],
    timings: &[TimingPoint],
    config: &BenchConfig,
) {
    let scenario_label = if config.quick_scenarios {
        "quick"
    } else {
        "full"
    };
    println!(
        "\\nCohorts benchmark(mode: {}, generator: {}, iterations: {}, samples: {}, time: {}ms, max_beads: {}, scenarios: {})",
        config.mode.name(),
        config.generator.name(),
        config.iterations,
        config.samples,
        config.measurement_time_ms,
        config.max_beads,
        scenario_label
    );
    println!(
        "| {:>10} | {:>14} | {:>18} | {:>16} |",
        "Total Beads", "Target Avg", "Actual Avg", "Avg Time (ms)"
    );
    println!("|{:-^13}|{:-^16}|{:-^20}|{:-^18}|", "", "", "", "");
    for &(total, target, actual, avg_ms) in rows {
        println!(
            "| {:>10} | {:>14.2} | {:>18.4} | {:>16.4} |",
            total, target, actual, avg_ms
        );
    }

    if let Some(result) = fit_cubic(timings) {
        println!("\nRegression:");
        println!("{}", result.format_line("cohorts"));
    } else {
        println!("\nNot enough points to compute regression");
    }
}

fn run_extend_mode(c: &mut Criterion, config: &BenchConfig) {
    let mut group = config.run_criterion.then(|| {
        let mut g = c.benchmark_group("extend_strategies");
        g.plot_config(PlotConfiguration::default().summary_scale(AxisScale::Logarithmic))
            .sample_size(config.samples)
            .measurement_time(Duration::from_millis(config.measurement_time_ms));
        g
    });

    let mut summary = Vec::new();
    let mut timing_map: HashMap<ExtendStrategy, Vec<TimingPoint>> = HashMap::new();

    let scenarios: Vec<_> = config
        .scenario_set()
        .par_iter()
        .copied()
        .filter(|(total, _)| *total <= config.max_beads)
        .map(|(total, avg)| {
            let (braid, next_bead, actual_avg) =
                build_braid_for_scenario(total, avg, config.generator, config.seed + total as u64);
            (total, avg, actual_avg, braid, next_bead)
        })
        .collect();

    if scenarios.is_empty() {
        println!(
            "No extend scenarios selected (max_beads: {}). Nothing to benchmark.",
            config.max_beads
        );
        return;
    }

    for (total, avg, actual_avg, braid, next_bead) in scenarios {
        let mut scenario_times = HashMap::new();

        for &strategy in &EXTEND_STRATEGIES {
            let avg_ms = measure_extend(&braid, &next_bead, strategy, config.iterations);
            scenario_times.insert(strategy, avg_ms);
            timing_map.entry(strategy).or_default().push(TimingPoint {
                total_beads: total as f64,
                duration_ms: avg_ms,
            });

            let bench_id =
                BenchmarkId::new(&format!("{:?}", strategy), format!("{}w{}", total, avg));
            if let Some(g) = group.as_mut() {
                let braid_template = braid.clone();
                let bead_template = next_bead.clone();
                g.bench_with_input(bench_id, &(total, avg), move |b, _| {
                    b.iter_batched(
                        || (braid_template.clone(), bead_template.clone()),
                        |(mut bra, bead)| {
                            bra.extend_strategy = strategy;
                            black_box(bra.extend(black_box(&bead)))
                        },
                        BatchSize::SmallInput,
                    );
                });
            }
        }

        let mut ordered_times = [0.0f64; 3];
        for (i, strategy) in EXTEND_STRATEGIES.iter().enumerate() {
            ordered_times[i] = *scenario_times.get(strategy).unwrap();
        }
        summary.push((total, avg, actual_avg, ordered_times));
    }

    if let Some(g) = group {
        g.finish();
    } else {
        println!("(Criterion runs skipped; summary-only mode)");
    }

    print_extend_summary(&summary);
    print_extend_regression(&timing_map, config);
}

fn measure_extend(braid: &Braid, bead: &Bead, strategy: ExtendStrategy, iterations: usize) -> f64 {
    let mut total_duration = Duration::new(0, 0);
    for _ in 0..iterations {
        let mut clone = braid.clone();
        clone.extend_strategy = strategy;
        let start = Instant::now();
        black_box(clone.extend(black_box(bead)));
        total_duration += start.elapsed();
    }
    total_duration.as_secs_f64() * 1000.0 / iterations as f64
}

fn build_braid_for_scenario(
    total_beads: usize,
    avg_cohort: f64,
    kind: ParentGeneratorKind,
    seed: u64,
) -> (Braid, Bead, f64) {
    let build_extra = avg_cohort.ceil() as usize + 5;
    let build_count = total_beads + build_extra;
    let mut attempt = 0;
    let mut parents;
    let mut actual_avg;
    loop {
        parents = generate_parents_for_scenario(kind, build_count, avg_cohort, seed + attempt);
        let children = algorithms::reverse(&parents);
        let mut cache = Relatives::new();
        let cohorts = algorithms::cohorts(&parents, &children, &Cohort::new(), &mut cache);
        actual_avg = if cohorts.is_empty() {
            0.0
        } else {
            build_count as f64 / cohorts.len() as f64
        };
        // If we're within 2x of the requested target, accept; otherwise retry with a different seed.
        if avg_cohort == 0.0
            || (actual_avg / avg_cohort < 2.0 && avg_cohort / (actual_avg.max(1e-9)) < 2.0)
            || attempt >= 3
        {
            break;
        }
        attempt += 1;
    }
    let beads = build_beads_from_parents(&parents);
    let initial_beads = beads[..total_beads].to_vec();
    let braid = Braid::new(initial_beads);
    (braid, beads[total_beads].clone(), actual_avg)
}

fn build_beads_from_parents(parents: &ParentMap) -> Vec<Bead> {
    let mut idx_to_hash = HashMap::new();
    let mut beads = Vec::with_capacity(parents.len());
    let mut indices: Vec<usize> = parents.keys().copied().collect();
    indices.sort_unstable();

    for index in indices {
        let parent_indices = parents.get(&index).cloned().unwrap_or_default();
        let parent_hashes: Vec<BlockHash> = parent_indices
            .into_iter()
            .map(|pid| idx_to_hash[&pid])
            .collect();
        let bead = create_dummy_bead(index, parent_hashes);
        idx_to_hash.insert(index, bead.hash());
        beads.push(bead);
    }

    beads
}

fn create_dummy_bead(index: usize, parents: Vec<BlockHash>) -> Bead {
    let committed = CommittedMetadata {
        parents: parents.iter().copied().collect(),
        weak_target: CompactTarget::from_consensus(0x207fffff),
        ..Default::default()
    };

    let uncommitted = UnCommittedMetadata::default();

    let merkle_root = TxMerkleNode::from_byte_array([0; 32]);
    let block_header = BlockHeader {
        bits: CompactTarget::from_consensus(0x207fffff),
        merkle_root,
        nonce: index as u32,
        prev_blockhash: BlockHash::from_byte_array([0; 32]),
        time: BlockTime::from_u32(12345 + index as u32),
        version: BlockVersion::TWO,
    };

    Bead {
        block_header,
        committed_metadata: committed,
        uncommitted_metadata: uncommitted,
    }
}

fn print_extend_summary(summary: &[(usize, f64, f64, [f64; 3])]) {
    println!("\nExtend strategies summary:");
    println!(
        "| {:>9} | {:>14} | {:>16} | {:>14} | {:>14} | {:>14} |",
        "Total", "Target Avg", "Actual Avg", "Heuristic (ms)", "Cached (ms)", "NoCache (ms)"
    );
    println!(
        "|{:-^11}|{:-^16}|{:-^18}|{:-^16}|{:-^16}|{:-^16}|",
        "", "", "", "", "", ""
    );
    for &(total, target, actual, times) in summary {
        println!(
            "| {:>9} | {:>14.2} | {:>16.4} | {:>14.4} | {:>14.4} | {:>14.4} |",
            total, target, actual, times[0], times[1], times[2]
        );
    }
}

fn print_extend_regression(
    timings: &HashMap<ExtendStrategy, Vec<TimingPoint>>,
    config: &BenchConfig,
) {
    let scenario_label = if config.quick_scenarios {
        "quick"
    } else {
        "full"
    };
    println!(
        "\nRegression (mode: {}, generator: {}, iterations: {}, samples: {}, time: {}ms, max_beads: {}, scenarios: {}):",
        config.mode.name(),
        config.generator.name(),
        config.iterations,
        config.samples,
        config.measurement_time_ms,
        config.max_beads,
        scenario_label
    );
    for &strategy in &EXTEND_STRATEGIES {
        if let Some(points) = timings.get(&strategy) {
            if let Some(result) = fit_cubic(points) {
                println!("{}", result.format_line(&format!("{:?}", strategy)));
            } else {
                println!("Not enough samples for {:?}", strategy);
            }
        }
    }
}

fn main() {
    let config = BenchConfig::from_env();
    let mut c = Criterion::default();
    benchmark_cohorts_performance(&mut c, config);
}
