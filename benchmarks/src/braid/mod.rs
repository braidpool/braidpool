pub mod analysis;
pub mod benchmark_types;
pub mod scenarios;
pub mod simple_generator;
pub mod utils;

pub use analysis::{fit_cubic, RegressionResult, TimingPoint};
pub use benchmark_types::{BeadIdx, NodeId, ParentMap, SimpleNetwork, SimpleNode, Transmission};
pub use scenarios::{DEFAULT_SCENARIOS, EXTEND_SCENARIOS};
pub use simple_generator::SimpleParentGenerator;
pub use utils::{generate_parents_for_scenario, ParentGeneratorKind};
