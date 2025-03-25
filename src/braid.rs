// Standard Imports
use std::collections::HashSet;

// Custom Imports
use crate::beads::DagBead;

pub struct DagBraid<'a> {
    beads: HashSet<DagBead<'a>>,
    tips: HashSet<&'a DagBead<'a>>,
    cohorts: HashSet<&'a DagBead<'a>>,
}
