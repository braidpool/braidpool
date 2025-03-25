// Standard Imports
use std::collections::HashSet;

// Custom Imports
use crate::beads::DagBead;

pub struct DagBraid<'a> {
    beads: HashSet<DagBead<'a>>,
    tips: HashSet<&'a DagBead<'a>>,
    cohorts: HashSet<&'a DagBead<'a>>,
}

impl<'a> DagBraid<'a> {
    pub fn new() -> Self {
        DagBraid {
            beads: HashSet::new(),
            tips: HashSet::new(),
            cohorts: HashSet::new()
        }
    }
}