// Custom Imports
use crate::beads::DagBead;

pub struct DagBraid<'a> {
    beads: Vec<DagBead<'a>>,
    tips: Vec<&'a DagBead<'a>>,
    cohorts: Vec<&'a DagBead<'a>>,
}

impl<'a> DagBraid<'a> {
    pub fn new() -> Self {
        DagBraid {
            beads: Vec::new(),
            tips: Vec::new(),
            cohorts: Vec::new()
        }
    }
}