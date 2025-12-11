#![allow(non_snake_case)]
use std::collections::HashMap;

use crate::bead::Bead;
pub mod db_handlers;
pub mod init_db;

#[derive(Debug, Clone)]

pub enum InsertTupleTypes {
    InsertBeadSequentially {
        bead_to_insert: Bead,
        curr_beads: Vec<Bead>,
        bead_index_mapping: HashMap<bitcoin::BlockHash, usize>,
    },
}
#[derive(Debug, Clone)]
pub enum BraidpoolDBTypes {
    InsertTupleTypes { query: InsertTupleTypes },
}
