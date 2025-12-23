#![allow(non_snake_case)]
use crate::bead::Bead;
pub mod db_handlers;
pub mod init_db;

#[derive(Debug, Clone)]

pub enum InsertTupleTypes {
    InsertBeadSequentially {
        bead_to_insert: Bead,
        txs_json: String,
        relative_json: String,
        parent_timestamp_json: String,
        bead_id: usize,
    },
}
#[derive(Debug, Clone)]
pub enum BraidpoolDBTypes {
    InsertTupleTypes { query: InsertTupleTypes },
}
