use crate::braid::Braid;
use std::sync::{Arc, RwLock};
pub struct Payout {
    local_braid: Arc<RwLock<Braid>>,
}
impl Payout {
    pub fn new(local_braid: Arc<RwLock<Braid>>) -> Self {
        Payout { local_braid }
    }
}
