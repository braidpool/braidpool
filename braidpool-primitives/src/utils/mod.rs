use ::bitcoin::BlockHash;

pub mod bitcoin;
pub mod test_utils;
// Type Definitions
pub type BeadHash = BlockHash;
pub type Byte = u8;
pub type Bytes = Vec<Byte>;
