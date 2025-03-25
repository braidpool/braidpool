pub mod bitcoin;

// TODO: Implement the various traits for implicit conversions!
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct Hash {
    pub hash: [u64; 4]
}