#![no_main]

use bitcoin::consensus::encode::Decodable;
use libfuzzer_sys::fuzz_target;
use node::bead::Bead;

// Decode a Bead straight from raw bytes, the same call shape BeadCodec uses
// on peer-supplied data. Bead pulls in CommittedMetadata and
// UnCommittedMetadata, so this covers every hand-written Decodable impl
// underneath it. Errors are expected and fine; a panic is a finding.
fuzz_target!(|data: &[u8]| {
    let _ = Bead::consensus_decode(&mut &data[..]);
});
