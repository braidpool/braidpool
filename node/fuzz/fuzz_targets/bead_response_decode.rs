#![no_main]

use bitcoin::consensus::encode::Decodable;
use libfuzzer_sys::fuzz_target;
use node::bead::BeadResponse;

// Mirrors BeadCodec::read_response. Responses carry full Beads (the Beads
// and GetAllBeads variants), so this exercises the deepest decode path a
// peer can trigger, including every nested metadata decoder.
fuzz_target!(|data: &[u8]| {
    let _ = BeadResponse::consensus_decode(&mut &data[..]);
});
