#![no_main]

use bitcoin::consensus::encode::Decodable;
use libfuzzer_sys::fuzz_target;
use node::bead::BeadRequest;

// Mirrors BeadCodec::read_request, which reads the whole stream into a buffer
// and calls BeadRequest::consensus_decode on it. This is the first thing a
// remote peer's bytes reach, so nothing here may panic.
fuzz_target!(|data: &[u8]| {
    let _ = BeadRequest::consensus_decode(&mut &data[..]);
});
