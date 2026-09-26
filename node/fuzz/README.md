# Fuzzing the node's network decoders

Fuzz targets for the bead sync protocol, built on
[`cargo-fuzz`](https://github.com/rust-fuzz/cargo-fuzz) (libFuzzer).

`BeadCodec` reads a peer's bytes into a buffer and hands them straight to
`consensus_decode`. Each target below calls that same function on arbitrary
bytes, so any panic it finds is reachable by a remote peer.

## Setup

`cargo-fuzz` needs a nightly toolchain:

```
rustup toolchain install nightly
cargo install cargo-fuzz
```

## Run

From the `node` crate directory:

```
cargo +nightly fuzz build
cargo +nightly fuzz run bead_response_decode
```

Add a time budget with `-- -max_total_time=60` for a bounded run. Crashes are
written to `fuzz/artifacts/<target>/` and replayed with:

```
cargo +nightly fuzz run <target> fuzz/artifacts/<target>/<crash-file>
```

## Targets

| Target | Decodes | Mirrors |
|---|---|---|
| `bead_decode` | `Bead` | the payload inside sync responses |
| `bead_request_decode` | `BeadRequest` | `BeadCodec::read_request` |
| `bead_response_decode` | `BeadResponse` | `BeadCodec::read_response` |

`bead_response_decode` is the broadest: the `Beads` and `GetAllBeads` variants
carry full `Bead` values, so it reaches every nested metadata decoder.

## Adding a target

1. Create `fuzz_targets/<name>.rs` with a `fuzz_target!` closure.
2. Add a matching `[[bin]]` entry in `fuzz/Cargo.toml`.
3. Call the decoder on `&mut &data[..]`, matching the codec's call shape.

Decode errors are the expected outcome for random bytes and are ignored; the
targets only care about panics.
