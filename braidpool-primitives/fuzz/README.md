# Fuzzing braidpool-primitives

Fuzz targets for the core data structures, built on
[`cargo-fuzz`](https://github.com/rust-fuzz/cargo-fuzz) (libFuzzer).

## Setup

`cargo-fuzz` needs a nightly toolchain:

```
rustup toolchain install nightly
cargo install cargo-fuzz
```

## Run

From the `braidpool-primitives` crate directory:

```
cargo +nightly fuzz build
cargo +nightly fuzz run merkle_path_proof
```

Add a time budget with `-- -max_total_time=60` for a bounded run. Crashes are
written to `fuzz/artifacts/<target>/` and replayed with:

```
cargo +nightly fuzz run merkle_path_proof fuzz/artifacts/merkle_path_proof/<crash-file>
```

## Targets

| Target | Exercises |
|---|---|
| `merkle_path_proof` | `MerklePathProof::calculate_corresponding_merkle_root` on arbitrary proof shapes, including empty and single-element paths across both `is_right_leaf` branches. |

## Adding a target

1. Create `fuzz_targets/<name>.rs` with a `fuzz_target!` closure.
2. Add a matching `[[bin]]` entry in `fuzz/Cargo.toml`.
3. Build structured inputs from `&[u8]` with `arbitrary::Unstructured`.

Targets are intentionally thin so they can be retargeted as the core
structures change.
