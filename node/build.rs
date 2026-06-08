use std::{
    env, fs,
    path::{Path, PathBuf},
};

fn main() {
    let manifest_dir = env::var("CARGO_MANIFEST_DIR").unwrap();
    let schema_dir = Path::new(&manifest_dir).join("schema");

    // Rebuild if the schema directory or Cargo.toml is touched.
    println!("cargo::rerun-if-changed=schema");
    println!(
        "cargo::rerun-if-changed={}",
        Path::new(&manifest_dir).join("Cargo.toml").display()
    );

    // Rebuild when cross-compilation target or the capnp binary path changes.
    println!("cargo::rerun-if-env-changed=TARGET");
    println!("cargo::rerun-if-env-changed=HOST");
    println!("cargo::rerun-if-env-changed=CAPNP");

    //  Reading architecture and OS for platform-specific linker configuration
    let target_os = env::var("CARGO_CFG_TARGET_OS").unwrap_or_default();
    let target_arch = env::var("CARGO_CFG_TARGET_ARCH").unwrap_or_default();

    configure_platform_linking(&target_os, &target_arch);

    compile_schemas(&schema_dir);
}

/// linker instructions according to OS and architecture
fn configure_platform_linking(target_os: &str, target_arch: &str) {
    match target_os {
        "macos" => {
            // Homebrew installs differ by CPU architecture on macOS.
            let homebrew_lib = if target_arch == "aarch64" {
                // Apple Silicon – Homebrew lives under /opt/homebrew
                "/opt/homebrew/lib"
            } else {
                // Intel Mac – Homebrew lives under /usr/local
                "/usr/local/lib"
            };
            println!("cargo::rustc-link-search=native={homebrew_lib}");
        }
        "linux" => {
            println!("cargo::rustc-link-search=native=/usr/local/lib");
            println!("cargo::rustc-link-search=native=/usr/lib");
        }
        _ => {}
    }
}

/// Resolve the Cap'n Proto compiler binary in a cross-platform way.
fn capnp_executable() -> PathBuf {
    if let Ok(explicit) = env::var("CAPNP") {
        return PathBuf::from(explicit);
    }
    PathBuf::from("capnp")
}

/// Walk `schema_dir` and compile every `*.capnp` file it contains.
fn compile_schemas(schema_dir: &Path) {
    let capnp = capnp_executable();

    match fs::read_dir(schema_dir) {
        Ok(entries) => {
            for entry in entries.flatten() {
                let path = entry.path();
                if path.extension().and_then(|e| e.to_str()) != Some("capnp") {
                    continue;
                }

                let mut cmd = capnpc::CompilerCommand::new();

                // Point at our custom binary if the default would not be found.
                // `capnp_executable()` already checked $CAPNP; we only set it
                // when the result differs from the bare "capnp" default.
                if capnp.to_str() != Some("capnp") {
                    cmd.capnp_executable(&capnp);
                }

                // `src_prefix` strips the leading path component so generated
                if let Err(e) = cmd.src_prefix("schema").file(&path).run() {
                    println!("cargo::error=Failed to compile {}: {e}", path.display());
                }
            }
        }
        Err(e) => {
            println!(
                "cargo::error=Failed to read schema directory '{}': {e}",
                schema_dir.display()
            );
        }
    }
}
