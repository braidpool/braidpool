use std::{fs, path::Path};

fn main() {
    //Fetching the `capnp` schema files and generating the corresponding rust-bindings during build-time before the
    //compilation of other workspace members
    let package_manifest_dir = std::env::var("CARGO_MANIFEST_DIR").unwrap();
    let schema_dir = Path::new(&package_manifest_dir).join("schema");
    //Re-running build-script only if schema dir is updated or `CARGO_MANIFEST_DIR` is changed for some custom output paths
    println!("cargo:rerun-if-changed=schema");
    println!(
        "cargo:rerun-if-changed={}",
        Path::new(&package_manifest_dir)
            .join("Cargo.toml")
            .display()
    );

    match fs::read_dir(&schema_dir) {
        Ok(entries) => {
            for entry in entries {
                match entry {
                    Ok(entry) => {
                        let path = entry.path();
                        if path.extension().and_then(|ext| ext.to_str()) == Some("capnp") {
                            println!("cargo:warning=Compiling schema file: {:?}", path);
                            //The output path for rust bindings is default `OUT_DIR` -
                            if let Err(e) = capnpc::CompilerCommand::new()
                                .src_prefix("schema")
                                .file(&path)
                                .run()
                            {
                                println!("cargo:error=Failed to compile {:?}: {}", path, e);
                            }
                        }
                    }
                    Err(e) => {
                        println!(
                            "cargo:error=Failed to process entry in schema directory: {}",
                            e
                        );
                    }
                }
            }
        }
        Err(e) => {
            println!("cargo:error=Failed to read schema directory: {}", e);
        }
    }
}
