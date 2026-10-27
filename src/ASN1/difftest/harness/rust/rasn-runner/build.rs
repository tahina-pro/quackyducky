// Compiles ../../../schemas/*.asn into Rust bindings for rasn, with
// rasn-compiler.
use rasn_compiler::{prelude::*, OutputMode};
use std::path::PathBuf;

fn main() {
    let schemas = PathBuf::from(std::env::var("CARGO_MANIFEST_DIR").unwrap()).join("../../../schemas");
    println!("cargo:rerun-if-changed={}", schemas.display());
    let mut paths: Vec<PathBuf> = std::fs::read_dir(&schemas)
        .unwrap()
        .map(|e| e.unwrap().path())
        .filter(|p| p.extension().is_some_and(|e| e == "asn"))
        .collect();
    paths.sort();
    let out = PathBuf::from(std::env::var("OUT_DIR").unwrap()).join("generated.rs");
    match Compiler::<RasnBackend, _>::new()
        .add_asn_sources_by_path(paths.iter())
        .set_output_mode(OutputMode::SingleFile(out))
        .compile()
    {
        Ok(warnings) => {
            for w in warnings {
                println!("cargo:warning=rasn-compiler: {w}");
            }
        }
        Err(e) => panic!("rasn-compiler: {e}"),
    }
}
