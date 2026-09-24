use std::path::PathBuf;

fn main() {
    let entry = std::env::var_os("H2R_ENTRY_DIR").map_or_else(
        || {
            PathBuf::from(
                std::env::var_os("CARGO_MANIFEST_DIR").expect("cargo sets CARGO_MANIFEST_DIR"),
            )
            .join("../build/rshellcheck")
        },
        PathBuf::from,
    );
    println!("cargo::rerun-if-env-changed=H2R_ENTRY_DIR");
    println!(
        "cargo::rerun-if-changed={}",
        entry.join("libh2r_entry.rlib").display()
    );
    println!("cargo::rustc-link-search=all={}", entry.display());
}
