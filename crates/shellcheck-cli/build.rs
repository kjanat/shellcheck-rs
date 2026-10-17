//! Exposes the upstream ShellCheck pin from `tools/oracle.json` to the CLI.

use std::error::Error;
use std::path::PathBuf;

#[path = "src/oracle.rs"]
mod oracle;

fn main() -> Result<(), Box<dyn Error>> {
    let pin = PathBuf::from(std::env::var("CARGO_MANIFEST_DIR")?).join("../../tools/oracle.json");
    println!("cargo:rerun-if-changed={}", pin.display());
    let pin: oracle::UpstreamPin = serde_json::from_str(&std::fs::read_to_string(&pin)?)?;
    println!(
        "cargo:rustc-env=RSHELLCHECK_UPSTREAM_VERSION={}",
        pin.version
    );
    println!(
        "cargo:rustc-env=RSHELLCHECK_UPSTREAM_REVISION={}",
        pin.revision
    );
    Ok(())
}
