//! Exposes the upstream ShellCheck pin from `tools/oracle.json` to the CLI.

use std::error::Error;
use std::path::PathBuf;

fn main() -> Result<(), Box<dyn Error>> {
    let pin = PathBuf::from(std::env::var("CARGO_MANIFEST_DIR")?).join("../../tools/oracle.json");
    println!("cargo:rerun-if-changed={}", pin.display());
    let json: serde_json::Value = serde_json::from_str(&std::fs::read_to_string(&pin)?)?;
    for (key, name) in [
        ("version", "RSHELLCHECK_UPSTREAM_VERSION"),
        ("revision", "RSHELLCHECK_UPSTREAM_REVISION"),
    ] {
        let value = json[key]
            .as_str()
            .ok_or_else(|| format!("{} lacks a string {key}", pin.display()))?;
        println!("cargo:rustc-env={name}={value}");
    }
    Ok(())
}
