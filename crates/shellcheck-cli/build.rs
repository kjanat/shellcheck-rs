//! Exposes the upstream ShellCheck pin from `upstream.json` to the CLI and
//! generates the completion scripts it embeds.

use sha2::{Digest, Sha256};
use std::error::Error;
use std::fmt::Write as _;
use std::path::PathBuf;

#[cfg(feature = "completions")]
#[path = "src/completion_generator.rs"]
mod completion_generator;
#[cfg(feature = "completions")]
#[path = "src/option_table.rs"]
mod option_table;
#[path = "src/oracle.rs"]
mod oracle;

fn main() -> Result<(), Box<dyn Error>> {
    let pin = PathBuf::from(std::env::var("CARGO_MANIFEST_DIR")?).join("upstream.json");
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
    let out = PathBuf::from(std::env::var("OUT_DIR")?);
    // Cargo owns OUT_DIR per package/build configuration. Checks, feature-off
    // builds and other checkouts must never mutate a final binary's assets.
    #[allow(unused_mut)]
    let mut files = std::collections::BTreeMap::<String, String>::new();
    #[cfg(feature = "completions")]
    {
        for source in ["src/completion_generator.rs", "src/option_table.rs"] {
            println!("cargo:rerun-if-changed={source}");
        }
        for shell in option_table::Shell::ALL {
            let script = completion_generator::generate(shell)?;
            let path = out.join(shell.file_name());
            stage(&path, &script)?;
            println!("cargo:rerun-if-changed={}", path.display());
            files.insert(format!("completions/{}", shell.file_name()), script);
        }
    }
    // A single producer-owned bundle is exported explicitly after linking.
    // Packaging never discovers Cargo outputs or runs a target executable.
    let payload = out.join("release-assets.json");
    let contents = serde_json::to_string(&files)?;
    stage(&payload, &contents)?;
    println!("cargo:rerun-if-changed={}", payload.display());
    let identity = out.join("release-asset-identity");
    let mut digest = String::with_capacity(64);
    for byte in Sha256::digest(contents.as_bytes()) {
        write!(&mut digest, "{byte:02x}")?;
    }
    stage(
        &identity,
        &format!("RSHELLCHECK-ASSETS-SHA256:{digest}:END"),
    )?;
    println!("cargo:rerun-if-changed={}", identity.display());
    Ok(())
}

/// Writes `contents` to `path` unless the file already holds them. Cargo
/// reruns this script while a watched file is newer than the last run.
fn stage(path: &std::path::Path, contents: &str) -> std::io::Result<()> {
    if std::fs::read(path).is_ok_and(|current| current == contents.as_bytes()) {
        return Ok(());
    }
    std::fs::write(path, contents)
}
