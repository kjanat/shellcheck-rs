//! Exposes the upstream ShellCheck pin from `upstream.json` to the CLI and
//! generates the completion scripts it embeds.

use std::error::Error;
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
    #[cfg(feature = "completions")]
    {
        let out = PathBuf::from(std::env::var("OUT_DIR")?);
        for source in ["src/completion_generator.rs", "src/option_table.rs"] {
            println!("cargo:rerun-if-changed={source}");
        }
        for shell in option_table::Shell::ALL {
            std::fs::write(
                out.join(shell.file_name()),
                completion_generator::generate(shell)?,
            )?;
        }
    }
    Ok(())
}
