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
    let out = PathBuf::from(std::env::var("OUT_DIR")?);
    let profile = out
        .ancestors()
        .find(|directory| directory.file_name().is_some_and(|name| name == "build"))
        .and_then(std::path::Path::parent)
        .ok_or("OUT_DIR has no build profile directory")?;
    let assets = profile.join("rshellcheck.assets");
    // The packager archives exactly the files this manifest lists.
    let manifest = profile.join("rshellcheck.assets.manifest");
    #[cfg(not(feature = "completions"))]
    {
        if manifest.is_file() {
            std::fs::remove_file(&manifest)?;
        }
        if assets.is_dir() {
            std::fs::remove_dir_all(&assets)?;
        }
        println!("cargo:rerun-if-changed={}", assets.display());
    }
    #[cfg(feature = "completions")]
    {
        let assets = assets.join("completions");
        let mut staged_names = String::new();
        for source in ["src/completion_generator.rs", "src/option_table.rs"] {
            println!("cargo:rerun-if-changed={source}");
        }
        std::fs::create_dir_all(&assets)?;
        for shell in option_table::Shell::ALL {
            let script = completion_generator::generate(shell)?;
            std::fs::write(out.join(shell.file_name()), &script)?;
            let staged = assets.join(shell.file_name());
            stage(&staged, &script)?;
            // Restore staged artifacts if a cache cleanup deletes or replaces them.
            println!("cargo:rerun-if-changed={}", staged.display());
            staged_names.push_str("completions/");
            staged_names.push_str(shell.file_name());
            staged_names.push('\n');
        }
        stage(&manifest, &staged_names)?;
        println!("cargo:rerun-if-changed={}", manifest.display());
    }
    Ok(())
}

/// Writes `contents` to `path` unless the file already holds them. Cargo
/// reruns this script while a watched file is newer than the last run.
#[cfg(feature = "completions")]
fn stage(path: &std::path::Path, contents: &str) -> std::io::Result<()> {
    if std::fs::read(path).is_ok_and(|current| current == contents.as_bytes()) {
        return Ok(());
    }
    std::fs::write(path, contents)
}
