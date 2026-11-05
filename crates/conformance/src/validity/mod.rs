//! The validity matrix: each diagnostic's reproducer and its fix run in real
//! shells, one container per shell and version. See `docs/validity.md`.

pub mod docker;
pub mod matrix;
pub mod outcomes;
mod pin;
mod rules;
mod run;
pub mod sources;
pub mod spec;

use std::io::Write;
use std::path::Path;
use std::process::{Command, Stdio};

use clap::ValueEnum;

pub const SOURCES: &str = "validity/sources.toml";
pub const MATRIX: &str = "validity/matrix.toml";
pub const SPECS: &str = "validity/specs";
pub const OUTCOMES: &str = "validity/outcomes.toml";
pub const REPORT: &str = "validity/REPORT.md";
pub const RULES: &str = "crates/shellcheck-rs/src/dialect_rules.rs";
pub const DOCKERFILES: &str = "docker/shells";
pub const REGISTRY: &str = "ghcr.io/kjanat/shellcheck-rs";
pub const SOURCE_URL: &str = "https://github.com/kjanat/shellcheck-rs";

/// Which part of the matrix to run.
#[derive(Clone, Copy, PartialEq, Eq, ValueEnum, Default)]
pub enum Step {
    /// Run every spec in every cell and compare with the recorded outcomes.
    #[default]
    Run,
    /// Resolve `sources.toml` into `matrix.toml`.
    Pin,
    /// Build the cell images, and push them with `--push`.
    Build,
    /// Print the cell ids as a JSON array.
    Cells,
    /// Write the added dialects' outcomes to `dialect_rules.rs`.
    Rules,
}

/// The options under the "Validity" heading.
#[derive(clap::Args)]
pub struct ValidityArgs {
    /// Rewrite `outcomes.toml` and `REPORT.md` with this run's results.
    #[arg(long, help_heading = "Validity")]
    pub record: bool,

    /// Push built images and record their digests (build only).
    #[arg(long, help_heading = "Validity")]
    pub push: bool,

    /// Re-resolve git tags and base image digests instead of keeping the
    /// recorded ones (pin only).
    #[arg(long, help_heading = "Validity")]
    pub refresh: bool,

    /// Only these cells, as `shell` or `shell:version`. Repeatable.
    #[arg(long, help_heading = "Validity")]
    pub cell: Vec<String>,

    /// Only these diagnostic codes. Repeatable.
    #[arg(long, help_heading = "Validity")]
    pub code: Vec<i64>,
}

pub fn formatted(path: &Path, text: &str) -> Result<String, String> {
    let path = std::path::absolute(path).map_err(|e| format!("{}: {e}", path.display()))?;
    let (Some(dir), Some(name)) = (path.parent(), path.file_name()) else {
        return Err(format!("{}: no file name", path.display()));
    };
    let mut child = Command::new("npx")
        .args(["--yes", "@kjanat/fmt", "--stdin"])
        .arg(name)
        .current_dir(dir)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(|e| format!("npx @kjanat/fmt: {e}"))?;
    let mut stdin = child
        .stdin
        .take()
        .ok_or_else(|| "npx @kjanat/fmt: no stdin".to_string())?;
    let output = std::thread::scope(|scope| {
        let writer = scope.spawn(move || stdin.write_all(text.as_bytes()));
        let output = child.wait_with_output();
        let written = writer
            .join()
            .map_err(|_| "npx @kjanat/fmt: stdin writer panicked".to_string())?;
        written.map_err(|e| format!("npx @kjanat/fmt: {e}"))?;
        output.map_err(|e| format!("npx @kjanat/fmt: {e}"))
    })?;
    if !output.status.success() {
        return Err(format!(
            "npx @kjanat/fmt {}: {}",
            path.display(),
            String::from_utf8_lossy(&output.stderr)
        ));
    }
    String::from_utf8(output.stdout).map_err(|e| format!("npx @kjanat/fmt: {e}"))
}

pub fn run(step: Step, args: &ValidityArgs) -> Result<bool, String> {
    match step {
        Step::Pin => pin::run(args.refresh).map(|()| true),
        Step::Build => docker::build_all(args).map(|()| true),
        Step::Cells => {
            let matrix = matrix::load()?;
            let ids: Vec<String> = matrix.cells(&args.cell).map(matrix::Cell::id).collect();
            println!(
                "{}",
                serde_json::to_string(&ids).map_err(|e| e.to_string())?
            );
            Ok(true)
        }
        Step::Run => run::run(args),
        Step::Rules => rules::run().map(|()| true),
    }
}
