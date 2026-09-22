//! Compiling the emitted Rust and comparing it against the Haskell oracle.
//!
//! Each entry is compiled twice. `-O` is the configuration the output is meant
//! to be used in; `-C overflow-checks=yes` turns every wrapping `Int#` result
//! this backend emits into a panic, so an arithmetic boundary the lowering got
//! wrong stops being a silent difference in the low bits.

use std::path::{Path, PathBuf};
use std::process::Command;

/// The two ways every entry is compiled.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Mode {
    Optimized,
    OverflowChecked,
}

impl Mode {
    pub const ALL: [Mode; 2] = [Mode::Optimized, Mode::OverflowChecked];

    pub fn suffix(self) -> &'static str {
        match self {
            Mode::Optimized => "",
            Mode::OverflowChecked => "-checked",
        }
    }

    fn flags(self) -> &'static [&'static str] {
        match self {
            Mode::Optimized => &["-O"],
            Mode::OverflowChecked => &["-C", "overflow-checks=yes"],
        }
    }
}

pub fn compile(source: &Path, binary: &Path, mode: Mode) -> Result<(), String> {
    let output = Command::new("rustc")
        .arg("--edition=2024")
        .args(mode.flags())
        .arg(source)
        .arg("-o")
        .arg(binary)
        .output()
        .map_err(|error| format!("running rustc: {error}"))?;
    if output.status.success() {
        return Ok(());
    }
    Err(format!(
        "rustc rejected {}:\n{}",
        source.display(),
        String::from_utf8_lossy(&output.stderr)
    ))
}

/// Compile the `--test` harness that reads the emitted boxed entries, and run
/// it. `H2R_CANARY_DIR` is how it finds them.
pub fn boxed_checks(source: &Path, binary: &Path, canary_dir: &Path) -> Result<(), String> {
    let compiled = Command::new("rustc")
        .arg("--edition=2024")
        .arg("--test")
        .arg(source)
        .arg("-o")
        .arg(binary)
        .env("H2R_CANARY_DIR", canary_dir)
        .output()
        .map_err(|error| format!("running rustc: {error}"))?;
    if !compiled.status.success() {
        return Err(format!(
            "rustc rejected {}:\n{}",
            source.display(),
            String::from_utf8_lossy(&compiled.stderr)
        ));
    }
    let ran = Command::new(binary)
        .output()
        .map_err(|error| format!("running {}: {error}", binary.display()))?;
    if ran.status.success() {
        return Ok(());
    }
    Err(format!(
        "{} failed:\n{}{}",
        binary.display(),
        String::from_utf8_lossy(&ran.stdout),
        String::from_utf8_lossy(&ran.stderr)
    ))
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Outcome {
    pub stdout: Vec<u8>,
    pub stderr: Vec<u8>,
    /// `None` when the process was killed by a signal.
    pub code: Option<i32>,
}

pub fn invoke(program: &Path, arguments: &[String]) -> Result<Outcome, String> {
    let output = Command::new(program)
        .args(arguments)
        .output()
        .map_err(|error| format!("running {}: {error}", program.display()))?;
    Ok(Outcome {
        stdout: output.stdout,
        stderr: output.stderr,
        code: output.status.code(),
    })
}

/// One differential case: the same entry, the same arguments, two programs.
#[derive(Debug, Clone)]
pub struct Case {
    pub occ: &'static str,
    pub mode: Mode,
    pub arguments: Vec<i64>,
}

impl Case {
    pub fn label(&self) -> String {
        let arguments: Vec<String> = self.arguments.iter().map(i64::to_string).collect();
        format!("{}{} {}", self.occ, self.mode.suffix(), arguments.join(" "))
    }
}

/// What differed, in the words of the thing that differed.
pub fn compare(case: &Case, oracle: &Outcome, candidate: &Outcome) -> Vec<String> {
    let mut differences = Vec::new();
    if oracle.stdout != candidate.stdout {
        differences.push(format!(
            "{}: stdout {:?} from GHC, {:?} from Rust",
            case.label(),
            String::from_utf8_lossy(&oracle.stdout),
            String::from_utf8_lossy(&candidate.stdout)
        ));
    }
    if oracle.stderr != candidate.stderr {
        differences.push(format!(
            "{}: stderr {:?} from GHC, {:?} from Rust",
            case.label(),
            String::from_utf8_lossy(&oracle.stderr),
            String::from_utf8_lossy(&candidate.stderr)
        ));
    }
    if oracle.code != candidate.code {
        differences.push(format!(
            "{}: exit {:?} from GHC, {:?} from Rust",
            case.label(),
            oracle.code,
            candidate.code
        ));
    }
    if oracle.code != Some(0) {
        differences.push(format!(
            "{}: the oracle itself did not succeed ({:?})",
            case.label(),
            oracle.code
        ));
    }
    differences
}

/// Where one entry's artifacts live.
pub struct Artifacts {
    pub source: PathBuf,
    pub binaries: [PathBuf; 2],
}

pub fn artifacts(out: &Path, occ: &str) -> Artifacts {
    Artifacts {
        source: out.join(format!("{occ}.rs")),
        binaries: [
            out.join(occ),
            out.join(format!("{occ}{}", Mode::OverflowChecked.suffix())),
        ],
    }
}

impl Artifacts {
    pub fn binary(&self, mode: Mode) -> &Path {
        match mode {
            Mode::Optimized => &self.binaries[0],
            Mode::OverflowChecked => &self.binaries[1],
        }
    }
}
