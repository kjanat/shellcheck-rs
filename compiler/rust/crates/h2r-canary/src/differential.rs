//! Compiling the emitted Rust and comparing it against the Haskell oracle.
//!
//! Each entry is compiled twice. `-O` is the configuration the output is meant
//! to be used in; `-C overflow-checks=yes` turns every wrapping `Int#` result
//! this backend emits into a panic, so an arithmetic boundary the lowering got
//! wrong stops being a silent difference in the low bits.

use std::io::Read;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::thread::JoinHandle;
use std::time::{Duration, Instant};

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

pub fn invoke(program: &Path, arguments: &[String], timeout: Duration) -> Result<Outcome, String> {
    let mut child = Command::new(program)
        .args(arguments)
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(|error| format!("running {}: {error}", program.display()))?;
    let started = Instant::now();
    // Drain both pipes concurrently: waiting first can deadlock on full pipes.
    let [stdout, stderr] = [
        drain(Box::new(child.stdout.take().expect("piped stdout"))),
        drain(Box::new(child.stderr.take().expect("piped stderr"))),
    ];
    let mut status = None;
    let result = loop {
        match child.try_wait() {
            Ok(Some(exit)) => status = Some(exit),
            Ok(None) => {}
            Err(error) => break Err(format!("waiting for {}: {error}", program.display())),
        }
        if let Some(exit) = status
            && stdout.is_finished()
            && stderr.is_finished()
        {
            break Ok(exit);
        }
        if started.elapsed() >= timeout {
            break Err(format!(
                "{} {arguments:?}: timed out after {timeout:?}",
                program.display()
            ));
        }
        std::thread::sleep(Duration::from_millis(2));
    };
    if result.is_err() {
        // Kill and reap the generated executable/oracle before returning.
        // Descendant-process isolation is not provided by this runner.
        let killed = child
            .kill()
            .map_err(|error| format!("killing {}: {error}", program.display()));
        child
            .wait()
            .map_err(|error| format!("reaping {}: {error}", program.display()))?;
        killed?;
    }
    let status = result?;
    Ok(Outcome {
        stdout: collect(stdout, "stdout")?,
        stderr: collect(stderr, "stderr")?,
        code: status.code(),
    })
}

fn drain(mut reader: Box<dyn Read + Send>) -> JoinHandle<std::io::Result<Vec<u8>>> {
    std::thread::spawn(move || {
        let mut bytes = Vec::new();
        reader.read_to_end(&mut bytes).map(|_| bytes)
    })
}

fn collect(reader: JoinHandle<std::io::Result<Vec<u8>>>, stream: &str) -> Result<Vec<u8>, String> {
    reader
        .join()
        .map_err(|payload| {
            format!(
                "reading {stream}: {}",
                h2r_core_ir::panic_message(&*payload)
            )
        })?
        .map_err(|error| format!("reading {stream}: {error}"))
}

#[cfg(all(test, unix))]
mod tests {
    use super::*;

    fn shell(script: &str, timeout: Duration) -> Result<Outcome, String> {
        invoke(Path::new("/bin/sh"), &["-c".into(), script.into()], timeout)
    }

    #[test]
    fn nontermination_is_a_timeout_failure() {
        let start = Instant::now();
        let error = shell("while :; do :; done", Duration::from_millis(50)).unwrap_err();
        assert!(error.contains("timed out"), "{error}");
        assert!(start.elapsed() < Duration::from_secs(5));
    }

    #[test]
    fn pipes_are_drained_and_exit_codes_preserved() {
        let output = shell(
            "i=0; while [ $i -lt 10000 ]; do printf 'abcdefghij'; printf '0123456789' >&2; i=$((i+1)); done; exit 7",
            Duration::from_secs(10),
        ).unwrap();
        assert_eq!(output.stdout.len(), 100000);
        assert_eq!(output.stderr.len(), 100000);
        assert_eq!(output.code, Some(7));
    }

    #[test]
    fn explicit_failure_case_compares_real_process_output() {
        let oracle = shell("printf 'message\\n' >&2; exit 1", Duration::from_secs(2)).unwrap();
        let candidate = shell("printf 'message\\n' >&2; exit 1", Duration::from_secs(2)).unwrap();
        let mut case = Case {
            occ: "expectedFailure",
            mode: Mode::Optimized,
            arguments: vec![],
            expected_exit: 1,
        };
        assert!(compare(&case, &oracle, &candidate).is_empty());
        case.expected_exit = 0;
        assert!(!compare(&case, &oracle, &candidate).is_empty());
    }
}

#[cfg(test)]
mod comparison_tests {
    use super::*;

    fn case(mode: Mode, expected_exit: i32) -> Case {
        Case {
            occ: "failure",
            mode,
            arguments: vec![42],
            expected_exit,
        }
    }

    fn outcome(code: Option<i32>) -> Outcome {
        Outcome {
            stdout: vec![],
            stderr: b"exact error\n".to_vec(),
            code,
        }
    }

    #[test]
    fn expected_failure_still_requires_exact_streams_and_status() {
        for mode in Mode::ALL {
            let case = case(mode, 1);
            let oracle = outcome(Some(1));
            assert!(compare(&case, &oracle, &oracle).is_empty());
            for change in 0..5 {
                let mut candidate = oracle.clone();
                match change {
                    0 => candidate.stdout.push(b'x'),
                    1 => candidate.stderr.push(b'x'),
                    2 => candidate.code = Some(0),
                    3 => candidate.code = Some(2),
                    _ => candidate.code = None,
                }
                assert!(
                    !compare(&case, &oracle, &candidate).is_empty(),
                    "mutation {change}"
                );
            }
        }
    }

    #[test]
    fn matching_wrong_outcomes_cannot_satisfy_a_fixture() {
        for mode in Mode::ALL {
            for required in [0, 1] {
                for actual in [None, Some(2), Some(124)] {
                    let output = outcome(actual);
                    assert!(!compare(&case(mode, required), &output, &output).is_empty());
                }
            }
            let success = outcome(Some(0));
            assert!(!compare(&case(mode, 1), &success, &success).is_empty());
            let failure = outcome(Some(1));
            assert!(!compare(&case(mode, 0), &failure, &failure).is_empty());
        }
    }
}

/// One differential case: the same entry, the same arguments, two programs.
#[derive(Debug, Clone)]
pub struct Case {
    pub occ: &'static str,
    pub mode: Mode,
    pub arguments: Vec<i64>,
    pub expected_exit: i32,
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
    if oracle.code != Some(case.expected_exit) {
        differences.push(format!(
            "{}: oracle exit {:?} does not match required exit {}",
            case.label(),
            oracle.code,
            case.expected_exit
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
