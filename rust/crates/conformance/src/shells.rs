//! External validity: do the tools agree with the shells they lint for?
//!
//! `gate` and `fuzz` establish *internal* validity — the port says what the
//! Haskell says. Both could be wrong together, and on a parse decision that is
//! not hypothetical: ShellCheck rejects `! # comment`, which bash runs.
//!
//! This mode asks the shells instead. For each script it compares two verdicts
//! per dialect:
//!
//! * the shell's: `<shell> -n`, which parses without running anything;
//! * each tool's: whether it reported the fatal parse trio (SC1073/SC1009/
//!   SC1072), which is exactly when it refuses to analyse the file.
//!
//! and sorts the disagreements into the two that matter:
//!
//! * **rejects-valid** — the shell accepts the script, the tool refuses to
//!   parse it. The expensive direction: the user gets no analysis at all for a
//!   script that runs.
//! * **accepts-invalid** — the shell rejects it, the tool analyses it happily.
//!   A syntax error the user is not told about.
//!
//! Both tools are measured the same way, so the oracle's own numbers are the
//! baseline: the port should be no worse, and where it is better that is a
//! sanctioned deviation (see [`crate::deviations`]).
//!
//! ## What this does not prove
//!
//! `-n` is a syntax check. A script can parse and still be nonsense at runtime,
//! and shells differ in what they defer to runtime, so "accepts" here is a
//! weaker claim than "works". The dialect mapping is also a judgement call:
//! `sh` is checked with dash, which is a POSIX shell but not *the* POSIX shell,
//! and `busybox` with `busybox sh`. Where a shell is not installed its dialect
//! is skipped and the report says so rather than quietly passing.

use std::collections::BTreeMap;
use std::io::Write;
use std::process::{Command, Stdio};

use crate::corpus;
use crate::fuzz::{Rng, generate};
use crate::oracle::Oracle;
use crate::{Args, port_keys};
use shellcheck_rs::interface::DiagnosticCode;

use crate::deviations::FATAL_PARSE_CODES;

/// ShellCheck's dialects, and the interpreter that speaks each one.
///
/// `ksh` is AT&T ksh93, the shell ShellCheck's ksh support is written against —
/// mksh is a different shell and is deliberately not used as a stand-in.
const DIALECTS: [(&str, &str, &[&str]); 4] = [
    ("bash", "bash", &["-n"]),
    ("sh", "dash", &["-n"]),
    ("ksh", "ksh93", &["-n"]),
    ("busybox", "busybox", &["sh", "-n"]),
];

#[derive(Default)]
struct Tally {
    checked: usize,
    rejects_valid: usize,
    accepts_invalid: usize,
    /// One smallest example of each disagreement, to make the number actionable.
    example_rejects_valid: Option<String>,
    example_accepts_invalid: Option<String>,
}

/// Ask a shell whether a script parses. `None` when the shell cannot be run at
/// all, which the caller reports rather than silently treating as agreement.
fn shell_parses(program: &str, args: &[&str], script: &str) -> Option<bool> {
    let mut child = Command::new(program)
        .args(args)
        .stdin(Stdio::piped())
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .spawn()
        .ok()?;
    child.stdin.as_mut()?.write_all(script.as_bytes()).ok()?;
    Some(child.wait().ok()?.success())
}

fn tool_parses(codes: &[DiagnosticCode]) -> bool {
    !codes.iter().any(|c| FATAL_PARSE_CODES.contains(c))
}

fn note(slot: &mut Option<String>, script: &str) {
    match slot {
        Some(existing) if existing.len() <= script.len() => {}
        _ => *slot = Some(script.to_string()),
    }
}

pub fn run(args: &Args) -> Result<bool, String> {
    let oracle = Oracle::new(args.oracle())?;
    println!(
        "{}",
        crate::oracle::verify(&oracle, &args.repo, args.any_oracle_version())?
    );

    // The same inputs the fuzzer uses: upstream's property scripts, plus
    // generated and mutated shell.
    let src = std::path::Path::new(&args.repo).join("src/ShellCheck");
    let seeds: Vec<String> = corpus::extract(&src)
        .map(|e| e.into_iter().map(|x| x.script).collect())
        .unwrap_or_default();
    let mut rng = Rng::new(args.fuzzing.seed.wrapping_add(7));
    let mut scripts: Vec<String> = seeds.clone();
    for _ in 0..args.fuzzing.iterations {
        scripts.push(generate(&mut rng, &seeds));
    }

    let mut tallies: Tallies = BTreeMap::new();
    let mut missing: Vec<&str> = Vec::new();

    for (dialect, program, flags) in DIALECTS {
        if shell_parses(program, flags, ":\n").is_none() {
            missing.push(dialect);
            continue;
        }
        // One oracle invocation per batch of scripts, as everywhere else.
        for chunk in scripts.chunks(crate::oracle::BATCH) {
            let named: Vec<(String, String)> =
                chunk.iter().map(|s| (oracle.name(), s.clone())).collect();
            let by_name = oracle.check(&named, Some(dialect))?;
            for (name, script) in &named {
                let Some(ocomments) = by_name.get(name) else {
                    continue;
                };
                let Some(shell_ok) = shell_parses(program, flags, script) else {
                    continue;
                };
                let ocodes: Vec<DiagnosticCode> = crate::oracle_keys(ocomments)
                    .iter()
                    .map(|k| k.code)
                    .collect();
                let path = oracle.dir().join(name);
                let pcodes: Vec<DiagnosticCode> =
                    port_keys(script, &path.to_string_lossy(), Some(dialect))?
                        .iter()
                        .map(|k| k.code)
                        .collect();

                let (oracle_tally, port_tally) = tallies.entry(dialect).or_default();
                for (tally, codes) in [(oracle_tally, &ocodes), (port_tally, &pcodes)] {
                    tally.checked += 1;
                    match (shell_ok, tool_parses(codes)) {
                        (true, false) => {
                            tally.rejects_valid += 1;
                            note(&mut tally.example_rejects_valid, script);
                        }
                        (false, true) => {
                            tally.accepts_invalid += 1;
                            note(&mut tally.example_accepts_invalid, script);
                        }
                        _ => {}
                    }
                }
            }
        }
    }

    report(&tallies, &missing);

    // This mode reports; it does not gate. Both tools disagree with the shells
    // in both directions today, by design in places (ShellCheck rejects some
    // valid-but-awful syntax on purpose), so a threshold would be arbitrary
    // until the numbers have been read and triaged.
    Ok(true)
}

/// Per dialect: the oracle's tally, then the port's.
type Tallies<'a> = BTreeMap<&'a str, (Tally, Tally)>;

fn report(tallies: &Tallies<'_>, missing: &[&str]) {
    println!(
        "\nexternal validity: does each tool's idea of \"this parses\" match the shell's?\n\
         (rejects-valid = shell runs it, tool refuses to analyse; \
         accepts-invalid = shell rejects it, tool analyses anyway)\n"
    );
    println!(
        "{:<9} {:>8}  {:>18} {:>18}",
        "dialect", "scripts", "rejects-valid", "accepts-invalid"
    );
    for (dialect, _, _) in DIALECTS {
        let Some((o, p)) = tallies.get(dialect) else {
            continue;
        };
        println!(
            "{dialect:<9} {:>8}  {:>8} / {:<7} {:>8} / {:<7}",
            p.checked,
            format!("{}", p.rejects_valid),
            format!("o:{}", o.rejects_valid),
            format!("{}", p.accepts_invalid),
            format!("o:{}", o.accepts_invalid),
        );
    }
    if !missing.is_empty() {
        println!(
            "\nnot measured (interpreter not installed): {}",
            missing.join(", ")
        );
    }
    for (dialect, _, _) in DIALECTS {
        let Some((_, p)) = tallies.get(dialect) else {
            continue;
        };
        if let Some(s) = &p.example_rejects_valid {
            println!("\n{dialect}: port rejects, {dialect} runs it:\n  {s:?}");
        }
        if let Some(s) = &p.example_accepts_invalid {
            println!("\n{dialect}: port analyses, {dialect} rejects it:\n  {s:?}");
        }
    }
}
