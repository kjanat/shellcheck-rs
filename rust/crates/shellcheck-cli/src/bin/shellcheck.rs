//! ShellCheck CLI (Rust port). Reads scripts from files or stdin, runs the
//! analyzer core, and emits the requested format.
//!
//! Option parsing lives in `shellcheck_cli::options` and mirrors the Haskell
//! `shellcheck.hs` driver (option set, `getOpt Permute` semantics, exit codes).
//! Supported formats: `json1` (used by the conformance harness) and a terse
//! `tty` default.

use std::io::{Read, Write};
use std::process::ExitCode;

use shellcheck_cli::formatter::json1;
use shellcheck_cli::options::{self, Outcome, RunConfig};
use shellcheck_rs::interface::{CheckSpec, PositionedComment};

fn main() -> ExitCode {
    let argv: Vec<String> = std::env::args().skip(1).collect();

    let config = match options::parse(&argv) {
        Outcome::Run(c) => c,
        Outcome::PrintVersion => {
            println!("{}", options::version_banner());
            return ExitCode::SUCCESS;
        }
        Outcome::PrintHelp => {
            print!("{}", options::usage());
            return ExitCode::SUCCESS;
        }
        Outcome::ListOptional => {
            // The port has no optional-check registry yet; mirror the exit-0
            // behaviour with an empty listing.
            return ExitCode::SUCCESS;
        }
        Outcome::Error { message, code } => {
            eprintln!("{message}");
            return ExitCode::from(code);
        }
    };

    run(config)
}

fn run(config: RunConfig) -> ExitCode {
    let RunConfig { format, inputs, spec_template } = config;

    let mut all: Vec<PositionedComment> = Vec::new();
    for input in &inputs {
        let (name, content) = if input == "-" {
            let mut s = String::new();
            if std::io::stdin().read_to_string(&mut s).is_err() {
                eprintln!("shellcheck-rs: failed to read stdin");
                return ExitCode::from(2);
            }
            ("-".to_string(), s)
        } else {
            match std::fs::read_to_string(input) {
                Ok(s) => (input.clone(), s),
                Err(e) => {
                    eprintln!("shellcheck-rs: {input}: {e}");
                    return ExitCode::from(2);
                }
            }
        };
        let spec = CheckSpec {
            filename: name,
            script: content,
            ..spec_template.clone()
        };
        let result = shellcheck_rs::check_script(&spec);
        all.extend(result.comments);
    }

    let stdout = std::io::stdout();
    let mut out = stdout.lock();
    match format.as_str() {
        "json1" => {
            let _ = writeln!(out, "{}", json1::render(&all));
        }
        _ => {
            // Terse "tty" default (full TTY formatter ported later).
            for c in &all {
                let _ = writeln!(
                    out,
                    "{}:{}:{}: {} SC{}: {}",
                    c.start.file, c.start.line, c.start.column,
                    c.comment.severity.as_str(), c.comment.code, c.comment.message
                );
            }
        }
    }

    if all.is_empty() {
        ExitCode::SUCCESS
    } else {
        ExitCode::from(1)
    }
}
