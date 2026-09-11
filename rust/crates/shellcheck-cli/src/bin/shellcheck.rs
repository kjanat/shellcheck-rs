//! ShellCheck CLI (Rust port). Minimal driver: reads scripts from files or
//! stdin, runs the analyzer core, and emits the requested format.
//!
//! Currently supports `--format=json1` (used by the conformance harness) and a
//! terse default. More formats and options are ported alongside the core.

use std::io::{Read, Write};
use std::process::ExitCode;

use shellcheck_cli::formatter::json1;
use shellcheck_rs::interface::{CheckSpec, PositionedComment};

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let mut format = "tty".to_string();
    let mut inputs: Vec<String> = Vec::new();
    let mut shell: Option<String> = None;

    let mut i = 0;
    while i < args.len() {
        let a = &args[i];
        if let Some(f) = a.strip_prefix("--format=") {
            format = f.to_string();
        } else if a == "--format" || a == "-f" {
            i += 1;
            if i < args.len() {
                format = args[i].clone();
            }
        } else if let Some(s) = a.strip_prefix("--shell=") {
            shell = Some(s.to_string());
        } else if a == "-" {
            inputs.push("-".to_string());
        } else if a.starts_with('-') && a.len() > 1 {
            // ignore unknown flags for now
        } else {
            inputs.push(a.clone());
        }
        i += 1;
    }
    if inputs.is_empty() {
        inputs.push("-".to_string());
    }

    let shell_override = shell.as_deref().and_then(parse_shell);

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
            shell_type_override: shell_override,
            ..Default::default()
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
            // Terse default (full TTY formatter ported later).
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

fn parse_shell(s: &str) -> Option<shellcheck_rs::interface::Shell> {
    use shellcheck_rs::interface::Shell::*;
    Some(match s {
        "sh" => Sh,
        "bash" => Bash,
        "dash" => Dash,
        "ksh" => Ksh,
        "busybox" => BusyboxSh,
        _ => return None,
    })
}
