//! ShellCheck CLI (Rust port). Reads scripts from files or stdin, runs the
//! analyzer core, and emits the requested format.
//!
//! Option parsing lives in `shellcheck_cli::options` and mirrors the Haskell
//! `shellcheck.hs` driver (option set, `getOpt Permute` semantics, exit codes).
//! Output formatting mirrors `ShellCheck.Formatter.*`: tty (default), gcc,
//! checkstyle, json, json1, quiet, and diff.

use std::io::{IsTerminal, Read, Write};
use std::process::ExitCode;

use shellcheck_cli::formatter::{
    self, checkstyle, diff, fixer, gcc, json, json1, tty,
};
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
            return ExitCode::SUCCESS;
        }
        Outcome::Error { message, code } => {
            eprintln!("{message}");
            return ExitCode::from(code);
        }
    };

    run(config)
}

/// One loaded input: either its parsed comments (already sorted/filtered) with
/// the source contents, or a read error.
struct Loaded {
    name: String,
    contents: String,
    comments: Vec<PositionedComment>,
}

enum Input {
    Ok(Loaded),
    Err { name: String, message: String },
}

fn load(name: &str, spec_template: &CheckSpec) -> Input {
    let contents = if name == "-" {
        let mut s = String::new();
        if std::io::stdin().read_to_string(&mut s).is_err() {
            return Input::Err { name: name.to_string(), message: "failed to read stdin".to_string() };
        }
        s
    } else {
        match std::fs::read_to_string(name) {
            Ok(s) => s,
            Err(e) => return Input::Err { name: name.to_string(), message: e.to_string() },
        }
    };
    let spec = CheckSpec {
        filename: name.to_string(),
        script: contents.clone(),
        ..spec_template.clone()
    };
    let result = shellcheck_rs::check_script(&spec);
    Input::Ok(Loaded { name: name.to_string(), contents, comments: result.comments })
}

fn run(config: RunConfig) -> ExitCode {
    let RunConfig { format, inputs, spec_template, color, wiki_link_count } = config;

    let loaded: Vec<Input> = inputs.iter().map(|i| load(i, &spec_template)).collect();

    let any_failure = loaded.iter().any(|i| matches!(i, Input::Err { .. }));
    let any_comments = loaded
        .iter()
        .any(|i| matches!(i, Input::Ok(l) if !l.comments.is_empty()));

    let is_tty = std::io::stdout().is_terminal();
    let use_color = formatter::should_output_color(color, is_tty);

    let stdout = std::io::stdout();
    let mut out = stdout.lock();
    let stderr = std::io::stderr();
    let mut err = stderr.lock();

    match format.as_str() {
        "quiet" => {
            // No output; exit 1 on any failure or any comments (matching the
            // Haskell Quiet formatter's immediate exitFailure).
            return if any_failure || any_comments { ExitCode::from(1) } else { ExitCode::SUCCESS };
        }

        "json1" => {
            // Untab per file (makeNonVirtual); comments prepended per file
            // (reverse file order), matching the Haskell IORef accumulation.
            let mut all: Vec<PositionedComment> = Vec::new();
            for i in &loaded {
                match i {
                    Input::Ok(l) => {
                        let mut new = fixer::make_non_virtual(&l.comments, &l.contents);
                        new.extend(std::mem::take(&mut all));
                        all = new;
                    }
                    Input::Err { name, message } => {
                        let _ = writeln!(err, "{name}: {message}");
                    }
                }
            }
            let _ = writeln!(out, "{}", json1::render(&all));
        }

        "json" => {
            // Legacy array; no untab; per-file comments prepended (reverse file
            // order), matching the Haskell IORef accumulation.
            let mut all: Vec<PositionedComment> = Vec::new();
            for i in &loaded {
                match i {
                    Input::Ok(l) => {
                        let mut new = l.comments.clone();
                        new.extend(std::mem::take(&mut all));
                        all = new;
                    }
                    Input::Err { name, message } => {
                        let _ = writeln!(err, "{name}: {message}");
                    }
                }
            }
            let _ = writeln!(out, "{}", json::render(&all));
        }

        "gcc" => {
            for i in &loaded {
                match i {
                    Input::Ok(l) => {
                        let mut buf = String::new();
                        gcc::render_file(&l.name, &l.contents, &l.comments, &mut buf);
                        let _ = out.write_all(buf.as_bytes());
                    }
                    Input::Err { name, message } => {
                        let _ = writeln!(err, "{}", gcc::render_failure(name, message));
                    }
                }
            }
        }

        "checkstyle" => {
            let _ = out.write_all(checkstyle::HEADER.as_bytes());
            for i in &loaded {
                match i {
                    Input::Ok(l) => {
                        let mut buf = String::new();
                        checkstyle::render_file(&l.name, &l.contents, &l.comments, &mut buf);
                        let _ = out.write_all(buf.as_bytes());
                    }
                    Input::Err { name, message } => {
                        // CheckStyle onFailure writes to stdout.
                        let _ = out.write_all(checkstyle::render_failure(name, message).as_bytes());
                    }
                }
            }
            let _ = out.write_all(checkstyle::FOOTER.as_bytes());
        }

        "diff" => {
            let color_fn = |s: &str| diff::color_bold_red(use_color, s);
            let mut reported = false;
            // Rendered per file in input order (the Haskell formatter runs
            // once per file as the driver folds over them).
            for i in &loaded {
                match i {
                    Input::Ok(l) => {
                        let d = diff::render_file(use_color, &l.name, &l.contents, &l.comments);
                        if d.reported {
                            let _ = out.write_all(d.text.as_bytes());
                            reported = true;
                        }
                    }
                    Input::Err { name, message } => {
                        let _ = writeln!(err, "{}", color_fn(&format!("{name}: {message}")));
                    }
                }
            }
            if any_comments && !reported {
                let _ = writeln!(err, "{}", color_fn(diff::NONE_FIXABLE_MSG));
            }
        }

        _ => {
            // tty (default).
            let color_func = formatter::tty_color_func(use_color);
            let mut wiki: Vec<tty::WikiEntry> = Vec::new();
            for i in &loaded {
                match i {
                    Input::Ok(l) => {
                        let mut buf = String::new();
                        tty::render_file(
                            &color_func,
                            &l.name,
                            &l.contents,
                            &l.comments,
                            &mut wiki,
                            &mut buf,
                        );
                        let _ = out.write_all(buf.as_bytes());
                    }
                    Input::Err { name, message } => {
                        let _ = writeln!(
                            err,
                            "{}",
                            color_func("error", &format!("{name}: {message}"))
                        );
                    }
                }
            }
            let mut wbuf = String::new();
            tty::render_wiki(&wiki, wiki_link_count, &mut wbuf);
            let _ = out.write_all(wbuf.as_bytes());
        }
    }

    // statusToCode: RuntimeException (2) > SomeProblems (1) > NoProblems (0).
    if any_failure {
        ExitCode::from(2)
    } else if any_comments {
        ExitCode::from(1)
    } else {
        ExitCode::SUCCESS
    }
}
