//! ShellCheck CLI (Rust port). Reads scripts from files or stdin, runs the
//! analyzer core, and emits the requested format.
//!
//! Option parsing lives in `shellcheck_cli::options` and mirrors the Haskell
//! `shellcheck.hs` driver (option set, `getOpt Permute` semantics, exit codes).
//! Output formatting mirrors `ShellCheck.Formatter.*`: tty (default), gcc,
//! checkstyle, json, json1, quiet, and diff.

use std::io::{IsTerminal, Read, Write};
use std::process::ExitCode;

use shellcheck_cli::formatter::{self, checkstyle, diff, fixer, gcc, json, json1, tty};
use shellcheck_cli::options::{self, Outcome, RunConfig};
use shellcheck_cli::rc::{self, RcConfig};
use shellcheck_rs::interface::{CheckSpec, PositionedComment};

fn main() -> ExitCode {
    // SHELLCHECK_OPTS is split on whitespace (Haskell `words`) and prepended to
    // argv before parsing, so env-configured defaults apply but explicit argv
    // can still override them (shellcheck.hs `getOptions`: env ++ args).
    let mut argv: Vec<String> = Vec::new();
    if let Ok(opts) = std::env::var("SHELLCHECK_OPTS") {
        argv.extend(opts.split_whitespace().map(|s| s.to_string()));
    }
    argv.extend(std::env::args().skip(1));

    let config = match options::parse(&argv) {
        Outcome::Run(c) => c,
        Outcome::PrintVersion => {
            println!("{}", options::version_banner());
            return ExitCode::SUCCESS;
        }
        Outcome::PrintHelp => {
            // `println!` adds the trailing blank line the oracle's --help emits
            // after the usage block (usage() itself ends with a single "\n").
            println!("{}", options::usage());
            return ExitCode::SUCCESS;
        }
        Outcome::ListOptional => {
            print!("{}", options::list_optional_text());
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

/// Load one input. `stdin_cache` holds the stdin contents once read, so that a
/// repeated `-` (e.g. `shellcheck - -`, or `-` listed twice via --files-from)
/// reuses the same script instead of reading EOF on the second pass, matching
/// the oracle's cache of non-reopenable inputs. Reading is lazy: stdin is only
/// touched when a `-` input is actually reached, preserving quiet-mode's
/// short-circuit (it must not block on stdin after an earlier file failed).
fn load(
    name: &str,
    spec_template: &CheckSpec,
    rc: Option<&RcConfig>,
    stdin_cache: &mut Option<String>,
) -> Input {
    let contents = if name == "-" {
        if stdin_cache.is_none() {
            let mut s = String::new();
            if std::io::stdin().read_to_string(&mut s).is_err() {
                return Input::Err {
                    name: name.to_string(),
                    message: "failed to read stdin".to_string(),
                };
            }
            *stdin_cache = Some(s);
        }
        stdin_cache.clone().unwrap()
    } else {
        match std::fs::read_to_string(name) {
            Ok(s) => s,
            Err(e) => {
                return Input::Err {
                    name: name.to_string(),
                    message: e.to_string(),
                };
            }
        }
    };
    let mut spec = CheckSpec {
        filename: name.to_string(),
        script: contents.clone(),
        ..spec_template.clone()
    };
    merge_rc(&mut spec, rc);
    let result = shellcheck_rs::check_script(&spec);
    Input::Ok(Loaded {
        name: name.to_string(),
        contents,
        comments: result.comments,
    })
}

/// Merge rc directives into the per-input `CheckSpec`. CLI flags (already on
/// `spec` via `spec_template`) win over rc where they conflict:
///   * rc `disable` codes ADD to `excluded_warnings`; `disable=all` excludes
///     everything (represented as an empty include set, which the checker
///     treats as "include nothing" — this also overrides any CLI include, as
///     the oracle does).
///   * rc `enable` names APPEND to `optional_checks` (alongside CLI enables).
///   * rc `shell` sets the override ONLY if the CLI did not (`--shell` wins).
///   * rc `extended-analysis` applies ONLY if the CLI did not set it.
///
/// rc disables are annotations in the established pipeline: they suppress a code
/// regardless of the CLI include filter (`should_include` ignores
/// `excluded_warnings` whenever an include list is present). So besides adding
/// the codes to `excluded_warnings`, we also strip them from any CLI include
/// list, so `--include=SC2086` cannot re-enable an rc-disabled SC2086 (the
/// oracle emits nothing in that case).
fn merge_rc(spec: &mut CheckSpec, rc: Option<&RcConfig>) {
    let rc = match rc {
        Some(rc) => rc,
        None => return,
    };
    if rc.disable_all {
        // Include nothing: `should_include` returns `included.contains(code)`,
        // false for every code -> all warnings suppressed.
        spec.included_warnings = Some(Vec::new());
    } else {
        spec.excluded_warnings
            .extend(rc.disabled_codes.iter().copied());
        if let Some(included) = &mut spec.included_warnings {
            included.retain(|c| !rc.disabled_codes.contains(c));
        }
    }
    for name in &rc.enabled_checks {
        spec.optional_checks.push(name.clone());
    }
    if spec.shell_type_override.is_none() {
        spec.shell_type_override = rc.shell;
    }
    if spec.extended_analysis.is_none() {
        spec.extended_analysis = rc.extended_analysis;
    }
}

fn run(config: RunConfig) -> ExitCode {
    let RunConfig {
        format,
        inputs,
        spec_template,
        color,
        wiki_link_count,
        rcfile,
    } = config;

    // Resolve the rc configuration policy up front (mirrors `getConfig`):
    //   * `--norc` (ignore_rc): never use any rc file.
    //   * `--rcfile <path>`: read exactly that file once, applied to every
    //     input; if unreadable, warn once and proceed with no config.
    //   * otherwise: discover `.shellcheckrc` per input by walking up from the
    //     input's directory (CWD for stdin) and then the user config dirs.
    let ignore_rc = spec_template.ignore_rc;
    let rcfile_config: Option<RcConfig> = if !ignore_rc {
        if let Some(path) = &rcfile {
            match rc::read_config_file(std::path::Path::new(path)) {
                Some(cfg) => Some(cfg),
                None => {
                    eprintln!("Warning: unable to read --rcfile {path}");
                    None
                }
            }
        } else {
            None
        }
    } else {
        None
    };
    // Per-input rc config: fixed rcfile config, directory discovery, or none.
    let resolve_rc = |name: &str| -> Option<RcConfig> {
        if ignore_rc {
            None
        } else if rcfile.is_some() {
            rcfile_config.clone()
        } else {
            rc::discover(name)
        }
    };

    // Quiet mode is a streaming short-circuit: process inputs in order and exit
    // 1 on the FIRST input that has any comment or fails to read, without
    // loading later inputs (so `-f quiet bad.sh -` never blocks on stdin once
    // bad.sh has a problem). Exit 0 only if every input is clean. This mirrors
    // the Haskell Quiet formatter, which folds inputs lazily and reports the
    // first failing result. A read failure counts as a problem (exit 1), not a
    // runtime error (2), matching the oracle.
    let mut stdin_cache: Option<String> = None;
    if format == "quiet" {
        for i in &inputs {
            let rc = resolve_rc(i);
            match load(i, &spec_template, rc.as_ref(), &mut stdin_cache) {
                Input::Ok(l) if !l.comments.is_empty() => return ExitCode::from(1),
                Input::Ok(_) => {}
                Input::Err { .. } => return ExitCode::from(1),
            }
        }
        return ExitCode::SUCCESS;
    }

    let loaded: Vec<Input> = inputs
        .iter()
        .map(|i| load(i, &spec_template, resolve_rc(i).as_ref(), &mut stdin_cache))
        .collect();

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
        // "quiet" is handled by the streaming short-circuit above and never
        // reaches this match.
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
