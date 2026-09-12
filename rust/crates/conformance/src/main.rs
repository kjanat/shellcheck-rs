//! The conformance gate for the ShellCheck Rust port.
//!
//! It runs the Haskell binary (the **oracle**) and the Rust port over the same
//! input and fails unless they agree exactly — same code, severity, span,
//! message, autofix and order, as `--format=json1` reports them.
//!
//! Two sources of input, because they catch different things:
//!
//! * `gate` replays ShellCheck's own `prop_` properties, extracted straight
//!   from `src/ShellCheck/**/*.hs` (see [`corpus`]). These are the cases the
//!   upstream authors considered decisive for each check, so they are the
//!   sharpest per-check signal available — but they only cover what somebody
//!   already thought to write a test for.
//!
//! * `fuzz` generates and mutates shell that nobody wrote a test for, which is
//!   where real divergence hides: a check firing on input the oracle ignores,
//!   or a parse failure handled differently. A green `gate` with a divergent
//!   `fuzz` is the normal state of an incomplete port, and the reason `gate`
//!   alone must never be read as "parity".
//!
//! The port runs in-process (`shellcheck_rs::check_script`); only the oracle
//! costs a process, and those are batched.
//!
//! Exit codes: 0 = agreement, 1 = at least one divergence, 2 = harness error.

mod corpus;
mod fuzz;
mod oracle;

use std::process::ExitCode;

use serde_json::Value;
use shellcheck_cli::formatter::{fixer, json1};
use shellcheck_rs::interface::CheckSpec;

// ---------------------------------------------------------------------------
// Comparison keys
// ---------------------------------------------------------------------------

/// One replacement in a fix, in comparison order.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ReplacementKey {
    line: i64,
    column: i64,
    end_line: i64,
    end_column: i64,
    insertion_point: String,
    precedence: i64,
    replacement: String,
}

/// The per-comment comparison key: everything a user can observe.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CommentKey {
    line: i64,
    column: i64,
    end_line: i64,
    end_column: i64,
    level: String,
    pub code: i64,
    message: String,
    fix: Option<Vec<ReplacementKey>>,
}

/// True iff the two ordered key sequences are identical (order included).
fn keys_match(port: &[CommentKey], oracle: &[CommentKey]) -> bool {
    port == oracle
}

/// A compact one-line rendering of a key sequence, for divergence reports.
fn render_keys(keys: &[CommentKey]) -> String {
    if keys.is_empty() {
        return "[]".to_string();
    }
    let parts: Vec<String> = keys
        .iter()
        .map(|k| {
            let fix = match &k.fix {
                None => "-".to_string(),
                Some(reps) => {
                    let inner: Vec<String> = reps
                        .iter()
                        .map(|r| {
                            format!(
                                "{}:{}-{}:{} {} p{} {:?}",
                                r.line,
                                r.column,
                                r.end_line,
                                r.end_column,
                                r.insertion_point,
                                r.precedence,
                                r.replacement
                            )
                        })
                        .collect();
                    format!("fix[{}]", inner.join(", "))
                }
            };
            format!(
                "SC{} {} {}:{}-{}:{} {:?} {}",
                k.code, k.level, k.line, k.column, k.end_line, k.end_column, k.message, fix
            )
        })
        .collect();
    format!("[{}]", parts.join(" | "))
}

fn as_i64(v: &Value, field: &str) -> i64 {
    v.get(field).and_then(Value::as_i64).unwrap_or(0)
}

fn as_str(v: &Value, field: &str) -> String {
    v.get(field)
        .and_then(Value::as_str)
        .unwrap_or("")
        .to_string()
}

/// Build a `CommentKey` from a json1-shaped comment, used for both sides so
/// the extraction can never differ between them.
fn key_from_value(v: &Value) -> CommentKey {
    let fix = match v.get("fix") {
        None | Some(Value::Null) => None,
        Some(f) => {
            let reps = f
                .get("replacements")
                .and_then(Value::as_array)
                .cloned()
                .unwrap_or_default();
            Some(
                reps.iter()
                    .map(|r| ReplacementKey {
                        line: as_i64(r, "line"),
                        column: as_i64(r, "column"),
                        end_line: as_i64(r, "endLine"),
                        end_column: as_i64(r, "endColumn"),
                        insertion_point: as_str(r, "insertionPoint"),
                        precedence: as_i64(r, "precedence"),
                        replacement: as_str(r, "replacement"),
                    })
                    .collect(),
            )
        }
    };
    CommentKey {
        line: as_i64(v, "line"),
        column: as_i64(v, "column"),
        end_line: as_i64(v, "endLine"),
        end_column: as_i64(v, "endColumn"),
        level: as_str(v, "level"),
        code: as_i64(v, "code"),
        message: as_str(v, "message"),
        fix,
    }
}

/// Run the port over `script` exactly as the CLI's json1 path does.
///
/// `filename` matters: both tools may infer a dialect from it, so the caller
/// passes whatever path the oracle saw.
pub fn port_keys(script: &str, filename: &str, shell: Option<&str>) -> Vec<CommentKey> {
    let spec = CheckSpec {
        filename: filename.to_string(),
        script: script.to_string(),
        shell_type_override: shell.and_then(parse_shell),
        ..CheckSpec::default()
    };
    let result = shellcheck_rs::check_script(&spec);
    let untabbed = fixer::make_non_virtual(&result.comments, script);
    untabbed
        .iter()
        .map(|pc| {
            let j = json1::to_comment(pc);
            let v = serde_json::to_value(&j).expect("json1 comment serializes");
            key_from_value(&v)
        })
        .collect()
}

fn parse_shell(s: &str) -> Option<shellcheck_rs::interface::Shell> {
    use shellcheck_rs::interface::Shell;
    match s {
        "sh" => Some(Shell::Sh),
        "bash" => Some(Shell::Bash),
        "dash" => Some(Shell::Dash),
        "ksh" => Some(Shell::Ksh),
        "busybox" => Some(Shell::BusyboxSh),
        _ => None,
    }
}

/// The oracle's comments for one script, as comparison keys.
fn oracle_keys(comments: &[Value]) -> Vec<CommentKey> {
    comments.iter().map(key_from_value).collect()
}

// ---------------------------------------------------------------------------
// gate: ShellCheck's own prop_ properties
// ---------------------------------------------------------------------------

fn gate(args: &Args) -> Result<bool, String> {
    let src = std::path::Path::new(&args.repo).join("src/ShellCheck");
    let mut entries = corpus::extract(&src)?;
    if let Some(n) = args.limit {
        entries.truncate(n);
    }
    if entries.is_empty() {
        return Err(format!("no prop_ properties found under {}", src.display()));
    }

    let oracle = oracle::Oracle::new(&args.oracle)?;
    println!("{}", oracle::verify(&oracle, &args.repo)?);
    // Name each script after its property so a divergence names itself.
    let named: Vec<(String, String)> = entries
        .iter()
        .map(|e| (oracle.name(), e.script.clone()))
        .collect();
    let by_name = oracle.check(&named, args.shell.as_deref())?;

    let mut divergent: Vec<(String, Vec<CommentKey>, Vec<CommentKey>)> = Vec::new();
    let mut compared = 0usize;
    for (entry, (name, script)) in entries.iter().zip(&named) {
        let Some(ocomments) = by_name.get(name) else {
            continue;
        };
        compared += 1;
        let path = oracle.dir().join(name);
        let ok = oracle_keys(ocomments);
        let pk = port_keys(script, &path.to_string_lossy(), args.shell.as_deref());
        if !keys_match(&pk, &ok) {
            divergent.push((entry.id.clone(), pk, ok));
        }
    }

    if !args.quiet {
        // `--max-findings` caps how many are spelled out, as it does for `fuzz`.
        let max = args.max_findings;
        for (id, port, oracle) in divergent.iter().take(max) {
            println!("DIVERGE {id}");
            println!("  oracle: {}", render_keys(oracle));
            println!("  port:   {}", render_keys(port));
        }
        if divergent.len() > max {
            println!("... and {} more", divergent.len() - max);
        }
    }
    println!(
        "gate: {} properties, {} agree, {} diverge",
        compared,
        compared - divergent.len(),
        divergent.len()
    );
    Ok(divergent.is_empty())
}

// ---------------------------------------------------------------------------
// Arguments
// ---------------------------------------------------------------------------

pub struct Args {
    cmd: String,
    oracle: String,
    pub repo: String,
    limit: Option<usize>,
    shell: Option<String>,
    quiet: bool,
    // fuzz
    pub seed: u64,
    pub iterations: usize,
    pub max_findings: usize,
    pub all_shells: bool,
}

fn parse_args(argv: &[String]) -> Result<Args, String> {
    let mut a = Args {
        cmd: "gate".to_string(),
        oracle: std::env::var("ORACLE").unwrap_or_else(|_| ".cache/shellcheck-oracle".to_string()),
        repo: ".".to_string(),
        limit: None,
        shell: None,
        quiet: false,
        seed: 0,
        iterations: 2000,
        max_findings: 25,
        all_shells: false,
    };
    let mut i = 0;
    if let Some(first) = argv.first()
        && !first.starts_with("--")
    {
        a.cmd = first.clone();
        i = 1;
    }
    while i < argv.len() {
        let arg = &argv[i];
        let next = |i: &mut usize| -> Result<String, String> {
            *i += 1;
            argv.get(*i)
                .cloned()
                .ok_or_else(|| format!("{arg} needs a value"))
        };
        match arg.as_str() {
            "--oracle" => a.oracle = next(&mut i)?,
            "--repo" => a.repo = next(&mut i)?,
            "--limit" => {
                a.limit = Some(next(&mut i)?.parse().map_err(|e| format!("--limit: {e}"))?)
            }
            "--shell" => a.shell = Some(next(&mut i)?),
            "--seed" => a.seed = next(&mut i)?.parse().map_err(|e| format!("--seed: {e}"))?,
            "--iterations" => {
                a.iterations = next(&mut i)?
                    .parse()
                    .map_err(|e| format!("--iterations: {e}"))?
            }
            "--max-findings" => {
                a.max_findings = next(&mut i)?
                    .parse()
                    .map_err(|e| format!("--max-findings: {e}"))?
            }
            "--all-shells" => a.all_shells = true,
            "--quiet" => a.quiet = true,
            other => return Err(format!("unknown argument {other}")),
        }
        i += 1;
    }
    Ok(a)
}

fn main() -> ExitCode {
    let argv: Vec<String> = std::env::args().skip(1).collect();
    let args = match parse_args(&argv) {
        Ok(a) => a,
        Err(msg) => {
            eprintln!("conformance: {msg}");
            return ExitCode::from(2);
        }
    };
    let res = match args.cmd.as_str() {
        "gate" => gate(&args),
        "fuzz" => fuzz::run(&args),
        "extract" => {
            let src = std::path::Path::new(&args.repo).join("src/ShellCheck");
            corpus::extract(&src).map(|e| {
                println!("{} properties", e.len());
                for entry in e.iter().take(args.limit.unwrap_or(0)) {
                    println!("{}\t{}\t{:?}", entry.id, entry.helper, entry.script);
                }
                true
            })
        }
        other => Err(format!("unknown command {other} (gate|fuzz|extract)")),
    };
    match res {
        Ok(true) => ExitCode::SUCCESS,
        Ok(false) => ExitCode::from(1),
        Err(msg) => {
            eprintln!("conformance: {msg}");
            ExitCode::from(2)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn ck(code: i64, msg: &str) -> CommentKey {
        CommentKey {
            line: 1,
            column: 1,
            end_line: 1,
            end_column: 1,
            level: "warning".to_string(),
            code,
            message: msg.to_string(),
            fix: None,
        }
    }

    #[test]
    fn identical_sequences_match() {
        let a = vec![ck(2086, "Double quote"), ck(2148, "Add shebang")];
        let b = vec![ck(2086, "Double quote"), ck(2148, "Add shebang")];
        assert!(keys_match(&a, &b));
    }

    #[test]
    fn order_matters() {
        let a = vec![ck(2086, "a"), ck(2148, "b")];
        let b = vec![ck(2148, "b"), ck(2086, "a")];
        assert!(!keys_match(&a, &b));
    }

    #[test]
    fn different_length_mismatches() {
        let a = vec![ck(2086, "a")];
        let b = vec![ck(2086, "a"), ck(2148, "b")];
        assert!(!keys_match(&a, &b));
    }

    #[test]
    fn key_from_value_extracts_fields_and_fix() {
        let v: Value = serde_json::from_str(
            r#"{"file":"-","line":2,"endLine":2,"column":3,"endColumn":9,
                "level":"style","code":2086,"message":"m",
                "fix":{"replacements":[{"line":2,"column":3,"endLine":2,"endColumn":3,
                       "insertionPoint":"beforeStart","precedence":7,"replacement":"\""}]}}"#,
        )
        .unwrap();
        let k = key_from_value(&v);
        assert_eq!((k.line, k.column, k.end_column), (2, 3, 9));
        assert_eq!(k.code, 2086);
        let reps = k.fix.expect("fix present");
        assert_eq!(reps[0].precedence, 7);
    }

    #[test]
    fn key_from_value_null_fix_is_none() {
        let v: Value = serde_json::from_str(
            r#"{"line":1,"endLine":1,"column":1,"endColumn":1,
                "level":"error","code":2148,"message":"x","fix":null}"#,
        )
        .unwrap();
        assert!(key_from_value(&v).fix.is_none());
    }

    #[test]
    fn render_keys_smoke() {
        assert_eq!(render_keys(&[]), "[]");
        assert!(render_keys(&[ck(2086, "hi")]).contains("SC2086"));
    }

    #[test]
    fn args_default_to_gate() {
        let a = parse_args(&[]).unwrap();
        assert_eq!(a.cmd, "gate");
    }

    #[test]
    fn args_take_a_subcommand_and_flags() {
        let a = parse_args(&["fuzz".into(), "--seed".into(), "7".into()]).unwrap();
        assert_eq!(a.cmd, "fuzz");
        assert_eq!(a.seed, 7);
    }
}
