//! Rust-native conformance runner for the ShellCheck port.
//!
//! This binary checks that the Rust port (`shellcheck-rs`) reproduces, byte for
//! byte, the `--format=json1` results committed as the oracle goldens. It is the
//! self-contained Rust counterpart to the Python harness
//! (`harness/run_conformance.py`): the Python harness runs the *real* Haskell
//! `shellcheck` binary over the corpus to *regenerate* the golden baseline
//! (`harness/goldens.jsonl`), while this runner *replays* that frozen baseline
//! against the port and fails if the port diverges. It never runs Haskell and
//! never writes the goldens, so it can gate the port in CI without a GHC
//! toolchain present.
//!
//! What it does, per corpus id that has a committed golden:
//!   1. Feed the corpus `script` to the port exactly as the CLI does for
//!      `--format=json1 -`: build a default `CheckSpec { filename: "-", .. }`,
//!      call `shellcheck_rs::check_script`, then untab the comments with
//!      `make_non_virtual` (mirroring `shellcheck.rs`'s json1 path).
//!   2. Reduce both the port's comments and the golden's comments to an ordered
//!      list of comparison keys `(line, column, endLine, endColumn, level, code,
//!      message, fix)` (the exact tuple the Python harness compares), where
//!      `fix` is `None` or a list of
//!      `(line, column, endLine, endColumn, insertionPoint, precedence,
//!      replacement)`.
//!   3. The id matches iff the two key sequences are identical, order included.
//!
//! Exit codes: 0 = every compared id matched; 1 = at least one mismatch;
//! 2 = IO / JSON parse error (missing or malformed harness files).
//!
//! Flags (tiny hand-rolled parser, no clap):
//!   --harness <dir>   directory holding corpus.json + goldens.jsonl (default: "harness")
//!   --limit <N>       only compare the first N corpus entries (quick runs)
//!   --quiet           print the summary line only

use std::collections::HashMap;
use std::process::ExitCode;

use serde_json::Value;
use shellcheck_cli::formatter::{fixer, json1};
use shellcheck_rs::interface::CheckSpec;

/// One replacement in a fix, in the harness comparison order.
#[derive(Debug, Clone, PartialEq, Eq)]
struct ReplacementKey {
    line: i64,
    column: i64,
    end_line: i64,
    end_column: i64,
    insertion_point: String,
    precedence: i64,
    replacement: String,
}

/// The per-comment comparison key: the exact tuple the Python harness diffs.
#[derive(Debug, Clone, PartialEq, Eq)]
struct CommentKey {
    line: i64,
    column: i64,
    end_line: i64,
    end_column: i64,
    level: String,
    code: i64,
    message: String,
    fix: Option<Vec<ReplacementKey>>,
}

/// True iff the two ordered key sequences are identical (order included).
fn keys_match(port: &[CommentKey], golden: &[CommentKey]) -> bool {
    port == golden
}

/// A compact, human-readable one-line rendering of a key sequence for diffs.
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

/// Extract an i64 from a JSON field, defaulting to 0 when absent/non-numeric.
fn as_i64(v: &Value, field: &str) -> i64 {
    v.get(field).and_then(Value::as_i64).unwrap_or(0)
}

/// Extract an owned string from a JSON field, defaulting to "".
fn as_str(v: &Value, field: &str) -> String {
    v.get(field).and_then(Value::as_str).unwrap_or("").to_string()
}

/// Build a `CommentKey` from a json1-shaped comment `Value` (used for both the
/// port's freshly serialized comments and the golden's stored comments, so the
/// extraction logic is guaranteed identical on both sides).
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

/// Run the port over `script` exactly as the CLI's json1 path does, and return
/// the ordered comparison keys.
fn port_keys(script: &str) -> Vec<CommentKey> {
    let spec = CheckSpec {
        filename: "-".to_string(),
        script: script.to_string(),
        ..CheckSpec::default()
    };
    let result = shellcheck_rs::check_script(&spec);
    // Mirror shellcheck.rs's json1 branch: untab per file, then map each
    // comment through the same json1 serialization used for real output.
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

struct Args {
    harness: String,
    limit: Option<usize>,
    quiet: bool,
}

/// Tiny hand-rolled argument parser. Returns Err(message) on bad usage.
fn parse_args(argv: &[String]) -> Result<Args, String> {
    let mut harness = "harness".to_string();
    let mut limit = None;
    let mut quiet = false;
    let mut it = argv.iter();
    while let Some(arg) = it.next() {
        match arg.as_str() {
            "--harness" => {
                harness = it
                    .next()
                    .ok_or_else(|| "--harness requires a directory argument".to_string())?
                    .clone();
            }
            "--limit" => {
                let n = it
                    .next()
                    .ok_or_else(|| "--limit requires a number argument".to_string())?;
                limit = Some(
                    n.parse::<usize>()
                        .map_err(|_| format!("--limit: not a number: {n}"))?,
                );
            }
            "--quiet" => quiet = true,
            other => return Err(format!("unknown argument: {other}")),
        }
    }
    Ok(Args { harness, limit, quiet })
}

/// Load the goldens: map id -> ordered comment keys, skipping provenance lines.
fn load_goldens(path: &str) -> Result<HashMap<String, Vec<CommentKey>>, String> {
    let text = std::fs::read_to_string(path).map_err(|e| format!("{path}: {e}"))?;
    let mut map = HashMap::new();
    for (lineno, line) in text.lines().enumerate() {
        let line = line.trim();
        if line.is_empty() {
            continue;
        }
        let v: Value = serde_json::from_str(line)
            .map_err(|e| format!("{path}:{}: {e}", lineno + 1))?;
        if v.get("__provenance__").is_some() {
            continue;
        }
        let id = match v.get("id").and_then(Value::as_str) {
            Some(id) => id.to_string(),
            None => continue,
        };
        let comments = v
            .get("result")
            .and_then(|r| r.get("comments"))
            .and_then(Value::as_array)
            .cloned()
            .unwrap_or_default();
        let keys: Vec<CommentKey> = comments.iter().map(key_from_value).collect();
        map.insert(id, keys);
    }
    Ok(map)
}

/// A corpus entry: only id and script matter here.
struct CorpusEntry {
    id: String,
    script: String,
}

fn load_corpus(path: &str) -> Result<Vec<CorpusEntry>, String> {
    let text = std::fs::read_to_string(path).map_err(|e| format!("{path}: {e}"))?;
    let v: Value = serde_json::from_str(&text).map_err(|e| format!("{path}: {e}"))?;
    let arr = v
        .as_array()
        .ok_or_else(|| format!("{path}: expected a JSON array"))?;
    let mut out = Vec::with_capacity(arr.len());
    for entry in arr {
        let id = entry
            .get("id")
            .and_then(Value::as_str)
            .ok_or_else(|| format!("{path}: corpus entry missing string id"))?
            .to_string();
        let script = entry
            .get("script")
            .and_then(Value::as_str)
            .unwrap_or("")
            .to_string();
        out.push(CorpusEntry { id, script });
    }
    Ok(out)
}

fn run(args: Args) -> Result<bool, String> {
    let corpus_path = format!("{}/corpus.json", args.harness);
    let goldens_path = format!("{}/goldens.jsonl", args.harness);

    let corpus = load_corpus(&corpus_path)?;
    let goldens = load_goldens(&goldens_path)?;

    let selected: &[CorpusEntry] = match args.limit {
        Some(n) => &corpus[..n.min(corpus.len())],
        None => &corpus,
    };

    let mut compared = 0usize;
    let mut matched = 0usize;
    let mut mismatches: Vec<(String, Vec<CommentKey>, Vec<CommentKey>)> = Vec::new();

    for entry in selected {
        let golden = match goldens.get(&entry.id) {
            Some(g) => g,
            None => continue, // corpus entry without a committed golden: skip
        };
        compared += 1;
        let port = port_keys(&entry.script);
        if keys_match(&port, golden) {
            matched += 1;
        } else {
            mismatches.push((entry.id.clone(), port, golden.clone()));
        }
    }

    let mismatched = mismatches.len();

    if !args.quiet {
        const MAX_SHOWN: usize = 20;
        for (id, port, golden) in mismatches.iter().take(MAX_SHOWN) {
            println!("MISMATCH {id}");
            println!("  port:   {}", render_keys(port));
            println!("  golden: {}", render_keys(golden));
        }
        if mismatched > MAX_SHOWN {
            println!("... and {} more mismatches", mismatched - MAX_SHOWN);
        }
    }

    println!(
        "conformance: compared {compared}, matched {matched}, mismatched {mismatched}"
    );

    Ok(mismatched == 0)
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
    match run(args) {
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
    fn empty_sequences_match() {
        assert!(keys_match(&[], &[]));
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
    fn differing_field_mismatches() {
        let a = vec![ck(2086, "a")];
        let mut c = ck(2086, "a");
        c.code = 2087;
        assert!(!keys_match(&a, &[c]));
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
        assert_eq!(k.line, 2);
        assert_eq!(k.column, 3);
        assert_eq!(k.end_column, 9);
        assert_eq!(k.level, "style");
        assert_eq!(k.code, 2086);
        assert_eq!(k.message, "m");
        let reps = k.fix.expect("fix present");
        assert_eq!(reps.len(), 1);
        assert_eq!(reps[0].insertion_point, "beforeStart");
        assert_eq!(reps[0].precedence, 7);
        assert_eq!(reps[0].replacement, "\"");
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
        let s = render_keys(&[ck(2086, "hi")]);
        assert!(s.contains("SC2086"));
        assert!(s.contains("warning"));
    }
}
