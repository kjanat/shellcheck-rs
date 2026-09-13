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

mod bench;
mod corpus;
mod deviations;
mod fuzz;
mod oracle;
mod shells;
mod snapshot;

use std::process::ExitCode;

use clap::{ArgAction, Parser, ValueEnum};
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
    port_keys_with(script, filename, shell, &[])
}

/// As [`port_keys`], with optional checks enabled — what `--enable` passes.
pub fn port_keys_with(
    script: &str,
    filename: &str,
    shell: Option<&str>,
    optional: &[String],
) -> Vec<CommentKey> {
    let spec = CheckSpec {
        filename: filename.to_string(),
        script: script.to_string(),
        shell_type_override: shell.and_then(parse_shell),
        optional_checks: optional.to_vec(),
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

/// Report the inputs the oracle died on, separately from divergences.
///
/// There is no comparison to make for these — the reference implementation
/// produced no answer — so they are neither agreement nor divergence. They are
/// still the most interesting thing a run can find, so they are printed, and
/// the count is returned for the caller's summary line.
fn report_crashes(oracle: &oracle::Oracle, max: usize, quiet: bool) -> usize {
    let crashes = oracle.crashes();
    if crashes.is_empty() {
        return 0;
    }
    if !quiet {
        for (script, why) in crashes.iter().take(max) {
            println!("ORACLE CRASH ({why})");
            println!("  script: {script:?}");
        }
        if crashes.len() > max {
            println!("... and {} more", crashes.len() - max);
        }
    }
    println!(
        "oracle crashed on {} input(s) -- an upstream defect, not a divergence",
        crashes.len()
    );
    crashes.len()
}

// ---------------------------------------------------------------------------
// gate: ShellCheck's own prop_ properties
// ---------------------------------------------------------------------------

fn gate(args: &Args) -> Result<bool, String> {
    let src = std::path::Path::new(&args.repo).join("src/ShellCheck");
    let coverage = corpus::coverage(&src)?;
    // Say what the corpus cannot reach before saying how well it did on the
    // rest: "2026 agree" means nothing without the denominator it left out.
    println!("{}", coverage.summary());
    let mut entries = coverage.entries;
    if let Some(n) = args.limit {
        entries.truncate(n);
    }
    if entries.is_empty() {
        return Err(format!("no prop_ properties found under {}", src.display()));
    }

    let oracle = oracle::Oracle::new(args.oracle())?;
    println!(
        "{}",
        oracle::verify(&oracle, &args.repo, args.any_oracle_version())?
    );
    // Name each script after its property so a divergence names itself.
    let named: Vec<(String, String)> = entries
        .iter()
        .map(|e| (oracle.name(), e.script.clone()))
        .collect();
    let by_name = oracle.check(&named, args.shell.as_deref())?;

    let mut divergent: Vec<(String, Vec<CommentKey>, Vec<CommentKey>)> = Vec::new();
    let mut deviations: Vec<(String, &'static deviations::Deviation)> = Vec::new();
    let mut compared = 0usize;
    for (entry, (name, script)) in entries.iter().zip(&named) {
        let Some(ocomments) = by_name.get(name) else {
            continue;
        };
        compared += 1;
        let path = oracle.dir().join(name);
        let ok = oracle_keys(ocomments);
        let pk = port_keys(script, &path.to_string_lossy(), args.shell.as_deref());
        if keys_match(&pk, &ok) {
            continue;
        }
        // A difference the port is entitled to is not a divergence.
        match deviations::sanctioned(script, args.shell.as_deref(), &pk, &ok) {
            Some(d) => deviations.push((entry.id.clone(), d)),
            None => divergent.push((entry.id.clone(), pk, ok)),
        }
    }

    // The optional checks, which nothing above can reach: a property's script
    // runs with the default set, so a `--enable` check that does nothing agrees
    // with the oracle everywhere. Both of upstream's examples per check, with
    // that check enabled on both sides.
    let mut optional_checked = 0usize;
    for ex in corpus::optional_examples(&src)? {
        for (kind, script) in [("positive", &ex.positive), ("negative", &ex.negative)] {
            let name = oracle.name();
            let named = [(name.clone(), script.clone())];
            let by_name = oracle.check_with(&named, args.shell.as_deref(), Some(&ex.name))?;
            let Some(ocomments) = by_name.get(&name) else {
                continue;
            };
            optional_checked += 1;
            let path = oracle.dir().join(&name);
            let ok = oracle_keys(ocomments);
            let pk = port_keys_with(
                script,
                &path.to_string_lossy(),
                args.shell.as_deref(),
                std::slice::from_ref(&ex.name),
            );
            if !keys_match(&pk, &ok) {
                divergent.push((format!("--enable={} ({kind})", ex.name), pk, ok));
            }
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
        for (id, d) in deviations.iter().take(max) {
            println!("DEVIATION {id} [{}]: {}", d.id, d.what);
        }
    }
    report_crashes(&oracle, args.max_findings, args.quiet);
    println!(
        "gate: {} properties + {optional_checked} optional-check examples, \
         {} agree, {} diverge, {} sanctioned deviations",
        compared,
        compared + optional_checked - divergent.len() - deviations.len(),
        divergent.len(),
        deviations.len()
    );
    Ok(divergent.is_empty())
}

// ---------------------------------------------------------------------------
// audit: the `try` emulation
// ---------------------------------------------------------------------------

/// Report every `reset` site that rewinds over a commitment.
///
/// The port emulates Parsec's `try` with an explicit commitment flag: a
/// production that fails after consuming input sets it, and `problem_at` then
/// reports nothing, because Haskell's parse is over at that point. `try_parse`
/// puts the flag back; a bare `mark`/`reset` does not. Wherever the Haskell
/// wraps an attempt in `try` and the port used `reset`, the parse stays
/// committed and every diagnostic after it is silently dropped -- which is
/// exactly how SC1019 went missing on `[ -n $(`.
///
/// This runs the corpus through a debug build and prints the sites reached, so
/// the list is generated rather than eyeballed over 130-odd `mark()` calls.
/// Each is either a genuine `try` in the Haskell (fix it) or a production that
/// cannot commit (harmless). Needs no oracle.
fn audit(args: &Args) -> Result<bool, String> {
    #[cfg(not(debug_assertions))]
    {
        let _ = args;
        Err(
            "audit needs a debug build (drop --release): the instrumentation is \
             behind debug_assertions"
                .to_string(),
        )
    }
    #[cfg(debug_assertions)]
    {
        let src = std::path::Path::new(&args.repo).join("src/ShellCheck");
        let coverage = corpus::coverage(&src)?;
        let mut sites: std::collections::BTreeMap<String, (usize, String)> =
            std::collections::BTreeMap::new();
        let mut scripts: Vec<String> = coverage.entries.iter().map(|e| e.script.clone()).collect();
        // The generated corpus reaches recovery paths the properties never do.
        let generated = fuzz::sample_scripts(&scripts.clone(), args.seed, args.iterations);
        scripts.extend(generated);
        for script in &scripts {
            for site in shellcheck_rs::parser::audit_commitment_backtracks("-", script) {
                let e = sites.entry(site).or_insert((0, script.clone()));
                e.0 += 1;
                if script.len() < e.1.len() {
                    e.1 = script.clone();
                }
            }
        }
        println!(
            "audit: {} scripts, {} reset site(s) rewound over a commitment",
            scripts.len(),
            sites.len()
        );
        for (site, (hits, smallest)) in &sites {
            println!("  {site}  ({hits} hits)");
            println!("    smallest input: {smallest:?}");
        }
        Ok(sites.is_empty())
    }
}

// ---------------------------------------------------------------------------
// Arguments
// ---------------------------------------------------------------------------

/// What to run. `gate` when nothing is named, since that is the check that
/// must pass.
#[derive(Clone, Copy, PartialEq, Eq, ValueEnum, Default)]
pub enum Command {
    #[default]
    Gate,
    Fuzz,
    /// External validity: both tools against the shells, not against each other.
    Shells,
    Extract,
    /// Where the port rewinds over a commitment instead of using a `try`.
    Audit,
    /// Freeze the port's own behaviour, or check nothing changed since.
    Snapshot,
    /// Where the port's time goes, phase by phase, against the oracle's.
    Bench,
}

#[derive(Parser)]
#[command(
    name = "conformance",
    about = "Differential conformance for the ShellCheck Rust port",
    long_about = "Runs the Haskell ShellCheck (the oracle) and the Rust port over the same \
                  input and reports every disagreement.\n\n\
                  Exit codes: 0 = agreement, 1 = at least one divergence, 2 = harness error.",
    disable_help_subcommand = true
)]
pub struct Args {
    /// What to run: the property gate, the fuzzer, or a listing of the corpus.
    #[arg(value_enum, default_value_t)]
    cmd: Command,

    /// ShellCheck to trust as the oracle: a path, or a name to find on PATH.
    ///
    /// Unset, it is the binary built from this tree if there is one, else
    /// whatever `shellcheck` is installed.
    #[arg(long, env = "ORACLE")]
    oracle: Option<String>,

    /// The ShellCheck source tree to take properties and versions from.
    #[arg(long, default_value = ".")]
    pub repo: String,

    /// Check only the first N properties (gate), or list N of them (extract).
    #[arg(long)]
    limit: Option<usize>,

    /// Dialect to check as, as `--shell` would name it to either tool.
    #[arg(long)]
    shell: Option<String>,

    /// Print only the verdict.
    #[arg(long)]
    quiet: bool,

    /// Compare against an oracle whose version is not this tree's.
    ///
    /// The banner then says MISMATCH, because the numbers describe that
    /// binary rather than this source. `ORACLE_ANY_VERSION` in the
    /// environment does the same, for any value but `0`, `false` or empty.
    #[arg(long, action = ArgAction::SetTrue)]
    any_oracle_version: bool,

    /// Seed for the generator, so a run can be replayed.
    #[arg(long, default_value_t = 0, help_heading = "Fuzzing")]
    pub seed: u64,

    /// How many generated scripts to check.
    #[arg(long, default_value_t = 2000, help_heading = "Fuzzing")]
    pub iterations: usize,

    /// Stop after this many distinct divergences.
    #[arg(long, default_value_t = 25, help_heading = "Fuzzing")]
    pub max_findings: usize,

    /// Check every dialect rather than one per script.
    #[arg(long, help_heading = "Fuzzing")]
    pub all_shells: bool,

    /// Re-freeze the snapshot instead of checking against it.
    ///
    /// Every write is a claim that the behaviour change is intended, so the
    /// diff of `rust/snapshot.txt` belongs in the commit that causes it.
    #[arg(long, help_heading = "Snapshot")]
    pub write: bool,

    /// Lines of generated shell to benchmark.
    #[arg(long, default_value_t = 4000, help_heading = "Bench")]
    pub lines: usize,

    /// Benchmark this file instead of generated shell.
    #[arg(long, help_heading = "Bench")]
    pub input: Option<String>,

    /// Time the port this many times and keep the fastest run.
    #[arg(long, default_value_t = 3, help_heading = "Bench")]
    pub repeat: usize,

    /// Write the benchmarked script here, so it can be re-run by hand.
    #[arg(long, help_heading = "Bench")]
    pub dump: Option<String>,
}

impl Args {
    /// Where the oracle comes from when `--oracle`/`$ORACLE` says nothing: the
    /// binary built from this tree if it is there, else whatever `shellcheck`
    /// is on `PATH`. The latter is what makes an installed release usable as
    /// the oracle with no build of its own.
    pub fn oracle_path(&self) -> &str {
        self.oracle()
    }

    fn oracle(&self) -> &str {
        // An empty `ORACLE=` reads as "not set", so it can be cleared in a
        // shell without naming a binary called "".
        match self.oracle.as_deref() {
            Some(explicit) if !explicit.is_empty() => explicit,
            _ => {
                let built = ".cache/shellcheck-oracle";
                if std::path::Path::new(built).is_file() {
                    built
                } else {
                    "shellcheck"
                }
            }
        }
    }

    /// The flag, or `ORACLE_ANY_VERSION` in the environment. Read here rather
    /// than through clap's `env`, which for a flag insists on the literal
    /// `true`/`false` and would reject the `=1` this has always accepted.
    pub fn any_oracle_version(&self) -> bool {
        self.any_oracle_version
            || std::env::var("ORACLE_ANY_VERSION")
                .is_ok_and(|v| !matches!(v.as_str(), "" | "0" | "false"))
    }
}

fn main() -> ExitCode {
    let args = Args::parse();
    let res = match args.cmd {
        Command::Gate => gate(&args),
        Command::Fuzz => fuzz::run(&args),
        Command::Shells => shells::run(&args),
        Command::Audit => audit(&args),
        Command::Snapshot => snapshot::run(&args),
        Command::Bench => bench::run(&args),
        Command::Extract => {
            let src = std::path::Path::new(&args.repo).join("src/ShellCheck");
            corpus::extract(&src).map(|e| {
                println!("{} properties", e.len());
                for entry in e.iter().take(args.limit.unwrap_or(0)) {
                    println!("{}\t{}\t{:?}", entry.id, entry.helper, entry.script);
                }
                true
            })
        }
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

    fn parse(argv: &[&str]) -> Args {
        Args::try_parse_from(std::iter::once("conformance").chain(argv.iter().copied())).unwrap()
    }

    #[test]
    fn args_default_to_gate() {
        assert!(parse(&[]).cmd == Command::Gate);
    }

    #[test]
    fn args_take_a_subcommand_and_flags() {
        let a = parse(&["fuzz", "--seed", "7"]);
        assert!(a.cmd == Command::Fuzz);
        assert_eq!(a.seed, 7);
    }

    #[test]
    fn unknown_argument_is_an_error() {
        assert!(Args::try_parse_from(["conformance", "--nope"]).is_err());
    }

    /// The oracle falls back to PATH only when nothing names one, and an empty
    /// `ORACLE=` counts as naming nothing.
    #[test]
    fn oracle_default_and_override() {
        assert_eq!(parse(&["--oracle", "/bin/sc"]).oracle(), "/bin/sc");
        let mut a = parse(&[]);
        a.oracle = Some(String::new());
        assert!(matches!(
            a.oracle(),
            ".cache/shellcheck-oracle" | "shellcheck"
        ));
    }

    /// clap validates the definition itself: conflicting flags, a bad default,
    /// a duplicated long name.
    #[test]
    fn command_definition_is_well_formed() {
        use clap::CommandFactory;
        Args::command().debug_assert();
    }
}
