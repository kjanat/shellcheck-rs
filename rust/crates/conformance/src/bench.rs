//! `bench`: where the port's time goes, and how it compares to the oracle.
//!
//! The port is measured in-process and broken into the phases `checkScript`
//! runs in order, so a regression can be attributed to one of them rather than
//! to "shellcheck is slow":
//!
//! | phase          | what it is                                             |
//! | -------------- | ------------------------------------------------------ |
//! | `parse`        | `parser::parse_script_spec` — source to AST             |
//! | `maps`         | `analyzer_lib::build_maps` — the id/parent maps         |
//! | `cfg`          | `cfg_analysis::analyze_control_flow` — graph + dataflow |
//! | `params-other` | the rest of `make_parameters` (mostly `variableFlow`)   |
//! | `checks`       | `analytics::analyze_with` — the tree and node walks     |
//! | `resolve`      | `checkScript`'s positioning, filter, nub and sort       |
//!
//! `maps` and `cfg` are timed by running the same pure functions the real
//! `make_parameters` runs, on the same AST; `params-other` is the difference
//! between the whole call and those two, so the split always adds up.
//!
//! The input is generated from the same seeded grammar `fuzz` uses, so
//! `bench --lines 4000 --seed 0` is the same script on every machine and every
//! run. `--input FILE` benchmarks a real script instead.
//!
//! The oracle is timed as a process (`-f json1 -`), which is the only way it
//! can be timed, so its number carries process startup — a few milliseconds
//! against seconds of work, but it is there.

use std::path::Path;
use std::time::{Duration, Instant};

use shellcheck_rs::analytics;
use shellcheck_rs::analyzer_lib;
use shellcheck_rs::cfg::CFGParameters;
use shellcheck_rs::cfg_analysis;
use shellcheck_rs::interface::CheckSpec;
use shellcheck_rs::parser;

use crate::Args;
use crate::corpus;
use crate::fuzz;

/// Does this fragment parse cleanly?
///
/// The fuzzer's job is to produce shell that does *not* parse, and ShellCheck
/// abandons a script at its first fatal parse error — everything after it is
/// never analyzed. A benchmark built out of such fragments would measure the
/// parser on line 16 and nothing else, so "parses" here means the strict thing:
/// no error-severity SC1xxx, which is what `Parsing stopped here` reports as.
fn parses(fragment: &str) -> bool {
    let out = parser::parse_script_spec(&parser::ParseSpec {
        filename: "-".to_string(),
        script: fragment.to_string(),
        ..parser::ParseSpec::default()
    });
    out.root.is_some()
        && !out
            .notes
            .iter()
            .any(|n| n.severity == shellcheck_rs::interface::Severity::ErrorC)
}

/// Generate a deterministic script of at least `lines` lines.
///
/// The generator emits small scripts, so the ones that parse are concatenated
/// until the line budget is met. Seeding is `fuzz`'s, so `--seed` reproduces an
/// input exactly.
pub fn generate_input(seeds: &[String], seed: u64, lines: usize) -> String {
    let mut rng = fuzz::Rng::new(seed.wrapping_add(0xbe5c));
    let mut out = String::new();
    let mut have = 0usize;
    while have < lines {
        let mut s = fuzz::generate(&mut rng, seeds);
        if !s.ends_with('\n') {
            s.push('\n');
        }
        // A `# shellcheck disable=all` anywhere silences every check from
        // there to the end of the file, which would benchmark a no-op. The
        // seeds are ShellCheck's own properties, so directives are common in
        // them; drop any fragment carrying one.
        if s.contains("shellcheck") || !parses(&s) {
            continue;
        }
        // Two fragments that each parse can still combine into one that does
        // not — an unterminated construct in the first swallowing the second —
        // and the whole tail of the script would then go unanalyzed. Keep the
        // accumulated script parseable at every step; parsing is the cheapest
        // phase, so re-checking it per fragment costs little.
        let candidate = format!("{out}{s}");
        if !parses(&candidate) {
            continue;
        }
        have += s.lines().count();
        out = candidate;
    }
    out
}

fn ms(d: Duration) -> f64 {
    d.as_secs_f64() * 1000.0
}

/// One timed run of the whole port pipeline, phase by phase.
struct Split {
    parse: Duration,
    maps: Duration,
    cfg: Duration,
    params_other: Duration,
    checks: Duration,
    resolve: Duration,
    total: Duration,
    comments: usize,
}

fn time_port(script: &str, filename: &str) -> Split {
    let spec = CheckSpec {
        filename: filename.to_string(),
        script: script.to_string(),
        ..CheckSpec::default()
    };

    // Phase 1: parse.
    let t0 = Instant::now();
    let parse = parser::parse_script_spec(&parser::ParseSpec {
        filename: spec.filename.clone(),
        script: spec.script.clone(),
        check_sourced: spec.check_sourced,
        shell_flag_specified: false,
        shell_hint: None,
        sys: std::rc::Rc::new(shellcheck_rs::interface::NoExternalSources),
    });
    let d_parse = t0.elapsed();
    let root = parse.root.clone().expect("benchmark input parses");

    // Phase 2/3: the two pure sub-phases of `make_parameters`, timed on their
    // own so the rest of it can be reported as a residual.
    let t1 = Instant::now();
    let _maps = analyzer_lib::build_maps(&root);
    let d_maps = t1.elapsed();

    let t2 = Instant::now();
    let _cfg = cfg_analysis::analyze_control_flow(
        &CFGParameters {
            cf_lastpipe: false,
            cf_pipefail: false,
        },
        &root,
    );
    let d_cfg = t2.elapsed();

    // Phase 4: the real `make_parameters`, which redoes both of the above.
    let t3 = Instant::now();
    let params = analyzer_lib::make_parameters_ext(
        root,
        parse.positions.clone(),
        None,
        None,
        spec.extended_analysis,
    );
    let d_params = t3.elapsed();

    // Phase 5: the check walks.
    let t4 = Instant::now();
    let analysis = analytics::analyze_with(&params, &[]);
    let d_checks = t4.elapsed();
    let n = analysis.len();
    drop(params);
    drop(analysis);

    // Phase 6: everything `checkScript` does after the checks. Timed as the
    // difference between the whole public entry point and the phases above,
    // which is the only way to reach code that is private to `checker`.
    let t5 = Instant::now();
    let result = shellcheck_rs::check_script(&spec);
    let d_whole = t5.elapsed();
    let d_resolve = d_whole
        .saturating_sub(d_parse)
        .saturating_sub(d_params)
        .saturating_sub(d_checks);

    Split {
        parse: d_parse,
        maps: d_maps,
        cfg: d_cfg,
        params_other: d_params.saturating_sub(d_maps).saturating_sub(d_cfg),
        checks: d_checks,
        resolve: d_resolve,
        total: d_whole,
        comments: n.max(result.comments.len()),
    }
}

/// Wall time of one oracle process over the same script, or `None` when no
/// oracle binary is there to run.
fn time_oracle(oracle: &str, script: &str) -> Option<Duration> {
    use std::io::Write;
    use std::process::{Command, Stdio};

    let t = Instant::now();
    let mut child = Command::new(oracle)
        .args(["-f", "json1", "-"])
        .stdin(Stdio::piped())
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .spawn()
        .ok()?;
    child
        .stdin
        .as_mut()
        .expect("stdin piped")
        .write_all(script.as_bytes())
        .ok()?;
    child.wait().ok()?;
    Some(t.elapsed())
}

pub fn run(args: &Args) -> Result<bool, String> {
    let (script, label) = match &args.input {
        Some(path) => (
            std::fs::read_to_string(path).map_err(|e| format!("{path}: {e}"))?,
            path.clone(),
        ),
        None => {
            let src = Path::new(&args.repo).join("src/ShellCheck");
            let seeds: Vec<String> = corpus::extract(&src)
                .map(|e| e.into_iter().map(|x| x.script).collect())
                .unwrap_or_default();
            (
                generate_input(&seeds, args.seed, args.lines),
                format!("generated seed={} lines={}", args.seed, args.lines),
            )
        }
    };

    if let Some(path) = &args.dump {
        std::fs::write(path, &script).map_err(|e| format!("{path}: {e}"))?;
        println!("bench: wrote {path}");
    }

    println!(
        "bench: {label} ({} lines, {} bytes), {} repeat(s)",
        script.lines().count(),
        script.len(),
        args.repeat
    );

    let mut best: Option<Split> = None;
    for _ in 0..args.repeat.max(1) {
        let s = time_port(&script, "-");
        if best.as_ref().is_none_or(|b| s.total < b.total) {
            best = Some(s);
        }
    }
    let s = best.expect("at least one repeat");

    let pct = |d: Duration| 100.0 * d.as_secs_f64() / s.total.as_secs_f64().max(f64::MIN_POSITIVE);
    println!(
        "  port  total      {:9.1} ms  ({} comments)",
        ms(s.total),
        s.comments
    );
    for (name, d) in [
        ("parse", s.parse),
        ("maps", s.maps),
        ("cfg", s.cfg),
        ("params-other", s.params_other),
        ("checks", s.checks),
        ("resolve", s.resolve),
    ] {
        println!("        {name:<12} {:9.1} ms  {:5.1}%", ms(d), pct(d));
    }

    let oracle_path = args.oracle_path();
    if let Some(d) = time_oracle(oracle_path, &script) {
        println!("  oracle           {:9.1} ms  (process, -f json1)", ms(d));
        println!(
            "  ratio            {:9.1}x  port/oracle",
            s.total.as_secs_f64() / d.as_secs_f64().max(f64::MIN_POSITIVE)
        );
    } else {
        println!("  oracle           (not runnable: {oracle_path})");
    }

    Ok(true)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The generator is deterministic and honours the line budget.
    #[test]
    fn generated_input_is_deterministic_and_long_enough() {
        let a = generate_input(&[], 1, 50);
        let b = generate_input(&[], 1, 50);
        assert_eq!(a, b);
        assert!(a.lines().count() >= 50);
        assert_ne!(a, generate_input(&[], 2, 50));
    }

    /// The phase split adds up to the measured total, within the slack that
    /// `resolve` being a residual allows.
    #[test]
    fn phase_split_covers_the_pipeline() {
        let s = time_port("echo $foo\nfor i in 1 2; do echo $i; done\n", "-");
        assert!(s.total > Duration::ZERO);
        assert!(s.parse <= s.total);
        assert!(s.comments > 0);
    }
}
