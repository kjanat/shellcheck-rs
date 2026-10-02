use std::path::PathBuf;
use std::time::Duration;
use std::{fs, process::ExitCode};

use anyhow::{Context, Result, bail};
use clap::{Parser, ValueEnum};
use h2r_conformance::{
    corpus, generator,
    runner::{self, Pair},
};
use serde_json::{Value, json};

#[derive(Clone, Copy, ValueEnum)]
enum Mode {
    Corpus,
    Gate,
    Fuzz,
}

#[derive(Parser)]
#[command(about = "Compare an emitted ShellCheck binary with the Haskell oracle")]
struct Args {
    #[arg(value_enum)]
    mode: Mode,
    #[arg(long, default_value = ".")]
    repo: PathBuf,
    /// Required for gate/fuzz; never silently substitute the oracle.
    #[arg(long)]
    candidate: Option<PathBuf>,
    #[arg(long, default_value = "compiler/matrix/A/shellcheck")]
    oracle: PathBuf,
    #[arg(long, default_value = "compiler/conformance")]
    output: PathBuf,
    #[arg(long, default_value_t = 100)]
    iterations: usize,
    #[arg(long, default_value_t = 1)]
    seed: u64,
    #[arg(long, value_parser = ["bash", "sh", "dash", "ksh", "busybox"])]
    shell: Option<String>,
    /// Check inferred dialect plus each explicitly supported dialect.
    #[arg(long, conflicts_with = "shell")]
    all_shells: bool,
    /// Limit corpus cases for a smoke test; zero means the full corpus.
    #[arg(long, default_value_t = 0)]
    limit: usize,
    #[arg(long, default_value_t = 10, value_parser = clap::value_parser!(u64).range(1..))]
    timeout: u64,
}

fn run(args: Args) -> Result<u8> {
    let src = args.repo.join("src/ShellCheck");
    let coverage = corpus::coverage(&src).map_err(anyhow::Error::msg)?;
    println!("{}", coverage.summary());
    if coverage.entries.is_empty() {
        bail!("empty corpus");
    }
    let optional = corpus::optional_examples(&src).map_err(anyhow::Error::msg)?;
    if matches!(args.mode, Mode::Corpus) {
        println!("{} optional-check examples", optional.len() * 2);
        return Ok(0);
    }
    let candidate = args
        .candidate
        .context("--candidate is required; no compiled candidate is assumed")?
        .canonicalize()?;
    let oracle = args.oracle.canonicalize()?;
    fs::create_dir_all(&args.output)?;
    let dir = args
        .output
        .canonicalize()?
        .join(format!("run-{}", std::process::id()));
    fs::create_dir(&dir).context("creating exclusive run directory")?;
    let pair = Pair {
        oracle,
        candidate,
        dir,
        timeout: Duration::from_secs(args.timeout),
    };
    let version = runner::capture(
        &pair.oracle,
        &["--version".into()],
        &pair.dir,
        "version",
        pair.timeout,
    )?;
    let cabal = fs::read_to_string(args.repo.join("ShellCheck.cabal"))?;
    let expected = cabal
        .lines()
        .find_map(|l| {
            l.trim()
                .strip_prefix("version:")
                .or_else(|| l.trim().strip_prefix("Version:"))
        })
        .context("missing package version")?
        .trim();
    let actual = version
        .stdout
        .lines()
        .find_map(|l| l.trim().strip_prefix("version:"))
        .unwrap_or("")
        .trim();
    if version.timed_out || version.exit != Some(0) || actual != expected {
        bail!("oracle version mismatch: expected {expected}, got {actual}");
    }
    let oracle_fingerprint = runner::fingerprint(&pair.oracle)?;
    let candidate_fingerprint = runner::fingerprint(&pair.candidate)?;
    let self_check = oracle_fingerprint == candidate_fingerprint;
    if self_check {
        println!(
            "SELF-CHECK: identical binary fingerprints; this does not establish compiler conformance"
        );
    }
    let mut cases: Vec<(String, String, Option<String>)> = match args.mode {
        Mode::Gate => coverage
            .entries
            .iter()
            .map(|e| {
                (
                    format!("{}:{}:{}", e.path, e.line, e.id),
                    e.script.clone(),
                    None,
                )
            })
            .collect(),
        Mode::Fuzz => {
            let seeds = coverage
                .entries
                .iter()
                .map(|e| e.script.clone())
                .collect::<Vec<_>>();
            let mut rng = generator::Rng::new(args.seed);
            (0..args.iterations)
                .map(|i| {
                    (
                        format!("seed-{}-{i}", args.seed),
                        generator::generate(&mut rng, &seeds),
                        None,
                    )
                })
                .collect()
        }
        Mode::Corpus => unreachable!(),
    };
    if args.limit > 0 {
        cases.truncate(args.limit);
    }
    if matches!(args.mode, Mode::Gate) {
        for e in optional {
            cases.push((
                format!("optional:{}:positive", e.name),
                e.positive,
                Some(e.name.clone()),
            ));
            cases.push((
                format!("optional:{}:negative", e.name),
                e.negative,
                Some(e.name),
            ));
        }
    }
    if cases.is_empty() {
        bail!("no cases requested");
    }
    let shells = if args.all_shells {
        vec![
            None,
            Some("bash"),
            Some("sh"),
            Some("dash"),
            Some("ksh"),
            Some("busybox"),
        ]
    } else {
        vec![args.shell.as_deref()]
    };
    let mut checked = 0;
    let mut failures = Vec::<Value>::new();
    let mut errors = 0;
    for (id, script, enable) in cases {
        for shell in &shells {
            checked += 1;
            let (oracle, candidate) = pair.check(&script, *shell, enable.as_deref())?;
            let comparison = runner::agrees(&oracle, &candidate);
            if !matches!(comparison, Ok(true)) {
                let error = comparison.err().map(|e| format!("{e:#}"));
                errors += usize::from(error.is_some());
                failures.push(json!({"id":id,"script":script,"shell":shell,"enable":enable,"oracle":oracle,"candidate":candidate,"error":error}));
            }
        }
    }
    let report = pair.dir.join("report.json");
    fs::write(
        &report,
        serde_json::to_vec_pretty(
            &json!({"oracle":pair.oracle,"candidate":pair.candidate,"oracle_fingerprint":oracle_fingerprint,"candidate_fingerprint":candidate_fingerprint,"oracle_version":actual,"self_check":self_check,"seed":args.seed,"checked":checked,"errors":errors,"failures":failures}),
        )?,
    )?;
    println!(
        "{checked} checked; {} differences/errors ({errors} errors). {}",
        failures.len(),
        report.display()
    );
    Ok(if errors > 0 {
        2
    } else if !failures.is_empty() {
        1
    } else {
        0
    })
}

fn main() -> ExitCode {
    match run(Args::parse()) {
        Ok(code) => ExitCode::from(code),
        Err(e) => {
            eprintln!("{e:#}");
            ExitCode::from(2)
        }
    }
}
