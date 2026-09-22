//! The differential canary: emit Rust from real GHC Core, compile it, and
//! check it against a GHC-built oracle of the same program.
//!
//! Two dumps of the same source are covered. `-O1` is the contract the rest of
//! the compiler is proved against; `-O0` keeps the dictionary spines, thunk
//! allocations and unfolded `++` calls that the simplifier would otherwise
//! remove before the plugin ever sees them, so several lowering rules have no
//! other way to be reached.
//!
//! Failures are collected rather than raised, so one run says everything that
//! is wrong instead of the first thing.

use std::path::{Path, PathBuf};
use std::sync::Mutex;
use std::sync::atomic::{AtomicUsize, Ordering};

use anyhow::{Result, bail};
use clap::Parser;
use h2r_core_ir::{Module, load_dir, with_big_stack};
use h2r_lower::emit::emit_entry;
use h2r_lower::nir::FnId;
use h2r_lower::nir::lower::lower_leaf_in_world;
use h2r_lower::nir::pretty::format_leaf;
use h2r_lower::nir::specialize::{Instance, survey};

mod differential;
mod evidence;
mod fixtures;

use differential::{Artifacts, Case, Mode};
use evidence::{Binding, Subject};
use fixtures::{Entry, FIXTURES, Fixture, Profile, REFUSALS};

/// How much stack a worker gets. Lowering is iterative, but the Core dump's
/// deserialiser is not, and the same pool runs both.
const WORKER_STACK: usize = 256 << 20;

#[derive(Parser)]
#[command(
    name = "h2r-canary",
    about = "Compile the canary from real Core and compare it with GHC"
)]
struct Cli {
    /// Where `canary:extract` left each profile's Core dump and oracle.
    #[arg(long, default_value = "compiler/build/canary")]
    build: PathBuf,
    /// The `--test` harness that reads the emitted boxed entries.
    #[arg(long, default_value = "compiler/canary/boxed_checks.rs")]
    boxed_checks: PathBuf,
    /// Run one profile instead of both.
    #[arg(long, default_value = "both", value_parser = ["both", "optimized", "unoptimized"])]
    profile: String,
    /// How many entries to compile and run at once.
    #[arg(long)]
    jobs: Option<usize>,
    /// Maximum seconds for each oracle or generated-binary invocation.
    #[arg(long, default_value_t = 10, value_parser = clap::value_parser!(u64).range(1..))]
    timeout_seconds: u64,
    /// Print one entry's NIR and the instances it needs, and run nothing.
    #[arg(long, value_name = "OCCURRENCE")]
    explain: Option<String>,
}

fn main() -> Result<()> {
    let cli = Cli::parse();
    with_big_stack(move || run(cli))?
}

fn run(cli: Cli) -> Result<()> {
    let jobs = cli
        .jobs
        .unwrap_or_else(|| std::thread::available_parallelism().map_or(4, std::num::NonZero::get));
    let profiles: Vec<Profile> = match cli.profile.as_str() {
        "both" => Profile::ALL.to_vec(),
        "optimized" => vec![Profile::Optimized],
        "unoptimized" => vec![Profile::Unoptimized],
        other => bail!("unknown profile {other:?}"),
    };

    if let Some(occ) = cli.explain.as_deref() {
        for profile in profiles {
            explain(&cli, profile, occ)?;
        }
        return Ok(());
    }

    let mut cases = 0usize;
    let mut failures = Vec::new();
    for profile in profiles {
        let report = profile_run(&cli, profile, jobs)?;
        println!(
            "{}: {} entries, {} evidence checks, {} differential cases",
            profile.name(),
            report.entries,
            report.checks,
            report.cases
        );
        cases += report.cases;
        failures.extend(
            report
                .failures
                .into_iter()
                .map(|failure| format!("{}: {failure}", profile.name())),
        );
    }

    if !failures.is_empty() {
        for failure in &failures {
            eprintln!("{failure}");
        }
        bail!("{} canary checks failed", failures.len());
    }
    println!("{cases} differential cases passed (stdout, stderr, exit status).");
    Ok(())
}

/// Print one entry's NIR, the instances it needs and what it was refused for,
/// so a fixture's evidence can be written from what the lowering does rather
/// than from a guess about it.
fn explain(cli: &Cli, profile: Profile, occ: &str) -> Result<()> {
    let core = profile_dir(cli, profile).join("core");
    let modules = load_dir(&core)?;
    let binding = evidence::resolve(&modules, occ).map_err(anyhow::Error::msg)?;
    println!("=== {} {} ({})", profile.name(), occ, binding.name);
    match lower_leaf_in_world(&modules, binding.module, binding.binder, FnId(0)) {
        Ok(leaf) => println!("{}", format_leaf(&leaf)),
        Err(error) => println!("not lowered: {}", error.reason),
    }
    let closure = survey(&modules, &[Instance::whole(binding.module, binding.binder)]);
    println!(
        "instances: {} lowered, {} refused",
        closure.lowered_count(),
        closure.refused.len()
    );
    for instance in &closure.instances {
        println!(
            "  {} at {} type arguments, {} dictionaries",
            modules[instance.module].binder(instance.binder).occ,
            instance.type_arguments.len(),
            instance.dictionaries.len()
        );
    }
    for refusal in &closure.refused {
        println!("  refused: {}", refusal.reason);
    }
    match emit_entry(&modules, &binding.name) {
        Ok(source) => println!("emitted {} bytes of Rust", source.len()),
        Err(reason) => println!("not emitted: {reason}"),
    }
    Ok(())
}

struct Report {
    entries: usize,
    checks: usize,
    cases: usize,
    failures: Vec<String>,
}

fn profile_dir(cli: &Cli, profile: Profile) -> PathBuf {
    match profile {
        Profile::Optimized => cli.build.clone(),
        Profile::Unoptimized => cli.build.join("unoptimized"),
    }
}

fn profile_run(cli: &Cli, profile: Profile, jobs: usize) -> Result<Report> {
    let out = profile_dir(cli, profile);
    let core = out.join("core");
    let oracle = out.join("oracle");
    if !oracle.is_file() {
        bail!(
            "{} is missing; run `mise run canary:extract` first",
            oracle.display()
        );
    }
    let modules = load_dir(&core)?;

    let mut failures = Vec::new();
    let mut checks = 0usize;

    // Emit and check the evidence. Each entry is independent of every other,
    // and lowering an instance closure is the slowest thing here.
    let selected: Vec<&Fixture> = FIXTURES
        .iter()
        .filter(|fixture| fixture.when.covers(profile))
        .collect();
    let prepared = parallel(&selected, jobs, |fixture| {
        prepare(&modules, fixture, profile)
    });
    let mut entries = Vec::new();
    for (fixture, outcome) in selected.iter().copied().zip(prepared) {
        match outcome {
            Ok(prepared) => {
                checks += fixture
                    .evidence
                    .iter()
                    .filter(|check| check.when.covers(profile))
                    .count();
                failures.extend(
                    prepared
                        .failures
                        .iter()
                        .map(|failure| format!("{}: {failure}", fixture.occ)),
                );
                if let Some(source) = prepared.source {
                    let artifacts = differential::artifacts(&out, fixture.occ);
                    std::fs::write(&artifacts.source, source)?;
                    entries.push((fixture, artifacts));
                }
            }
            Err(error) => failures.push(format!("{}: {error}", fixture.occ)),
        }
    }

    // Compile every emitted entry, both ways.
    let compilations: Vec<(&Artifacts, Mode)> = entries
        .iter()
        .flat_map(|(_, artifacts)| Mode::ALL.map(|mode| (artifacts, mode)))
        .collect();
    let compiled = parallel(&compilations, jobs, |(artifacts, mode)| {
        differential::compile(&artifacts.source, artifacts.binary(*mode), *mode)
    });
    // Without binaries there is nothing to compare, but the evidence that has
    // already been gathered is still worth reporting.
    let rejected: Vec<String> = compiled.into_iter().filter_map(Result::err).collect();
    let compiles = rejected.is_empty();
    failures.extend(rejected);
    if !compiles {
        return Ok(Report {
            entries: entries.len(),
            checks,
            cases: 0,
            failures,
        });
    }

    // Run each entry against the oracle over its own argument grid.
    let runs: Vec<(&Fixture, &Artifacts, Vec<i64>)> = entries
        .iter()
        .flat_map(|(fixture, artifacts)| {
            fixture
                .inputs
                .grid()
                .into_iter()
                .map(move |arguments| (*fixture, artifacts, arguments))
        })
        .collect();
    let compared = parallel(&runs, jobs, |(fixture, artifacts, arguments)| {
        differ(
            &oracle,
            fixture,
            artifacts,
            arguments,
            std::time::Duration::from_secs(cli.timeout_seconds),
        )
    });
    let mut cases = 0usize;
    for outcome in compared {
        match outcome {
            Ok((ran, differences)) => {
                cases += ran;
                failures.extend(differences);
            }
            Err(error) => failures.push(error),
        }
    }

    // The boxed entries are also read back by a Rust test harness, which
    // checks what the emitted code does rather than only what it prints.
    if let Err(error) = differential::boxed_checks(
        &cli.boxed_checks,
        &out.join("boxed-checks"),
        out.canonicalize()?.as_path(),
    ) {
        failures.push(error);
    }

    failures.extend(refusals(&modules, profile));

    Ok(Report {
        entries: entries.len(),
        checks,
        cases,
        failures,
    })
}

struct Prepared {
    /// `None` for an entry that exists to be lowered, not entered.
    source: Option<String>,
    failures: Vec<String>,
}

fn prepare(modules: &[Module], fixture: &Fixture, profile: Profile) -> Result<Prepared, String> {
    let binding = evidence::resolve(modules, fixture.occ)?;
    let emitted = if fixture.inputs.runs() {
        emit_entry(modules, &binding.name)
    } else {
        Err("this entry is lowered for its evidence and never emitted".into())
    };
    let mut subject = Subject::new(modules, &binding);
    let failures = evidence::check(&mut subject, fixture, profile, &emitted);
    let source = match (fixture.inputs.runs(), emitted) {
        (true, Ok(source)) => Some(source),
        (true, Err(error)) => return Err(error),
        (false, _) => None,
    };
    Ok(Prepared { source, failures })
}

/// Run one argument list against the oracle and both compiled binaries.
fn differ(
    oracle: &Path,
    fixture: &Fixture,
    artifacts: &Artifacts,
    arguments: &[i64],
    timeout: std::time::Duration,
) -> Result<(usize, Vec<String>), String> {
    let numbers: Vec<String> = arguments.iter().map(i64::to_string).collect();
    let mut invocation = vec![fixture.occ.to_string()];
    invocation.extend(numbers.iter().cloned());
    let expected = differential::invoke(oracle, &invocation, timeout)?;
    let mut differences = Vec::new();
    let mut ran = 0;
    for mode in Mode::ALL {
        let case = Case {
            occ: fixture.occ,
            mode,
            arguments: arguments.to_vec(),
            expected_exit: fixture.expected_exit,
        };
        let actual = differential::invoke(artifacts.binary(mode), &numbers, timeout)?;
        differences.extend(differential::compare(&case, &expected, &actual));
        ran += 1;
    }
    Ok((ran, differences))
}

/// Entries whose only correct outcome is a refusal. A wrong answer for one of
/// these would be a miscompile, not a missing feature.
fn refusals(modules: &[Module], profile: Profile) -> Vec<String> {
    REFUSALS
        .iter()
        .filter(|refusal| refusal.when.covers(profile))
        .filter_map(|refusal| {
            let name = match refusal.entry {
                Entry::Stable(name) => name.to_string(),
                Entry::Occurrence(occ) => match evidence::resolve(modules, occ) {
                    Ok(Binding { name, .. }) => name,
                    Err(error) => return Some(error),
                },
            };
            match (emit_entry(modules, &name), refusal.because) {
                (Ok(_), _) => Some(format!("{name} was emitted; it must be refused")),
                (Err(_), None) => None,
                (Err(reason), Some(because)) if reason.contains(because) => None,
                (Err(reason), Some(because)) => Some(format!(
                    "{name} was refused for {reason:?}, expected a refusal mentioning {because:?}"
                )),
            }
        })
        .collect()
}

/// Run `items` across `jobs` workers, keeping the results in input order.
fn parallel<T: Sync, R: Send>(items: &[T], jobs: usize, run: impl Fn(&T) -> R + Sync) -> Vec<R> {
    let next = AtomicUsize::new(0);
    let results: Vec<Mutex<Option<R>>> = items.iter().map(|_| Mutex::new(None)).collect();
    let workers = jobs.clamp(1, items.len().max(1));
    let run = &run;
    let results = &results;
    let next = &next;
    std::thread::scope(|scope| {
        for worker in 0..workers {
            std::thread::Builder::new()
                .name(format!("canary-{worker}"))
                .stack_size(WORKER_STACK)
                .spawn_scoped(scope, move || {
                    loop {
                        let index = next.fetch_add(1, Ordering::Relaxed);
                        let Some(item) = items.get(index) else { break };
                        *results[index].lock().expect("no worker panics") = Some(run(item));
                    }
                })
                .expect("spawning a canary worker");
        }
    });
    results
        .iter()
        .map(|cell| {
            cell.lock()
                .expect("no worker panics")
                .take()
                .expect("every item ran")
        })
        .collect()
}
