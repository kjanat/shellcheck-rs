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
use h2r_core_ir::{Module, load_dirs, with_big_stack};
use h2r_lower::emit::emit_entry;
use h2r_lower::nir::FnId;
use h2r_lower::nir::lower::lower_leaf_in_world;
use h2r_lower::nir::pretty::format_leaf;
use h2r_lower::nir::specialize::{Instance, survey};

mod bench;
mod corpus;
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
    /// The optimized profile's `--test` harness for tail calls a million deep.
    #[arg(long, default_value = "compiler/canary/stack_checks.rs")]
    stack_checks: PathBuf,
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
    /// Time the entries of `Bench.hs` against the oracle at growing sizes, and run nothing else.
    #[arg(long, conflicts_with = "explain")]
    bench: bool,
    /// Compare this built ShellCheck entry binary with the library oracle on every `prop_` snippet, and run nothing else.
    #[arg(long, value_name = "PROGRAM", conflicts_with_all = ["explain", "bench"])]
    shellcheck: Option<PathBuf>,
    /// The oracle entry the `--shellcheck` binary was built from.
    #[arg(long, default_value = "parseMessages")]
    entry: String,
    /// Where the `--shellcheck` snippets are read from.
    #[arg(long, default_value = "src/ShellCheck")]
    corpus: PathBuf,
    /// The `--shellcheck` binary is a linter: write each snippet to a file and lint that file.
    #[arg(long, requires = "shellcheck")]
    lint: bool,
    /// With `--lint`: lint the files this file lists, one path per line, instead of the snippets.
    #[arg(long, requires = "lint")]
    paths: Option<PathBuf>,
    /// The canonical ShellCheck Core the library suite emits from.
    #[arg(long, default_value = "compiler/core-json")]
    library_core: PathBuf,
    /// The GHC-built driver that calls the same ShellCheck functions.
    #[arg(long, default_value = "compiler/build/shellcheck-oracle/oracle")]
    library_oracle: PathBuf,
    /// Skip the ShellCheck library suite.
    #[arg(long)]
    no_library: bool,
    /// Library dumps loaded beside every program's own, from `extract:libraries`.
    #[arg(
        long = "with",
        value_name = "DIR",
        default_values = [
            "compiler/library-json/containers",
            "compiler/library-json/transformers",
            "compiler/library-json/mtl",
            "compiler/library-json/base",
            "compiler/library-json/ghc-prim",
            "compiler/library-json/ghc-bignum",
        ]
    )]
    with: Vec<PathBuf>,
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

    if cli.bench {
        let out = profile_dir(&cli, Profile::Optimized);
        let modules = load_dirs(&out.join("core"), &cli.with)?.modules;
        let lines = bench::run(
            &modules,
            &out.join("oracle"),
            &out.join("bench"),
            std::time::Duration::from_secs(cli.timeout_seconds),
        )
        .map_err(anyhow::Error::msg)?;
        for line in lines {
            println!("{line}");
        }
        return Ok(());
    }

    if let Some(program) = &cli.shellcheck {
        return shellcheck_corpus(&cli, program, jobs);
    }

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

    if !cli.no_library {
        let report = library_run(&cli, jobs)?;
        println!(
            "library: {} ShellCheck bindings, {} differential cases",
            report.entries, report.cases
        );
        cases += report.cases;
        failures.extend(
            report
                .failures
                .into_iter()
                .map(|failure| format!("library: {failure}")),
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

fn shellcheck_corpus(cli: &Cli, program: &Path, jobs: usize) -> Result<()> {
    let snippets: Vec<String> = match &cli.paths {
        Some(list) => std::fs::read_to_string(list)?
            .lines()
            .filter(|line| !line.is_empty())
            .map(str::to_string)
            .collect(),
        None => corpus::snippets(&cli.corpus)
            .map_err(anyhow::Error::msg)?
            .into_iter()
            .collect(),
    };
    let timeout = std::time::Duration::from_secs(cli.timeout_seconds);
    let inputs: Vec<String> = if cli.paths.is_some() {
        snippets.clone()
    } else if cli.lint {
        let dir = program.parent().map_or_else(
            || PathBuf::from("lint-corpus"),
            |dir| dir.join("lint-corpus"),
        );
        std::fs::create_dir_all(&dir)?;
        let extensions = ["sh", "bash", "ksh", "dash", "bats", "envrc", "txt"];
        snippets
            .iter()
            .enumerate()
            .map(|(index, snippet)| {
                let path = dir.join(format!(
                    "{index:04}.{}",
                    extensions[index % extensions.len()]
                ));
                std::fs::write(&path, snippet)?;
                Ok(path.to_string_lossy().into_owned())
            })
            .collect::<std::io::Result<_>>()?
    } else {
        snippets.clone()
    };
    let compared = parallel(&inputs, jobs, |input| {
        let expected = differential::invoke(
            &cli.library_oracle,
            &[cli.entry.clone(), input.clone()],
            timeout,
        )?;
        let actual = differential::invoke(program, std::slice::from_ref(input), timeout)?;
        let case = Case {
            occ: &cli.entry,
            mode: Mode::Optimized,
            arguments: vec![input.clone()],
            expected_exit: if cli.lint && !expected.stdout.is_empty() {
                1
            } else {
                0
            },
        };
        Ok::<_, String>((
            differential::compare(&case, &expected, &actual),
            expected.stdout,
        ))
    });
    let mut failures = Vec::new();
    let mut outputs = std::collections::BTreeSet::new();
    for outcome in compared {
        match outcome {
            Ok((differences, stdout)) => {
                failures.extend(differences);
                outputs.insert(stdout);
            }
            Err(error) => failures.push(error),
        }
    }
    for failure in &failures {
        eprintln!("{failure}");
    }
    println!(
        "{}: {} inputs, {} distinct oracle outputs, {} differences",
        cli.entry,
        snippets.len(),
        outputs.len(),
        failures.len()
    );
    if !failures.is_empty() {
        bail!("{} corpus checks failed", failures.len());
    }
    Ok(())
}

/// Print one entry's NIR, the instances it needs and what it was refused for,
/// so a fixture's evidence can be written from what the lowering does rather
/// than from a guess about it.
fn explain(cli: &Cli, profile: Profile, occ: &str) -> Result<()> {
    let core = profile_dir(cli, profile).join("core");
    let modules = load_dirs(&core, &cli.with)?.modules;
    let binding = evidence::resolve(&modules, occ).map_err(anyhow::Error::msg)?;
    println!("=== {} {} ({})", profile.name(), occ, binding.name);
    match lower_leaf_in_world(&modules, binding.module, binding.binder, FnId(0)) {
        Ok(leaf) => println!("{}", format_leaf(&leaf)),
        Err(error) => println!(
            "not lowered: {}{}",
            error.reason,
            error
                .detail
                .map(|detail| format!(" [about {detail}]"))
                .unwrap_or_default()
        ),
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
        println!(
            "  refused: {}{}",
            refusal.reason,
            refusal
                .detail
                .as_deref()
                .map(|detail| format!(" [about {detail}]"))
                .unwrap_or_default()
        );
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
    let modules = load_dirs(&core, &cli.with)?.modules;

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
    if profile == Profile::Optimized
        && let Err(error) = differential::boxed_checks(
            &cli.stack_checks,
            &out.join("stack-checks"),
            out.canonicalize()?.as_path(),
        )
    {
        failures.push(error);
    }

    failures.extend(refusals(&modules, profile));
    let probes: Vec<&fixtures::Probe> = fixtures::ERROR_PROBES
        .iter()
        .filter(|probe| probe.when.covers(profile))
        .collect();
    let probe_failures = error_probes(
        &modules,
        &oracle,
        profile,
        &probes,
        std::time::Duration::from_secs(cli.timeout_seconds),
    );
    println!(
        "{}: {} error/branch differential probes (two Rust modes), {} failures",
        profile.name(),
        probes.len(),
        probe_failures.len()
    );
    failures.extend(probe_failures);

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
/// ShellCheck's own exported bindings, emitted from the canonical dump and
/// compared with the GHC-built library called through the oracle driver.
fn library_run(cli: &Cli, jobs: usize) -> Result<Report> {
    if !cli.library_oracle.is_file() {
        bail!(
            "{} is missing; run `mise run canary:library` first",
            cli.library_oracle.display()
        );
    }
    let modules = load_dirs(&cli.library_core, &cli.with)?.modules;
    let out = cli
        .library_oracle
        .parent()
        .map_or_else(|| PathBuf::from("."), |dir| dir.join("entries"));
    std::fs::create_dir_all(&out)?;
    let mut failures = Vec::new();
    let mut entries = Vec::new();
    for library in fixtures::LIBRARY {
        let occ = library.occ();
        match emit_entry(&modules, library.name) {
            Ok(source) => {
                let artifacts = differential::artifacts(&out, occ);
                std::fs::write(&artifacts.source, source)?;
                entries.push((library, artifacts));
            }
            Err(reason) => failures.push(format!("{occ}: {reason}")),
        }
    }
    let compilations: Vec<(&Artifacts, Mode)> = entries
        .iter()
        .flat_map(|(_, artifacts)| Mode::ALL.map(|mode| (artifacts, mode)))
        .collect();
    let rejected: Vec<String> = parallel(&compilations, jobs, |(artifacts, mode)| {
        differential::compile(&artifacts.source, artifacts.binary(*mode), *mode)
    })
    .into_iter()
    .filter_map(Result::err)
    .collect();
    if !rejected.is_empty() {
        failures.extend(rejected);
        return Ok(Report {
            entries: entries.len(),
            checks: 0,
            cases: 0,
            failures,
        });
    }
    let runs: Vec<(&fixtures::Library, &Artifacts, &[&str])> = entries
        .iter()
        .flat_map(|(library, artifacts)| {
            library
                .inputs
                .iter()
                .map(move |inputs| (*library, artifacts, *inputs))
        })
        .collect();
    let timeout = std::time::Duration::from_secs(cli.timeout_seconds);
    let compared = parallel(&runs, jobs, |(library, artifacts, inputs)| {
        let arguments: Vec<String> = inputs.iter().map(|input| (*input).to_string()).collect();
        let mut invocation = vec![library.occ().to_string()];
        invocation.extend(arguments.iter().cloned());
        let expected = differential::invoke(&cli.library_oracle, &invocation, timeout)?;
        let mut differences = Vec::new();
        for mode in Mode::ALL {
            let case = Case {
                occ: library.occ(),
                mode,
                arguments: arguments.clone(),
                expected_exit: 0,
            };
            let actual = differential::invoke(artifacts.binary(mode), &arguments, timeout)?;
            differences.extend(differential::compare(&case, &expected, &actual));
        }
        Ok::<_, String>(differences)
    });
    let mut cases = 0;
    for outcome in compared {
        match outcome {
            Ok(differences) => {
                cases += Mode::ALL.len();
                failures.extend(differences);
            }
            Err(error) => failures.push(error),
        }
    }
    Ok(Report {
        entries: entries.len(),
        checks: 0,
        cases,
        failures,
    })
}

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
            arguments: numbers.clone(),
            expected_exit: fixture.expected_exit,
        };
        let actual = differential::invoke(artifacts.binary(mode), &numbers, timeout)?;
        differences.extend(differential::compare(&case, &expected, &actual));
        ran += 1;
    }
    Ok((ran, differences))
}

/// Forced errors: independently assert the oracle contract, then compare both
/// generated executables. Only the executable-name prefix differs by design.
fn error_probes(
    modules: &[Module],
    oracle: &Path,
    profile: Profile,
    probes: &[&fixtures::Probe],
    timeout: std::time::Duration,
) -> Vec<String> {
    let mut failures = Vec::new();
    if let Err(error) = error_evidence(modules) {
        failures.push(error);
    }
    if let Err(error) = call_stack_error_evidence(modules) {
        failures.push(format!("errorCall: {error}"));
    }
    for entry in ["stringEqual", "elemChar", "prefixOf"] {
        if let Err(error) = predicate_evidence(modules, entry) {
            failures.push(format!("{entry}: {error}"));
        }
    }
    for entry in [
        "mapChars",
        "filterChars",
        "dropWhileChars",
        "takeWhileChars",
    ] {
        if let Err(error) = list_function_evidence(modules, entry) {
            failures.push(format!("{entry}: {error}"));
        }
    }
    if let Err(error) = tag_evidence(modules) {
        failures.push(format!("tagColour: {error}"));
    }
    if profile == Profile::Optimized
        && let Err(error) = compare_evidence(modules)
    {
        failures.push(format!("compareStrings: {error}"));
    }
    let mut compiled = std::collections::BTreeSet::new();
    let Some(program_name) = oracle.file_name().and_then(|name| name.to_str()) else {
        return vec!["oracle path lacks a UTF-8 program name".into()];
    };
    for &&fixtures::Probe {
        entry,
        input,
        message,
        located,
        ..
    } in probes
    {
        let arguments = vec![entry.to_string(), input.to_string(), "42".into()];
        let oracle_run = differential::invoke(oracle, &arguments, timeout);
        let suffix = if located {
            let lead = [
                format!("{program_name}: ").as_bytes(),
                message.unwrap_or_default(),
            ]
            .concat();
            match oracle_run
                .as_ref()
                .ok()
                .and_then(|run| run.stderr.strip_prefix(lead.as_slice()))
            {
                Some(rest)
                    if rest.starts_with(b"\nCallStack (from HasCallStack):\n  ")
                        && rest.ends_with(b"\n") =>
                {
                    rest.to_vec()
                }
                _ => {
                    failures.push(format!(
                        "{entry}: the oracle printed no call stack after its message: {oracle_run:?}"
                    ));
                    continue;
                }
            }
        } else {
            b"\n".to_vec()
        };
        let expected_for = |name: &str| differential::Outcome {
            stdout: if message.is_some() {
                vec![]
            } else {
                b"42\n".to_vec()
            },
            stderr: message
                .map(|m| {
                    let mut bytes = format!("{name}: ").into_bytes();
                    bytes.extend_from_slice(m);
                    bytes.extend_from_slice(&suffix);
                    bytes
                })
                .unwrap_or_default(),
            code: Some(if message.is_some() { 1 } else { 0 }),
        };
        let expected = expected_for(program_name);
        match oracle_run {
            Ok(actual) if actual == expected => {}
            Ok(actual) => failures.push(format!(
                "{entry}: error oracle contract differs: expected {expected:?}, got {actual:?}"
            )),
            Err(error) => failures.push(format!("{entry}: {error}")),
        }
        match evidence::resolve(modules, entry) {
            Ok(binding) => match emit_entry(modules, &binding.name) {
                Err(reason) => failures.push(format!("{entry}: error emission failed: {reason}")),
                Ok(source) => {
                    let artifacts =
                        differential::artifacts(oracle.parent().expect("oracle directory"), entry);
                    if let Err(error) = std::fs::write(&artifacts.source, source) {
                        failures.push(format!("{entry}: {error}"));
                        continue;
                    }
                    for mode in Mode::ALL {
                        let binary = artifacts.binary(mode);
                        if !compiled.contains(binary) {
                            if let Err(error) =
                                differential::compile(&artifacts.source, binary, mode)
                            {
                                failures.push(error);
                                continue;
                            }
                            compiled.insert(binary.to_path_buf());
                        }
                        let candidate_name = binary.file_name().unwrap().to_str().unwrap();
                        let expected = expected_for(candidate_name);
                        match differential::invoke(binary, &arguments[1..], timeout) {
                            Ok(actual) if actual == expected => {}
                            Ok(actual) => failures.push(format!(
                                "{entry} {mode:?}: expected {expected:?}, got {actual:?}"
                            )),
                            Err(error) => failures.push(error),
                        }
                    }
                }
            },
            Err(error) => failures.push(error),
        }
    }
    failures
}

/// Mutate real, source-verified error NIR rather than trusting successful
/// execution alone to establish that the independent verifier rejects forgeries.
fn error_evidence(modules: &[Module]) -> Result<(), String> {
    use h2r_lower::nir::{Operation, Rule, ValueId, verify::verify_leaf_in_world};
    let binding = evidence::resolve(modules, "errorPlain")?;
    let leaf = lower_leaf_in_world(modules, binding.module, binding.binder, FnId(0))
        .map_err(|e| e.reason)?;
    verify_leaf_in_world(modules, binding.module, binding.binder, FnId(0), &leaf)?;
    for mutation in 0..4 {
        let mut forged = leaf.clone();
        let instruction = forged
            .function
            .blocks
            .iter_mut()
            .flat_map(|b| &mut b.instructions)
            .find(|i| matches!(i.operation, Operation::RaiseError { .. }))
            .ok_or("errorPlain lacks explicit error operation")?;
        let Operation::RaiseError { message } = instruction.operation else {
            unreachable!()
        };
        match mutation {
            0 => {
                instruction.operation = Operation::RaiseError {
                    message: ValueId(u32::MAX),
                }
            }
            1 => instruction.operation = Operation::Move(message),
            2 => instruction.origin.rule = Rule::Literal,
            _ => {
                instruction.result.ty =
                    h2r_lower::nir::shared(&h2r_lower::nir::strings::string_ty())
            }
        }
        if verify_leaf_in_world(modules, binding.module, binding.binder, FnId(0), &forged).is_ok() {
            return Err(format!("error verifier accepted mutation {mutation}"));
        }
    }
    Ok(())
}

fn call_stack_error_evidence(modules: &[Module]) -> Result<(), String> {
    use h2r_lower::nir::specialize::{Instance, survey};
    use h2r_lower::nir::{Operation, Rule, verify::verify_leaf_in_world};
    let root = evidence::resolve(modules, "errorCall")?;
    let closure = survey(modules, &[Instance::whole(root.module, root.binder)]);
    let (module, binder) = closure
        .instances
        .iter()
        .zip(&closure.lowered)
        .find_map(|(instance, leaf)| {
            let raises = leaf.as_ref()?.function.blocks.iter().any(|b| {
                b.instructions
                    .iter()
                    .any(|i| matches!(i.operation, Operation::RaiseCallStackError(_)))
            });
            (raises && instance.type_arguments.is_empty() && instance.dictionaries.is_empty())
                .then_some((instance.module, instance.binder))
        })
        .ok_or("no instance errorCall needs raises an error with a call stack")?;
    let binding = evidence::Binding {
        module,
        binder,
        name: modules[module].binder(binder).name.clone(),
    };
    let leaf = lower_leaf_in_world(modules, binding.module, binding.binder, FnId(0))
        .map_err(|e| e.reason)?;
    verify_leaf_in_world(modules, binding.module, binding.binder, FnId(0), &leaf)?;
    for mutation in 0..3 {
        let mut forged = leaf.clone();
        let instruction = forged
            .function
            .blocks
            .iter_mut()
            .flat_map(|b| &mut b.instructions)
            .find(|i| matches!(i.operation, Operation::RaiseCallStackError(_)))
            .ok_or("no error call in the entry's own leaf")?;
        let Operation::RaiseCallStackError(error) = &mut instruction.operation else {
            unreachable!()
        };
        match mutation {
            0 => std::mem::swap(&mut error.message, &mut error.stack),
            1 => std::mem::swap(&mut error.layouts.push, &mut error.layouts.empty),
            _ => instruction.origin.rule = Rule::ListFunction,
        }
        if verify_leaf_in_world(modules, binding.module, binding.binder, FnId(0), &forged).is_ok() {
            return Err(format!("error verifier accepted mutation {mutation}"));
        }
    }
    Ok(())
}

fn predicate_evidence(modules: &[Module], entry: &str) -> Result<(), String> {
    use h2r_lower::nir::{
        Operation, Predicate, Rule, external::Equality, verify::verify_leaf_in_world,
    };
    let binding = evidence::resolve(modules, entry)?;
    let leaf = lower_leaf_in_world(modules, binding.module, binding.binder, FnId(0))
        .map_err(|e| e.reason)?;
    verify_leaf_in_world(modules, binding.module, binding.binder, FnId(0), &leaf)?;
    for mutation in 0..5 {
        let mut forged = leaf.clone();
        let instruction = forged
            .function
            .blocks
            .iter_mut()
            .flat_map(|b| &mut b.instructions)
            .find(|i| matches!(i.operation, Operation::ListPredicate(_)))
            .ok_or("no list predicate in the entry's own leaf")?;
        let Operation::ListPredicate(predicate) = &mut instruction.operation else {
            unreachable!()
        };
        match mutation {
            0 => {
                predicate.equality = match predicate.equality {
                    Equality::Char => Equality::String,
                    Equality::String => Equality::Char,
                }
            }
            1 => {
                predicate.predicate = match predicate.predicate {
                    Predicate::Elem => Predicate::IsPrefixOf,
                    Predicate::EqString | Predicate::IsPrefixOf => Predicate::Elem,
                }
            }
            2 => std::mem::swap(&mut predicate.left, &mut predicate.right),
            3 => std::mem::swap(&mut predicate.false_, &mut predicate.true_),
            _ => instruction.origin.rule = Rule::AppendList,
        }
        if verify_leaf_in_world(modules, binding.module, binding.binder, FnId(0), &forged).is_ok() {
            return Err(format!(
                "list predicate verifier accepted mutation {mutation}"
            ));
        }
    }
    Ok(())
}

fn list_function_evidence(modules: &[Module], entry: &str) -> Result<(), String> {
    use h2r_lower::nir::{ListOp, Operation, Rule, verify::verify_leaf_in_world};
    let binding = evidence::resolve(modules, entry)?;
    let leaf = lower_leaf_in_world(modules, binding.module, binding.binder, FnId(0))
        .map_err(|e| e.reason)?;
    verify_leaf_in_world(modules, binding.module, binding.binder, FnId(0), &leaf)?;
    for mutation in 0..5 {
        let mut forged = leaf.clone();
        let instruction = forged
            .function
            .blocks
            .iter_mut()
            .flat_map(|b| &mut b.instructions)
            .find(|i| matches!(i.operation, Operation::ListFunction(_)))
            .ok_or("no list function in the entry's own leaf")?;
        let Operation::ListFunction(list) = &mut instruction.operation else {
            unreachable!()
        };
        match mutation {
            0 => {
                list.function = match list.function {
                    ListOp::Map => ListOp::Filter,
                    ListOp::Filter => ListOp::TakeWhile,
                    ListOp::TakeWhile => ListOp::DropWhile,
                    ListOp::DropWhile => ListOp::Filter,
                    ListOp::Reverse => ListOp::ReverseOnto,
                    ListOp::ReverseOnto => ListOp::Reverse,
                    ListOp::Length => ListOp::ReverseOnto,
                    ListOp::ConsAppend => ListOp::Map,
                }
            }
            1 => list.arguments.reverse(),
            2 => {
                list.truth = match list.truth {
                    Some(_) => None,
                    None => Some((list.nil.clone(), list.cons.clone())),
                }
            }
            3 => {
                list.mapped = match list.mapped {
                    Some(_) => None,
                    None => Some((list.nil.clone(), list.cons.clone())),
                }
            }
            _ => instruction.origin.rule = Rule::AppendList,
        }
        if verify_leaf_in_world(modules, binding.module, binding.binder, FnId(0), &forged).is_ok() {
            return Err(format!(
                "list function verifier accepted mutation {mutation}"
            ));
        }
    }
    Ok(())
}

fn tag_evidence(modules: &[Module]) -> Result<(), String> {
    use h2r_lower::nir::{Operation, Rule, verify::verify_leaf_in_world};
    let binding = evidence::resolve(modules, "tagColour")?;
    let leaf = lower_leaf_in_world(modules, binding.module, binding.binder, FnId(0))
        .map_err(|e| e.reason)?;
    verify_leaf_in_world(modules, binding.module, binding.binder, FnId(0), &leaf)?;
    for mutation in 0..2 {
        let mut forged = leaf.clone();
        let instruction = forged
            .function
            .blocks
            .iter_mut()
            .flat_map(|b| &mut b.instructions)
            .find(|i| matches!(i.operation, Operation::DataToTag { .. }))
            .ok_or("no dataToTag# in the entry's own leaf")?;
        let Operation::DataToTag { constructors, .. } = &mut instruction.operation else {
            unreachable!()
        };
        match mutation {
            0 => constructors.reverse(),
            _ => instruction.origin.rule = Rule::PointerEquality,
        }
        if verify_leaf_in_world(modules, binding.module, binding.binder, FnId(0), &forged).is_ok() {
            return Err(format!("dataToTag# verifier accepted mutation {mutation}"));
        }
    }
    Ok(())
}

fn compare_evidence(modules: &[Module]) -> Result<(), String> {
    use h2r_lower::nir::{Operation, Rule, verify::verify_leaf_in_world};
    let binding = evidence::resolve(modules, "compareStrings")?;
    let leaf = lower_leaf_in_world(modules, binding.module, binding.binder, FnId(0))
        .map_err(|e| e.reason)?;
    verify_leaf_in_world(modules, binding.module, binding.binder, FnId(0), &leaf)?;
    for mutation in 0..3 {
        let mut forged = leaf.clone();
        let instruction = forged
            .function
            .blocks
            .iter_mut()
            .flat_map(|b| &mut b.instructions)
            .find(|i| matches!(i.operation, Operation::CompareStrings(_)))
            .ok_or("no string comparison in the entry's own leaf")?;
        let Operation::CompareStrings(compare) = &mut instruction.operation else {
            unreachable!()
        };
        match mutation {
            0 => std::mem::swap(&mut compare.left, &mut compare.right),
            1 => std::mem::swap(&mut compare.lt, &mut compare.gt),
            _ => instruction.origin.rule = Rule::ListPredicate,
        }
        if verify_leaf_in_world(modules, binding.module, binding.binder, FnId(0), &forged).is_ok() {
            return Err(format!(
                "string comparison verifier accepted mutation {mutation}"
            ));
        }
    }
    Ok(())
}

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
