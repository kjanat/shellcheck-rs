//! Peak resident memory comes from GNU time's `%M`.

use std::path::Path;
use std::time::{Duration, Instant};

use crate::differential::{self, Mode, Outcome};

pub struct Bench {
    pub occ: &'static str,
    pub what: &'static str,
    pub sizes: &'static [i64],
    pub second: i64,
}

pub const BENCHES: &[Bench] = &[
    Bench {
        occ: "benchSet",
        what: "Set.insert of n pseudo-random Ints",
        sizes: &[1_000, 10_000, 100_000, 1_000_000],
        second: 7,
    },
    Bench {
        occ: "benchText",
        what: "build, map and scan an n-character String",
        sizes: &[1_000, 10_000, 100_000, 1_000_000],
        second: 5,
    },
    Bench {
        occ: "benchDeep",
        what: "non-tail recursion n deep over a list",
        sizes: &[1_000, 10_000, 100_000, 1_000_000],
        second: 1,
    },
    Bench {
        occ: "benchCps",
        what: "n tail calls through a continuation argument",
        sizes: &[1_000, 10_000, 100_000, 1_000_000],
        second: 3,
    },
    Bench {
        occ: "benchChain",
        what: "forcing a chain of n thunks",
        sizes: &[1_000, 10_000, 100_000, 1_000_000],
        second: 0,
    },
    Bench {
        occ: "benchLoop",
        what: "a tail loop n long returning a boxed Int",
        sizes: &[1_000, 10_000, 100_000, 1_000_000],
        second: 0,
    },
];

pub struct Measurement {
    pub seconds: f64,
    pub peak_kib: Option<u64>,
    pub outcome: Outcome,
}

pub fn measure(
    program: &Path,
    arguments: &[String],
    timeout: Duration,
    stats: &Path,
) -> Result<Measurement, String> {
    let mut wrapped = vec![
        "-f".to_string(),
        "%M".to_string(),
        "-o".to_string(),
        stats.display().to_string(),
        program.display().to_string(),
    ];
    wrapped.extend_from_slice(arguments);
    let started = Instant::now();
    let outcome = differential::invoke(Path::new("/usr/bin/time"), &wrapped, timeout)?;
    let seconds = started.elapsed().as_secs_f64();
    let peak_kib = std::fs::read_to_string(stats).ok().and_then(|text| {
        text.lines()
            .last()
            .and_then(|line| line.trim().parse().ok())
    });
    Ok(Measurement {
        seconds,
        peak_kib,
        outcome,
    })
}

pub fn run(
    modules: &[h2r_core_ir::Module],
    oracle: &Path,
    out: &Path,
    timeout: Duration,
) -> Result<Vec<String>, String> {
    std::fs::create_dir_all(out).map_err(|error| format!("creating {}: {error}", out.display()))?;
    let stats = out.join("time.txt");
    let mut lines = Vec::new();
    for bench in BENCHES {
        lines.push(format!("{}: {}", bench.occ, bench.what));
        let binding = crate::evidence::resolve(modules, bench.occ)?;
        let source = match h2r_lower::emit::emit_entry(modules, &binding.name) {
            Ok(source) => source,
            Err(reason) => {
                lines.push(format!("    not emitted: {reason}"));
                continue;
            }
        };
        let artifacts = differential::artifacts(out, bench.occ);
        std::fs::write(&artifacts.source, source)
            .map_err(|error| format!("writing {}: {error}", artifacts.source.display()))?;
        differential::compile(
            &artifacts.source,
            artifacts.binary(Mode::Optimized),
            Mode::Optimized,
        )?;
        for &size in bench.sizes {
            let arguments = vec![size.to_string(), bench.second.to_string()];
            let mut named = vec![bench.occ.to_string()];
            named.extend_from_slice(&arguments);
            let ghc = measure(oracle, &named, timeout, &stats);
            let rust = measure(
                artifacts.binary(Mode::Optimized),
                &arguments,
                timeout,
                &stats,
            );
            lines.push(format!(
                "    n={size:<10} ghc {}  rust {}{}",
                describe(&ghc),
                describe(&rust),
                ratio(&ghc, &rust)
            ));
        }
    }
    Ok(lines)
}

fn describe(run: &Result<Measurement, String>) -> String {
    match run {
        Err(error) if error.contains("timed out") => "timed out".into(),
        Err(error) => format!("failed: {error}"),
        Ok(measurement) => {
            let memory = measurement.peak_kib.map_or_else(
                || "?".into(),
                |kib| format!("{:.1} MiB", kib as f64 / 1024.0),
            );
            let status = match measurement.outcome.code {
                Some(0) => String::new(),
                code => {
                    let stderr = String::from_utf8_lossy(&measurement.outcome.stderr);
                    format!(
                        " exit {code:?}: {}",
                        stderr
                            .lines()
                            .find(|line| !line.trim().is_empty())
                            .unwrap_or_default()
                    )
                }
            };
            format!("{:.3}s {memory}{status}", measurement.seconds)
        }
    }
}

fn ratio(ghc: &Result<Measurement, String>, rust: &Result<Measurement, String>) -> String {
    let (Ok(ghc), Ok(rust)) = (ghc, rust) else {
        return String::new();
    };
    if ghc.outcome.code != Some(0) || rust.outcome.code != Some(0) {
        return String::new();
    }
    if ghc.outcome.stdout != rust.outcome.stdout {
        return format!(
            "  OUTPUT DIFFERS: {:?} from GHC, {:?} from Rust",
            String::from_utf8_lossy(&ghc.outcome.stdout),
            String::from_utf8_lossy(&rust.outcome.stdout)
        );
    }
    let memory = match (ghc.peak_kib, rust.peak_kib) {
        (Some(g), Some(r)) if g > 0 => format!(", {:.1}x memory", r as f64 / g as f64),
        _ => String::new(),
    };
    format!(
        "  ({:.1}x time{memory})",
        rust.seconds / ghc.seconds.max(f64::EPSILON)
    )
}
