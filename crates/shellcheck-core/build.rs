use std::process::ExitCode;

use anyhow::{Context, Result};
use h2r_lower::build::Rustc;
use h2r_lower::emit::Driver;

const ENTRIES: [&str; 3] = [
    "$h2r-entry$ShellCheckEntry$lint",
    "$h2r-entry$ShellCheckEntry$optional",
    "$h2r-entry$ShellCheckEntry$version",
];

const BUDGET: usize = 4_000_000;

fn main() -> ExitCode {
    match generate() {
        Ok(()) => ExitCode::SUCCESS,
        Err(error) => {
            eprintln!("{error:#}");
            ExitCode::FAILURE
        }
    }
}

fn generate() -> Result<()> {
    println!("cargo::rerun-if-changed=build.rs");
    let rustc = rustc()?;
    let fingerprint = rustc.fingerprint().map_err(anyhow::Error::msg)?;
    let (work, _claim) =
        h2r_build::layer::claim(&format!("shellcheck-core-{}", &fingerprint[..16]))?;
    let emitted = work.clone();
    h2r_core_ir::with_big_stack(move || -> Result<()> {
        let modules = h2r_core_ir::parse_dumps(
            [hs_libraries::DUMPS, hs_shellcheck::DUMPS, hs_entry::DUMPS]
                .into_iter()
                .flatten()
                .copied(),
        )?;
        h2r_lower::build::emit(&modules, &ENTRIES, &emitted, BUDGET, Driver::Api)
            .map_err(anyhow::Error::msg)
    })??;
    h2r_lower::build::compile(&work, &rustc).map_err(anyhow::Error::msg)?;
    println!("cargo::rustc-link-search=all={}", work.display());
    Ok(())
}

fn rustc() -> Result<Rustc> {
    let variable = |name: &str| {
        std::env::var(name).with_context(|| format!("cargo sets {name} for build scripts"))
    };
    let mut flags: Vec<String> = variable("CARGO_ENCODED_RUSTFLAGS")?
        .split('\x1f')
        .filter(|flag| !flag.is_empty())
        .map(String::from)
        .collect();
    let (target, host) = (variable("TARGET")?, variable("HOST")?);
    if target != host {
        flags.extend(["--target".to_string(), target]);
    }
    Ok(Rustc {
        program: variable("RUSTC")?.into(),
        opt_level: variable("OPT_LEVEL")?,
        debug: variable("DEBUG")? == "true",
        flags,
    })
}
