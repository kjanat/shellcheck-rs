use std::fmt::Write as _;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::ExitCode;

use anyhow::{Context, Result};

use crate::Checkout;
use crate::extract::{self, LAYOUTS, ProgramOptions, Tools};

pub fn libraries() -> ExitCode {
    report(|| {
        let checkout = Checkout::locate();
        let tools = Tools::new()?;
        watch([
            checkout.plugin(),
            checkout.plugin_project().join("cabal.project"),
            tools.store_db(None)?,
        ]);
        let (work, _claim) = claim("hs-libraries")?;
        for layout in LAYOUTS {
            extract::library(
                &tools,
                &checkout,
                layout.package,
                &work.join(layout.package),
                &work.join("build"),
                None,
                jobs()?,
            )?;
        }
        embed(LAYOUTS.iter().map(|layout| work.join(layout.package)))
    })
}

pub fn shellcheck() -> ExitCode {
    report(|| {
        let checkout = Checkout::locate();
        let tools = Tools::new()?;
        watch(extract::inputs(&checkout));
        let (work, _claim) = claim("hs-shellcheck")?;
        let build = work.join("build");
        extract::program(
            &tools,
            &checkout,
            &ProgramOptions {
                opt: "-O1".to_string(),
                build_dir: build.clone(),
                core_dir: work.join("core"),
                keep_dir: None,
                jobs: jobs()?,
                source_ref: None,
                constraints: None,
            },
        )?;
        println!(
            "cargo::rustc-env=HS_SHELLCHECK_PACKAGE_DB={}",
            extract::package_db(&tools, &build).display()
        );
        embed([work.join("core")])
    })
}

pub fn entry(shellcheck_db: &str) -> ExitCode {
    report(|| {
        let checkout = Checkout::locate();
        let tools = Tools::new()?;
        watch([
            checkout.entry_source(),
            checkout.plugin(),
            checkout.plugin_project().join("cabal.project"),
        ]);
        let (work, _claim) = claim("hs-entry")?;
        extract::entry(
            &tools,
            &checkout,
            &work.join("core"),
            &work.join("build"),
            Path::new(shellcheck_db),
            None,
        )?;
        embed([work.join("core")])
    })
}

pub fn claim(layer: &str) -> Result<(PathBuf, fs::File)> {
    let out = variable("OUT_DIR")?;
    let root = out
        .ancestors()
        .find(|dir| dir.join("CACHEDIR.TAG").is_file())
        .with_context(|| format!("no Cargo build directory holds {}", out.display()))?;
    let work = root.join("h2r").join(layer);
    fs::create_dir_all(&work).with_context(|| format!("creating {}", work.display()))?;
    let lock = fs::File::create(work.join("lock"))?;
    lock.lock()
        .with_context(|| format!("locking {}", work.display()))?;
    Ok((work, lock))
}

fn embed(dirs: impl IntoIterator<Item = PathBuf>) -> Result<()> {
    let mut source = String::from("&[\n");
    for dir in dirs {
        for dump in extract::dumps(&dir)? {
            let path = dump.display().to_string();
            writeln!(source, "    ({path:?}, include_bytes!({path:?})),")?;
        }
    }
    source.push_str("]\n");
    let path = variable("OUT_DIR")?.join("dumps.rs");
    fs::write(&path, source).with_context(|| format!("writing {}", path.display()))
}

fn watch(paths: impl IntoIterator<Item = PathBuf>) {
    for path in paths {
        println!("cargo::rerun-if-changed={}", path.display());
    }
}

fn jobs() -> Result<Option<usize>> {
    std::env::var("NUM_JOBS")
        .ok()
        .map(|jobs| jobs.parse().context("NUM_JOBS is a count"))
        .transpose()
}

fn variable(name: &str) -> Result<PathBuf> {
    std::env::var_os(name)
        .map(PathBuf::from)
        .with_context(|| format!("cargo sets {name} for build scripts"))
}

fn report(run: impl FnOnce() -> Result<()>) -> ExitCode {
    match run() {
        Ok(()) => ExitCode::SUCCESS,
        Err(error) => {
            eprintln!("{error:#}");
            ExitCode::FAILURE
        }
    }
}
