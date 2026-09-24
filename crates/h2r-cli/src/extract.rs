use std::fs;
use std::path::PathBuf;
use std::time::Instant;

use anyhow::{Context, Result, bail};
use clap::{Args, Subcommand};
use h2r_build::Checkout;
use h2r_build::extract::{self, PROFILES, ProgramOptions, Tools, sha256_hex};

#[derive(Subcommand)]
pub enum Extract {
    #[command(
        about = "Compile one installed library from source with the plugin into compiler/library-json/<package>"
    )]
    Library {
        package: String,
        #[arg(
            long,
            help = "Where the dumps go (default compiler/library-json/<package>)"
        )]
        out: Option<PathBuf>,
        #[arg(
            long,
            help = "The cabal store package db (default ~/.local/state/cabal/store/ghc-<version>/package.db)"
        )]
        store_db: Option<PathBuf>,
    },
    #[command(
        about = "Compile crates/rshellcheck/entry/ShellCheckEntry.hs with the plugin into compiler/build/entry/core-json"
    )]
    Entry {
        #[arg(
            long,
            help = "The cabal store package db (default ~/.local/state/cabal/store/ghc-<version>/package.db)"
        )]
        store_db: Option<PathBuf>,
    },
    #[command(about = "Build the ShellCheck program with the plugin and collect its Core dumps")]
    Program(Program),
    #[command(
        about = "Extract everything rshellcheck compiles: the program, its twelve libraries and the entry module"
    )]
    World,
    #[command(
        about = "Build the canary oracle and write its Core dumps into compiler/build/canary, at -O1 and at -O0 under unoptimized/"
    )]
    Canary,
    #[command(
        about = "Build the GHC driver that calls ShellCheck's own functions into compiler/build/shellcheck-oracle/oracle"
    )]
    Oracle,
    #[command(
        about = "Extract the program under each GHC optimisation profile into compiler/matrix/<profile>"
    )]
    Matrix {
        #[arg(help = "Profiles to extract (default all)")]
        profiles: Vec<String>,
    },
    #[command(
        about = "Compare every installed interface with its rebuilt counterpart after normalisation"
    )]
    Interfaces {
        installed: PathBuf,
        rebuilt: PathBuf,
        #[arg(help = "Interface paths, relative to the installed directory, declared to differ")]
        declared: Vec<String>,
    },
    #[command(about = "Print the Paths_ module cabal generates for an installed library")]
    PathsModule {
        module: String,
        prefix: String,
        version: String,
    },
}

#[derive(Args)]
pub struct Program {
    #[arg(
        long,
        default_value = "-O1",
        allow_hyphen_values = true,
        help = "GHC optimisation flags for the ShellCheck package"
    )]
    opt: String,
    #[arg(long, help = "Scratch build tree (default compiler/build/canonical)")]
    build_dir: Option<PathBuf>,
    #[arg(long, help = "Where the dumps go (default compiler/core-json)")]
    core_dir: Option<PathBuf>,
    #[arg(
        long,
        help = "Copy the built binary, cabal's build plan and a provenance record here"
    )]
    keep_dir: Option<PathBuf>,
    #[arg(
        long,
        help = "Concurrent build jobs (default the number of available CPUs)"
    )]
    jobs: Option<usize>,
    #[arg(long, help = "A historical commit for the sources and the plugin")]
    source_ref: Option<String>,
    #[arg(
        long,
        help = "An existing cabal plan whose dependency versions are pinned"
    )]
    plan: Option<PathBuf>,
}

impl Program {
    fn options(self) -> Result<ProgramOptions> {
        Ok(ProgramOptions {
            opt: self.opt,
            build_dir: absolute(self.build_dir)?,
            core_dir: absolute(self.core_dir)?,
            keep_dir: absolute(self.keep_dir)?,
            jobs: self.jobs,
            source_ref: self.source_ref,
            plan: absolute(self.plan)?,
        })
    }
}

pub fn run(command: Extract) -> Result<()> {
    let checkout = Checkout::locate()?;
    match command {
        Extract::Library {
            package,
            out,
            store_db,
        } => locked(&checkout, |tools| {
            extract::library(
                tools,
                &checkout,
                &package,
                absolute(out)?,
                absolute(store_db)?,
            )
        }),
        Extract::Entry { store_db } => locked(&checkout, |tools| {
            extract::entry(tools, &checkout, absolute(store_db)?)
        }),
        Extract::Program(program) => locked(&checkout, |tools| {
            extract::program(tools, &checkout, &program.options()?)
        }),
        Extract::World => locked(&checkout, |tools| extract::world(tools, &checkout)),
        Extract::Canary => locked(&checkout, |tools| extract::canary(tools, &checkout)),
        Extract::Oracle => locked(&checkout, |tools| extract::oracle(tools, &checkout)),
        Extract::Matrix { profiles } => matrix(&checkout, &profiles),
        Extract::Interfaces {
            installed,
            rebuilt,
            declared,
        } => extract::compare_interfaces(&Tools::new()?, &installed, &rebuilt, &declared),
        Extract::PathsModule {
            module,
            prefix,
            version,
        } => {
            print!("{}", extract::paths_module(&module, &prefix, &version));
            Ok(())
        }
    }
}

fn locked(checkout: &Checkout, run: impl FnOnce(&Tools) -> Result<()>) -> Result<()> {
    let _lock = checkout.lock()?;
    run(&Tools::new()?)
}

fn absolute(path: Option<PathBuf>) -> Result<Option<PathBuf>> {
    path.map(|path| {
        std::path::absolute(&path).with_context(|| format!("resolving {}", path.display()))
    })
    .transpose()
}

fn matrix(checkout: &Checkout, selected: &[String]) -> Result<()> {
    let matrix = checkout.root().join("compiler/matrix");
    let selected: Vec<String> = if selected.is_empty() {
        PROFILES.iter().map(|(name, _)| name.to_string()).collect()
    } else {
        selected.to_vec()
    };
    let executable = std::env::current_exe()?;
    for profile in &selected {
        let Some((_, flags)) = PROFILES.iter().find(|(name, _)| name == profile) else {
            bail!("unknown profile {profile}");
        };
        let dir = matrix.join(profile);
        fs::create_dir_all(&dir)?;
        fs::write(dir.join("flags"), format!("{flags}\n"))?;
        println!("==> profile {profile}: {flags}");
        let start = Instant::now();
        let log = dir.join("extract.log.next");
        let file = fs::File::create(&log)?;
        let status = std::process::Command::new(&executable)
            .args(["extract", "program", "--opt", flags])
            .arg("--build-dir")
            .arg(dir.join("build"))
            .arg("--core-dir")
            .arg(dir.join("core-json"))
            .arg("--keep-dir")
            .arg(&dir)
            .stdout(file.try_clone()?)
            .stderr(file)
            .status()?;
        if !status.success() {
            fs::rename(&log, dir.join("extract.log"))?;
            bail!(
                "    extraction failed; see {}",
                dir.join("extract.log").display()
            );
        }
        let text = fs::read_to_string(&log)?;
        if text
            .lines()
            .any(|line| line.starts_with("==> extraction unchanged:"))
        {
            print!("{text}");
            fs::remove_file(&log)?;
            continue;
        }
        fs::rename(&log, dir.join("extract.log"))?;
        let seconds = start.elapsed().as_secs();
        fs::write(dir.join("time"), format!("{seconds}\n"))?;
        let size = std::process::Command::new("du")
            .arg("-sh")
            .arg(dir.join("core-json"))
            .output()?;
        let size = String::from_utf8(size.stdout)?;
        println!(
            "    done in {seconds}s, {} of Core",
            size.split('\t').next().unwrap_or("").trim()
        );
    }
    println!();
    println!("==> module sets");
    for profile in &selected {
        let modules = fs::read(matrix.join(profile).join("modules"))?;
        println!(
            "    {profile}: {} modules, list sha {}",
            modules.iter().filter(|byte| **byte == b'\n').count(),
            &sha256_hex(&modules)[..12]
        );
    }
    Ok(())
}
