use std::ffi::OsString;
use std::fmt::Write as _;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

use anyhow::{Context, Result, bail};
use clap::Subcommand;
use sha2::{Digest, Sha256};

mod interfaces;
mod library;
mod paths;
mod program;

pub use interfaces::compare as compare_interfaces;

const SOURCES: [(&str, &str); 5] = [
    (
        "compiler/rust/crates/h2r-cli/src/extract/mod.rs",
        include_str!("mod.rs"),
    ),
    (
        "compiler/rust/crates/h2r-cli/src/extract/library.rs",
        include_str!("library.rs"),
    ),
    (
        "compiler/rust/crates/h2r-cli/src/extract/interfaces.rs",
        include_str!("interfaces.rs"),
    ),
    (
        "compiler/rust/crates/h2r-cli/src/extract/paths.rs",
        include_str!("paths.rs"),
    ),
    (
        "compiler/rust/crates/h2r-cli/src/extract/program.rs",
        include_str!("program.rs"),
    ),
];

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
        about = "Compile compiler/entry/ShellCheckEntry.hs with the plugin into compiler/build/entry/core-json"
    )]
    Entry {
        #[arg(
            long,
            help = "The cabal store package db (default ~/.local/state/cabal/store/ghc-<version>/package.db)"
        )]
        store_db: Option<PathBuf>,
    },
    #[command(about = "Build the ShellCheck program with the plugin and collect its Core dumps")]
    Program(program::Options),
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

pub fn run(command: Extract) -> Result<()> {
    match command {
        Extract::Library {
            package,
            out,
            store_db,
        } => library::extract(
            &Tools::new()?,
            &package,
            absolute(out)?,
            absolute(store_db)?,
        ),
        Extract::Entry { store_db } => program::entry(&Tools::new()?, absolute(store_db)?),
        Extract::Program(options) => program::extract(&Tools::new()?, &options.absolute()?),
        Extract::Canary => program::canary(&Tools::new()?),
        Extract::Oracle => program::oracle(&Tools::new()?),
        Extract::Matrix { profiles } => program::matrix(&profiles),
        Extract::Interfaces {
            installed,
            rebuilt,
            declared,
        } => compare_interfaces(&Tools::new()?, &installed, &rebuilt, &declared),
        Extract::PathsModule {
            module,
            prefix,
            version,
        } => {
            print!("{}", paths::module(&module, &prefix, &version));
            Ok(())
        }
    }
}

pub fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .ancestors()
        .nth(4)
        .expect("the crate sits four levels below the repository root")
        .to_path_buf()
}

pub fn world() -> (PathBuf, Vec<PathBuf>) {
    let root = repo_root();
    let libraries = [
        "containers",
        "transformers",
        "mtl",
        "base",
        "parsec",
        "ghc-prim",
        "ghc-bignum",
        "regex-base",
        "regex-tdfa",
        "fgl",
        "array",
    ];
    let mut with: Vec<PathBuf> = libraries
        .iter()
        .map(|library| root.join("compiler/library-json").join(library))
        .collect();
    with.push(root.join("compiler/build/entry/core-json"));
    (root.join("compiler/core-json"), with)
}

pub(crate) struct Tools {
    path: Option<OsString>,
    pub ghc_version: String,
}

impl Tools {
    fn new() -> Result<Tools> {
        let mut tools = Tools {
            path: ghcup_path(),
            ghc_version: String::new(),
        };
        tools.ghc_version = tools
            .output(tools.command("ghc").arg("--numeric-version"))?
            .trim()
            .to_string();
        Ok(tools)
    }

    pub fn command(&self, program: &str) -> Command {
        let mut command = Command::new(program);
        if let Some(path) = &self.path {
            command.env("PATH", path);
        }
        command
    }

    pub fn run(&self, command: &mut Command) -> Result<()> {
        let status = command
            .status()
            .with_context(|| format!("running {}", describe(command)))?;
        if !status.success() {
            bail!("{} failed with {status}", describe(command));
        }
        Ok(())
    }

    pub fn output(&self, command: &mut Command) -> Result<String> {
        let output = command
            .stderr(Stdio::inherit())
            .output()
            .with_context(|| format!("running {}", describe(command)))?;
        if !output.status.success() {
            bail!("{} failed with {}", describe(command), output.status);
        }
        String::from_utf8(output.stdout)
            .with_context(|| format!("{} printed non-UTF-8", describe(command)))
    }

    pub fn store_db(&self, given: Option<PathBuf>) -> Result<PathBuf> {
        match given {
            Some(db) => Ok(db),
            None => Ok(home()?.join(format!(
                ".local/state/cabal/store/ghc-{}/package.db",
                self.ghc_version
            ))),
        }
    }

    pub fn plugin(&self, build: &Path) -> Result<Plugin> {
        println!("==> building the h2r plugin");
        self.run(
            self.command("cabal")
                .current_dir(repo_root().join("compiler/canary"))
                .arg("build")
                .arg("--offline")
                .arg(format!("--builddir={}", build.join("cabal").display()))
                .arg("h2r-plugin"),
        )?;
        let db = build
            .join("cabal/packagedb")
            .join(format!("ghc-{}", self.ghc_version));
        let field = |name: &str| -> Result<String> {
            Ok(self
                .output(
                    self.command("ghc-pkg")
                        .arg(format!("--package-db={}", db.display()))
                        .args(["field", "h2r-plugin", name, "--simple-output"]),
                )?
                .trim()
                .to_string())
        };
        let unit = field("id")?;
        let dir = field("dynamic-library-dirs")?;
        let library = field("hs-libraries")?;
        Ok(Plugin {
            unit,
            object: PathBuf::from(dir).join(format!("lib{library}-ghc{}.so", self.ghc_version)),
        })
    }
}

pub(crate) struct Plugin {
    unit: String,
    object: PathBuf,
}

impl Plugin {
    pub fn flag(&self, out: &Path) -> String {
        format!(
            "-fplugin-library={};{};H2R.CorePlugin;[\"outdir={}\"]",
            self.object.display(),
            self.unit,
            out.display()
        )
    }
}

fn ghcup_path() -> Option<OsString> {
    let home = std::env::var_os("HOME").map(PathBuf::from)?;
    let ghcup = home.join(".ghcup/bin");
    if !ghcup.is_dir() {
        return None;
    }
    let current = std::env::var_os("PATH").unwrap_or_default();
    if std::env::split_paths(&current).any(|entry| entry == ghcup) {
        return None;
    }
    let entries = [home.join(".cabal/bin"), ghcup]
        .into_iter()
        .chain(std::env::split_paths(&current));
    std::env::join_paths(entries).ok()
}

fn describe(command: &Command) -> String {
    std::iter::once(command.get_program())
        .chain(command.get_args())
        .map(|part| part.to_string_lossy().into_owned())
        .collect::<Vec<_>>()
        .join(" ")
}

fn absolute(path: Option<PathBuf>) -> Result<Option<PathBuf>> {
    path.map(|path| {
        std::path::absolute(&path).with_context(|| format!("resolving {}", path.display()))
    })
    .transpose()
}

pub(crate) fn home() -> Result<PathBuf> {
    std::env::var_os("HOME")
        .map(PathBuf::from)
        .context("HOME is not set")
}

pub(crate) fn sha256_hex(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .fold(String::with_capacity(64), |mut hex, byte| {
            write!(hex, "{byte:02x}").expect("writing to a String");
            hex
        })
}

pub(crate) fn sha256_file(path: &Path) -> Result<String> {
    Ok(sha256_hex(
        &fs::read(path).with_context(|| format!("reading {}", path.display()))?,
    ))
}

pub(crate) fn sha256sum_line(path: &Path, shown: &str) -> Result<String> {
    Ok(format!("{}  {shown}\n", sha256_file(path)?))
}

pub(crate) fn extractor_sources() -> String {
    SOURCES
        .iter()
        .map(|(path, source)| format!("{}  {path}\n", sha256_hex(source.as_bytes())))
        .collect()
}

pub(crate) fn files_under(dir: &Path) -> Result<Vec<PathBuf>> {
    let mut files = Vec::new();
    let mut pending = vec![dir.to_path_buf()];
    while let Some(dir) = pending.pop() {
        for entry in fs::read_dir(&dir).with_context(|| format!("listing {}", dir.display()))? {
            let entry = entry?;
            let kind = entry.file_type()?;
            if kind.is_dir() {
                pending.push(entry.path());
            } else if kind.is_file() {
                files.push(entry.path());
            }
        }
    }
    files.sort_by(|left, right| left.as_os_str().cmp(right.as_os_str()));
    Ok(files)
}

pub(crate) fn dumps(dir: &Path) -> Result<Vec<PathBuf>> {
    Ok(files_under(dir)?
        .into_iter()
        .filter(|path| path.to_string_lossy().ends_with(".core.json"))
        .collect())
}

pub(crate) fn top_level(dir: &Path, suffix: &str) -> Result<Vec<String>> {
    let mut names = Vec::new();
    for entry in fs::read_dir(dir).with_context(|| format!("listing {}", dir.display()))? {
        let name = entry?.file_name().to_string_lossy().into_owned();
        if name.ends_with(suffix) {
            names.push(name);
        }
    }
    names.sort();
    Ok(names)
}

pub(crate) fn dump_checksums(dir: &Path) -> Result<String> {
    let mut lines = String::new();
    for suffix in [".core.json", ".tidy-align.txt"] {
        for name in top_level(dir, suffix)? {
            lines.push_str(&sha256sum_line(&dir.join(&name), &name)?);
        }
    }
    Ok(lines)
}

pub(crate) fn unchanged(out: &Path, fingerprint: &str) -> Result<bool> {
    let Ok(recorded) = fs::read_to_string(out.join("inputs.sha256")) else {
        return Ok(false);
    };
    if recorded.trim_end() != fingerprint {
        return Ok(false);
    }
    let Ok(checksums) = fs::read_to_string(out.join("outputs.sha256")) else {
        return Ok(false);
    };
    for line in checksums.lines() {
        let Some((hash, name)) = line.split_once("  ") else {
            return Ok(false);
        };
        let path = out.join(name);
        if !path.is_file() || sha256_file(&path)? != hash {
            return Ok(false);
        }
    }
    Ok(true)
}

pub(crate) fn remove_dir(path: &Path) -> Result<()> {
    match fs::remove_dir_all(path) {
        Ok(()) => Ok(()),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => Ok(()),
        Err(error) => Err(error).with_context(|| format!("removing {}", path.display())),
    }
}
