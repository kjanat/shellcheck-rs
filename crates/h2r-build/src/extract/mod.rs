use std::ffi::OsString;
use std::fmt::Write as _;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

use anyhow::{Context, Result, bail};
use sha2::{Digest, Sha256};

use crate::Checkout;

mod interfaces;
mod library;
mod paths;
mod program;

pub use interfaces::compare as compare_interfaces;
pub use library::{LAYOUTS, extract as library};
pub use paths::module as paths_module;
pub use program::{
    Options as ProgramOptions, PROFILES, canary, entry, extract as program, inputs, oracle,
    package_db,
};

const SOURCES: [(&str, &str); 5] = [
    (
        "crates/h2r-build/src/extract/mod.rs",
        include_str!("mod.rs"),
    ),
    (
        "crates/h2r-build/src/extract/library.rs",
        include_str!("library.rs"),
    ),
    (
        "crates/h2r-build/src/extract/interfaces.rs",
        include_str!("interfaces.rs"),
    ),
    (
        "crates/h2r-build/src/extract/paths.rs",
        include_str!("paths.rs"),
    ),
    (
        "crates/h2r-build/src/extract/program.rs",
        include_str!("program.rs"),
    ),
];

pub struct Tools {
    path: Option<OsString>,
    pub ghc_version: String,
}

impl Tools {
    pub fn new() -> Result<Tools> {
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

    pub(crate) fn plugin(&self, checkout: &Checkout, build: &Path) -> Result<Plugin> {
        println!("==> building the h2r plugin");
        self.run(
            self.command("cabal")
                .current_dir(checkout.plugin_project())
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

pub(crate) fn home() -> Result<PathBuf> {
    std::env::var_os("HOME")
        .map(PathBuf::from)
        .context("HOME is not set")
}

pub fn sha256_hex(bytes: &[u8]) -> String {
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
