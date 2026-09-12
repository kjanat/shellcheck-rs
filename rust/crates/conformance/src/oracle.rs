//! Running the Haskell ShellCheck binary as the oracle.
//!
//! The oracle is a separate process, so the cost that matters is process
//! startup, not analysis. ShellCheck accepts many files in one invocation and
//! tags every diagnostic with the file it came from, so this module writes a
//! batch of scripts to a scratch directory and checks them all in a single
//! run: ~1700 corpus scripts cost about nine invocations instead of 1700.
//!
//! The environment is scrubbed the way the port's own defaults are, so a
//! personal `SHELLCHECK_OPTS` or a stray `.shellcheckrc` in a parent directory
//! cannot silently change what the oracle says.

use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::process::Command;

use serde_json::Value;

pub struct Oracle {
    /// The resolved binary, so every later use (running it, reading it for a
    /// fingerprint) names the same file, whatever the caller wrote.
    binary: PathBuf,
    dir: PathBuf,
    counter: std::cell::Cell<u64>,
}

/// How many scripts to check per oracle invocation.
pub const BATCH: usize = 200;

/// Resolve an oracle spec to the file that will actually be run.
///
/// A spec with a path separator (or a leading `.`) is a path and is used as
/// given; a bare name is looked up on `PATH`, the way a shell would -- on
/// Windows trying each `PATHEXT` suffix as well. Resolving here rather than
/// leaving it to `Command` means the fingerprint and the banner name the same
/// file the comparison ran against, instead of a name that only the OS can
/// turn into one.
fn resolve(spec: &str) -> Result<PathBuf, String> {
    let as_path = Path::new(spec);
    if spec.contains('/') || spec.contains('\\') || as_path.components().count() > 1 {
        return if as_path.is_file() {
            Ok(as_path.to_path_buf())
        } else {
            Err(format!("oracle {spec}: not a file"))
        };
    }
    // A bare name: PATH, with the Windows extensions where they apply.
    let exts: Vec<String> = if cfg!(windows) {
        std::env::var("PATHEXT")
            .unwrap_or_else(|_| ".COM;.EXE;.BAT;.CMD".to_string())
            .split(';')
            .filter(|e| !e.is_empty())
            .map(|e| e.to_string())
            .collect()
    } else {
        Vec::new()
    };
    let path = std::env::var_os("PATH").unwrap_or_default();
    for dir in std::env::split_paths(&path) {
        let base = dir.join(spec);
        if base.is_file() {
            return Ok(base);
        }
        for ext in &exts {
            let candidate = dir.join(format!("{spec}{ext}"));
            if candidate.is_file() {
                return Ok(candidate);
            }
        }
    }
    Err(format!(
        "oracle {spec}: not found on PATH. Pass --oracle with a path, or put \
         shellcheck on PATH, or build one from this tree:\n    \
         cabal build shellcheck && cp \"$(cabal list-bin shellcheck)\" .cache/shellcheck-oracle"
    ))
}

impl Oracle {
    /// Prepare an oracle runner with its own scratch directory.
    ///
    /// `spec` is either a path to the binary or a bare command name to look up
    /// on `PATH`, so `--oracle shellcheck` uses the installed ShellCheck
    /// without a build of its own.
    pub fn new(spec: &str) -> Result<Oracle, String> {
        let binary = resolve(spec)?;
        let dir =
            std::env::temp_dir().join(format!("shellcheck-conformance-{}", std::process::id()));
        std::fs::create_dir_all(&dir).map_err(|e| format!("{}: {e}", dir.display()))?;
        Ok(Oracle {
            binary,
            dir,
            counter: std::cell::Cell::new(0),
        })
    }

    /// The scratch directory, so callers can name files inside it.
    pub fn dir(&self) -> &Path {
        &self.dir
    }

    /// A fresh file name for one script. Deliberately extension-less: both
    /// tools derive a dialect from a recognised extension, and a batch must not
    /// change what a script means.
    pub fn name(&self) -> String {
        let n = self.counter.get();
        self.counter.set(n + 1);
        format!("s{n:06}")
    }

    /// Check `scripts` (name -> source) in as few invocations as possible,
    /// returning each script's diagnostics keyed by the same name.
    ///
    /// A name missing from the result had no diagnostics. A name mapping to
    /// `Err` means the oracle produced nothing parseable for it.
    pub fn check(
        &self,
        scripts: &[(String, String)],
        shell: Option<&str>,
    ) -> Result<HashMap<String, Vec<Value>>, String> {
        let mut out: HashMap<String, Vec<Value>> = HashMap::new();
        for chunk in scripts.chunks(BATCH) {
            let mut paths: Vec<String> = Vec::with_capacity(chunk.len());
            for (name, body) in chunk {
                let p = self.dir.join(name);
                std::fs::write(&p, body).map_err(|e| format!("{}: {e}", p.display()))?;
                paths.push(p.to_string_lossy().into_owned());
                out.entry(name.clone()).or_default();
            }
            let mut cmd = Command::new(&self.binary);
            cmd.arg("--norc").arg("--format=json1");
            if let Some(s) = shell {
                cmd.arg(format!("--shell={s}"));
            }
            cmd.args(&paths);
            cmd.env_remove("SHELLCHECK_OPTS");
            let res = cmd
                .output()
                .map_err(|e| format!("running {}: {e}", self.binary.display()))?;
            let stdout = String::from_utf8_lossy(&res.stdout);
            let v: Value = serde_json::from_str(stdout.trim())
                .map_err(|e| format!("oracle json1: {e}: {}", &stdout[..stdout.len().min(200)]))?;
            for c in v
                .get("comments")
                .and_then(Value::as_array)
                .cloned()
                .unwrap_or_default()
            {
                let file = c.get("file").and_then(Value::as_str).unwrap_or_default();
                let base = Path::new(file)
                    .file_name()
                    .map(|s| s.to_string_lossy().into_owned())
                    .unwrap_or_default();
                out.entry(base).or_default().push(c);
            }
            for p in &paths {
                let _ = std::fs::remove_file(p);
            }
        }
        Ok(out)
    }

    /// Check a single script, also returning the process exit status, which a
    /// batch cannot attribute to one file.
    pub fn check_one(
        &self,
        script: &str,
        shell: Option<&str>,
    ) -> Result<(Vec<Value>, i32), String> {
        let name = self.name();
        let p = self.dir.join(&name);
        std::fs::write(&p, script).map_err(|e| format!("{}: {e}", p.display()))?;
        let mut cmd = Command::new(&self.binary);
        cmd.arg("--norc").arg("--format=json1");
        if let Some(s) = shell {
            cmd.arg(format!("--shell={s}"));
        }
        cmd.arg(&p);
        cmd.env_remove("SHELLCHECK_OPTS");
        let res = cmd
            .output()
            .map_err(|e| format!("running {}: {e}", self.binary.display()))?;
        let _ = std::fs::remove_file(&p);
        let stdout = String::from_utf8_lossy(&res.stdout);
        let v: Value =
            serde_json::from_str(stdout.trim()).map_err(|e| format!("oracle json1: {e}"))?;
        let comments = v
            .get("comments")
            .and_then(Value::as_array)
            .cloned()
            .unwrap_or_default();
        Ok((comments, res.status.code().unwrap_or(-1)))
    }
}

impl Oracle {
    /// The version the binary reports, from its `--version` banner.
    pub fn version(&self) -> Result<String, String> {
        let out = Command::new(&self.binary)
            .arg("--version")
            .output()
            .map_err(|e| format!("running {} --version: {e}", self.binary.display()))?;
        let text = String::from_utf8_lossy(&out.stdout);
        text.lines()
            .find_map(|l| l.strip_prefix("version:"))
            .map(|v| v.trim().to_string())
            .ok_or_else(|| {
                format!(
                    "{}: no version line in --version output",
                    self.binary.display()
                )
            })
    }

    /// A cheap fingerprint of the binary (FNV-1a), enough to tell two builds
    /// apart in a log. Not a cryptographic digest and not claimed to be one.
    pub fn fingerprint(&self) -> Result<String, String> {
        let bytes = std::fs::read(&self.binary)
            .map_err(|e| format!("reading {}: {e}", self.binary.display()))?;
        let mut h: u64 = 0xcbf2_9ce4_8422_2325;
        for b in &bytes {
            h ^= u64::from(*b);
            h = h.wrapping_mul(0x0000_0100_0000_01b3);
        }
        Ok(format!("{h:016x} ({} bytes)", bytes.len()))
    }
}

/// Establish that the binary being trusted as the oracle really is the
/// ShellCheck of this repository's sources, and say so out loud.
///
/// A conformance result means nothing if it was measured against the wrong
/// reference: a stale binary, or one built from a different version, turns
/// every "agrees" into a statement about something else entirely. The version
/// check below is necessary, not sufficient — the sufficient check is to
/// rebuild from `src/` and compare behaviour, which `--verify-oracle`
/// documents how to do. `allow_mismatch` (`--any-oracle-version`) keeps a
/// differently-versioned binary usable, but says so in the banner every time.
pub fn verify(oracle: &Oracle, repo: &str, allow_mismatch: bool) -> Result<String, String> {
    let cabal_path = std::path::Path::new(repo).join("ShellCheck.cabal");
    let cabal = std::fs::read_to_string(&cabal_path)
        .map_err(|e| format!("{}: {e}", cabal_path.display()))?;
    let expected = cabal
        .lines()
        .find_map(|l| {
            let l = l.trim();
            let rest = l
                .strip_prefix("Version:")
                .or_else(|| l.strip_prefix("version:"))?;
            Some(rest.trim().to_string())
        })
        .ok_or_else(|| format!("{}: no Version: field", cabal_path.display()))?;
    let actual = oracle.version()?;
    let mismatch = if actual == expected {
        String::new()
    } else if allow_mismatch {
        // Said out loud on every run: the results describe the binary that
        // answered, which is no longer the ShellCheck of this tree.
        format!(" -- MISMATCH: {} says {expected}", cabal_path.display())
    } else {
        return Err(format!(
            "oracle is version {actual}, but {} says {expected}.\n  \
             The oracle must be ShellCheck built from this tree:\n    \
             cabal build shellcheck && cp \"$(cabal list-bin shellcheck)\" .cache/shellcheck-oracle\n  \
             To compare against this binary anyway, pass --any-oracle-version.",
            cabal_path.display()
        ));
    };
    Ok(format!(
        "oracle: {} version {actual}, fingerprint {}{mismatch}",
        oracle.binary.display(),
        oracle.fingerprint()?
    ))
}

impl Drop for Oracle {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.dir);
    }
}
