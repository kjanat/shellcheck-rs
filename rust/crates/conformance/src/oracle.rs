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
    binary: String,
    dir: PathBuf,
    counter: std::cell::Cell<u64>,
}

/// How many scripts to check per oracle invocation.
pub const BATCH: usize = 200;

impl Oracle {
    /// Prepare an oracle runner with its own scratch directory.
    pub fn new(binary: &str) -> Result<Oracle, String> {
        let dir =
            std::env::temp_dir().join(format!("shellcheck-conformance-{}", std::process::id()));
        std::fs::create_dir_all(&dir).map_err(|e| format!("{}: {e}", dir.display()))?;
        Ok(Oracle {
            binary: binary.to_string(),
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
                .map_err(|e| format!("running {}: {e}", self.binary))?;
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
            .map_err(|e| format!("running {}: {e}", self.binary))?;
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
            .map_err(|e| format!("running {} --version: {e}", self.binary))?;
        let text = String::from_utf8_lossy(&out.stdout);
        text.lines()
            .find_map(|l| l.strip_prefix("version:"))
            .map(|v| v.trim().to_string())
            .ok_or_else(|| format!("{}: no version line in --version output", self.binary))
    }

    /// A cheap fingerprint of the binary (FNV-1a), enough to tell two builds
    /// apart in a log. Not a cryptographic digest and not claimed to be one.
    pub fn fingerprint(&self) -> Result<String, String> {
        let bytes =
            std::fs::read(&self.binary).map_err(|e| format!("reading {}: {e}", self.binary))?;
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
/// documents how to do.
pub fn verify(oracle: &Oracle, repo: &str) -> Result<String, String> {
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
    if actual != expected {
        return Err(format!(
            "oracle is version {actual}, but {} says {expected}.\n  \
             The oracle must be ShellCheck built from this tree:\n    \
             cabal build shellcheck && cp \"$(cabal list-bin shellcheck)\" .cache/shellcheck-oracle",
            cabal_path.display()
        ));
    }
    Ok(format!(
        "oracle: {} version {actual}, fingerprint {}",
        oracle.binary,
        oracle.fingerprint()?
    ))
}

impl Drop for Oracle {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.dir);
    }
}
