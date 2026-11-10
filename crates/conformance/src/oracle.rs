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
use std::io::Read;
use std::path::{Path, PathBuf};
use std::process::{Command, ExitStatus, Stdio};
use std::time::{Duration, Instant};

use serde_json::Value;

pub struct Oracle {
    /// The resolved binary, so every later use (running it, reading it for a
    /// fingerprint) names the same file, whatever the caller wrote.
    binary: PathBuf,
    dir: PathBuf,
    counter: std::cell::Cell<u64>,
    /// Inputs the oracle could not answer for: it crashed, or produced nothing
    /// readable. Recorded rather than fatal, because a reference
    /// implementation that dies on an input is a finding about *it* — and a
    /// run that stops there tells us nothing about the rest of the corpus.
    crashes: std::cell::RefCell<Vec<(String, String)>>,
    allowance: Allowance,
}

/// How long one invocation may run before it is killed: `base`, plus
/// `per_script` for each script it checks. A run past this is stuck, and its
/// scripts are retried one at a time like those of a crashed batch.
#[derive(Debug, Clone, Copy)]
struct Allowance {
    base: Duration,
    per_script: Duration,
}

impl Allowance {
    const DEFAULT: Self = Self {
        base: Duration::from_secs(60),
        per_script: Duration::from_secs(2),
    };

    fn for_scripts(self, scripts: usize) -> Duration {
        self.base.saturating_add(
            self.per_script
                .saturating_mul(u32::try_from(scripts).unwrap_or(u32::MAX)),
        )
    }
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
            .map(std::string::ToString::to_string)
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
         shellcheck on PATH, or build the pinned upstream oracle:\n    \
         python tools/oracle.py"
    ))
}

/// The diagnostics of a `--format=json1` report, one list for each of `paths`
/// in the same order.
///
/// `None` unless ShellCheck could have printed the report for exactly these
/// files: a `comments` array whose every entry carries each json1 field the
/// comparison reads and names one of `paths`. A comment naming no file or
/// another file would otherwise leave every real input looking clean.
fn json1_report(stdout: &[u8], paths: &[String]) -> Option<Vec<Vec<Value>>> {
    let stdout = String::from_utf8_lossy(stdout);
    let report = serde_json::from_str::<Value>(stdout.trim()).ok()?;
    let mut by_path = vec![Vec::new(); paths.len()];
    for comment in report.get("comments")?.as_array()? {
        let file = comment.get("file")?.as_str()?;
        let at = paths.iter().position(|p| p == file)?;
        if !json1_comment(comment) {
            return None;
        }
        by_path[at].push(comment.clone());
    }
    Some(by_path)
}

/// Does `comment` carry every field of a json1 comment, each with its type?
fn json1_comment(comment: &Value) -> bool {
    let fields = |value: &Value, numbers: &[&str], texts: &[&str]| {
        numbers
            .iter()
            .all(|k| value.get(k).is_some_and(Value::is_i64))
            && texts
                .iter()
                .all(|k| value.get(k).is_some_and(Value::is_string))
    };
    fields(
        comment,
        &["line", "endLine", "column", "endColumn", "code"],
        &["level", "message"],
    ) && match comment.get("fix") {
        None | Some(Value::Null) => true,
        Some(fix) => fix
            .get("replacements")
            .and_then(Value::as_array)
            .is_some_and(|replacements| {
                replacements.iter().all(|r| {
                    fields(
                        r,
                        &["line", "endLine", "column", "endColumn", "precedence"],
                        &["insertionPoint", "replacement"],
                    )
                })
            }),
    }
}

/// How one oracle invocation ended.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Ended {
    Exited(i32),
    Signalled,
    /// Killed when its allowance ran out.
    OutOfTime(Duration),
}

/// What one oracle invocation produced.
struct Run {
    ended: Ended,
    stdout: Vec<u8>,
    stderr: Vec<u8>,
}

impl Run {
    /// Did the oracle check every file it was given? ShellCheck exits 0
    /// without findings and 1 with them; any other ending means it gave up
    /// on some input, whatever it printed first.
    fn checked(&self) -> bool {
        matches!(self.ended, Ended::Exited(0 | 1))
    }

    /// The exit code, with -1 for a process a signal ended.
    fn code(&self) -> i32 {
        match self.ended {
            Ended::Exited(code) => code,
            Ended::Signalled | Ended::OutOfTime(_) => -1,
        }
    }

    /// Why the oracle gave no usable report: how it ended and the first line
    /// it wrote to standard error, which is what names an upstream bug.
    fn failure(&self) -> String {
        let stderr = String::from_utf8_lossy(&self.stderr);
        let why = stderr
            .lines()
            .find(|l| !l.trim().is_empty())
            .unwrap_or("no json1 report for the file")
            .trim();
        match self.ended {
            Ended::Exited(code) => format!("exit {code}: {why}"),
            Ended::Signalled => format!("killed by a signal: {why}"),
            Ended::OutOfTime(limit) => format!("no answer within {limit:?}: {why}"),
        }
    }
}

impl Oracle {
    /// Prepare an oracle runner with its own scratch directory.
    ///
    /// `spec` is either a path to the binary or a bare command name to look up
    /// on `PATH`, so `--oracle shellcheck` uses the installed ShellCheck
    /// without a build of its own.
    pub fn new(spec: &str) -> Result<Self, String> {
        static INSTANCES: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
        let binary = resolve(spec)?;
        let instance = INSTANCES.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        let dir = std::env::temp_dir().join(format!(
            "shellcheck-conformance-{}-{instance}",
            std::process::id()
        ));
        std::fs::create_dir_all(&dir).map_err(|e| format!("{}: {e}", dir.display()))?;
        Ok(Self {
            binary,
            dir,
            counter: std::cell::Cell::new(0),
            crashes: std::cell::RefCell::new(Vec::new()),
            allowance: Allowance::DEFAULT,
        })
    }

    /// This oracle with `base` and `per_script` as its allowance, so a test
    /// reaches the deadline without waiting a minute.
    #[cfg(test)]
    fn with_allowance(mut self, base: Duration, per_script: Duration) -> Self {
        self.allowance = Allowance { base, per_script };
        self
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
    /// A name the oracle gave no usable report for is missing from the
    /// result, and [`Oracle::crashes`] says why.
    pub fn check(
        &self,
        scripts: &[(String, String)],
        shell: Option<&str>,
    ) -> Result<HashMap<String, Vec<Value>>, String> {
        self.check_with(scripts, shell, None)
    }

    /// As [`Oracle::check`], with an optional check enabled (`--enable`).
    pub fn check_with(
        &self,
        scripts: &[(String, String)],
        shell: Option<&str>,
        enable: Option<&str>,
    ) -> Result<HashMap<String, Vec<Value>>, String> {
        let mut out: HashMap<String, Vec<Value>> = HashMap::new();
        for chunk in scripts.chunks(BATCH) {
            let mut paths: Vec<String> = Vec::with_capacity(chunk.len());
            for (name, body) in chunk {
                paths.push(self.place(name, body)?);
            }
            let run = self.invoke(&paths, shell, enable);
            for p in &paths {
                self.clear(p);
            }
            let run = run?;
            if run.checked()
                && let Some(by_path) = json1_report(&run.stdout, &paths)
            {
                out.extend(chunk.iter().map(|(name, _)| name.clone()).zip(by_path));
                continue;
            }
            // One input in this batch killed the oracle, or its report is not
            // one for these files, and the answer for the other 199 went with
            // it. Re-run them one at a time so the run continues and the
            // culprit is named, rather than ending the comparison there.
            for (name, body) in chunk {
                match self.run_named(name, body, shell, enable) {
                    Ok((Some(comments), run)) if run.checked() => {
                        out.insert(name.clone(), comments);
                    }
                    Ok((_, run)) => self
                        .crashes
                        .borrow_mut()
                        .push((body.clone(), run.failure())),
                    Err(why) => self.crashes.borrow_mut().push((body.clone(), why)),
                }
            }
        }
        Ok(out)
    }

    /// Write `body` under `name` in the scratch directory, creating the
    /// directory a name such as `s000001/build.bash` puts it in, and return
    /// the path the oracle is given.
    fn place(&self, name: &str, body: &str) -> Result<String, String> {
        let p = self.dir.join(name);
        if let Some(parent) = p.parent() {
            std::fs::create_dir_all(parent).map_err(|e| format!("{}: {e}", parent.display()))?;
        }
        std::fs::write(&p, body).map_err(|e| format!("{}: {e}", p.display()))?;
        Ok(p.to_string_lossy().into_owned())
    }

    /// Remove a file [`Oracle::place`] wrote, and the directory it created.
    fn clear(&self, path: &str) {
        let p = Path::new(path);
        let _ = std::fs::remove_file(p);
        if let Some(parent) = p.parent()
            && parent != self.dir
        {
            let _ = std::fs::remove_dir(parent);
        }
    }

    /// The oracle invocation every check shares: json1 output, no rc file,
    /// no `SHELLCHECK_OPTS`.
    fn command(&self, shell: Option<&str>, enable: Option<&str>) -> Command {
        let mut cmd = Command::new(&self.binary);
        cmd.arg("--norc").arg("--format=json1");
        if let Some(s) = shell {
            cmd.arg(format!("--shell={s}"));
        }
        if let Some(e) = enable {
            cmd.arg(format!("--enable={e}"));
        }
        cmd.env_remove("SHELLCHECK_OPTS");
        cmd
    }

    /// Run the oracle over `paths`, killing it once its allowance runs out.
    /// `Err` means it could not be started.
    fn invoke(
        &self,
        paths: &[String],
        shell: Option<&str>,
        enable: Option<&str>,
    ) -> Result<Run, String> {
        let running = |e: std::io::Error| format!("running {}: {e}", self.binary.display());
        let mut child = self
            .command(shell, enable)
            .args(paths)
            .stdin(Stdio::null())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .map_err(running)?;
        let limit = self.allowance.for_scripts(paths.len());
        let deadline = Instant::now() + limit;
        let (closed, pipes_closed) = std::sync::mpsc::channel();
        let stdout = drain(child.stdout.take(), closed.clone());
        let stderr = drain(child.stderr.take(), closed);
        // The pipes close when the process exits, which wakes this thread
        // without polling. A process that closes them and runs on is polled
        // until the deadline.
        for _ in 0..2 {
            let left = deadline.saturating_duration_since(Instant::now());
            if pipes_closed.recv_timeout(left).is_err() {
                break;
            }
        }
        let status: Option<ExitStatus> = loop {
            if let Some(status) = child.try_wait().map_err(running)? {
                break Some(status);
            }
            if Instant::now() >= deadline {
                break None;
            }
            std::thread::sleep(Duration::from_millis(1));
        };
        if status.is_none() {
            let _ = child.kill();
            let _ = child.wait();
        }
        Ok(Run {
            ended: status.map_or(Ended::OutOfTime(limit), |s| {
                s.code().map_or(Ended::Signalled, Ended::Exited)
            }),
            stdout: stdout.join().unwrap_or_default(),
            stderr: stderr.join().unwrap_or_default(),
        })
    }

    /// Check a single script, also returning the process exit status, which a
    /// batch cannot attribute to one file.
    pub fn check_one(
        &self,
        script: &str,
        shell: Option<&str>,
    ) -> Result<(Vec<Value>, i32), String> {
        self.check_one_enabled(script, shell, None)
    }

    /// As [`Oracle::check_one`], with an optional check enabled (`--enable`).
    pub fn check_one_enabled(
        &self,
        script: &str,
        shell: Option<&str>,
        enable: Option<&str>,
    ) -> Result<(Vec<Value>, i32), String> {
        self.check_named(&self.name(), script, shell, enable)
    }

    /// As [`Oracle::check_one_enabled`], under `name`, so a recognised
    /// extension in it still selects the dialect.
    fn check_named(
        &self,
        name: &str,
        script: &str,
        shell: Option<&str>,
        enable: Option<&str>,
    ) -> Result<(Vec<Value>, i32), String> {
        let (comments, run) = self.run_named(name, script, shell, enable)?;
        let comments = comments.ok_or_else(|| run.failure())?;
        Ok((comments, run.code()))
    }

    /// Check `script` alone under `name`: its diagnostics, if the oracle
    /// printed a usable report, and how the oracle ended.
    fn run_named(
        &self,
        name: &str,
        script: &str,
        shell: Option<&str>,
        enable: Option<&str>,
    ) -> Result<(Option<Vec<Value>>, Run), String> {
        let path = self.place(name, script)?;
        let run = self.invoke(std::slice::from_ref(&path), shell, enable);
        self.clear(&path);
        let run = run?;
        let comments = json1_report(&run.stdout, std::slice::from_ref(&path))
            .and_then(|mut by_path| by_path.pop());
        Ok((comments, run))
    }

    /// Inputs the oracle could not answer for, as (script, reason) pairs.
    ///
    /// These are not divergences — there is nothing to compare against — but
    /// they are findings about the reference implementation, so a run reports
    /// them separately rather than dropping them.
    pub fn crashes(&self) -> Vec<(String, String)> {
        self.crashes.borrow().clone()
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
/// rebuild the pinned upstream checkout and compare behaviour, which `--verify-oracle`
/// documents how to do. `allow_mismatch` (`--any-oracle-version`) keeps a
/// differently-versioned binary usable, but says so in the banner every time.
pub fn verify(oracle: &Oracle, repo: &str, allow_mismatch: bool) -> Result<String, String> {
    let cabal_path = std::path::Path::new(repo).join("ShellCheck.cabal");
    let cabal = if cabal_path.is_file() {
        std::fs::read_to_string(&cabal_path)
            .map_err(|e| format!("{}: {e}", cabal_path.display()))?
    } else {
        let path = std::path::Path::new(repo).join("tools/oracle.json");
        let pin: rshellcheck::oracle::UpstreamPin = serde_json::from_str(
            &std::fs::read_to_string(&path).map_err(|e| format!("{}: {e}", path.display()))?,
        )
        .map_err(|e| e.to_string())?;
        format!("Version: {}", pin.version)
    };
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
             Build the pinned upstream oracle:\n    \
             python tools/oracle.py\n  \
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

/// Read `pipe` to its end on a thread of its own, then say so on `closed`.
fn drain(
    pipe: Option<impl Read + Send + 'static>,
    closed: std::sync::mpsc::Sender<()>,
) -> std::thread::JoinHandle<Vec<u8>> {
    std::thread::spawn(move || {
        let mut buf = Vec::new();
        if let Some(mut pipe) = pipe {
            let _ = pipe.read_to_end(&mut buf);
        }
        let _ = closed.send(());
        buf
    })
}

impl Drop for Oracle {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.dir);
    }
}

#[cfg(test)]
pub fn test_oracle() -> Option<Oracle> {
    let spec = std::env::var("CONFORMANCE_ORACLE").unwrap_or_else(|_| {
        Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../.cache/shellcheck-oracle")
            .to_string_lossy()
            .into_owned()
    });
    Oracle::new(&spec)
        .inspect_err(|e| {
            println!("skipped: no oracle at {spec}: {e} (build one: python tools/oracle.py)");
        })
        .ok()
}

/// A scratch directory removed when the test ends.
#[cfg(test)]
pub struct Scratch(PathBuf);

#[cfg(test)]
impl Scratch {
    pub fn new(test: &str) -> Self {
        let dir = std::env::temp_dir().join(format!("conformance-{test}-{}", std::process::id()));
        std::fs::create_dir_all(&dir).expect("scratch directory");
        Self(dir)
    }

    pub fn path(&self) -> &Path {
        &self.0
    }
}

#[cfg(test)]
impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

/// A shell script in `dir` standing in for the oracle, running `body` for
/// every invocation except `--version`.
#[cfg(all(test, unix))]
pub fn fake_oracle(dir: &Path, body: &str) -> Oracle {
    let fake = dir.join("oracle");
    std::fs::write(
        &fake,
        format!("#!/bin/sh\n[ \"$1\" = --version ] && exit 0\n{body}\n"),
    )
    .expect("write oracle");
    std::fs::set_permissions(&fake, std::os::unix::fs::PermissionsExt::from_mode(0o755))
        .expect("chmod oracle");
    // A child another test thread forked while the write was open holds
    // the descriptor until it execs, and exec fails with ETXTBSY until
    // then. Once one exec succeeds, no process can hold it any more.
    for _ in 0..100 {
        match Command::new(&fake).arg("--version").output() {
            Err(e) if e.kind() == std::io::ErrorKind::ExecutableFileBusy => {
                std::thread::sleep(std::time::Duration::from_millis(10));
            }
            ran => {
                ran.expect("run fake oracle");
                break;
            }
        }
    }
    Oracle::new(&fake.to_string_lossy()).expect("oracle")
}

/// A fake oracle body that reports one SC2086 for every file containing
/// `dirty`, and nothing for any other.
#[cfg(all(test, unix))]
pub const DIRTY_ORACLE: &str = r#"sep=
printf '{"comments":['
for f; do
  case $f in --*) continue ;; esac
  case $(cat "$f") in
    *dirty*)
      printf '%s{"file":"%s","line":1,"endLine":1,"column":1,"endColumn":2,"level":"style","code":2086,"message":"m","fix":null}' "$sep" "$f"
      sep=,
      ;;
  esac
done
printf ']}\n'"#;

#[cfg(test)]
mod tests {
    use super::*;

    fn oracle() -> Option<Oracle> {
        test_oracle()
    }

    /// An input that kills the oracle must not take the rest of the batch with
    /// it: upstream 0.11.0 dies on `coproc` inside a command substitution
    /// (`Analytics.hs` `checkExpansionWithRedirection`, non-exhaustive
    /// `checkCmd`), and a run that stopped there would say nothing about the
    /// other 199 scripts it was given.
    #[test]
    fn a_crashing_input_does_not_lose_the_rest_of_the_batch() {
        let Some(o) = oracle() else { return };
        let scripts = vec![
            ("crasher".to_string(), "x=$(coproc foo)\n".to_string()),
            ("healthy".to_string(), "echo $x\n".to_string()),
        ];
        let out = o.check(&scripts, None).expect("batch must not fail");
        assert!(
            !out.contains_key("crasher"),
            "an unanswered script must have no answer, not an empty one"
        );
        let healthy = out.get("healthy").expect("the rest of the batch survives");
        assert!(
            healthy
                .iter()
                .any(|c| c.get("code").and_then(Value::as_i64) == Some(2086)),
            "expected SC2086 for `echo $x`, got {healthy:?}"
        );
        let crashes = o.crashes();
        assert_eq!(crashes.len(), 1, "one recorded crash: {crashes:?}");
        assert!(crashes[0].0.contains("coproc"));
    }

    /// The one-at-a-time retry after a crash checks each script under its own
    /// name, so a `.bash` file keeps the dialect its extension implies.
    #[test]
    fn a_crash_retry_keeps_each_scripts_file_name() {
        let Some(o) = oracle() else { return };
        let scripts = vec![
            ("crasher".to_string(), "x=$(coproc foo)\n".to_string()),
            ("healthy.bash".to_string(), "true\n".to_string()),
        ];
        let out = o.check(&scripts, None).expect("batch must not fail");
        let healthy = out
            .get("healthy.bash")
            .expect("the rest of the batch survives");
        assert!(
            healthy.is_empty(),
            "a `.bash` file needs no shebang, got {healthy:?}"
        );
    }

    #[cfg(unix)]
    fn scripts(oracle: &Oracle, bodies: &[&str]) -> Vec<(String, String)> {
        bodies
            .iter()
            .map(|b| (oracle.name(), (*b).to_string()))
            .collect()
    }

    #[cfg(unix)]
    #[test]
    fn each_file_gets_the_comments_naming_it() {
        let dir = Scratch::new("naming-it");
        let o = fake_oracle(dir.path(), DIRTY_ORACLE);
        let batch = scripts(&o, &["dirty\n", "clean\n"]);
        let out = o.check(&batch, None).expect("check");
        assert_eq!(out[&batch[0].0].len(), 1, "{out:?}");
        assert!(out[&batch[1].0].is_empty(), "{out:?}");
        assert!(o.crashes().is_empty());
    }

    /// A report the oracle could not have printed for these files answers
    /// for none of them, so no input reads as clean on its say-so.
    #[cfg(unix)]
    #[test]
    fn a_report_with_an_unusable_comment_answers_nothing() {
        let fields = r#""line":1,"endLine":1,"column":1,"endColumn":2,"level":"style","code":2086,"message":"m""#;
        let reporting = |comment: &str| {
            format!(
                "for f; do last=$f; done\nprintf '%s\\n' '{{\"comments\":[{comment}]}}' | sed \"s|@FILE@|$last|\""
            )
        };
        let dir = Scratch::new("usable");
        let o = fake_oracle(
            dir.path(),
            &reporting(&format!(r#"{{"file":"@FILE@",{fields},"fix":null}}"#)),
        );
        let one = scripts(&o, &["true\n"]);
        let out = o.check(&one, None).expect("check");
        assert_eq!(
            out[&one[0].0].len(),
            1,
            "the control report is usable: {out:?}"
        );
        for comment in [
            "{}".to_string(),
            format!("{{{fields}}}"),
            format!(r#"{{"file":"elsewhere",{fields}}}"#),
            r#"{"file":"@FILE@","line":1}"#.to_string(),
            format!(r#"{{"file":"@FILE@",{fields},"fix":{{"replacements":[{{}}]}}}}"#),
        ] {
            let dir = Scratch::new("unusable");
            let o = fake_oracle(dir.path(), &reporting(&comment));
            let batch = scripts(&o, &["true\n", "true\n"]);
            let out = o.check(&batch, None).expect("check");
            assert!(out.is_empty(), "{comment}: {out:?}");
            assert_eq!(o.crashes().len(), 2, "{comment}");
        }
    }

    /// A run that failed answers for no file it was given, even when it
    /// printed a valid report first.
    #[cfg(unix)]
    #[test]
    fn a_report_from_a_failed_run_answers_nothing() {
        for (body, why) in [
            (r#"echo '{"comments":[]}'; exit 2"#, "exit 2: "),
            (
                r#"echo '{"comments":[]}'; kill -9 $$"#,
                "killed by a signal: ",
            ),
        ] {
            let dir = Scratch::new("failed-run");
            let o = fake_oracle(dir.path(), body);
            let batch = scripts(&o, &["true\n", "true\n"]);
            let out = o.check(&batch, None).expect("check");
            assert!(out.is_empty(), "{body}: {out:?}");
            let crashes = o.crashes();
            assert_eq!(crashes.len(), 2, "{body}");
            assert!(
                crashes.iter().all(|(_, reason)| reason.starts_with(why)),
                "{crashes:?}"
            );
        }
    }

    /// A single check still reports the exit status, so the fuzzer can
    /// compare it with the port's.
    #[cfg(unix)]
    #[test]
    fn a_single_check_returns_the_exit_status_with_the_report() {
        let dir = Scratch::new("single-status");
        let o = fake_oracle(dir.path(), r#"echo '{"comments":[]}'; exit 2"#);
        assert_eq!(o.check_one("true\n", None), Ok((Vec::new(), 2)));
    }

    /// An oracle that hangs is killed when its allowance runs out, and the
    /// scripts it held are recorded as unanswered.
    #[cfg(unix)]
    #[test]
    fn a_hung_oracle_is_killed_at_its_deadline() {
        // The second oracle closes its output first, so only polling sees it.
        for body in ["exec sleep 30", "exec >&- 2>&-; exec sleep 30"] {
            let dir = Scratch::new("hung");
            let o = fake_oracle(dir.path(), body)
                .with_allowance(Duration::from_millis(100), Duration::ZERO);
            let batch = scripts(&o, &["true\n", "true\n"]);
            let started = Instant::now();
            let out = o.check(&batch, None).expect("check");
            assert!(
                started.elapsed() < Duration::from_secs(10),
                "{body}: {:?}",
                started.elapsed()
            );
            assert!(out.is_empty(), "{body}: {out:?}");
            let crashes = o.crashes();
            assert_eq!(crashes.len(), 2, "{body}");
            assert!(
                crashes
                    .iter()
                    .all(|(_, why)| why.starts_with("no answer within 100ms: ")),
                "{body}: {crashes:?}"
            );
        }
    }

    #[test]
    fn the_allowance_grows_with_the_scripts_in_a_run() {
        assert_eq!(Allowance::DEFAULT.for_scripts(1), Duration::from_secs(62));
        assert_eq!(
            Allowance::DEFAULT.for_scripts(BATCH),
            Duration::from_secs(460)
        );
    }

    #[test]
    fn without_a_cabal_file_the_pin_supplies_the_version() {
        let Some(o) = oracle() else { return };
        let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
        let banner = verify(&o, &root.to_string_lossy(), false).unwrap();
        assert!(banner.starts_with("oracle: "), "{banner}");
    }

    /// The published `rshellcheck` package cannot reach `tools/oracle.json`, so
    /// it builds its banner from a copy that a pin move has to update too.
    #[test]
    fn the_cli_copy_of_the_pin_matches_tools_oracle_json() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
        let read = |path: &str| -> rshellcheck::oracle::UpstreamPin {
            let text = std::fs::read_to_string(root.join(path)).unwrap();
            serde_json::from_str(&text).unwrap()
        };
        assert_eq!(
            read("crates/shellcheck-cli/upstream.json"),
            read("tools/oracle.json"),
            "copy the pin in tools/oracle.json to crates/shellcheck-cli/upstream.json"
        );
    }
}
