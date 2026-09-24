use std::fs::{self, File};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

use anyhow::{Context, Result, bail};
use serde::Serialize;
use serde_json::Value;

#[derive(Debug, Serialize)]
pub struct Output {
    pub exit: Option<i32>,
    pub timed_out: bool,
    pub stdout: String,
    pub stderr: String,
}

/// Same non-cryptographic FNV-1a identity used by rust-port's oracle runner.
pub fn fingerprint(binary: &Path) -> Result<String> {
    let bytes = fs::read(binary)?;
    let mut hash: u64 = 0xcbf2_9ce4_8422_2325;
    for byte in &bytes {
        hash ^= u64::from(*byte);
        hash = hash.wrapping_mul(0x0000_0100_0000_01b3);
    }
    Ok(format!("{hash:016x} ({} bytes)", bytes.len()))
}

/// Files rather than unread pipes prevent a verbose child from deadlocking.
pub fn capture(
    binary: &Path,
    args: &[String],
    dir: &Path,
    label: &str,
    timeout: Duration,
) -> Result<Output> {
    let stdout = dir.join(format!("{label}.stdout"));
    let stderr = dir.join(format!("{label}.stderr"));
    let mut child = Command::new(binary)
        .args(args)
        .env_remove("SHELLCHECK_OPTS")
        .env("LC_ALL", "C")
        .env("TERM", "dumb")
        .stdin(Stdio::null())
        .stdout(File::create(&stdout)?)
        .stderr(File::create(&stderr)?)
        .spawn()
        .with_context(|| format!("starting {}", binary.display()))?;
    let start = Instant::now();
    let (status, timed_out) = loop {
        if let Some(status) = child.try_wait()? {
            break (status, false);
        }
        if start.elapsed() >= timeout {
            child.kill().context("killing timed-out checker")?;
            break (child.wait()?, true);
        }
        std::thread::sleep(Duration::from_millis(2));
    };
    Ok(Output {
        exit: status.code(),
        timed_out,
        stdout: fs::read_to_string(stdout).context("checker stdout is not UTF-8")?,
        stderr: fs::read_to_string(stderr).context("checker stderr is not UTF-8")?,
    })
}

fn diagnostics(out: &Output) -> Result<Value> {
    if out.timed_out || !matches!(out.exit, Some(0 | 1)) {
        bail!(
            "checker failed: exit {:?}, timeout {}",
            out.exit,
            out.timed_out
        );
    }
    let value: Value = serde_json::from_str(&out.stdout).context("invalid json1")?;
    if !value.get("comments").is_some_and(Value::is_array) {
        bail!("json1 has no comments array");
    }
    Ok(value)
}

/// Preserve diagnostic order, spans, fixes and all JSON fields. A crash or
/// invalid output is an error even when both binaries fail identically.
pub fn agrees(oracle: &Output, candidate: &Output) -> Result<bool> {
    let expected = diagnostics(oracle).context("oracle")?;
    let actual = diagnostics(candidate).context("candidate")?;
    Ok(expected == actual && oracle.exit == candidate.exit && oracle.stderr == candidate.stderr)
}

pub struct Pair {
    pub oracle: PathBuf,
    pub candidate: PathBuf,
    pub dir: PathBuf,
    pub timeout: Duration,
}

impl Pair {
    pub fn check(
        &self,
        script: &str,
        shell: Option<&str>,
        enable: Option<&str>,
    ) -> Result<(Output, Output)> {
        let path = self.dir.join("input");
        fs::write(&path, script)?;
        let mut args = vec!["--norc".into(), "--format=json1".into()];
        if let Some(shell) = shell {
            args.push(format!("--shell={shell}"));
        }
        if let Some(enable) = enable {
            args.push(format!("--enable={enable}"));
        }
        args.push(path.to_string_lossy().into_owned());
        Ok((
            capture(&self.oracle, &args, &self.dir, "oracle", self.timeout)?,
            capture(&self.candidate, &args, &self.dir, "candidate", self.timeout)?,
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn output(value: Value) -> Output {
        Output {
            exit: Some(1),
            timed_out: false,
            stdout: value.to_string(),
            stderr: String::new(),
        }
    }
    #[test]
    fn compares_order_fixes_and_exit_status() {
        let a = serde_json::json!({"comments":[{"code":1,"fix":{"replacement":"a"}},{"code":2}]});
        assert!(agrees(&output(a.clone()), &output(a.clone())).unwrap());
        let mut b = a.clone();
        b["comments"].as_array_mut().unwrap().reverse();
        assert!(!agrees(&output(a.clone()), &output(b)).unwrap());
        let mut b = a.clone();
        b["comments"][0]["fix"]["replacement"] = "b".into();
        assert!(!agrees(&output(a.clone()), &output(b)).unwrap());
        let mut b = output(a.clone());
        b.exit = Some(0);
        assert!(!agrees(&output(a), &b).unwrap());
    }
    #[test]
    fn failures_cannot_be_green() {
        let mut o = output(serde_json::json!({"comments":[]}));
        o.timed_out = true;
        assert!(agrees(&o, &o).is_err());
        o.timed_out = false;
        o.exit = None;
        assert!(agrees(&o, &o).is_err());
        o.exit = Some(2);
        assert!(agrees(&o, &o).is_err());
        o.exit = Some(0);
        o.stdout = "{}".into();
        assert!(agrees(&o, &o).is_err());
        o.stdout = "not json".into();
        assert!(agrees(&o, &o).is_err());
    }

    #[cfg(unix)]
    #[test]
    fn subprocess_exit_and_timeout_are_observed() {
        let root = crate::checkout()
            .expect("the ShellCheck checkout")
            .join("compiler/conformance");
        fs::create_dir_all(&root).unwrap();
        let dir = root.join(format!("test-{}", std::process::id()));
        fs::create_dir(&dir).unwrap();
        let out = capture(
            Path::new("/bin/sh"),
            &["-c".into(), "printf '{\"comments\":[]}'; exit 1".into()],
            &dir,
            "normal",
            Duration::from_secs(2),
        )
        .unwrap();
        assert_eq!(out.exit, Some(1));
        assert!(agrees(&out, &out).unwrap());
        let out = capture(
            Path::new("/bin/sleep"),
            &["2".into()],
            &dir,
            "timeout",
            Duration::from_millis(20),
        )
        .unwrap();
        assert!(out.timed_out);
        assert!(agrees(&out, &out).is_err());
        fs::remove_dir_all(&dir).unwrap();
    }
}
