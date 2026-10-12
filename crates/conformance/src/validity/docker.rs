use std::io::Write;
use std::process::{Command, Stdio};

use super::matrix::{self, Cell};
use super::{DOCKERFILES, ValidityArgs};

pub const TIMEOUT_SECONDS: &str = "5";
const TIMEOUT_STATUS: i32 = 124;

pub fn build_all(args: &ValidityArgs) -> Result<(), String> {
    let mut matrix = matrix::load()?;
    let mut pushed = false;
    for cell in matrix.cell.iter_mut().filter(|c| c.matches(&args.cell)) {
        build(cell)?;
        if args.push {
            push(cell)?;
            pushed = true;
        }
    }
    if pushed {
        matrix::save(&matrix)?;
    }
    Ok(())
}

fn build(cell: &Cell) -> Result<(), String> {
    let mut cmd = Command::new("docker");
    cmd.args(["build", "--file"])
        .arg(format!("{DOCKERFILES}/{}/Dockerfile", cell.dockerfile))
        .args(["--tag", &cell.image])
        .arg("--build-arg")
        .arg(format!("BASE={}", cell.base))
        .arg("--build-arg")
        .arg(format!("VERSION={}", cell.version));
    for (key, value) in cell.source.build_args() {
        cmd.arg("--build-arg").arg(format!("{key}={value}"));
    }
    cmd.arg(DOCKERFILES);
    inherit(cmd, &format!("build {}", cell.id()))
}

fn push(cell: &mut Cell) -> Result<(), String> {
    let mut cmd = Command::new("docker");
    cmd.args(["push", &cell.image]);
    inherit(cmd, &format!("push {}", cell.id()))?;
    let out = Command::new("docker")
        .args([
            "image",
            "inspect",
            "--format",
            "{{index .RepoDigests 0}}",
            &cell.image,
        ])
        .output()
        .map_err(|e| format!("docker: {e}"))?;
    let text = String::from_utf8_lossy(&out.stdout);
    cell.digest = text
        .trim()
        .rsplit_once('@')
        .map(|(_, d)| d.to_string())
        .ok_or_else(|| format!("{}: no repository digest after push", cell.id()))?;
    Ok(())
}

fn inherit(mut cmd: Command, what: &str) -> Result<(), String> {
    let status = cmd.status().map_err(|e| format!("docker: {e}"))?;
    if status.success() {
        Ok(())
    } else {
        Err(format!("{what}: docker exited with {status}"))
    }
}

fn quiet(args: &[&str]) -> bool {
    Command::new("docker")
        .args(args)
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .status()
        .is_ok_and(|s| s.success())
}

pub fn available(reference: &str) -> bool {
    quiet(&["image", "inspect", reference])
        || (reference.contains("@sha256:") && quiet(&["pull", "--quiet", reference]))
}

pub struct Run {
    pub status: i32,
    pub stdout: String,
    pub stderr: String,
    pub timed_out: bool,
}

pub struct Container {
    id: String,
}

impl Container {
    pub fn start(reference: &str) -> Result<Self, String> {
        let out = Command::new("docker")
            .args([
                "run",
                "--detach",
                "--rm",
                "--network",
                "none",
                "--read-only",
                "--tmpfs",
                "/tmp:size=16m,exec",
                "--cap-drop",
                "ALL",
                "--pids-limit",
                "64",
                "--memory",
                "256m",
                "--cpus",
                "1",
                "--user",
                "65534:65534",
                "--env",
                "LC_ALL=C",
                "--env",
                "TZ=UTC",
                "--env",
                "HOME=/tmp",
                reference,
                "sleep",
                "infinity",
            ])
            .output()
            .map_err(|e| format!("docker: {e}"))?;
        if !out.status.success() {
            return Err(format!(
                "{reference}: container did not start: {}",
                String::from_utf8_lossy(&out.stderr).trim()
            ));
        }
        Ok(Self {
            id: String::from_utf8_lossy(&out.stdout).trim().to_string(),
        })
    }

    pub fn mkdir(&self, dir: &str) -> Result<(), String> {
        self.plain(&["mkdir", "-p", dir])
    }

    pub fn remove(&self, dir: &str) -> Result<(), String> {
        self.plain(&["rm", "-rf", dir])
    }

    fn plain(&self, argv: &[&str]) -> Result<(), String> {
        let status = Command::new("docker")
            .args(["exec", &self.id])
            .args(argv)
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .status()
            .map_err(|e| format!("docker: {e}"))?;
        if status.success() {
            Ok(())
        } else {
            Err(format!("container {}: {} failed", self.id, argv.join(" ")))
        }
    }

    pub fn exec(&self, dir: &str, argv: &[String], stdin: &str) -> Result<Run, String> {
        let mut child = Command::new("docker")
            .args(["exec", "--interactive", "--workdir", dir, "--env"])
            .arg(format!("TMPDIR={dir}"))
            .args([&self.id, "timeout", TIMEOUT_SECONDS])
            .args(argv)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .map_err(|e| format!("docker: {e}"))?;
        if let Some(mut input) = child.stdin.take() {
            let _ = input.write_all(stdin.as_bytes());
        }
        let out = child
            .wait_with_output()
            .map_err(|e| format!("docker: {e}"))?;
        let status = out.status.code().unwrap_or(-1);
        Ok(Run {
            status,
            stdout: String::from_utf8_lossy(&out.stdout).into_owned(),
            stderr: String::from_utf8_lossy(&out.stderr).into_owned(),
            timed_out: status == TIMEOUT_STATUS,
        })
    }

    pub fn stop(self) {
        let _ = Command::new("docker")
            .args(["rm", "--force", &self.id])
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .status();
    }
}
