use std::env;
use std::fs::OpenOptions;
use std::io::Write;
use std::process::{Command, Stdio};

use super::matrix::{self, Cell};
use super::{DOCKERFILES, SOURCE_URL, ValidityArgs, pin};

pub const TIMEOUT_SECONDS: &str = "5";
const TIMEOUT_STATUS: i32 = 124;

pub fn build_all(args: &ValidityArgs) -> Result<(), String> {
    if args.push && !in_actions(env::var("GITHUB_ACTIONS").ok().as_deref()) {
        return Err("--push publishes only from shells.yml".to_string());
    }
    let mut matrix = matrix::load()?;
    let revision = revision()?;
    for cell in matrix.cell.iter_mut().filter(|c| c.matches(&args.cell)) {
        build(cell, &revision, args.push)?;
        if args.push {
            cell.digest = pin::manifest_digest(&cell.image)
                .ok_or_else(|| format!("{}: no manifest digest after push", cell.id()))?;
            step_output(cell)?;
        }
    }
    if args.push {
        matrix::save(&matrix)?;
    }
    Ok(())
}

fn in_actions(github_actions: Option<&str>) -> bool {
    github_actions == Some("true")
}

fn build(cell: &Cell, revision: &str, push: bool) -> Result<(), String> {
    inherit(
        build_command(cell, revision, push),
        &format!("build {}", cell.id()),
    )
}

fn build_command(cell: &Cell, revision: &str, push: bool) -> Command {
    let mut cmd = Command::new("docker");
    cmd.args(["buildx", "build", "--file"])
        .arg(format!("{DOCKERFILES}/{}/Dockerfile", cell.dockerfile))
        .args(["--tag", &cell.image])
        .arg("--build-arg")
        .arg(format!("BASE={}", cell.base))
        .arg("--build-arg")
        .arg(format!("VERSION={}", cell.version));
    for (key, value) in cell.source.build_args() {
        cmd.arg("--build-arg").arg(format!("{key}={value}"));
    }
    for (key, value) in labels(cell, revision) {
        cmd.arg("--label")
            .arg(format!("org.opencontainers.image.{key}={value}"));
    }
    if push {
        cmd.args(["--push", "--provenance=mode=max", "--sbom=true"]);
    } else {
        cmd.arg("--load");
    }
    cmd.arg(DOCKERFILES);
    cmd
}

fn labels(cell: &Cell, revision: &str) -> Vec<(&'static str, String)> {
    vec![
        ("source", SOURCE_URL.to_string()),
        ("url", SOURCE_URL.to_string()),
        ("revision", revision.to_string()),
        ("version", cell.version.clone()),
        ("title", format!("shell-{}", cell.dockerfile)),
        (
            "description",
            format!(
                "{} {} for the validity matrix",
                cell.dockerfile, cell.version
            ),
        ),
    ]
}

fn revision() -> Result<String, String> {
    let out = Command::new("git")
        .args(["rev-parse", "HEAD"])
        .output()
        .map_err(|e| format!("git: {e}"))?;
    if !out.status.success() {
        return Err("git rev-parse HEAD failed".to_string());
    }
    Ok(String::from_utf8_lossy(&out.stdout).trim().to_string())
}

fn step_output(cell: &Cell) -> Result<(), String> {
    env::var("GITHUB_OUTPUT").map_or(Ok(()), |path| write_step_output(&path, cell))
}

fn write_step_output(path: &str, cell: &Cell) -> Result<(), String> {
    let repository = cell
        .image
        .rsplit_once(':')
        .map_or(cell.image.as_str(), |(r, _)| r);
    let mut file = OpenOptions::new()
        .append(true)
        .open(path)
        .map_err(|e| format!("{path}: {e}"))?;
    writeln!(file, "repository={repository}\ndigest={}", cell.digest)
        .map_err(|e| format!("{path}: {e}"))
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

pub fn locate(cell: &Cell) -> Option<String> {
    pick(&cell.reference(), &cell.image, quiet)
}

fn pick(pinned: &str, tag: &str, probe: impl Fn(&[&str]) -> bool) -> Option<String> {
    if probe(&["image", "inspect", pinned]) {
        return Some(pinned.to_string());
    }
    if pinned.contains("@sha256:") && probe(&["pull", "--quiet", pinned]) {
        return Some(pinned.to_string());
    }
    if pinned != tag && probe(&["image", "inspect", tag]) {
        return Some(tag.to_string());
    }
    None
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

#[cfg(test)]
mod tests {
    use super::super::matrix::SourcePin;
    use super::{Cell, build_command, in_actions, pick, write_step_output};

    const PINNED: &str = "ghcr.io/x/shell-bash@sha256:abc";
    const TAG: &str = "ghcr.io/x/shell-bash:5.3";

    fn cell() -> Cell {
        Cell {
            shell: "bash".to_string(),
            version: "5.3".to_string(),
            image: TAG.to_string(),
            digest: "sha256:abc".to_string(),
            base: "debian@sha256:0".to_string(),
            dockerfile: "bash".to_string(),
            argv: vec!["bash".to_string()],
            parse: vec!["-n".to_string()],
            shipped: true,
            dialect: Some("bash".to_string()),
            source: SourcePin::Tarball {
                url: "u".to_string(),
                sha256: "s".to_string(),
            },
        }
    }

    fn args(cell: &Cell, push: bool) -> Vec<String> {
        build_command(cell, "deadbeef", push)
            .get_args()
            .map(|a| a.to_string_lossy().into_owned())
            .collect()
    }

    #[test]
    fn push_is_reserved_for_actions() {
        assert!(in_actions(Some("true")));
        assert!(!in_actions(Some("false")));
        assert!(!in_actions(None));
    }

    #[test]
    fn a_push_build_attaches_provenance_and_sbom() {
        let a = args(&cell(), true);
        for flag in ["--push", "--provenance=mode=max", "--sbom=true"] {
            assert!(a.contains(&flag.to_string()), "{flag} missing from {a:?}");
        }
        assert!(!a.contains(&"--load".to_string()));
    }

    #[test]
    fn a_local_build_loads_and_never_pushes() {
        let a = args(&cell(), false);
        assert!(a.contains(&"--load".to_string()));
        assert!(!a.contains(&"--push".to_string()));
    }

    #[test]
    fn every_build_carries_source_and_revision_labels() {
        let a = args(&cell(), false);
        for label in [
            "org.opencontainers.image.source=https://github.com/kjanat/shellcheck-rs",
            "org.opencontainers.image.revision=deadbeef",
            "org.opencontainers.image.version=5.3",
            "org.opencontainers.image.title=shell-bash",
        ] {
            assert!(a.contains(&label.to_string()), "{label} missing from {a:?}");
        }
    }

    #[test]
    fn step_output_names_repository_and_digest() {
        let path =
            std::env::temp_dir().join(format!("validity-step-output-{}", std::process::id()));
        std::fs::write(&path, "").unwrap();
        write_step_output(path.to_str().unwrap(), &cell()).unwrap();
        let text = std::fs::read_to_string(&path).unwrap();
        std::fs::remove_file(&path).unwrap();
        assert_eq!(text, "repository=ghcr.io/x/shell-bash\ndigest=sha256:abc\n");
    }

    #[test]
    fn pinned_image_present_locally_wins() {
        let found = pick(PINNED, TAG, |a| a == ["image", "inspect", PINNED]);
        assert_eq!(found.as_deref(), Some(PINNED));
    }

    #[test]
    fn pinned_image_is_pulled_before_the_tag_is_tried() {
        let found = pick(PINNED, TAG, |a| a == ["pull", "--quiet", PINNED]);
        assert_eq!(found.as_deref(), Some(PINNED));
    }

    #[test]
    fn local_tag_serves_when_the_digest_is_unreachable() {
        let found = pick(PINNED, TAG, |a| a == ["image", "inspect", TAG]);
        assert_eq!(found.as_deref(), Some(TAG));
    }

    #[test]
    fn unpinned_cell_never_pulls() {
        let found = pick(TAG, TAG, |a| a[0] == "pull");
        assert_eq!(found, None);
    }

    #[test]
    fn nothing_available_is_none() {
        assert_eq!(pick(PINNED, TAG, |_| false), None);
    }
}
