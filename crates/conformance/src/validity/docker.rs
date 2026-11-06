use std::env;
use std::fmt::Write as _;
use std::fs::OpenOptions;
use std::io::Write;
use std::path::Path;
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
    for cell in matrix.cell.iter_mut().filter(|c| c.matches(&args.cell)) {
        build(cell, args.push)?;
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

fn build(cell: &Cell, push: bool) -> Result<(), String> {
    inherit(build_command(cell, push), &format!("build {}", cell.id()))
}

fn build_command(cell: &Cell, push: bool) -> Command {
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
    for (key, value) in labels(cell) {
        cmd.arg("--label")
            .arg(format!("org.opencontainers.image.{key}={value}"));
    }
    // Separate tags keep parallel cells from overwriting each other's cache.
    // PR builds may consume published caches but never replace trusted caches.
    let cache = format!("{}-buildcache", cell.image);
    cmd.arg("--cache-from")
        .arg(format!("type=registry,ref={cache}"));
    if push {
        cmd.arg("--cache-to")
            .arg(format!("type=registry,ref={cache},mode=max"));
        // Keep commit-specific provenance and SBOMs outside the content-addressed
        // image so rebuilding identical inputs preserves the manifest digest.
        cmd.args(["--push", "--provenance=false", "--sbom=false"]);
    } else {
        cmd.arg("--load");
    }
    cmd.arg(DOCKERFILES);
    cmd
}

fn labels(cell: &Cell) -> Vec<(&'static str, String)> {
    vec![
        ("source", SOURCE_URL.to_string()),
        ("url", SOURCE_URL.to_string()),
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
    pick(&cell.reference(), quiet)
}

fn pick(pinned: &str, probe: impl Fn(&[&str]) -> bool) -> Option<String> {
    if probe(&["image", "inspect", pinned]) {
        return Some(pinned.to_string());
    }
    if pinned.contains("@sha256:") && probe(&["pull", "--quiet", pinned]) {
        return Some(pinned.to_string());
    }
    None
}

#[derive(Clone)]
pub struct Run {
    pub status: i32,
    pub stdout: String,
    pub stderr: String,
    pub timed_out: bool,
}

pub struct Container {
    id: String,
    vm: bool,
}

const KVM: &str = "/dev/kvm";

impl Container {
    pub fn start(cell: &Cell, reference: &str) -> Result<Self, String> {
        let mut cmd = Command::new("docker");
        cmd.args([
            "run",
            "--detach",
            "--rm",
            "--network",
            "none",
            "--read-only",
            "--cap-drop",
            "ALL",
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
        ]);
        if cell.vm {
            cmd.args([
                "--tmpfs",
                "/tmp:size=1g,exec",
                "--pids-limit",
                "128",
                "--memory",
                "1g",
            ]);
            if Path::new(KVM).exists() {
                cmd.args(["--device", KVM]);
            }
            cmd.args([reference, "vmboot"]);
        } else {
            cmd.args([
                "--tmpfs",
                "/tmp:size=16m,exec",
                "--pids-limit",
                "64",
                "--memory",
                "256m",
            ]);
            cmd.args([reference, "sleep", "infinity"]);
        }
        let out = cmd.output().map_err(|e| format!("docker: {e}"))?;
        if !out.status.success() {
            return Err(format!(
                "{reference}: container did not start: {}",
                String::from_utf8_lossy(&out.stderr).trim()
            ));
        }
        let container = Self {
            id: String::from_utf8_lossy(&out.stdout).trim().to_string(),
            vm: cell.vm,
        };
        if cell.vm
            && let Err(e) = container.plain(&["true"])
        {
            container.stop();
            return Err(format!("{reference}: guest did not come up: {e}"));
        }
        Ok(container)
    }

    const fn prefix(&self) -> &'static [&'static str] {
        if self.vm { &["vmsh"] } else { &[] }
    }

    pub fn mkdir(&self, dir: &str) -> Result<(), String> {
        self.plain(&["mkdir", "-p", dir])
    }

    fn plain(&self, argv: &[&str]) -> Result<(), String> {
        let out = Command::new("docker")
            .args(["exec", &self.id])
            .args(self.prefix())
            .args(argv)
            .output()
            .map_err(|e| format!("docker: {e}"))?;
        if out.status.success() {
            Ok(())
        } else {
            Err(format!(
                "container {}: {} failed: {}",
                self.id,
                argv.join(" "),
                String::from_utf8_lossy(&out.stderr).trim()
            ))
        }
    }

    pub fn exec(&self, dir: &str, argv: &[String], stdin: &str) -> Result<Run, String> {
        let workdir = if self.vm { "/tmp" } else { dir };
        let mut child = Command::new("docker")
            .args(["exec", "--interactive", "--workdir", workdir, "--env"])
            .arg(format!("TMPDIR={dir}"))
            .args([&self.id, "timeout", TIMEOUT_SECONDS])
            .args(self.prefix())
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

    pub fn run_all(&self, dirs: &[String], requests: &[Request]) -> Result<Vec<Run>, String> {
        let script = driver(self.prefix(), self.vm, dirs, requests);
        let child = Command::new("docker")
            .args(["exec", "--interactive", &self.id, "sh", "-s"])
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .map_err(|e| format!("docker: {e}"))?;
        let out = feed(child, &script)?;
        if !out.status.success() {
            return Err(format!(
                "container {}: driver failed: {}",
                self.id,
                String::from_utf8_lossy(&out.stderr).trim()
            ));
        }
        parse_runs(&out.stdout, requests.len())
    }

    pub fn stop(self) {
        let _ = Command::new("docker")
            .args(["rm", "--force", &self.id])
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .status();
    }
}

pub struct Request {
    pub dir: String,
    pub argv: Vec<String>,
    pub stdin: String,
}

fn feed(mut child: std::process::Child, script: &str) -> Result<std::process::Output, String> {
    let mut stdin = child
        .stdin
        .take()
        .ok_or_else(|| "driver: no stdin".to_string())?;
    std::thread::scope(|scope| {
        let writer = scope.spawn(move || stdin.write_all(script.as_bytes()));
        let output = child.wait_with_output();
        writer
            .join()
            .map_err(|_| "driver: stdin writer panicked".to_string())?
            .map_err(|e| format!("driver: {e}"))?;
        output.map_err(|e| format!("driver: {e}"))
    })
}

fn quote(text: &str) -> String {
    format!("'{}'", text.replace('\'', r"'\''"))
}

fn driver(prefix: &[&str], vm: bool, dirs: &[String], requests: &[Request]) -> String {
    let prefix = prefix.iter().fold(String::new(), |mut out, part| {
        let _ = write!(out, "{} ", quote(part));
        out
    });
    let quoted_dirs: Vec<String> = dirs.iter().map(|d| quote(d)).collect();
    let quoted_dirs = quoted_dirs.join(" ");
    let mut script = String::from("in=$(mktemp -d) || exit 1\n");
    if !dirs.is_empty() {
        let _ = writeln!(
            script,
            "{prefix}mkdir -p {quoted_dirs} </dev/null || exit 1"
        );
    }
    for (i, request) in requests.iter().enumerate() {
        let workdir = if vm { "/tmp" } else { request.dir.as_str() };
        let argv: Vec<String> = request.argv.iter().map(|a| quote(a)).collect();
        let _ = writeln!(
            script,
            "printf '%s' {} > \"$in/{i}\"",
            quote(&request.stdin)
        );
        let _ = writeln!(
            script,
            "cat \"$in/{i}\" | (cd {} && TMPDIR={} exec timeout {TIMEOUT_SECONDS} {prefix}{}) > \"$in/{i}.out\" 2> \"$in/{i}.err\"",
            quote(workdir),
            quote(&request.dir),
            argv.join(" ")
        );
        let _ = writeln!(script, "status=$?");
        let _ = writeln!(
            script,
            "printf '@run {i} %s %s %s\\n' \"$status\" \"$(wc -c < \"$in/{i}.out\")\" \"$(wc -c < \"$in/{i}.err\")\""
        );
        let _ = writeln!(script, "cat \"$in/{i}.out\" \"$in/{i}.err\"");
    }
    if !dirs.is_empty() {
        let _ = writeln!(script, "{prefix}rm -rf {quoted_dirs} </dev/null || exit 1");
    }
    script.push_str("rm -rf \"$in\"\n");
    script
}

fn parse_runs(output: &[u8], count: usize) -> Result<Vec<Run>, String> {
    let mut runs = Vec::with_capacity(count);
    let mut rest = output;
    for i in 0..count {
        let end = rest
            .iter()
            .position(|&b| b == b'\n')
            .ok_or_else(|| format!("driver: no record for run {i}"))?;
        let header = String::from_utf8_lossy(&rest[..end]);
        let fields: Vec<&str> = header.split_whitespace().collect();
        let [tag, index, status, out_len, err_len] = fields[..] else {
            return Err(format!("driver: bad record header {header:?}"));
        };
        if tag != "@run" || index != i.to_string() {
            return Err(format!("driver: expected run {i}, got {header:?}"));
        }
        let number = |field: &str| {
            field
                .parse::<usize>()
                .map_err(|e| format!("driver: {header:?}: {e}"))
        };
        let status: i32 = status
            .parse()
            .map_err(|e| format!("driver: {header:?}: {e}"))?;
        let (out_len, err_len) = (number(out_len)?, number(err_len)?);
        let body = &rest[end + 1..];
        if body.len() < out_len + err_len {
            return Err(format!("driver: run {i} output is truncated"));
        }
        runs.push(Run {
            status,
            stdout: String::from_utf8_lossy(&body[..out_len]).into_owned(),
            stderr: String::from_utf8_lossy(&body[out_len..out_len + err_len]).into_owned(),
            timed_out: status == TIMEOUT_STATUS,
        });
        rest = &body[out_len + err_len..];
    }
    Ok(runs)
}

#[cfg(test)]
mod tests {
    use super::super::matrix::SourcePin;
    use super::{
        Cell, Container, Request, Run, build_command, driver, feed, in_actions, parse_runs, pick,
        write_step_output,
    };
    use std::process::{Command, Stdio};

    fn drive(prefix: &[&str], vm: bool, dirs: &[String], requests: &[Request]) -> Vec<Run> {
        let child = Command::new("sh")
            .arg("-s")
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .unwrap();
        let out = feed(child, &driver(prefix, vm, dirs, requests)).unwrap();
        assert!(
            out.status.success(),
            "{}",
            String::from_utf8_lossy(&out.stderr)
        );
        parse_runs(&out.stdout, requests.len()).unwrap()
    }

    fn scratch(name: &str) -> [String; 2] {
        let root = std::env::temp_dir().join(format!("validity-{name}-{}", std::process::id()));
        [root.join("a"), root.join("b")].map(|dir| dir.display().to_string())
    }

    fn sh(dir: &str, script: &str) -> Request {
        Request {
            dir: dir.to_string(),
            argv: vec!["sh".to_string()],
            stdin: script.to_string(),
        }
    }

    #[test]
    fn one_driver_runs_every_request_and_frames_each_output() {
        let dirs = scratch("driver");
        let runs = drive(
            &[],
            false,
            &dirs,
            &[
                sh(&dirs[0], "printf 'x\\ny'; echo oops >&2; exit 3\n"),
                sh(
                    &dirs[1],
                    "pwd; echo \"$TMPDIR\"; echo \"it's @run 9 0 0 0\"\n",
                ),
            ],
        );
        assert_eq!(runs.len(), 2);
        assert_eq!((runs[0].status, runs[0].stdout.as_str()), (3, "x\ny"));
        assert_eq!(runs[0].stderr, "oops\n");
        assert!(!runs[0].timed_out);
        assert_eq!(
            runs[1].stdout,
            format!("{0}\n{0}\nit's @run 9 0 0 0\n", dirs[1])
        );
        assert!(dirs.iter().all(|dir| !std::path::Path::new(dir).exists()));
    }

    #[test]
    fn a_guest_driver_runs_from_tmp_through_the_prefix() {
        let dirs = scratch("guest");
        let runs = drive(
            &["env"],
            true,
            &dirs,
            &[sh(&dirs[0], "pwd; echo \"$TMPDIR\"\n")],
        );
        assert_eq!(runs[0].stdout, format!("/tmp\n{}\n", dirs[0]));
        assert!(dirs.iter().all(|dir| !std::path::Path::new(dir).exists()));
    }

    #[test]
    fn records_mark_timeouts_and_reject_missing_or_short_output() {
        let runs = parse_runs(b"@run 0 124 2 0\nhi", 1).unwrap();
        assert!(runs[0].timed_out);
        assert_eq!(runs[0].stdout, "hi");
        assert!(parse_runs(b"@run 0 0 5 0\nhi", 1).is_err());
        assert!(parse_runs(b"@run 1 0 0 0\n", 1).is_err());
        assert!(parse_runs(b"", 1).is_err());
    }

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
            vm: false,
            dialect: Some("bash".to_string()),
            source: SourcePin::Tarball {
                url: "u".to_string(),
                sha256: "s".to_string(),
            },
        }
    }

    fn args(cell: &Cell, push: bool) -> Vec<String> {
        build_command(cell, push)
            .get_args()
            .map(|a| a.to_string_lossy().into_owned())
            .collect()
    }

    #[test]
    fn a_guest_container_routes_every_command_through_vmsh() {
        let guest = Container {
            id: "c".to_string(),
            vm: true,
        };
        let native = Container {
            id: "c".to_string(),
            vm: false,
        };
        assert_eq!(guest.prefix(), ["vmsh"]);
        assert_eq!(native.prefix(), [] as [&str; 0]);
    }

    #[test]
    fn push_is_reserved_for_actions() {
        assert!(in_actions(Some("true")));
        assert!(!in_actions(Some("false")));
        assert!(!in_actions(None));
    }

    #[test]
    fn a_push_build_keeps_attestations_outside_the_image() {
        let a = args(&cell(), true);
        for flag in ["--push", "--provenance=false", "--sbom=false"] {
            assert!(a.contains(&flag.to_string()), "{flag} missing from {a:?}");
        }
        assert!(!a.contains(&"--load".to_string()));
    }

    #[test]
    fn a_local_build_loads_and_never_pushes() {
        let a = args(&cell(), false);
        assert!(a.contains(&"--load".to_string()));
        assert!(!a.contains(&"--push".to_string()));
        assert!(!a.contains(&"--cache-to".to_string()));
    }

    #[test]
    fn published_builds_share_versioned_registry_cache_with_pr_builds() {
        let first = cell();
        let mut second = cell();
        second.image = "ghcr.io/x/shell-bash:4.0".to_string();
        for c in [&first, &second] {
            let import = format!("type=registry,ref={}-buildcache", c.image);
            let export = format!("{import},mode=max");
            assert!(
                args(c, false)
                    .windows(2)
                    .any(|a| a == ["--cache-from", &import])
            );
            assert!(
                args(c, true)
                    .windows(2)
                    .any(|a| a == ["--cache-to", &export])
            );
            assert!(!args(c, false).contains(&export));
        }
    }

    #[test]
    fn every_build_carries_stable_source_labels() {
        let a = args(&cell(), false);
        for label in [
            "org.opencontainers.image.source=https://github.com/kjanat/shellcheck-rs",
            "org.opencontainers.image.version=5.3",
            "org.opencontainers.image.title=shell-bash",
        ] {
            assert!(a.contains(&label.to_string()), "{label} missing from {a:?}");
        }
        assert!(
            !a.iter()
                .any(|arg| arg.starts_with("org.opencontainers.image.revision=")),
            "revision label makes identical image inputs produce different digests: {a:?}"
        );
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
        let found = pick(PINNED, |a| a == ["image", "inspect", PINNED]);
        assert_eq!(found.as_deref(), Some(PINNED));
    }

    #[test]
    fn pinned_image_is_pulled_before_the_tag_is_tried() {
        let found = pick(PINNED, |a| a == ["pull", "--quiet", PINNED]);
        assert_eq!(found.as_deref(), Some(PINNED));
    }

    #[test]
    fn an_unreachable_digest_is_never_replaced_by_the_tag() {
        let found = pick(PINNED, |a| a == ["image", "inspect", TAG]);
        assert_eq!(found, None);
    }

    #[test]
    fn unpinned_cell_never_pulls() {
        let found = pick(TAG, |a| a[0] == "pull");
        assert_eq!(found, None);
    }

    #[test]
    fn nothing_available_is_none() {
        assert_eq!(pick(PINNED, |_| false), None);
    }
}
