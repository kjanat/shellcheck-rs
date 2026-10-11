//! File workers must preserve ordered diagnostics, configuration and stream behavior.
use std::io::Write;
use std::path::PathBuf;
use std::process::{Command, Output, Stdio};
use std::sync::atomic::{AtomicU64, Ordering};

static NEXT: AtomicU64 = AtomicU64::new(0);
struct Fixture(PathBuf);
impl Fixture {
    fn new() -> Self {
        let path = std::env::temp_dir().join(format!(
            "shellcheck-parallel-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        std::fs::create_dir(&path).unwrap();
        Self(path)
    }
    fn write(&self, name: &str, text: &str) {
        std::fs::write(self.0.join(name), text).unwrap();
    }
    fn run(&self, jobs: &str, args: &[&str], stdin: &str) -> Output {
        let mut child = Command::new(env!("CARGO_BIN_EXE_rshellcheck"))
            .current_dir(&self.0)
            .env_remove("SHELLCHECK_OPTS")
            .args(["--jobs", jobs])
            .args(args)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .unwrap();
        child
            .stdin
            .take()
            .unwrap()
            .write_all(stdin.as_bytes())
            .unwrap();
        child.wait_with_output().unwrap()
    }
    fn compare(&self, args: &[&str], stdin: &str) -> Output {
        let serial = self.run("1", args, stdin);
        let parallel = self.run("4", args, stdin);
        assert_eq!(serial.status, parallel.status, "{args:?}");
        assert_eq!(serial.stdout, parallel.stdout, "{args:?}");
        assert_eq!(serial.stderr, parallel.stderr, "{args:?}");
        serial
    }
}
impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

#[test]
fn workers_preserve_all_formats_and_cross_file_sources() {
    let f = Fixture::new();
    f.write("a.sh", "#!/bin/bash\nsource lib.sh\necho $a\n");
    f.write("b.sh", "#!/bin/bash\necho `date`\n");
    f.write("lib.sh", "#!/bin/bash\necho $library\n");
    for format in ["gcc", "json", "json1", "checkstyle", "diff", "tty", "quiet"] {
        let result = f.compare(
            &[
                "--norc",
                "-a",
                "-P",
                "SCRIPTDIR",
                "-f",
                format,
                "a.sh",
                "b.sh",
                "lib.sh",
                "a.sh",
            ],
            "",
        );
        assert_eq!(result.status.code(), Some(1));
        if format == "gcc" {
            assert!(!String::from_utf8_lossy(&result.stdout).contains("SC1091"));
        }
    }
}

#[test]
fn worker_configuration_is_resolved_once_in_input_order() {
    let f = Fixture::new();
    f.write("a.sh", "#!/bin/bash\necho $a\n");
    f.write("b.sh", "#!/bin/bash\necho $b\n");
    let output = f.compare(&["--rcfile", "missing.rc", "-f", "gcc", "a.sh", "b.sh"], "");
    assert_eq!(
        String::from_utf8_lossy(&output.stderr)
            .matches("Warning: unable to read")
            .count(),
        1
    );
    f.write("config.rc", "disable=SC2086\n");
    f.write(
        ".editorconfig",
        "root = true\n[*.sh]\nshellcheck.disable = SC2154\n",
    );
    let output = f.compare(
        &["--rcfile", "config.rc", "-f", "json1", "a.sh", "b.sh"],
        "",
    );
    assert_eq!(output.status.code(), Some(0));
}

#[test]
fn streams_missing_files_and_empty_work_are_handled() {
    let f = Fixture::new();
    f.write("a.sh", "#!/bin/bash\necho $a\n");
    assert_eq!(
        f.compare(
            &["--norc", "-f", "gcc", "a.sh", "-", "-"],
            "#!/bin/bash\necho $stdin\n"
        )
        .status
        .code(),
        Some(1)
    );
    assert_eq!(
        f.compare(&["--norc", "-f", "gcc", "missing.sh", "a.sh"], "")
            .status
            .code(),
        Some(2)
    );
    f.write("empty", "");
    assert_eq!(
        f.compare(&["--files-from", "empty"], "").status.code(),
        Some(0)
    );
}

#[test]
fn quiet_workers_do_not_read_stdin_after_a_finding() {
    let f = Fixture::new();
    f.write("bad.sh", "#!/bin/bash\necho $bad\n");
    let mut child = Command::new(env!("CARGO_BIN_EXE_rshellcheck"))
        .current_dir(&f.0)
        .env_remove("SHELLCHECK_OPTS")
        .args(["--jobs", "4", "--norc", "-f", "quiet", "bad.sh", "-"])
        .stdin(Stdio::piped())
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .spawn()
        .unwrap();
    // Keep stdin open: reading it would block. Bound the test and reap on failure.
    let deadline = std::time::Instant::now() + std::time::Duration::from_secs(5);
    loop {
        if let Some(status) = child.try_wait().unwrap() {
            assert_eq!(status.code(), Some(1));
            break;
        }
        if std::time::Instant::now() >= deadline {
            child.kill().unwrap();
            child.wait().unwrap();
            panic!("quiet mode read later stdin");
        }
        std::thread::sleep(std::time::Duration::from_millis(10));
    }
}

#[test]
fn worker_count_must_be_positive() {
    let f = Fixture::new();
    for value in ["0", "-1", "no", "99999999999999999999999999"] {
        assert_eq!(f.run(value, &["--norc", "-"], "").status.code(), Some(3));
    }
}
