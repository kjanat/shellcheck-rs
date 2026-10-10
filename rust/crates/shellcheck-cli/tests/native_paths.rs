//! Native filename identities must survive CLI parsing and formatter re-reads.
#![cfg(unix)]

use std::ffi::OsString;
use std::os::unix::ffi::OsStringExt;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::atomic::{AtomicU64, Ordering};

static NEXT: AtomicU64 = AtomicU64::new(0);

struct Fixture(PathBuf);

impl Fixture {
    fn new() -> Self {
        let dir = std::env::temp_dir().join(format!(
            "shellcheck-native-paths-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        std::fs::create_dir(&dir).unwrap_or_else(|e| panic!("create fixture: {e}"));
        Self(dir)
    }

    fn file(&self, name: &[u8], script: &str) -> PathBuf {
        let path = self.0.join(OsString::from_vec(name.to_vec()));
        std::fs::write(&path, script).unwrap_or_else(|e| panic!("write fixture: {e}"));
        path
    }
}

impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

fn run(format: &str, files: &[&Path]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_rshellcheck"))
        .env_remove("SHELLCHECK_OPTS")
        .args(["--norc", "--format", format, "--"])
        .args(files)
        .output()
        .unwrap_or_else(|e| panic!("run CLI: {e}"))
}

#[test]
fn colliding_display_names_cannot_hide_findings_in_either_order() {
    let fixture = Fixture::new();
    let bad = fixture.file(
        b"input-\xfe.sh",
        "#!/bin/bash\necho \"$undefined_variable\"\n",
    );
    let clean = fixture.file(b"input-\xff.sh", "#!/bin/bash\necho clean\n");
    let replacement = fixture.file("input-\u{fffd}.sh".as_bytes(), "#!/bin/bash\necho clean\n");
    assert_eq!(bad.to_string_lossy(), clean.to_string_lossy());
    for files in [
        vec![bad.as_path(), clean.as_path(), replacement.as_path()],
        vec![replacement.as_path(), clean.as_path(), bad.as_path()],
    ] {
        assert_eq!(run("quiet", &files).status.code(), Some(1));
    }
}

#[test]
fn colliding_inputs_keep_their_own_content_and_diagnostics_in_every_formatter() {
    let fixture = Fixture::new();
    let first = fixture.file(b"input-\xfe.sh", "#!/bin/bash\n\techo $first\n");
    let second = fixture.file(b"input-\xff.sh", "#!/bin/bash\necho $second\n");
    for format in ["gcc", "tty", "diff", "checkstyle", "json", "json1"] {
        let together = run(format, &[&first, &second]);
        assert_eq!(together.status.code(), Some(1), "{format}");
        let text = String::from_utf8(together.stdout.clone()).unwrap();
        let (first_text, second_text) = if format == "diff" {
            ("first", "second")
        } else {
            ("first is referenced", "second is referenced")
        };
        assert!(text.contains(first_text), "{format}: {text}");
        assert!(text.contains(second_text), "{format}: {text}");
        if format == "gcc" {
            let mut expected = run(format, &[&first]).stdout;
            expected.extend(run(format, &[&second]).stdout);
            assert_eq!(together.stdout, expected);
        }
        if format == "json1" {
            let one: serde_json::Value =
                serde_json::from_slice(&run(format, &[&first]).stdout).unwrap();
            let two: serde_json::Value =
                serde_json::from_slice(&run(format, &[&second]).stdout).unwrap();
            let combined: serde_json::Value = serde_json::from_slice(&together.stdout).unwrap();
            let mut expected = two["comments"].as_array().unwrap().clone();
            expected.extend(one["comments"].as_array().unwrap().iter().cloned());
            assert_eq!(combined["comments"], serde_json::json!(expected));
        }
    }
}

#[test]
fn a_missing_native_input_is_not_replaced_with_a_colliding_existing_file() {
    let fixture = Fixture::new();
    let clean = fixture.file(b"input-\xff.sh", "#!/bin/bash\necho clean\n");
    let missing = fixture
        .0
        .join(OsString::from_vec(b"input-\xfe.sh".to_vec()));
    assert_eq!(run("gcc", &[&missing, &clean]).status.code(), Some(2));
    assert_eq!(run("quiet", &[&missing, &clean]).status.code(), Some(1));
}

#[test]
fn a_native_directory_survives_scriptdir_source_resolution() {
    let fixture = Fixture::new();
    let dir = fixture
        .0
        .join(OsString::from_vec(b"directory-\xfe".to_vec()));
    std::fs::create_dir(&dir).unwrap();
    let main = dir.join("main.sh");
    let lib = dir.join("lib.sh");
    std::fs::write(&main, "#!/bin/bash\nsource lib.sh\n").unwrap();
    std::fs::write(&lib, "#!/bin/bash\necho \"$undefined_variable\"\n").unwrap();
    let result = Command::new(env!("CARGO_BIN_EXE_rshellcheck"))
        .env_remove("SHELLCHECK_OPTS")
        .args(["--norc", "-a", "-P", "SCRIPTDIR", "-f", "gcc"])
        .args([&main, &lib])
        .output()
        .unwrap();
    let output = String::from_utf8(result.stdout).unwrap();
    assert!(output.contains("SC2154"), "{output}");
    assert!(!output.contains("SC1091"), "{output}");
}
