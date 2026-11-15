//! Invocation-state merges must produce the same diagnostics in fresh processes.

use std::io::Write;
use std::process::{Command, Stdio};

#[test]
fn multiple_call_sites_and_nested_invocations_have_stable_output() {
    let script = b"#!/bin/bash\nf() { echo $value; }\nvalue=plain\nf\nvalue='two words'\nf\ng() { local value=42; f; }\ng\nunset value\nf\n";
    let mut expected = None;
    for _ in 0..24 {
        let mut child = Command::new(env!("CARGO_BIN_EXE_rshellcheck"))
            .env_remove("SHELLCHECK_OPTS")
            .args(["--norc", "-f", "json1", "-"])
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .unwrap();
        child.stdin.take().unwrap().write_all(script).unwrap();
        let result = child.wait_with_output().unwrap();
        assert_eq!(result.status.code(), Some(1));
        assert_eq!(result.stderr, [] as [u8; 0]);
        let diagnostics: serde_json::Value = serde_json::from_slice(&result.stdout).unwrap();
        assert!(
            diagnostics["comments"]
                .as_array()
                .unwrap()
                .iter()
                .any(|c| c["code"] == 2086)
        );
        if let Some(previous) = &expected {
            assert_eq!(&result.stdout, previous);
        } else {
            expected = Some(result.stdout);
        }
    }
}
