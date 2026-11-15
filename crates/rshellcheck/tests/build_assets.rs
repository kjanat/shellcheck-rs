//! Release assets must be the scripts embedded by the same build.
#![cfg(feature = "completions")]

use std::path::Path;
use std::process::Command;

#[test]
fn staged_completions_match_the_binary() {
    let binary = Path::new(env!("CARGO_BIN_EXE_rshellcheck"));
    let shells = [
        ("bash", "rshellcheck.bash"),
        ("zsh", "_rshellcheck"),
        ("fish", "rshellcheck.fish"),
        ("powershell", "rshellcheck.ps1"),
    ];
    let assets: std::collections::BTreeMap<String, String> = serde_json::from_str(include_str!(
        concat!(env!("OUT_DIR"), "/release-assets.json")
    ))
    .unwrap_or_else(|error| panic!("read asset bundle: {error}"));
    assert_eq!(assets.len(), shells.len());
    for (shell, name) in shells {
        let output = Command::new(binary)
            .env_remove("SHELLCHECK_OPTS")
            .args(["--completions", shell])
            .output()
            .unwrap_or_else(|error| panic!("run {shell}: {error}"));
        assert!(output.status.success(), "{shell}: {:?}", output.stderr);
        let staged = assets
            .get(&format!("completions/{name}"))
            .expect("generated asset");
        assert_eq!(staged.as_bytes(), output.stdout, "{shell}");
    }
}
