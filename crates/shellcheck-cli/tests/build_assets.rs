//! Release assets must be the scripts embedded by the same build.
#![cfg(feature = "completions")]

use std::path::Path;
use std::process::Command;

#[test]
fn staged_completions_match_the_binary() {
    let binary = Path::new(env!("CARGO_BIN_EXE_rshellcheck"));
    let assets = binary.with_extension("assets").join("completions");
    for (shell, name) in [
        ("bash", "rshellcheck.bash"),
        ("zsh", "_rshellcheck"),
        ("fish", "rshellcheck.fish"),
        ("powershell", "rshellcheck.ps1"),
    ] {
        let output = Command::new(binary)
            .env_remove("SHELLCHECK_OPTS")
            .args(["--generate-completions", shell])
            .output()
            .unwrap_or_else(|error| panic!("run {shell}: {error}"));
        assert!(output.status.success(), "{shell}: {:?}", output.stderr);
        let staged =
            std::fs::read(assets.join(name)).unwrap_or_else(|error| panic!("read {name}: {error}"));
        assert_eq!(staged, output.stdout, "{shell}");
    }
}
