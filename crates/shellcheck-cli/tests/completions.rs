//! Loads the script `--generate-completions` prints into each shell and asks
//! that shell to complete `rshellcheck` command lines.
#![cfg(all(unix, feature = "completions"))]

use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::atomic::{AtomicU64, Ordering};

static NEXT: AtomicU64 = AtomicU64::new(0);

/// A directory holding `my script.sh`, `other.sh`, `-dash.sh` and `subdir/`.
struct Fixture(PathBuf);

impl Fixture {
    fn new() -> Self {
        let dir = std::env::temp_dir().join(format!(
            "shellcheck-completions-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        std::fs::create_dir(&dir).unwrap_or_else(|e| panic!("create fixture: {e}"));
        for name in ["my script.sh", "other.sh", "-dash.sh"] {
            std::fs::write(dir.join(name), "").unwrap_or_else(|e| panic!("write fixture: {e}"));
        }
        std::fs::create_dir(dir.join("subdir")).unwrap_or_else(|e| panic!("create fixture: {e}"));
        Self(dir)
    }
}

impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

/// Whether `program` can run. A missing shell skips its test on a developer
/// machine and fails it in CI.
fn installed(program: &str) -> bool {
    let found = Command::new(program)
        .arg("--version")
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .status()
        .is_ok();
    if !found {
        assert!(
            std::env::var_os("CI").is_none(),
            "{program} is not installed"
        );
        eprintln!("skipped: {program} is not installed");
    }
    found
}

fn script(shell: &str) -> String {
    let output = Command::new(env!("CARGO_BIN_EXE_rshellcheck"))
        .env_remove("SHELLCHECK_OPTS")
        .args(["--generate-completions", shell])
        .output()
        .unwrap_or_else(|e| panic!("run CLI: {e}"));
    assert!(output.status.success());
    assert_eq!(String::from_utf8_lossy(&output.stderr), "");
    String::from_utf8(output.stdout).unwrap_or_else(|e| panic!("{shell} script: {e}"))
}

fn run(dir: &Path, program: &str, args: &[&str], stdin: &str) -> String {
    let mut child = Command::new(program)
        .current_dir(dir)
        .args(args)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap_or_else(|e| panic!("start {program}: {e}"));
    child
        .stdin
        .take()
        .unwrap_or_else(|| panic!("{program} stdin"))
        .write_all(stdin.as_bytes())
        .unwrap_or_else(|e| panic!("write {program} stdin: {e}"));
    let output = child
        .wait_with_output()
        .unwrap_or_else(|e| panic!("wait for {program}: {e}"));
    assert!(
        output.status.success(),
        "{program} failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    String::from_utf8(output.stdout).unwrap_or_else(|e| panic!("{program} output: {e}"))
}

fn quote(word: &str) -> String {
    format!("'{}'", word.replace('\'', "'\\''"))
}

/// The words after `rshellcheck`, the last one being completed, and the
/// candidates every shell offers for it, sorted.
const CASES: &[(&[&str], &[&str])] = &[
    (&["--fo"], &["--format"]),
    (&["--generate"], &["--generate-completions"]),
    (&["--format", "j"], &["json", "json1"]),
    (&["--format=g"], &["--format=gcc"]),
    (&["-fj"], &["-fjson", "-fjson1"]),
    (&["-xs", "z"], &["zsh"]),
    (&["-S", ""], &["error", "info", "style", "warning"]),
    (
        &["--generate-completions", ""],
        &["bash", "fish", "powershell", "zsh"],
    ),
    (&["--extended-analysis", ""], &["false", "true"]),
    (&["my"], &["my script.sh"]),
    (&["--color", "my"], &["my script.sh"]),
    (&["-x", "--norc", "oth"], &["other.sh"]),
    (&["--rcfile", "my"], &["my script.sh"]),
    (&["--files-from=oth"], &["--files-from=other.sh"]),
    (&["--", "oth"], &["other.sh"]),
    (&["-j", ""], &[]),
    (&["--include", ""], &[]),
];

/// One candidate per line, without a description column, quoting, `./` or a
/// directory's trailing slash.
fn candidates(section: &str) -> Vec<String> {
    let mut found: Vec<String> = section
        .lines()
        .filter(|line| !line.is_empty())
        .map(|line| {
            let text = line.split('\t').next().unwrap_or(line);
            let text = text.trim_matches('\'').replace("=./", "=");
            let text = text.strip_prefix("./").unwrap_or(&text);
            text.strip_suffix('/').unwrap_or(text).to_string()
        })
        .collect();
    found.sort();
    found
}

fn assert_cases(shell: &str, output: &str) {
    let sections: Vec<&str> = output.split("==CASE\n").skip(1).collect();
    assert_eq!(sections.len(), CASES.len(), "{shell}: {output}");
    for ((words, expected), section) in CASES.iter().zip(sections) {
        assert_eq!(candidates(section), *expected, "{shell} {words:?}");
    }
}

fn bash_probe(script: &str, cases: &[&[&str]]) -> String {
    let mut probe = script.to_string();
    for words in cases {
        let argv: Vec<String> = words.iter().map(|word| quote(word)).collect();
        let _ = std::fmt::Write::write_fmt(
            &mut probe,
            format_args!(
                "\necho '==CASE'; COMP_WORDBREAKS=' '; COMP_WORDS=(rshellcheck {}); COMP_CWORD={}; COMPREPLY=(); _rshellcheck_complete; printf '%s\\n' \"${{COMPREPLY[@]}}\"\n",
                argv.join(" "),
                words.len()
            ),
        );
    }
    probe
}

#[test]
fn bash_completes_options_values_and_files() {
    if !installed("bash") {
        return;
    }
    let fixture = Fixture::new();
    let script = script("bash");
    let cases: Vec<&[&str]> = CASES.iter().map(|(words, _)| *words).collect();
    let output = run(
        &fixture.0,
        "bash",
        &["--noprofile", "--norc"],
        &bash_probe(&script, &cases),
    );
    assert_cases("bash", &output);
}

#[test]
fn bash_completes_lists_and_names_after_the_separator() {
    if !installed("bash") {
        return;
    }
    let fixture = Fixture::new();
    let output = run(
        &fixture.0,
        "bash",
        &["--noprofile", "--norc"],
        &bash_probe(
            &script("bash"),
            &[
                &["-o", "add-default-case,dep"],
                &["--enable=all,use"],
                &["-P", ".:sub"],
                &["--", "-d"],
                &["--", "--fo"],
            ],
        ),
    );
    let sections: Vec<Vec<String>> = output.split("==CASE\n").skip(1).map(candidates).collect();
    assert_eq!(
        sections,
        [
            vec!["add-default-case,deprecate-which"],
            vec!["--enable=all,useless-use-of-cat"],
            vec![".:subdir"],
            vec!["-dash.sh"],
            vec![],
        ]
    );
}

#[test]
fn fish_completes_options_values_and_files() {
    if !installed("fish") {
        return;
    }
    let fixture = Fixture::new();
    let mut probe = script("fish");
    for (words, _) in CASES {
        let line = format!("rshellcheck {}", words.join(" "));
        let _ = std::fmt::Write::write_fmt(
            &mut probe,
            format_args!("\necho '==CASE'; complete -C {}\n", quote(&line)),
        );
    }
    let output = run(&fixture.0, "fish", &["--no-config"], &probe);
    assert_cases("fish", &output);
}

#[test]
fn fish_completes_lists_and_names_after_the_separator() {
    if !installed("fish") {
        return;
    }
    let fixture = Fixture::new();
    let mut probe = script("fish");
    for line in [
        "rshellcheck -o add-default-case,dep",
        "rshellcheck --enable=all,use",
        "rshellcheck -P .:sub",
        "rshellcheck -- -d",
    ] {
        let _ = std::fmt::Write::write_fmt(
            &mut probe,
            format_args!("\necho '==CASE'; complete -C {}\n", quote(line)),
        );
    }
    let output = run(&fixture.0, "fish", &["--no-config"], &probe);
    let sections: Vec<Vec<String>> = output.split("==CASE\n").skip(1).map(candidates).collect();
    assert_eq!(
        sections,
        [
            vec!["add-default-case,deprecate-which"],
            vec!["--enable=all,useless-use-of-cat"],
            vec![".:subdir"],
            vec!["-dash.sh"],
        ]
    );
}

#[test]
fn powershell_completes_options_values_and_files() {
    if !installed("pwsh") {
        return;
    }
    let fixture = Fixture::new();
    let mut probe = format!("$ErrorActionPreference = 'Stop'\n{}", script("powershell"));
    for (words, _) in CASES {
        let line = format!("rshellcheck {}", words.join(" ")).replace('\'', "''");
        let _ = std::fmt::Write::write_fmt(
            &mut probe,
            format_args!(
                "\n'==CASE'; $t='{line}'; [System.Management.Automation.CommandCompletion]::CompleteInput($t,$t.Length,$null).CompletionMatches | ForEach-Object CompletionText\n"
            ),
        );
    }
    // `-Command -` reads stdin through a reader that can emit terminal control
    // sequences, so the probe is the argument.
    let output = run(
        &fixture.0,
        "pwsh",
        &[
            "-NoLogo",
            "-NoProfile",
            "-NonInteractive",
            "-Command",
            &probe,
        ],
        "",
    );
    assert_cases("powershell", &output);
}

/// Zsh's completion widgets need a terminal, so `compadd`, `compset` and
/// `_files` print what the script asks of them.
#[test]
fn zsh_asks_for_options_values_and_files() {
    if !installed("zsh") {
        return;
    }
    let fixture = Fixture::new();
    run(&fixture.0, "zsh", &["-n"], &script("zsh"));
    let cases: &[(&[&str], &str)] = &[
        (&["--fo"], "<--format>"),
        (
            &["--format", "j"],
            "<checkstyle> <diff> <gcc> <json> <json1> <quiet> <tty> \n",
        ),
        (&["--format=g"], "compset -P --format=\n<checkstyle>"),
        (&["-fj"], "compset -P -f\n<checkstyle>"),
        (&["-xs", "z"], "<sh> <bash> <dash> <ksh> <busybox> <zsh>"),
        (
            &["-o", "add-default-case,dep"],
            "compset -P add-default-case,\n<all> <clarify-parse-errors>",
        ),
        (&["-P", ".:sub"], "compset -P .:\nFILES\n"),
        (&["my"], "FILES\n"),
        (&["--color", "my"], "FILES\n"),
        (&["--rcfile", "my"], "FILES\n"),
        (&["--", "-d"], "FILES\n"),
        (&["-j", ""], "status=1\n"),
    ];
    let mut probe = format!(
        "compdef() {{ :; }}\ncompadd() {{ while [[ $1 != -- && $# -gt 0 ]]; do shift; done; shift; printf '<%s> ' \"$@\"; print; }}\n_files() {{ print FILES; }}\ncompset() {{ print -r -- \"compset $*\"; }}\n{}",
        script("zsh")
    );
    for (words, _) in cases {
        let argv: Vec<String> = words.iter().map(|word| quote(word)).collect();
        let _ = std::fmt::Write::write_fmt(
            &mut probe,
            format_args!(
                "\nprint '==CASE'; words=(rshellcheck {}); CURRENT={}; _rshellcheck_complete; print status=$?\n",
                argv.join(" "),
                words.len() + 1
            ),
        );
    }
    let output = run(&fixture.0, "zsh", &["-f"], &probe);
    let sections: Vec<&str> = output.split("==CASE\n").skip(1).collect();
    assert_eq!(sections.len(), cases.len(), "{output}");
    for ((words, expected), section) in cases.iter().zip(sections) {
        assert!(section.contains(expected), "{words:?}: {section}");
        if *expected == "FILES\n" {
            assert!(!section.contains('<'), "{words:?}: {section}");
        }
    }
}
