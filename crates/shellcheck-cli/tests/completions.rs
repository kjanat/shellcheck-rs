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
    (&["--color=al"], &["--color=always"]),
    (&["-Cal"], &["-Calways"]),
    (&["--for", "j"], &["json", "json1"]),
    (&["--sh=z"], &["--sh=zsh"]),
    (&["--g", "b"], &["bash"]),
    (&["-x", "--norc", "oth"], &["other.sh"]),
    (&["--rcfile", "my"], &["my script.sh"]),
    (&["--files-from=oth"], &["--files-from=other.sh"]),
    (&["--", "oth"], &["other.sh"]),
];

/// Values without a candidate list. PowerShell 7.6 rejects an empty result and
/// completes file names for these, so only Bash and Fish are asked.
const FREE_TEXT: &[(&[&str], &[&str])] = &[(&["-j", ""], &[]), (&["--include", ""], &[])];

type Case = (&'static [&'static str], &'static [&'static str]);

fn cases_with(more: &[&[Case]]) -> Vec<Case> {
    CASES
        .iter()
        .chain(more.iter().copied().flatten())
        .copied()
        .collect()
}

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

fn assert_cases(shell: &str, cases: &[(&[&str], &[&str])], output: &str) {
    let sections: Vec<&str> = output.split("==CASE\n").skip(1).collect();
    assert_eq!(sections.len(), cases.len(), "{shell}: {output}");
    for ((words, expected), section) in cases.iter().zip(sections) {
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
    let cases = cases_with(&[FREE_TEXT]);
    let words: Vec<&[&str]> = cases.iter().map(|(words, _)| *words).collect();
    let output = run(
        &fixture.0,
        "bash",
        &["--noprofile", "--norc"],
        &bash_probe(&script, &words),
    );
    assert_cases("bash", &cases, &output);
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

/// Readline's default word breaks split `--format=j` into three words. The
/// probe has no bash-completion, so the script joins them itself.
#[test]
fn bash_completes_a_value_readline_split_at_the_equals_sign() {
    if !installed("bash") {
        return;
    }
    let fixture = Fixture::new();
    let probe = format!(
        "{}\nCOMP_WORDS=(rshellcheck --format = j); COMP_CWORD=3; COMPREPLY=(); _rshellcheck_complete; printf '%s\\n' \"${{COMPREPLY[@]}}\"\n",
        script("bash")
    );
    let output = run(&fixture.0, "bash", &["--noprofile", "--norc"], &probe);
    assert_eq!(candidates(&output), ["json", "json1"]);
}

#[test]
fn fish_completes_options_values_and_files() {
    if !installed("fish") {
        return;
    }
    let fixture = Fixture::new();
    let mut probe = script("fish");
    let cases = cases_with(&[FREE_TEXT]);
    for (words, _) in &cases {
        let line = format!("rshellcheck {}", words.join(" "));
        let _ = std::fmt::Write::write_fmt(
            &mut probe,
            format_args!("\necho '==CASE'; complete -C {}\n", quote(&line)),
        );
    }
    let output = run(&fixture.0, "fish", &["--no-config"], &probe);
    let sections: Vec<&str> = output.split("==CASE\n").skip(1).collect();
    assert_eq!(sections.len(), cases.len(), "fish: {output}");
    for ((words, expected), section) in cases.iter().zip(sections) {
        // Fish 4.2.1 lists `--files-from` for `--fo` for any command that
        // declares both options, so only prefix matches are compared.
        let word = words.last().copied().unwrap_or_default();
        let mut found = candidates(section);
        found.retain(|candidate| candidate.starts_with(word));
        assert_eq!(found, *expected, "fish {words:?}");
    }
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
    let cases = cases_with(&[]);
    for (words, _) in &cases {
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
    assert_cases("powershell", &cases, &output);
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
        (
            &["--for", "j"],
            "<checkstyle> <diff> <gcc> <json> <json1> <quiet> <tty> \n",
        ),
        (&["--g", "b"], "<bash> <zsh> <fish> <powershell> \n"),
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
