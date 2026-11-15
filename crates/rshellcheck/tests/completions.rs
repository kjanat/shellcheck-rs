//! Loads the script `--generate-completions` prints into each shell and asks
//! that shell to complete `rshellcheck` command lines.
#![cfg(all(unix, feature = "completions"))]

use std::fmt::Write as _;
use std::os::unix::process::CommandExt;
use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{Duration, Instant};

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
    let found = bounded(
        Command::new(program).arg("--version"),
        "",
        Duration::from_secs(10),
    )
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
    let output = bounded(
        Command::new(env!("CARGO_BIN_EXE_rshellcheck"))
            .env_remove("SHELLCHECK_OPTS")
            .args(["--generate-completions", shell]),
        "",
        Duration::from_secs(30),
    )
    .unwrap_or_else(|e| panic!("run CLI: {e}"));
    assert!(output.status.success());
    assert_eq!(String::from_utf8_lossy(&output.stderr), "");
    String::from_utf8(output.stdout).unwrap_or_else(|e| panic!("{shell} script: {e}"))
}

/// Files avoid pipe backpressure (including stdin) while the parent enforces
/// a deadline. A process group also terminates subprocesses spawned by shells.
fn bounded(command: &mut Command, stdin: &str, timeout: Duration) -> Result<Output, String> {
    let capture = Fixture::new();
    let input = capture.0.join("stdin");
    let stdout = capture.0.join("stdout");
    let stderr = capture.0.join("stderr");
    std::fs::write(&input, stdin).map_err(|e| e.to_string())?;
    let mut child = command
        .process_group(0)
        .stdin(Stdio::from(
            std::fs::File::open(input).map_err(|e| e.to_string())?,
        ))
        .stdout(Stdio::from(
            std::fs::File::create(&stdout).map_err(|e| e.to_string())?,
        ))
        .stderr(Stdio::from(
            std::fs::File::create(&stderr).map_err(|e| e.to_string())?,
        ))
        .spawn()
        .map_err(|e| e.to_string())?;
    let started = Instant::now();
    let mut expired = false;
    let status = loop {
        if let Some(status) = child.try_wait().map_err(|e| e.to_string())? {
            break status;
        }
        if started.elapsed() >= timeout {
            expired = true;
            let _ = Command::new("kill")
                .args(["-KILL", "--", &format!("-{}", child.id())])
                .status();
            let _ = child.kill();
            break child.wait().map_err(|e| e.to_string())?;
        }
        std::thread::sleep(Duration::from_millis(10));
    };
    let output = Output {
        status,
        stdout: std::fs::read(stdout).map_err(|e| e.to_string())?,
        stderr: std::fs::read(stderr).map_err(|e| e.to_string())?,
    };
    if expired {
        return Err(format!(
            "{command:?} timed out after {timeout:?}; stdout={}; stderr={}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        ));
    }
    Ok(output)
}

fn run(dir: &Path, program: &str, args: &[&str], stdin: &str) -> String {
    let output = bounded(
        Command::new(program).current_dir(dir).args(args),
        stdin,
        Duration::from_secs(30),
    )
    .unwrap_or_else(|e| panic!("run {program}: {e}"));
    assert!(
        output.status.success(),
        "{program} failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    String::from_utf8(output.stdout).unwrap_or_else(|e| panic!("{program} output: {e}"))
}

#[test]
fn a_stuck_shell_is_killed_and_preserves_diagnostics() {
    let started = Instant::now();
    let error = bounded(
        Command::new("sh").args([
            "-c",
            "echo before; echo problem >&2; sleep 60 & echo \"descendant=$!.\"; wait",
        ]),
        "",
        Duration::from_millis(150),
    )
    .expect_err("shell must time out");
    assert!(started.elapsed() < Duration::from_secs(5));
    assert!(
        error.contains("timed out") && error.contains("before") && error.contains("problem"),
        "{error}"
    );
    let Some((descendant, _)) = error
        .split_once("descendant=")
        .and_then(|(_, rest)| rest.split_once('.'))
    else {
        panic!("no descendant pid: {error}");
    };
    let deadline = Instant::now() + Duration::from_secs(5);
    while Command::new("kill")
        .args(["-0", descendant])
        .stderr(Stdio::null())
        .status()
        .is_ok_and(|status| status.success())
    {
        assert!(
            Instant::now() < deadline,
            "descendant {descendant} survived"
        );
        std::thread::sleep(Duration::from_millis(10));
    }
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

/// Exercise real compset/compadd/_files inside a ZLE completion widget. zpty
/// supplies a terminal without an external PTY driver or interactive user.
#[test]
fn zsh_inserts_attached_lists_and_quoted_paths() {
    if !installed("zsh") {
        return;
    }
    let fixture = Fixture::new();
    std::fs::write(fixture.0.join("it's mine.sh"), "").expect("quoted fixture");
    std::fs::write(fixture.0.join("completion.zsh"), script("zsh")).expect("completion script");
    let cases = [
        ("rshellcheck --format=g", "rshellcheck --format=gcc"),
        ("rshellcheck -fjso", "rshellcheck -fjson"),
        (
            "rshellcheck -o add-default-case,dep",
            "rshellcheck -o add-default-case,deprecate-which",
        ),
        (
            "rshellcheck --source-path=.:sub",
            "rshellcheck --source-path=.:subdir/",
        ),
        (
            "rshellcheck --rcfile my",
            "rshellcheck --rcfile my\\ script.sh",
        ),
        (
            "rshellcheck --files-from=it",
            "rshellcheck --files-from=it\\'s\\ mine.sh",
        ),
    ];
    let mut widget = String::from("probe() {\n");
    for (index, (line, _)) in cases.iter().enumerate() {
        writeln!(widget, "BUFFER={}; CURSOR=$#BUFFER; zle complete-word; print -r -- \"$BUFFER\" > result-{index}", quote(line)).expect("widget source");
    }
    widget.push_str("BUFFER=''; }\nzle -N probe\nbindkey '^X' probe\n");
    std::fs::write(fixture.0.join("widget.zsh"), widget).expect("widget script");
    let probe = r#"
zmodload zsh/zpty
zpty -b child zsh -f
zpty -w child "PS1=''; PS2=''; autoload -Uz compinit; compinit -D -u && source ./completion.zsh && source ./widget.zsh"
zpty -w -n child $'\x18'
while [[ ! -f result-5 ]]; do
  zpty -r child line && print -r -- "$line"
  sleep 0.01
done
zpty -d child
"#;
    run(&fixture.0, "zsh", &["-f"], probe);
    for (index, (line, expected)) in cases.iter().enumerate() {
        let inserted = std::fs::read_to_string(fixture.0.join(format!("result-{index}")))
            .expect("completion result");
        assert_eq!(inserted.trim_end(), *expected, "{line}");
    }
}
