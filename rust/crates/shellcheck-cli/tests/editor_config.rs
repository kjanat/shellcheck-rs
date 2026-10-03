//! Configuration lookup (`.shellcheckrc`, EditorConfig, `--rcfile`, `--norc`)
//! and exit codes, against output captured from the oracle (v0.11.0).
//!
//! Expected output names the fixture's root as `{T}`, its checkstyle escape as
//! `{TX}`, and the first 15 characters of it as `{T15}`.

use std::io::Write;
use std::os::unix::fs::PermissionsExt;
use std::path::PathBuf;
use std::process::{Command, Stdio};

const SCRIPT: &str = "#!/bin/sh\necho $x\n";

const FILES: &[(&str, &str)] = &[
    (
        "z/.editorconfig",
        "root = true\n[foo]\nshellcheck.shell=zsh\n",
    ),
    ("z/foo", "#!/bin/sh\necho \"hi\"\n"),
    (
        "r/.editorconfig",
        "root = true\n[*.sh]\nshellcheck.disable=SC2154\n",
    ),
    (
        "r/b/.editorconfig",
        "# c\nroot = maybe\n[*.sh]\nshellcheck.shell=sh\n",
    ),
    ("r/b/x.sh", SCRIPT),
    (
        "m/.editorconfig",
        "root = true\n[*.sh]\nshellcheck.disable=SC2154\n",
    ),
    ("m/.shellcheckrc", "disable=SC2086\n"),
    ("m/x.sh", SCRIPT),
    (
        "j/.editorconfig",
        "root = true\n[*.sh]\n\tshellcheck.shell = fish\n",
    ),
    ("j/.shellcheckrc", "disable=SC2086\n"),
    ("j/x.sh", SCRIPT),
    (
        "k/.editorconfig",
        "root = true\n[*.sh]\nshellcheck.disable=SC2154\n",
    ),
    ("k/.shellcheckrc", "oops\n"),
    ("k/x.sh", SCRIPT),
    (
        "s/.editorconfig",
        "root = true\n[-]\nshellcheck.disable=SC2086\n",
    ),
    ("g/.editorconfig", "root = true\n"),
    ("g/x.sh", SCRIPT),
    ("rcf", "disable=SC2154\n"),
    (
        "u/.editorconfig",
        "root = true\n[*]\nshellcheck.disable=SC2086\n",
    ),
    ("u/x.sh", SCRIPT),
];

const X_2154_2086: &str = r#"{"file":"X","line":2,"endLine":2,"column":6,"endColumn":8,"level":"warning","code":2154,"message":"x is referenced but not assigned.","fix":null},{"file":"X","line":2,"endLine":2,"column":6,"endColumn":8,"level":"info","code":2086,"message":"Double quote to prevent globbing and word splitting.","fix":{"replacements":[{"column":6,"endColumn":6,"endLine":2,"insertionPoint":"afterEnd","line":2,"precedence":7,"replacement":"\""},{"column":8,"endColumn":8,"endLine":2,"insertionPoint":"beforeStart","line":2,"precedence":7,"replacement":"\""}]}}"#;

const X_2154: &str = r#"{"file":"X","line":2,"endLine":2,"column":6,"endColumn":8,"level":"warning","code":2154,"message":"x is referenced but not assigned.","fix":null}"#;

const X_2086: &str = r#"{"file":"X","line":2,"endLine":2,"column":6,"endColumn":8,"level":"info","code":2086,"message":"Double quote to prevent globbing and word splitting.","fix":{"replacements":[{"column":6,"endColumn":6,"endLine":2,"insertionPoint":"afterEnd","line":2,"precedence":7,"replacement":"\""},{"column":8,"endColumn":8,"endLine":2,"insertionPoint":"beforeStart","line":2,"precedence":7,"replacement":"\""}]}}"#;

/// The json comment for an SC1134 at `line:column` of `file`.
fn sc1134(file: &str, line: u32, column: u32) -> String {
    format!(
        r#"{{"file":"{file}","line":{line},"endLine":{line},"column":{column},"endColumn":{column},"level":"error","code":1134,"message":"Failed to process {file}, line {line}: Expected '=' after directive key. Fix any mentioned problems and try again.","fix":null}}"#
    )
}

fn on(template: &str, file: &str) -> String {
    template.replace("\"X\"", &format!("\"{file}\""))
}

fn json1(comments: &[String]) -> String {
    format!(r#"{{"comments":[{}]}}"#, comments.join(","))
}

/// `escape'` of the checkstyle formatter.
fn checkstyle_escape(s: &str) -> String {
    s.chars()
        .map(|c| {
            if c.is_ascii_alphanumeric() || matches!(c, ' ' | '.' | '/') {
                c.to_string()
            } else {
                format!("&#{};", c as u32)
            }
        })
        .collect()
}

/// A copy of `FILES` in its own directory, with `HOME` and `XDG_CONFIG_HOME`
/// inside it.
struct Fixture(PathBuf);

struct Run {
    stdout: String,
    stderr: String,
    code: i32,
}

impl Fixture {
    fn new(name: &str) -> Fixture {
        let dir = std::env::temp_dir().join(format!(
            "rshellcheck-editorconfig-{name}-{}",
            std::process::id()
        ));
        std::fs::remove_dir_all(&dir).ok();
        for (path, contents) in FILES {
            let path = dir.join(path);
            std::fs::create_dir_all(path.parent().unwrap()).unwrap();
            std::fs::write(path, contents).unwrap();
        }
        std::fs::create_dir_all(dir.join("home")).unwrap();
        std::fs::create_dir_all(dir.join("xdg")).unwrap();
        Fixture(std::fs::canonicalize(dir).unwrap())
    }

    fn root(&self) -> String {
        self.0.display().to_string()
    }

    fn write(&self, path: &str, contents: &str) {
        std::fs::write(self.0.join(path), contents).unwrap();
    }

    fn expand(&self, template: &str) -> String {
        let root = self.root();
        let first: String = root.chars().take(15).collect();
        template
            .replace("{T15}", &first)
            .replace("{TX}", &checkstyle_escape(&root))
            .replace("{T}", &root)
    }

    fn run(&self, args: &[&str]) -> Run {
        self.run_in("", &[], None, args)
    }

    fn run_in(&self, dir: &str, env: &[(&str, String)], stdin: Option<&str>, args: &[&str]) -> Run {
        let mut cmd = Command::new(env!("CARGO_BIN_EXE_rshellcheck"));
        cmd.args(args)
            .current_dir(self.0.join(dir))
            .env_remove("SHELLCHECK_OPTS")
            .env("HOME", self.0.join("home"))
            .env("XDG_CONFIG_HOME", self.0.join("xdg"))
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped());
        for (key, value) in env {
            cmd.env(key, value);
        }
        let mut child = cmd.spawn().unwrap();
        let mut input = child.stdin.take().unwrap();
        input
            .write_all(stdin.unwrap_or_default().as_bytes())
            .unwrap();
        drop(input);
        let out = child.wait_with_output().unwrap();
        Run {
            stdout: String::from_utf8(out.stdout).unwrap(),
            stderr: String::from_utf8(out.stderr).unwrap(),
            code: out.status.code().unwrap(),
        }
    }

    fn assert(&self, run: &Run, stdout: &str, stderr: &str, code: i32) {
        assert_eq!(
            run.stdout.trim_end_matches('\n'),
            self.expand(stdout),
            "stdout"
        );
        assert_eq!(
            run.stderr.trim_end_matches('\n'),
            self.expand(stderr),
            "stderr"
        );
        assert_eq!(run.code, code, "exit code");
    }
}

impl Drop for Fixture {
    fn drop(&mut self) {
        std::fs::remove_dir_all(&self.0).ok();
    }
}

#[test]
fn an_unknown_shell_is_an_sc1134_in_the_editorconfig_and_exits_4() {
    let f = Fixture::new("zsh");
    let ec = sc1134("{T}/z/.editorconfig", 3, 8);
    let cases: [(&str, String, i32); 6] = [
        ("json1", json1(std::slice::from_ref(&ec)), 4),
        ("json", format!("[{ec}]"), 4),
        (
            "gcc",
            "{T}/z/.editorconfig:3:8: error: Failed to process {T}/z/.editorconfig, line 3: Expected '=' after directive key. Fix any mentioned problems and try again. [SC1134]".to_string(),
            4,
        ),
        (
            "tty",
            concat!(
                "\n",
                "In {T}/z/.editorconfig line 3:\n",
                "shellcheck.shell=zsh\n",
                "       ^-- SC1134 (error): Failed to process {T}/z/.editorconfig, line 3: Expected '=' after directive key. Fix any mentioned problems and try again.\n",
                "\n",
                "For more information:\n",
                "  https://www.shellcheck.net/wiki/SC1134 -- Failed to process {T15}...",
            )
            .to_string(),
            4,
        ),
        (
            "checkstyle",
            concat!(
                "<?xml version='1.0' encoding='UTF-8'?>\n",
                "<checkstyle version='4.3'>\n",
                "<file name='{TX}/z/.editorconfig' >\n",
                "<error line='3' column='8' severity='error' message='Failed to process {TX}/z/.editorconfig&#44; line 3&#58; Expected &#39;&#61;&#39; after directive key. Fix any mentioned problems and try again.' source='ShellCheck.SC1134' />\n",
                "</file>\n",
                "</checkstyle>",
            )
            .to_string(),
            4,
        ),
        ("quiet", String::new(), 1),
    ];
    for (format, stdout, code) in cases {
        let run = f.run(&["-f", format, "z/foo"]);
        f.assert(&run, &stdout, "", code);
    }
}

#[test]
fn an_invalid_root_rejects_the_editorconfig_and_its_parents() {
    let f = Fixture::new("root");
    let ec = sc1134("{T}/r/b/.editorconfig", 2, 8);
    let script = on(X_2154_2086, "r/b/x.sh");
    let cases: [(&str, String, i32); 6] = [
        ("json1", json1(&[script.clone(), ec.clone()]), 4),
        ("json", format!("[{ec},{script},{ec},{script}]"), 4),
        (
            "gcc",
            concat!(
                "{T}/r/b/.editorconfig:2:8: error: Failed to process {T}/r/b/.editorconfig, line 2: Expected '=' after directive key. Fix any mentioned problems and try again. [SC1134]\n",
                "r/b/x.sh:2:6: warning: x is referenced but not assigned. [SC2154]\n",
                "r/b/x.sh:2:6: note: Double quote to prevent globbing and word splitting. [SC2086]",
            )
            .to_string(),
            4,
        ),
        (
            "tty",
            concat!(
                "\n",
                "In {T}/r/b/.editorconfig line 2:\n",
                "root = maybe\n",
                "       ^-- SC1134 (error): Failed to process {T}/r/b/.editorconfig, line 2: Expected '=' after directive key. Fix any mentioned problems and try again.\n",
                "\n",
                "\n",
                "In r/b/x.sh line 2:\n",
                "echo $x\n",
                "     ^-- SC2154 (warning): x is referenced but not assigned.\n",
                "     ^-- SC2086 (info): Double quote to prevent globbing and word splitting.\n",
                "\n",
                "Did you mean:\n",
                "echo \"$x\"\n",
                "\n",
                "For more information:\n",
                "  https://www.shellcheck.net/wiki/SC1134 -- Failed to process {T15}...\n",
                "  https://www.shellcheck.net/wiki/SC2154 -- x is referenced but not assigned.\n",
                "  https://www.shellcheck.net/wiki/SC2086 -- Double quote to prevent globbing ...",
            )
            .to_string(),
            4,
        ),
        (
            "checkstyle",
            concat!(
                "<?xml version='1.0' encoding='UTF-8'?>\n",
                "<checkstyle version='4.3'>\n",
                "<file name='{TX}/r/b/.editorconfig' >\n",
                "<error line='2' column='8' severity='error' message='Failed to process {TX}/r/b/.editorconfig&#44; line 2&#58; Expected &#39;&#61;&#39; after directive key. Fix any mentioned problems and try again.' source='ShellCheck.SC1134' />\n",
                "</file>\n",
                "<file name='r/b/x.sh' >\n",
                "<error line='2' column='6' severity='warning' message='x is referenced but not assigned.' source='ShellCheck.SC2154' />\n",
                "<error line='2' column='6' severity='info' message='Double quote to prevent globbing and word splitting.' source='ShellCheck.SC2086' />\n",
                "</file>\n",
                "</checkstyle>",
            )
            .to_string(),
            4,
        ),
        ("quiet", String::new(), 1),
    ];
    for (format, stdout, code) in cases {
        let run = f.run(&["-f", format, "r/b/x.sh"]);
        f.assert(&run, &stdout, "", code);
    }
}

#[test]
fn the_shellcheckrc_and_the_editorconfig_both_apply() {
    let f = Fixture::new("merge");
    let run = f.run(&["-f", "json1", "m/x.sh"]);
    f.assert(&run, &json1(&[]), "", 0);
}

#[test]
fn a_rejected_editorconfig_replaces_the_shellcheckrc() {
    let f = Fixture::new("fish");
    let ec = sc1134("{T}/j/.editorconfig", 3, 1);
    let run = f.run(&["-f", "json1", "j/x.sh"]);
    f.assert(&run, &json1(&[on(X_2154_2086, "j/x.sh"), ec]), "", 4);

    let run = f.run(&["j/x.sh"]);
    let tty = concat!(
        "\n",
        "In {T}/j/.editorconfig line 3:\n",
        "\tshellcheck.shell = fish\n",
        "       ^-- SC1134 (error): Failed to process {T}/j/.editorconfig, line 3: Expected '=' after directive key. Fix any mentioned problems and try again.\n",
        "\n",
        "\n",
        "In j/x.sh line 2:\n",
        "echo $x\n",
        "     ^-- SC2154 (warning): x is referenced but not assigned.\n",
        "     ^-- SC2086 (info): Double quote to prevent globbing and word splitting.\n",
        "\n",
        "Did you mean:\n",
        "echo \"$x\"\n",
        "\n",
        "For more information:\n",
        "  https://www.shellcheck.net/wiki/SC1134 -- Failed to process {T15}...\n",
        "  https://www.shellcheck.net/wiki/SC2154 -- x is referenced but not assigned.\n",
        "  https://www.shellcheck.net/wiki/SC2086 -- Double quote to prevent globbing ...",
    );
    f.assert(&run, tty, "", 4);
}

#[test]
fn a_broken_shellcheckrc_is_an_sc1134_in_it_and_exits_1() {
    let f = Fixture::new("brokenrc");
    let rc = sc1134("{T}/k/.shellcheckrc", 1, 5);
    let run = f.run(&["-f", "json1", "k/x.sh"]);
    f.assert(&run, &json1(&[on(X_2154_2086, "k/x.sh"), rc]), "", 1);
}

#[test]
fn stdin_matches_a_section_named_dash() {
    let f = Fixture::new("stdin");
    let run = f.run_in("s", &[], Some(SCRIPT), &["-f", "json1", "-"]);
    f.assert(&run, &json1(&[on(X_2154, "-")]), "", 1);
}

#[test]
fn norc_skips_the_editorconfig_too() {
    let f = Fixture::new("norc");
    let run = f.run(&["--norc", "-f", "json1", "m/x.sh"]);
    f.assert(&run, &json1(&[on(X_2154_2086, "m/x.sh")]), "", 1);
}

#[test]
fn rcfile_replaces_the_shellcheckrc_and_keeps_the_editorconfig() {
    let f = Fixture::new("rcfile");
    let run = f.run(&["--rcfile", "rcf", "-f", "json1", "m/x.sh"]);
    f.assert(&run, &json1(&[on(X_2086, "m/x.sh")]), "", 1);

    let run = f.run(&["--rcfile", "nope", "-f", "json1", "m/x.sh"]);
    f.assert(
        &run,
        &json1(&[on(X_2086, "m/x.sh")]),
        "Warning: unable to read --rcfile nope",
        1,
    );
}

#[test]
fn a_missing_rcfile_is_not_read_for_an_input_that_is_not_read() {
    let f = Fixture::new("missingboth");
    let run = f.run(&["--rcfile", "nope", "-f", "json1", "nope.sh"]);
    f.assert(
        &run,
        &json1(&[]),
        "nope.sh: nope.sh: openBinaryFile: does not exist (No such file or directory)",
        2,
    );
}

#[test]
fn the_global_editorconfig_applies_without_exit_4() {
    let f = Fixture::new("global");
    f.write("xdg/editorconfig.ini", "[*.sh]\nshellcheck.shell=zsh\n");
    let ini = sc1134("{T}/xdg/editorconfig.ini", 2, 8);
    let run = f.run(&["-f", "json1", "g/x.sh"]);
    f.assert(&run, &json1(&[on(X_2154_2086, "g/x.sh"), ini]), "", 1);

    f.write(
        "xdg/editorconfig.ini",
        "[*.sh]\nshellcheck.disable=SC2086\n",
    );
    let run = f.run(&["-f", "json1", "g/x.sh"]);
    f.assert(&run, &json1(&[on(X_2154, "g/x.sh")]), "", 1);

    let relative = [("XDG_CONFIG_HOME", "xdg".to_string())];
    let run = f.run_in("", &relative, None, &["-f", "json1", "g/x.sh"]);
    f.assert(&run, &json1(&[on(X_2154_2086, "g/x.sh")]), "", 1);
}

#[test]
fn a_failed_input_outranks_exit_4() {
    let f = Fixture::new("twomissing");
    let run = f.run(&["-f", "json1", "z/foo", "missing.sh"]);
    f.assert(
        &run,
        &json1(&[sc1134("{T}/z/.editorconfig", 3, 8)]),
        "missing.sh: missing.sh: openBinaryFile: does not exist (No such file or directory)",
        2,
    );
}

#[test]
fn exit_4_outranks_a_clean_input() {
    let f = Fixture::new("twoclean");
    let run = f.run(&["-f", "gcc", "z/foo", "m/x.sh"]);
    f.assert(
        &run,
        "{T}/z/.editorconfig:3:8: error: Failed to process {T}/z/.editorconfig, line 3: Expected '=' after directive key. Fix any mentioned problems and try again. [SC1134]",
        "",
        4,
    );
}

#[test]
fn an_unreadable_editorconfig_is_reported_for_every_input() {
    let f = Fixture::new("unreadable");
    let ec = f.0.join("u/.editorconfig");
    std::fs::set_permissions(&ec, std::fs::Permissions::from_mode(0o000)).unwrap();
    assert!(
        std::fs::read(&ec).is_err(),
        "the fixture needs a user who cannot read a mode 000 file"
    );
    let denied = "{T}/u/.editorconfig: {T}/u/.editorconfig: openBinaryFile: permission denied (Permission denied)";
    let script = on(X_2154_2086, "u/x.sh");

    let run = f.run(&["-f", "json1", "u/x.sh"]);
    f.assert(&run, &json1(std::slice::from_ref(&script)), denied, 1);

    let run = f.run(&["-f", "json1", "u/x.sh", "u/x.sh"]);
    f.assert(
        &run,
        &json1(&[script.clone(), script]),
        &format!("{denied}\n{denied}"),
        1,
    );
}
