//! `judge`: whether the port's findings on given files differ from the
//! oracle's only by sanctioned deviations.
//!
//! The benchmark compares the port's output with a ShellCheck build it times
//! as its baseline. A byte difference there is either a port defect or a
//! deviation [`crate::deviations`] sanctions, and only the classifier can tell
//! which. `judge` reads one path per line on standard input, checks each file
//! with both tools and prints one JSON document:
//!
//! ```json
//! {"files": [{"path": "bin/a", "verdict": "sanctioned", "deviations": ["stable-trap-variables"]}]}
//! ```
//!
//! A verdict is `identical`, `sanctioned`, or `differs`. A file the oracle
//! produced nothing parseable for is `differs`: the judge fails closed. The
//! oracle is whatever `--oracle` names, at any version, since the caller picks
//! the build it compares against.
//!
//! Exit codes: 0 = no file differs, 1 = at least one does, 2 = harness error.

use std::io::{BufRead, Write};
use std::path::Path;

use rshellcheck_core::interface::decode_bytes;
use serde::Serialize;

use crate::{Args, deviations, keys_match, oracle, oracle_keys, port_keys};

/// One file's verdict.
#[derive(Debug, Serialize, PartialEq, Eq)]
pub struct Judgement {
    pub path: String,
    pub verdict: Verdict,
    /// The sanctioning classes, outermost first; empty unless `sanctioned`.
    pub deviations: Vec<&'static str>,
}

#[derive(Debug, Serialize, PartialEq, Eq, Clone, Copy)]
#[serde(rename_all = "lowercase")]
pub enum Verdict {
    Identical,
    Sanctioned,
    Differs,
}

#[derive(Serialize)]
struct Report<'a> {
    files: &'a [Judgement],
}

/// Judge every path named on standard input and print the report.
pub fn run(args: &Args) -> Result<bool, String> {
    run_on(args, std::io::stdin().lock(), &mut std::io::stdout().lock())
}

/// [`run`], reading the paths from `input` and writing the report to `out`.
fn run_on(args: &Args, input: impl BufRead, out: &mut impl Write) -> Result<bool, String> {
    let paths: Vec<String> = input
        .lines()
        .map(|line| line.map_err(|e| format!("reading paths from standard input: {e}")))
        .filter(|line| line.as_ref().map_or(true, |l| !l.trim().is_empty()))
        .collect::<Result<_, _>>()?;
    let oracle = oracle::Oracle::new(args.oracle())?;
    let files = judge(&oracle, &paths, args.shell.as_deref())?;
    let json = serde_json::to_string(&Report { files: &files }).map_err(|e| e.to_string())?;
    writeln!(out, "{json}").map_err(|e| format!("writing the report: {e}"))?;
    Ok(files.iter().all(|f| f.verdict != Verdict::Differs))
}

/// The verdict for each of `paths`, in order.
pub fn judge(
    oracle: &oracle::Oracle,
    paths: &[String],
    shell: Option<&str>,
) -> Result<Vec<Judgement>, String> {
    let mut named = Vec::with_capacity(paths.len());
    for path in paths {
        let bytes = std::fs::read(path).map_err(|e| format!("{path}: {e}"))?;
        // Upstream's lenient decoding, as the CLI reads a file.
        let script = decode_bytes(&bytes);
        // Both tools infer a dialect from a recognised extension, so the copy
        // the oracle reads keeps the file's own name, in a directory of its
        // own: a prefix could push a valid name past the length limit.
        let base = Path::new(path)
            .file_name()
            .map_or_else(String::new, |n| n.to_string_lossy().into_owned());
        named.push((format!("{}/{base}", oracle.name()), script));
    }
    let by_name = oracle.check(&named, shell)?;
    named
        .iter()
        .zip(paths)
        .map(|((name, script), path)| {
            let Some(comments) = by_name.get(name) else {
                return Ok(Judgement {
                    path: path.clone(),
                    verdict: Verdict::Differs,
                    deviations: Vec::new(),
                });
            };
            let ok = oracle_keys(comments);
            let filename = oracle.dir().join(name).to_string_lossy().into_owned();
            let pk = port_keys(script, &filename, shell)?;
            if keys_match(&pk, &ok) {
                return Ok(Judgement {
                    path: path.clone(),
                    verdict: Verdict::Identical,
                    deviations: Vec::new(),
                });
            }
            let ids: Vec<&'static str> =
                deviations::sanctioned(script, &filename, shell, &pk, &ok, Some(oracle))
                    .iter()
                    .map(|d| d.id)
                    .collect();
            Ok(Judgement {
                path: path.clone(),
                verdict: if ids.is_empty() {
                    Verdict::Differs
                } else {
                    Verdict::Sanctioned
                },
                deviations: ids,
            })
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::oracle::Scratch;

    fn write(dir: &Path, name: &str, body: &str) -> String {
        let path = dir.join(name);
        std::fs::write(&path, body).expect("write fixture");
        path.to_string_lossy().into_owned()
    }

    #[test]
    fn each_file_is_identical_or_sanctioned_in_input_order() {
        let Some(oracle) = crate::oracle::test_oracle() else {
            return;
        };
        let dir = Scratch::new("classify");
        let paths = [
            write(
                dir.path(),
                "stable-trap.sh",
                "ENGINE=podman; trap \"$ENGINE rm -f x\" EXIT\n",
            ),
            write(dir.path(), "clean.sh", "#!/bin/sh\ntrue\n"),
        ];
        let got = judge(&oracle, &paths, None).expect("judge");
        assert_eq!(
            got,
            [
                Judgement {
                    path: paths[0].clone(),
                    verdict: Verdict::Sanctioned,
                    deviations: vec!["stable-trap-variables"],
                },
                Judgement {
                    path: paths[1].clone(),
                    verdict: Verdict::Identical,
                    deviations: Vec::new(),
                },
            ]
        );
    }

    /// A fake oracle printing `stdout`, whatever it is asked.
    #[cfg(unix)]
    fn fake_oracle(dir: &Path, stdout: &str) -> oracle::Oracle {
        oracle::fake_oracle(dir, &format!("echo '{stdout}'"))
    }

    #[cfg(unix)]
    #[test]
    fn a_file_the_oracle_cannot_answer_for_differs() {
        let dir = Scratch::new("unanswered");
        let oracle = fake_oracle(dir.path(), "not json");
        let path = write(dir.path(), "clean.sh", "#!/bin/sh\ntrue\n");
        let got = judge(&oracle, std::slice::from_ref(&path), None).expect("judge");
        assert_eq!(
            got,
            [Judgement {
                path,
                verdict: Verdict::Differs,
                deviations: Vec::new(),
            }]
        );
    }

    #[cfg(unix)]
    #[test]
    fn an_oracle_answer_without_a_comments_array_differs() {
        let dir = Scratch::new("no-comments");
        let oracle = fake_oracle(dir.path(), "{}");
        let path = write(dir.path(), "clean.sh", "#!/bin/sh\ntrue\n");
        let got = judge(&oracle, std::slice::from_ref(&path), None).expect("judge");
        assert_eq!(
            got,
            [Judgement {
                path,
                verdict: Verdict::Differs,
                deviations: Vec::new(),
            }]
        );
    }

    #[cfg(unix)]
    #[test]
    fn an_oracle_comment_naming_no_file_differs() {
        let dir = Scratch::new("malformed-comment");
        let oracle = fake_oracle(dir.path(), r#"{"comments":[{}]}"#);
        let path = write(dir.path(), "clean.sh", "#!/bin/sh\ntrue\n");
        let got = judge(&oracle, std::slice::from_ref(&path), None).expect("judge");
        assert_eq!(
            got,
            [Judgement {
                path,
                verdict: Verdict::Differs,
                deviations: Vec::new(),
            }]
        );
    }

    #[cfg(unix)]
    #[test]
    fn a_file_with_invalid_utf8_is_judged() {
        let dir = Scratch::new("latin1");
        let oracle = fake_oracle(dir.path(), "{\"comments\":[]}");
        let path = dir.path().join("latin1.sh");
        std::fs::write(&path, b"#!/bin/sh\necho caf\xe9\n").expect("write fixture");
        let path = path.to_string_lossy().into_owned();
        let got = judge(&oracle, std::slice::from_ref(&path), None).expect("judge");
        assert_eq!(
            got,
            [Judgement {
                path,
                verdict: Verdict::Identical,
                deviations: Vec::new(),
            }]
        );
    }

    /// A name at the 255-byte limit stays valid in the oracle's scratch
    /// directory, and nothing of it is left there afterwards.
    #[cfg(unix)]
    #[test]
    fn a_file_name_of_maximum_length_is_judged() {
        let dir = Scratch::new("long-name");
        let oracle = oracle::fake_oracle(dir.path(), oracle::DIRTY_ORACLE);
        let name = format!("{}.sh", "a".repeat(252));
        assert_eq!(name.len(), 255);
        let path = write(dir.path(), &name, "#!/bin/sh\ntrue\n");
        let got = judge(&oracle, std::slice::from_ref(&path), None).expect("judge");
        assert_eq!(
            got,
            [Judgement {
                path,
                verdict: Verdict::Identical,
                deviations: Vec::new(),
            }]
        );
        let left: Vec<_> = std::fs::read_dir(oracle.dir())
            .expect("scratch directory")
            .collect();
        assert!(left.is_empty(), "{left:?}");
    }

    /// Two inputs with the same file name get the oracle's answer for each
    /// file's own content.
    #[cfg(unix)]
    #[test]
    fn files_sharing_a_name_get_their_own_answers() {
        let dir = Scratch::new("same-name");
        let oracle = oracle::fake_oracle(dir.path(), oracle::DIRTY_ORACLE);
        for sub in ["one", "two"] {
            std::fs::create_dir_all(dir.path().join(sub)).expect("fixture directory");
        }
        let paths = [
            write(dir.path(), "one/x.sh", "#!/bin/sh\n# dirty\n"),
            write(dir.path(), "two/x.sh", "#!/bin/sh\ntrue\n"),
        ];
        let got = judge(&oracle, &paths, None).expect("judge");
        assert_eq!(
            got,
            [
                Judgement {
                    path: paths[0].clone(),
                    verdict: Verdict::Differs,
                    deviations: Vec::new(),
                },
                Judgement {
                    path: paths[1].clone(),
                    verdict: Verdict::Identical,
                    deviations: Vec::new(),
                },
            ]
        );
    }

    /// `conformance judge` as the benchmark runs it: `argv` after the command
    /// name, `stdin` holding the paths. Returns the exit status and stdout.
    fn cli(argv: &[&str], stdin: &str) -> (u8, String) {
        use clap::Parser;
        let args = Args::try_parse_from(["conformance", "judge"].iter().chain(argv)).expect("args");
        let mut out = Vec::new();
        let res = run_on(&args, stdin.as_bytes(), &mut out);
        (
            crate::status(&res),
            String::from_utf8(out).expect("utf-8 report"),
        )
    }

    /// The verdicts in a report, after checking it is one JSON document on
    /// one line.
    fn verdicts(report: &str) -> Vec<(String, String)> {
        assert_eq!(report.lines().count(), 1, "{report}");
        let doc: serde_json::Value = serde_json::from_str(report).expect("one JSON document");
        doc["files"]
            .as_array()
            .expect("files")
            .iter()
            .map(|f| {
                (
                    f["path"].as_str().expect("path").to_string(),
                    f["verdict"].as_str().expect("verdict").to_string(),
                )
            })
            .collect()
    }

    #[cfg(unix)]
    #[test]
    fn the_cli_reports_every_path_in_input_order_and_exits_by_verdict() {
        let dir = Scratch::new("cli-verdicts");
        let oracle = dir.path().join("oracle").to_string_lossy().into_owned();
        drop(oracle::fake_oracle(dir.path(), oracle::DIRTY_ORACLE));
        let clean = write(dir.path(), "clean.sh", "#!/bin/sh\ntrue\n");
        let dirty = write(dir.path(), "dirty.sh", "#!/bin/sh\n# dirty\n");
        let (status, out) = cli(&["--oracle", &oracle], &format!("{dirty}\n\n{clean}\n"));
        assert_eq!(status, 1, "{out}");
        assert_eq!(
            verdicts(&out),
            [
                (dirty, "differs".to_string()),
                (clean.clone(), "identical".to_string())
            ]
        );
        let (status, out) = cli(&["--oracle", &oracle], &format!("{clean}\n"));
        assert_eq!(status, 0, "{out}");
        assert_eq!(verdicts(&out), [(clean, "identical".to_string())]);
    }

    #[cfg(unix)]
    #[test]
    fn the_cli_fails_closed_on_unusable_oracle_output() {
        let dir = Scratch::new("cli-garbage");
        let oracle = dir.path().join("oracle").to_string_lossy().into_owned();
        drop(oracle::fake_oracle(dir.path(), "echo 'not json'"));
        let clean = write(dir.path(), "clean.sh", "#!/bin/sh\ntrue\n");
        let (status, out) = cli(&["--oracle", &oracle], &format!("{clean}\n"));
        assert_eq!(status, 1, "{out}");
        assert_eq!(verdicts(&out), [(clean, "differs".to_string())]);
    }

    #[cfg(unix)]
    #[test]
    fn the_cli_exits_2_and_prints_nothing_for_a_missing_file() {
        let dir = Scratch::new("cli-missing");
        let oracle = dir.path().join("oracle").to_string_lossy().into_owned();
        drop(oracle::fake_oracle(dir.path(), oracle::DIRTY_ORACLE));
        let missing = dir.path().join("absent.sh").to_string_lossy().into_owned();
        let (status, out) = cli(&["--oracle", &oracle], &format!("{missing}\n"));
        assert_eq!((status, out.as_str()), (2, ""));
    }

    /// `--shell` reaches both tools: the fake oracle refuses to answer
    /// without it, and the port would ask for a shebang.
    #[cfg(unix)]
    #[test]
    fn the_cli_checks_as_the_shell_it_is_given() {
        let dir = Scratch::new("cli-shell");
        let oracle = dir.path().join("oracle").to_string_lossy().into_owned();
        drop(oracle::fake_oracle(
            dir.path(),
            r#"case " $* " in *" --shell=bash "*) ;; *) exit 3 ;; esac; echo '{"comments":[]}'"#,
        ));
        let script = write(dir.path(), "plain", "true\n");
        let (status, out) = cli(
            &["--oracle", &oracle, "--shell", "bash"],
            &format!("{script}\n"),
        );
        assert_eq!(status, 0, "{out}");
        assert_eq!(verdicts(&out), [(script.clone(), "identical".to_string())]);
        let (status, out) = cli(&["--oracle", &oracle], &format!("{script}\n"));
        assert_eq!(status, 1, "{out}");
        assert_eq!(verdicts(&out), [(script, "differs".to_string())]);
    }

    #[test]
    fn a_missing_file_is_a_harness_error() {
        let dir = Scratch::new("missing");
        let fake = dir.path().join("oracle");
        std::fs::write(&fake, "").expect("write oracle");
        let oracle = oracle::Oracle::new(&fake.to_string_lossy()).expect("oracle");
        let missing = dir.path().join("absent.sh").to_string_lossy().into_owned();
        let err = judge(&oracle, std::slice::from_ref(&missing), None).expect_err("missing file");
        assert!(err.starts_with(&missing), "{err}");
    }
}
