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

use std::io::BufRead;
use std::path::Path;

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
    let paths: Vec<String> = std::io::stdin()
        .lock()
        .lines()
        .map(|line| line.map_err(|e| format!("reading paths from standard input: {e}")))
        .filter(|line| line.as_ref().map_or(true, |l| !l.trim().is_empty()))
        .collect::<Result<_, _>>()?;
    let oracle = oracle::Oracle::new(args.oracle())?;
    let files = judge(&oracle, &paths, args.shell.as_deref())?;
    let json = serde_json::to_string(&Report { files: &files }).map_err(|e| e.to_string())?;
    println!("{json}");
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
        let script = std::fs::read_to_string(path).map_err(|e| format!("{path}: {e}"))?;
        // Both tools infer a dialect from a recognised extension, so the copy
        // the oracle reads keeps the file's own name after a unique prefix.
        let base = Path::new(path)
            .file_name()
            .map_or_else(String::new, |n| n.to_string_lossy().into_owned());
        named.push((format!("{}-{base}", oracle.name()), script));
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
            let pk = port_keys(script, &oracle.dir().join(name).to_string_lossy(), shell)?;
            if keys_match(&pk, &ok) {
                return Ok(Judgement {
                    path: path.clone(),
                    verdict: Verdict::Identical,
                    deviations: Vec::new(),
                });
            }
            let ids: Vec<&'static str> =
                deviations::sanctioned(script, shell, &pk, &ok, Some(oracle))
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

    /// A scratch directory removed when the test ends.
    struct Scratch(std::path::PathBuf);

    impl Scratch {
        fn new(test: &str) -> Self {
            let dir = std::env::temp_dir().join(format!("judge-{test}-{}", std::process::id()));
            std::fs::create_dir_all(&dir).expect("scratch directory");
            Self(dir)
        }

        fn path(&self) -> &Path {
            &self.0
        }
    }

    impl Drop for Scratch {
        fn drop(&mut self) {
            let _ = std::fs::remove_dir_all(&self.0);
        }
    }

    fn write(dir: &Path, name: &str, body: &str) -> String {
        let path = dir.join(name);
        std::fs::write(&path, body).expect("write fixture");
        path.to_string_lossy().into_owned()
    }

    #[test]
    fn each_file_is_identical_sanctioned_or_differs_in_input_order() {
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

    #[test]
    fn a_file_the_oracle_cannot_answer_for_differs() {
        let dir = Scratch::new("unanswered");
        let fake = dir.path().join("oracle");
        std::fs::write(&fake, "#!/bin/sh\necho 'not json'\n").expect("write oracle");
        std::fs::set_permissions(&fake, std::os::unix::fs::PermissionsExt::from_mode(0o755))
            .expect("chmod oracle");
        let oracle = oracle::Oracle::new(&fake.to_string_lossy()).expect("oracle");
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

    #[test]
    fn a_missing_file_is_a_harness_error() {
        let dir = Scratch::new("missing");
        let fake = dir.path().join("oracle");
        std::fs::write(&fake, "#!/bin/sh\necho '{\"comments\":[]}'\n").expect("write oracle");
        std::fs::set_permissions(&fake, std::os::unix::fs::PermissionsExt::from_mode(0o755))
            .expect("chmod oracle");
        let oracle = oracle::Oracle::new(&fake.to_string_lossy()).expect("oracle");
        let missing = dir.path().join("absent.sh").to_string_lossy().into_owned();
        let err = judge(&oracle, std::slice::from_ref(&missing), None).expect_err("missing file");
        assert!(err.starts_with(&missing), "{err}");
    }
}
