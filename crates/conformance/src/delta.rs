use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;
use std::path::Path;

use serde::{Deserialize, Serialize};
use shellcheck_rs::Dialect;

use crate::{Args, CommentKey, port_keys};

/// GitHub refuses a pull request body longer than 65536 characters.
const BUDGET: usize = 60_000;

const CONTEXT: i64 = 3;

#[derive(Serialize, Deserialize, Default, Debug, PartialEq, Eq)]
pub struct Findings {
    dropped: Vec<(String, i64)>,
    inputs: Vec<Input>,
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq)]
struct Input {
    id: String,
    script: String,
    findings: BTreeMap<String, Vec<Finding>>,
}

#[derive(Serialize, Deserialize, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct Finding {
    code: i64,
    line: i64,
    column: i64,
    end_line: i64,
    end_column: i64,
    level: String,
    message: String,
}

impl From<&CommentKey> for Finding {
    fn from(k: &CommentKey) -> Self {
        Self {
            code: k.code,
            line: k.line,
            column: k.column,
            end_line: k.end_line,
            end_column: k.end_column,
            level: k.level.clone(),
            message: k.message.clone(),
        }
    }
}

fn added() -> impl Iterator<Item = Dialect> {
    Dialect::ALL.into_iter().filter(|d| d.is_added())
}

pub fn collect(args: &Args) -> Result<Findings, String> {
    let dropped = shellcheck_rs::dialect_policy::dropped()
        .into_iter()
        .map(|(dialect, code)| (dialect.name().to_string(), code))
        .collect();
    let mut inputs = Vec::new();
    for (id, script) in crate::snapshot::inputs(args)? {
        let mut findings = BTreeMap::new();
        for dialect in added() {
            let keys = port_keys(&script, "-", Some(dialect.name()))?;
            if !keys.is_empty() {
                findings.insert(
                    dialect.name().to_string(),
                    keys.iter().map(Finding::from).collect(),
                );
            }
        }
        if !findings.is_empty() {
            inputs.push(Input {
                id,
                script,
                findings,
            });
        }
    }
    Ok(Findings { dropped, inputs })
}

pub fn write(args: &Args, path: &Path) -> Result<(), String> {
    let json = serde_json::to_string(&collect(args)?).map_err(|e| e.to_string())?;
    std::fs::write(path, json).map_err(|e| format!("{}: {e}", path.display()))
}

pub fn explain_since(args: &Args, path: &Path) -> Result<String, String> {
    let text = std::fs::read_to_string(path).map_err(|e| format!("{}: {e}", path.display()))?;
    let before: Findings =
        serde_json::from_str(&text).map_err(|e| format!("{}: {e}", path.display()))?;
    Ok(explain(&before, &collect(args)?))
}

fn rank(name: &str) -> usize {
    Dialect::ALL
        .iter()
        .position(|d| d.name() == name)
        .unwrap_or(Dialect::ALL.len())
}

fn codes(codes: &[i64]) -> String {
    if codes.is_empty() {
        return "none".to_string();
    }
    codes
        .iter()
        .map(|c| format!("SC{c}"))
        .collect::<Vec<_>>()
        .join(", ")
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Change {
    Lost,
    Gained,
}

impl Change {
    const fn word(self) -> &'static str {
        match self {
            Self::Lost => "lost",
            Self::Gained => "gained",
        }
    }
}

struct Example<'a> {
    id: &'a str,
    dialect: &'a str,
    finding: &'a Finding,
    script: &'a str,
}

#[derive(Default)]
struct Group<'a> {
    dialects: BTreeSet<(usize, &'a str)>,
    findings: usize,
    inputs: BTreeSet<&'a str>,
    example: Option<Example<'a>>,
}

fn difference<'a>(from: &'a [Finding], without: &[Finding]) -> Vec<&'a Finding> {
    let mut left: BTreeMap<&Finding, usize> = BTreeMap::new();
    for finding in without {
        *left.entry(finding).or_default() += 1;
    }
    from.iter()
        .filter(|finding| match left.get_mut(finding) {
            Some(count) if *count > 0 => {
                *count -= 1;
                false
            }
            _ => true,
        })
        .collect()
}

fn groups<'a>(
    before: &'a Findings,
    after: &'a Findings,
) -> (BTreeMap<(i64, Change), Group<'a>>, usize) {
    let index = |findings: &'a Findings| -> BTreeMap<&'a str, &'a Input> {
        findings.inputs.iter().map(|i| (i.id.as_str(), i)).collect()
    };
    let (was, now) = (index(before), index(after));
    let ids: BTreeSet<&str> = was.keys().chain(now.keys()).copied().collect();
    let mut groups: BTreeMap<(i64, Change), Group<'a>> = BTreeMap::new();
    let mut changed = 0;
    for id in ids {
        let (old, new) = (was.get(id), now.get(id));
        let mut dialects: Vec<&str> = old
            .iter()
            .chain(new.iter())
            .flat_map(|i| i.findings.keys().map(String::as_str))
            .collect();
        dialects.sort_by_key(|name| (rank(name), *name));
        dialects.dedup();
        let mut moved = false;
        for dialect in dialects {
            let find = |input: Option<&&'a Input>| {
                input
                    .and_then(|i| i.findings.get(dialect))
                    .map_or(&[][..], Vec::as_slice)
            };
            let (old_findings, new_findings) = (find(old), find(new));
            for (change, input, findings) in [
                (Change::Lost, old, difference(old_findings, new_findings)),
                (Change::Gained, new, difference(new_findings, old_findings)),
            ] {
                let Some(input) = input else { continue };
                for finding in findings {
                    moved = true;
                    let group = groups.entry((finding.code, change)).or_default();
                    group.dialects.insert((rank(dialect), dialect));
                    group.findings += 1;
                    group.inputs.insert(input.id.as_str());
                    group.example.get_or_insert(Example {
                        id: input.id.as_str(),
                        dialect,
                        finding,
                        script: input.script.as_str(),
                    });
                }
            }
        }
        changed += usize::from(moved);
    }
    (groups, changed)
}

fn policy(before: &Findings, after: &Findings) -> String {
    let set = |f: &Findings| -> BTreeSet<(String, i64)> { f.dropped.iter().cloned().collect() };
    let (was, now) = (set(before), set(after));
    let mut dialects: Vec<&str> = was
        .iter()
        .chain(now.iter())
        .map(|(d, _)| d.as_str())
        .collect();
    dialects.sort_by_key(|name| (rank(name), *name));
    dialects.dedup();
    let mut out = String::new();
    for dialect in dialects {
        let pick = |set: &BTreeSet<(String, i64)>, other: &BTreeSet<(String, i64)>, keep: bool| {
            set.iter()
                .filter(|(d, _)| d == dialect)
                .filter(|pair| other.contains(*pair) == keep)
                .map(|(_, code)| *code)
                .collect::<Vec<_>>()
        };
        let (dropped, restored, still) = (
            pick(&now, &was, false),
            pick(&was, &now, false),
            pick(&now, &was, true),
        );
        if dropped.is_empty() && restored.is_empty() {
            continue;
        }
        let _ = writeln!(
            out,
            "| {dialect} | {} | {} | {} |",
            codes(&dropped),
            codes(&restored),
            still.len()
        );
    }
    if out.is_empty() {
        return "No added dialect drops or restores a code.\n".to_string();
    }
    format!(
        "| Dialect | Newly dropped | Restored | Still dropped |\n| --- | --- | --- | ---: |\n{out}"
    )
}

fn fence(script: &str) -> String {
    let longest = script.split(|c| c != '`').map(str::len).max().unwrap_or(0);
    "`".repeat(longest.max(2) + 1)
}

fn example(code: i64, change: Change, group: &Group<'_>) -> String {
    let Some(example) = &group.example else {
        return String::new();
    };
    let finding = example.finding;
    let lines: Vec<&str> = example.script.lines().collect();
    let first = (finding.line - CONTEXT).max(1);
    let last = (finding.line + CONTEXT).min(i64::try_from(lines.len()).unwrap_or(i64::MAX));
    let window: Vec<&str> = (first..=last)
        .filter_map(|n| {
            usize::try_from(n - 1)
                .ok()
                .and_then(|i| lines.get(i).copied())
        })
        .collect();
    let body = window.join("\n");
    let fence = fence(&body);
    format!(
        "**SC{code} {}** as {}, line {} column {} of `{}`, lines {first} to {last} shown: \
         {}\n\n{fence}sh\n{body}\n{fence}\n\n",
        change.word(),
        example.dialect,
        finding.line,
        finding.column,
        example.id,
        finding.message,
    )
}

pub fn explain(before: &Findings, after: &Findings) -> String {
    let mut out = String::from("### Dropped codes\n\n");
    out.push_str(&policy(before, after));
    out.push_str("\n### Findings\n\n");
    let (groups, changed) = groups(before, after);
    if groups.is_empty() {
        out.push_str("No corpus input changes its findings for an added dialect.\n");
        return out;
    }
    let _ = writeln!(
        out,
        "Corpus inputs whose findings change for an added dialect: {changed}. \
         Each is one changed line in `rust/snapshot.txt`, under the same id.\n"
    );
    out.push_str(
        "| Code | Change | Dialects | Findings | Inputs |\n| --- | --- | --- | ---: | ---: |\n",
    );
    for ((code, change), group) in &groups {
        let dialects: Vec<&str> = group.dialects.iter().map(|(_, d)| *d).collect();
        let _ = writeln!(
            out,
            "| SC{code} | {} | {} | {} | {} |",
            change.word(),
            dialects.join(", "),
            group.findings,
            group.inputs.len()
        );
    }
    out.push_str("\n<details><summary>One example per code and change</summary>\n\n");
    let mut omitted = 0;
    for ((code, change), group) in &groups {
        let text = example(*code, *change, group);
        if out.len() + text.len() > BUDGET {
            omitted += 1;
        } else {
            out.push_str(&text);
        }
    }
    if omitted > 0 {
        let _ = writeln!(
            out,
            "{omitted} more examples are in the `validity-findings` artifact.\n"
        );
    }
    out.push_str("</details>\n");
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    fn finding(code: i64, line: i64, message: &str) -> Finding {
        Finding {
            code,
            line,
            column: 6,
            end_line: line,
            end_column: 8,
            level: "info".to_string(),
            message: message.to_string(),
        }
    }

    fn input(id: &str, script: &str, findings: &[(&str, Vec<Finding>)]) -> Input {
        Input {
            id: id.to_string(),
            script: script.to_string(),
            findings: findings
                .iter()
                .map(|(d, f)| ((*d).to_string(), f.clone()))
                .collect(),
        }
    }

    fn dropped(pairs: &[(&str, i64)]) -> Vec<(String, i64)> {
        pairs.iter().map(|(d, c)| ((*d).to_string(), *c)).collect()
    }

    const SCRIPT: &str = "#!/bin/zsh\na=1\nb=2\nc=3\necho $x\nd=4\ne=5\nf=6\ng=7\n";

    #[test]
    fn a_dropped_code_is_listed_per_dialect_with_the_findings_it_removes() {
        let quote = finding(
            2086,
            5,
            "Double quote to prevent globbing and word splitting.",
        );
        let other = finding(2034, 2, "a appears unused.");
        let before = Findings {
            dropped: dropped(&[("zsh", 2016), ("mksh", 2046)]),
            inputs: vec![input(
                "A.hs:prop_a 1",
                SCRIPT,
                &[
                    ("zsh", vec![other.clone(), quote.clone()]),
                    ("osh", vec![quote]),
                ],
            )],
        };
        let after = Findings {
            dropped: dropped(&[("zsh", 2016), ("zsh", 2086), ("osh", 2086)]),
            inputs: vec![input("A.hs:prop_a 1", SCRIPT, &[("zsh", vec![other])])],
        };
        let text = explain(&before, &after);
        assert_eq!(
            text,
            "### Dropped codes\n\n\
             | Dialect | Newly dropped | Restored | Still dropped |\n\
             | --- | --- | --- | ---: |\n\
             | zsh | SC2086 | none | 1 |\n\
             | mksh | none | SC2046 | 0 |\n\
             | osh | SC2086 | none | 0 |\n\
             \n### Findings\n\n\
             Corpus inputs whose findings change for an added dialect: 1. \
             Each is one changed line in `rust/snapshot.txt`, under the same id.\n\n\
             | Code | Change | Dialects | Findings | Inputs |\n\
             | --- | --- | --- | ---: | ---: |\n\
             | SC2086 | lost | zsh, osh | 2 | 1 |\n\
             \n<details><summary>One example per code and change</summary>\n\n\
             **SC2086 lost** as zsh, line 5 column 6 of `A.hs:prop_a 1`, lines 2 to 8 shown: \
             Double quote to prevent globbing and word splitting.\n\n\
             ```sh\na=1\nb=2\nc=3\necho $x\nd=4\ne=5\nf=6\n```\n\n\
             </details>\n"
        );
    }

    #[test]
    fn a_restored_code_shows_gained_findings_from_an_input_seen_only_after() {
        let before = Findings {
            dropped: dropped(&[("yash", 3040)]),
            inputs: Vec::new(),
        };
        let after = Findings {
            dropped: Vec::new(),
            inputs: vec![input(
                "B.hs:prop_b 2",
                "set -o errtrace\n",
                &[(
                    "yash",
                    vec![finding(
                        3040,
                        1,
                        "In POSIX sh, set option errtrace is undefined.",
                    )],
                )],
            )],
        };
        let text = explain(&before, &after);
        assert!(text.contains("| yash | none | SC3040 | 0 |"), "{text}");
        assert!(
            text.contains("| SC3040 | gained | yash | 1 | 1 |"),
            "{text}"
        );
        assert!(text.contains("```sh\nset -o errtrace\n```"), "{text}");
    }

    #[test]
    fn repeated_findings_count_once_per_occurrence() {
        let same = finding(2086, 1, "m");
        let before = Findings {
            dropped: Vec::new(),
            inputs: vec![input(
                "C 3",
                "echo $x $x\n",
                &[("zsh", vec![same.clone(), same.clone()])],
            )],
        };
        let after = Findings {
            dropped: Vec::new(),
            inputs: vec![input("C 3", "echo $x $x\n", &[("zsh", vec![same])])],
        };
        assert!(explain(&before, &after).contains("| SC2086 | lost | zsh | 1 | 1 |"));
    }

    #[test]
    fn nothing_changed_says_so_in_both_sections() {
        let same = Findings {
            dropped: dropped(&[("zsh", 2086)]),
            inputs: vec![input(
                "D 4",
                "echo\n",
                &[("zsh", vec![finding(2148, 1, "m")])],
            )],
        };
        assert_eq!(
            explain(&same, &same),
            "### Dropped codes\n\nNo added dialect drops or restores a code.\n\n\
             ### Findings\n\nNo corpus input changes its findings for an added dialect.\n"
        );
    }

    #[test]
    fn a_script_holding_a_fence_gets_a_longer_one() {
        assert_eq!(fence("echo ```"), "````");
        assert_eq!(fence("echo `x`"), "```");
    }

    #[test]
    fn examples_past_the_budget_are_counted_instead_of_printed() {
        let long = "x".repeat(BUDGET / 4);
        let inputs = (0..8)
            .map(|i| {
                input(
                    &format!("E {i}"),
                    &format!("{long}\n"),
                    &[("zsh", vec![finding(2000 + i, 1, "m")])],
                )
            })
            .collect();
        let before = Findings {
            dropped: Vec::new(),
            inputs,
        };
        let text = explain(&before, &Findings::default());
        assert!(text.len() <= BUDGET + 200, "{}", text.len());
        assert!(text.contains("more examples are in the `validity-findings` artifact."));
        assert!(text.ends_with("</details>\n"));
    }

    #[test]
    fn findings_round_trip_through_json() {
        let findings = Findings {
            dropped: dropped(&[("zsh", 2086)]),
            inputs: vec![input(
                "F 5",
                "echo $x\n",
                &[("zsh", vec![finding(2148, 1, "m")])],
            )],
        };
        let json = serde_json::to_string(&findings).unwrap();
        assert_eq!(serde_json::from_str::<Findings>(&json).unwrap(), findings);
    }
}
