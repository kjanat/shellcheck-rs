use super::ValidityArgs;
use super::docker::{self, Container, Run};
use super::matrix::{self, Cell};
use super::outcomes::{self, Outcome, Outcomes, Row};
use super::spec::{self, Kind, Spec};
use crate::port_keys;

pub fn run(args: &ValidityArgs) -> Result<bool, String> {
    let matrix = matrix::load()?;
    let specs = spec::load(&args.code)?;
    if specs.is_empty() {
        return Err("no spec matches --code".to_string());
    }
    let recorded = outcomes::load()?;
    let mut rows: Vec<Row> = Vec::new();
    let mut missing: Vec<String> = Vec::new();
    let mut ran = 0usize;
    for cell in matrix.cells(&args.cell) {
        let Some(reference) = docker::locate(cell) else {
            missing.push(cell.id());
            continue;
        };
        ran += 1;
        let container = Container::start(cell, &reference)?;
        for (n, s) in specs.iter().enumerate() {
            let result = evaluate(&container, cell, s, n);
            let (outcome, observed) = match result {
                Ok(pair) => pair,
                Err(e) => {
                    container.stop();
                    return Err(e);
                }
            };
            println!("{:<10} {:<20} SC{}", outcome.label(), cell.id(), s.code);
            rows.push(Row {
                code: s.code,
                shell: cell.shell.clone(),
                version: cell.version.clone(),
                outcome,
                observed,
            });
        }
        container.stop();
    }
    if ran == 0 {
        return Err(format!(
            "no cell image is available; build with `cargo validity build` ({} missing)",
            missing.len()
        ));
    }
    let (failures, drift) = compare(
        &matrix,
        &recorded,
        &rows,
        &specs,
        Coverage::of(&args.cell),
        Baseline::of(args.record),
    );
    for line in &drift {
        println!("DRIFT {line}");
    }
    for line in &failures {
        println!("FAIL {line}");
    }
    if !missing.is_empty() {
        println!("missing images: {}", missing.join(", "));
    }
    println!(
        "validity: {} cells, {} specs, {} rows, {} drift, {} failures",
        ran,
        specs.len(),
        rows.len(),
        drift.len(),
        failures.len()
    );
    if args.record {
        let mut all = recorded;
        all.merge(&rows);
        outcomes::save(&all, &specs)?;
    }
    Ok(failures.is_empty())
}

fn compare(
    matrix: &matrix::Matrix,
    recorded: &Outcomes,
    rows: &[Row],
    specs: &[Spec],
    coverage: Coverage,
    baseline: Baseline,
) -> (Vec<String>, Vec<String>) {
    let mut failures = Vec::new();
    let mut drift = Vec::new();
    for row in rows {
        let shipped = matrix
            .find(&row.shell, &row.version)
            .is_some_and(|c| c.shipped);
        let id = format!(
            "SC{} {}:{} {}",
            row.code,
            row.shell,
            row.version,
            row.outcome.label()
        );
        if shipped && row.outcome == Outcome::PortMiss {
            failures.push(format!("{id} {}", row.observed));
            continue;
        }
        match recorded.find(row) {
            Some(prev) if prev.outcome == row.outcome && prev.observed == row.observed => {}
            Some(prev) if shipped => failures.push(format!(
                "{id} (recorded {}) {}",
                prev.outcome.label(),
                row.observed
            )),
            Some(prev) => drift.push(format!("{id} (recorded {})", prev.outcome.label())),
            None if coverage == Coverage::Matrix && baseline == Baseline::Verify => {
                failures.push(format!("{id} (unrecorded)"));
            }
            None => drift.push(format!("{id} (new)")),
        }
    }
    for s in specs {
        let mine: Vec<&Row> = rows.iter().filter(|r| r.code == s.code).collect();
        if coverage == Coverage::Matrix
            && !mine.is_empty()
            && mine.iter().all(|r| r.outcome != Outcome::Reproduces)
        {
            failures.push(format!("SC{} reproduces in no cell", s.code));
        }
    }
    (failures, drift)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Coverage {
    Matrix,
    Cells,
}

impl Coverage {
    const fn of(cells: &[String]) -> Self {
        if cells.is_empty() {
            Self::Matrix
        } else {
            Self::Cells
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Baseline {
    Verify,
    Record,
}

impl Baseline {
    const fn of(record: bool) -> Self {
        if record { Self::Record } else { Self::Verify }
    }
}

fn evaluate(
    container: &Container,
    cell: &Cell,
    spec: &Spec,
    n: usize,
) -> Result<(Outcome, String), String> {
    let dirs = [format!("/tmp/run{n}a"), format!("/tmp/run{n}b")];
    for d in &dirs {
        container.mkdir(d)?;
    }
    let result = observe(container, cell, spec, &dirs);
    for d in &dirs {
        container.remove(d)?;
    }
    result
}

fn observe(
    container: &Container,
    cell: &Cell,
    spec: &Spec,
    dirs: &[String; 2],
) -> Result<(Outcome, String), String> {
    let snippet = format!("{}\n", spec.snippet.script);
    let fixed = format!("{}\n", spec.fixed.script);
    let mut parse_argv = cell.argv.clone();
    parse_argv.extend(cell.parse.iter().cloned());
    let parsed = [
        container.exec(&dirs[0], &parse_argv, &snippet)?,
        container.exec(&dirs[0], &parse_argv, &fixed)?,
    ];
    if let Some(outcome) = parse_verdict(spec, &parsed) {
        return Ok(outcome);
    }
    let ran = [
        container.exec(&dirs[0], &cell.argv, &snippet)?,
        container.exec(&dirs[1], &cell.argv, &fixed)?,
    ];
    match verdict(spec, &parsed, &ran) {
        Verdict::Snippet => port_check(cell, spec, &snippet, &fixed),
        Verdict::Outcome(outcome, observed) => Ok((outcome, observed)),
    }
}

#[derive(Debug, PartialEq, Eq)]
enum Verdict {
    Snippet,
    Outcome(Outcome, String),
}

fn parse_verdict(spec: &Spec, parsed: &[Run; 2]) -> Option<(Outcome, String)> {
    if parsed.iter().any(|r| r.timed_out) {
        return Some((Outcome::Timeout, "parse".to_string()));
    }
    if parsed[0].status != 0 && !spec.observes_parse() {
        return Some((Outcome::Unparsable, first_line(&parsed[0].stderr)));
    }
    if parsed[1].status != 0 {
        return Some((Outcome::Unparsable, first_line(&parsed[1].stderr)));
    }
    None
}

fn verdict(spec: &Spec, parsed: &[Run; 2], ran: &[Run; 2]) -> Verdict {
    if ran.iter().any(|r| r.timed_out) {
        return Verdict::Outcome(Outcome::Timeout, String::new());
    }
    let holds = |i: usize, expected: fn(&spec::Observe) -> &str| {
        spec.observe
            .iter()
            .all(|o| matches(&ran[i], &parsed[i], o.kind, expected(o)))
    };
    let a_snippet = holds(0, |o| &o.snippet);
    let a_fixed = holds(0, |o| &o.fixed);
    let b_fixed = holds(1, |o| &o.fixed);
    if a_snippet && b_fixed {
        return Verdict::Snippet;
    }
    if a_fixed && b_fixed {
        return Verdict::Outcome(Outcome::Absent, String::new());
    }
    Verdict::Outcome(
        Outcome::Differs,
        format!("snippet {} fixed {}", render(&ran[0]), render(&ran[1])),
    )
}

fn matches(run: &Run, parsed: &Run, kind: Kind, expected: &str) -> bool {
    match kind {
        Kind::Stdout => run.stdout == expected,
        Kind::Status => run.status.to_string() == expected,
        Kind::StderrContains => run.stderr.contains(expected),
        Kind::Parse => parse_label(parsed) == expected,
    }
}

const fn parse_label(parsed: &Run) -> &'static str {
    if parsed.status == 0 {
        spec::PARSE_ACCEPTED
    } else {
        spec::PARSE_REJECTED
    }
}

fn render(run: &Run) -> String {
    format!(
        "[status {} stdout {:?} stderr {:?}]",
        run.status,
        run.stdout,
        first_line(&run.stderr)
    )
}

fn first_line(text: &str) -> String {
    text.lines().next().unwrap_or("").trim().to_string()
}

fn port_check(
    cell: &Cell,
    spec: &Spec,
    snippet: &str,
    fixed: &str,
) -> Result<(Outcome, String), String> {
    let Some(dialect) = cell.port_shell() else {
        return Ok((Outcome::Reproduces, String::new()));
    };
    if spec.shell.as_deref().is_some_and(|s| s != dialect) {
        return Ok((Outcome::Reproduces, String::new()));
    }
    let codes = |script: &str| -> Result<Vec<i64>, String> {
        Ok(port_keys(script, "-", Some(dialect))?
            .iter()
            .map(|k| k.code)
            .collect())
    };
    let on_snippet = codes(snippet)?;
    let on_fixed = codes(fixed)?;
    if on_snippet.contains(&spec.code) && !on_fixed.contains(&spec.code) {
        return Ok((Outcome::Reproduces, String::new()));
    }
    Ok((
        Outcome::PortMiss,
        format!("port as {dialect}: snippet {on_snippet:?} fixed {on_fixed:?}"),
    ))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn run_with(status: i32, stdout: &str, stderr: &str) -> Run {
        Run {
            status,
            stdout: stdout.to_string(),
            stderr: stderr.to_string(),
            timed_out: false,
        }
    }

    #[test]
    fn observables_compare_by_kind() {
        let r = run_with(3, "a\n", "oops: bad\nmore");
        let parsed = run_with(0, "", "");
        assert!(matches(&r, &parsed, Kind::Stdout, "a\n"));
        assert!(!matches(&r, &parsed, Kind::Stdout, "a"));
        assert!(matches(&r, &parsed, Kind::Status, "3"));
        assert!(matches(&r, &parsed, Kind::StderrContains, "bad"));
        assert!(matches(&r, &parsed, Kind::Parse, "accepted"));
        assert!(matches(
            &r,
            &run_with(2, "", "Syntax error"),
            Kind::Parse,
            "rejected"
        ));
        assert_eq!(first_line(&r.stderr), "oops: bad");
    }

    fn spec_with(kind: Kind, snippet: &str, fixed: &str) -> Spec {
        Spec {
            code: 3001,
            claim: String::new(),
            shell: Some("sh".to_string()),
            snippet: spec::Script {
                script: "cat <(echo hi)".to_string(),
            },
            fixed: spec::Script {
                script: "echo hi | cat".to_string(),
            },
            observe: vec![spec::Observe {
                kind,
                snippet: snippet.to_string(),
                fixed: fixed.to_string(),
            }],
        }
    }

    fn parse_spec() -> Spec {
        spec_with(Kind::Parse, "rejected", "accepted")
    }

    #[test]
    fn a_parse_observe_reproduces_when_only_the_snippet_is_rejected() {
        let spec = parse_spec();
        let parsed = [run_with(2, "", "sh: 1: Syntax error"), run_with(0, "", "")];
        assert_eq!(parse_verdict(&spec, &parsed), None);
        let ran = [
            run_with(2, "", "sh: 1: Syntax error"),
            run_with(0, "hi\n", ""),
        ];
        assert_eq!(verdict(&spec, &parsed, &ran), Verdict::Snippet);
    }

    #[test]
    fn a_parse_observe_is_absent_when_both_scripts_parse() {
        let spec = parse_spec();
        let parsed = [run_with(0, "", ""), run_with(0, "", "")];
        assert_eq!(parse_verdict(&spec, &parsed), None);
        let ran = [run_with(0, "hi\n", ""), run_with(0, "hi\n", "")];
        assert_eq!(
            verdict(&spec, &parsed, &ran),
            Verdict::Outcome(Outcome::Absent, String::new())
        );
    }

    #[test]
    fn a_parse_observe_is_unparsable_when_the_fix_is_rejected() {
        let spec = parse_spec();
        let parsed = [
            run_with(2, "", "sh: 1: Syntax error: \"(\" unexpected"),
            run_with(2, "", "sh: 1: Syntax error: \"|\" unexpected"),
        ];
        assert_eq!(
            parse_verdict(&spec, &parsed),
            Some((
                Outcome::Unparsable,
                "sh: 1: Syntax error: \"|\" unexpected".to_string()
            ))
        );
    }

    #[test]
    fn without_a_parse_observe_a_rejected_snippet_is_unparsable() {
        let spec = spec_with(Kind::Stdout, "", "hi\n");
        let parsed = [
            run_with(2, "", "sh: 1: Syntax error\nmore"),
            run_with(0, "", ""),
        ];
        assert_eq!(
            parse_verdict(&spec, &parsed),
            Some((Outcome::Unparsable, "sh: 1: Syntax error".to_string()))
        );
        let parsed = [run_with(0, "", ""), run_with(0, "", "")];
        assert_eq!(parse_verdict(&spec, &parsed), None);
        let ran = [run_with(0, "", ""), run_with(0, "hi\n", "")];
        assert_eq!(verdict(&spec, &parsed, &ran), Verdict::Snippet);
        let ran = [run_with(0, "x\n", ""), run_with(0, "hi\n", "")];
        assert!(matches!(
            verdict(&spec, &parsed, &ran),
            Verdict::Outcome(Outcome::Differs, _)
        ));
    }

    #[test]
    fn a_shipped_cell_fails_on_change_and_an_unshipped_one_drifts() {
        let mut m = matrix::Matrix::default();
        for (shell, shipped) in [("bash", true), ("zsh", false)] {
            m.cell.push(Cell {
                shell: shell.to_string(),
                version: "1".to_string(),
                image: String::new(),
                digest: String::new(),
                base: String::new(),
                dockerfile: shell.to_string(),
                argv: vec![],
                parse: vec![],
                shipped,
                vm: false,
                dialect: None,
                source: matrix::SourcePin::Crate {
                    version: "1".to_string(),
                },
            });
        }
        let row = |shell: &str, outcome: Outcome| Row {
            code: 2086,
            shell: shell.to_string(),
            version: "1".to_string(),
            outcome,
            observed: String::new(),
        };
        let mut recorded = Outcomes::default();
        recorded.merge(&[
            row("bash", Outcome::Reproduces),
            row("zsh", Outcome::Reproduces),
        ]);
        let rows = [row("bash", Outcome::Absent), row("zsh", Outcome::Absent)];
        let (failures, drift) = compare(
            &m,
            &recorded,
            &rows,
            &[],
            Coverage::Matrix,
            Baseline::Verify,
        );
        assert_eq!(failures.len(), 1);
        assert!(failures[0].starts_with("SC2086 bash:1 absent"));
        assert_eq!(drift.len(), 1);
        assert!(drift[0].starts_with("SC2086 zsh:1 absent"));
        let (failures, drift) = compare(
            &m,
            &Outcomes::default(),
            &rows,
            &[],
            Coverage::Matrix,
            Baseline::Record,
        );
        assert_eq!(failures, Vec::<String>::new());
        assert_eq!(drift.len(), 2);
    }

    #[test]
    fn an_unrecorded_row_fails_only_a_full_matrix_verification() {
        let m = matrix::Matrix::default();
        let rows = [Row {
            code: 3001,
            shell: "dash".to_string(),
            version: "1".to_string(),
            outcome: Outcome::Reproduces,
            observed: String::new(),
        }];
        let none = Outcomes::default();
        let (failures, drift) = compare(&m, &none, &rows, &[], Coverage::Matrix, Baseline::Verify);
        assert_eq!(
            failures,
            vec!["SC3001 dash:1 reproduces (unrecorded)".to_string()]
        );
        assert_eq!(drift, Vec::<String>::new());
        for (coverage, baseline) in [
            (Coverage::Matrix, Baseline::Record),
            (Coverage::Cells, Baseline::Verify),
            (Coverage::Cells, Baseline::Record),
        ] {
            let (failures, drift) = compare(&m, &none, &rows, &[], coverage, baseline);
            assert_eq!(failures, Vec::<String>::new(), "{coverage:?} {baseline:?}");
            assert_eq!(drift, vec!["SC3001 dash:1 reproduces (new)".to_string()]);
        }
        assert_eq!(Baseline::of(true), Baseline::Record);
        assert_eq!(Baseline::of(false), Baseline::Verify);
    }

    fn cell(shell: &str, dialect: Option<&str>) -> Cell {
        Cell {
            shell: shell.to_string(),
            version: "1".to_string(),
            image: String::new(),
            digest: String::new(),
            base: String::new(),
            dockerfile: shell.to_string(),
            argv: vec![],
            parse: vec![],
            shipped: true,
            vm: false,
            dialect: dialect.map(str::to_string),
            source: matrix::SourcePin::Crate {
                version: "1".to_string(),
            },
        }
    }

    #[test]
    fn the_port_checks_a_cell_as_its_stand_in_else_as_its_own_shell() {
        assert_eq!(cell("dash", Some("sh")).port_shell(), Some("sh"));
        assert_eq!(cell("zsh-sh", Some("sh")).port_shell(), Some("sh"));
        assert_eq!(cell("zsh", None).port_shell(), Some("zsh"));
        assert_eq!(cell("freebsd-sh", None).port_shell(), Some("freebsd-sh"));
        assert_eq!(cell("tcsh", None).port_shell(), None);
    }

    #[test]
    fn an_added_dialect_cell_runs_the_port_assertions() {
        let spec = Spec {
            code: 2086,
            claim: String::new(),
            shell: None,
            snippet: spec::Script {
                script: String::new(),
            },
            fixed: spec::Script {
                script: String::new(),
            },
            observe: vec![],
        };
        let snippet = "x=\"a b\"; printf '<%s>' $x\n";
        let fixed = "x=\"a b\"; printf '<%s>' \"$x\"\n";
        assert_eq!(
            port_check(&cell("mksh", None), &spec, snippet, fixed),
            Ok((Outcome::Reproduces, String::new()))
        );
        assert!(matches!(
            port_check(&cell("zsh", None), &spec, snippet, fixed),
            Ok((Outcome::PortMiss, _))
        ));
        assert_eq!(
            port_check(&cell("tcsh", None), &spec, snippet, fixed),
            Ok((Outcome::Reproduces, String::new()))
        );
    }

    #[test]
    fn a_spec_must_reproduce_somewhere_only_when_the_run_covers_the_matrix() {
        let row = |outcome: Outcome| Row {
            code: 3001,
            shell: "dash".to_string(),
            version: "1".to_string(),
            outcome,
            observed: String::new(),
        };
        let specs = [parse_spec()];
        let m = matrix::Matrix::default();
        let none = Outcomes::default();
        let absent = [row(Outcome::Absent)];
        let reproduces = [row(Outcome::Reproduces)];
        assert_eq!(Coverage::of(&[]), Coverage::Matrix);
        assert_eq!(Coverage::of(&["dash:1".to_string()]), Coverage::Cells);
        let record = Baseline::Record;
        let (failures, _) = compare(&m, &none, &absent, &specs, Coverage::Cells, record);
        assert_eq!(failures, Vec::<String>::new());
        let (failures, _) = compare(&m, &none, &absent, &specs, Coverage::Matrix, record);
        assert_eq!(failures, vec!["SC3001 reproduces in no cell".to_string()]);
        let (failures, _) = compare(&m, &none, &reproduces, &specs, Coverage::Matrix, record);
        assert_eq!(failures, Vec::<String>::new());
    }
}
