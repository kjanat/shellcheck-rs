use super::ValidityArgs;
use super::docker::{self, Container, Run};
use super::matrix::{self, Cell};
use super::outcomes::{self, Outcome, Outcomes, Row};
use super::spec::{self, Kind, Spec};
use crate::port_keys;
use shellcheck_rs::Dialect;

pub fn run(args: &ValidityArgs) -> Result<bool, String> {
    let matrix = matrix::load()?;
    let specs = spec::load(&args.code)?;
    if specs.is_empty() {
        return Err("no spec matches --code".to_string());
    }
    let recorded = outcomes::load()?;
    let baseline = Baseline::of(args.record);
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
            let result = evaluate(&container, cell, s, n, baseline, &recorded);
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
    let (mut failures, drift) = compare(
        &matrix,
        &recorded,
        &rows,
        &specs,
        Coverage::of(&args.cell, &missing),
        baseline,
    );
    failures.extend(unrun_cells(&args.cell, &missing, baseline));
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
        let all_specs = spec::load(&[])?;
        all.retain_current(&all_specs, &matrix);
        let rules = super::rules::render(&all, &matrix)?;
        outcomes::save(&all, &all_specs)?;
        super::rules::save(&rules)?;
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
            Some(prev) if shipped && baseline == Baseline::Verify => failures.push(format!(
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
    const fn of(cells: &[String], missing: &[String]) -> Self {
        if cells.is_empty() && missing.is_empty() {
            Self::Matrix
        } else {
            Self::Cells
        }
    }
}

fn unrun_cells(cells: &[String], missing: &[String], baseline: Baseline) -> Option<String> {
    (cells.is_empty() && !missing.is_empty() && baseline == Baseline::Verify)
        .then(|| format!("full matrix ran without {}", missing.join(", ")))
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
    baseline: Baseline,
    recorded: &Outcomes,
) -> Result<(Outcome, String), String> {
    let dirs = [format!("/tmp/run{n}a"), format!("/tmp/run{n}b")];
    for d in &dirs {
        container.mkdir(d)?;
    }
    let result = observe(container, cell, spec, &dirs, baseline, recorded);
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
    baseline: Baseline,
    recorded: &Outcomes,
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
    let ran = if spec.observes_runtime() {
        [
            container.exec(&dirs[0], &cell.argv, &snippet)?,
            container.exec(&dirs[1], &cell.argv, &fixed)?,
        ]
    } else {
        parsed.clone()
    };
    match verdict(spec, &parsed, &ran) {
        Verdict::Claim(claim) => {
            port_check_claim(cell, spec, &snippet, &fixed, claim, baseline, recorded)
        }
        Verdict::Outcome(outcome, observed) => Ok((outcome, observed)),
    }
}

#[derive(Debug, PartialEq, Eq)]
enum Verdict {
    Claim(Claim),
    Outcome(Outcome, String),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Claim {
    Reproduces,
    Absent,
}

impl Claim {
    const fn outcome(self) -> Outcome {
        match self {
            Self::Reproduces => Outcome::Reproduces,
            Self::Absent => Outcome::Absent,
        }
    }

    fn agrees(
        self,
        code: i64,
        dialect: &str,
        recorded: &Outcomes,
        on_snippet: &[i64],
        on_fixed: &[i64],
    ) -> bool {
        let reports = on_snippet.contains(&code);
        let snippet_agrees = match self {
            Self::Reproduces => reports,
            Self::Absent => {
                // Base dialects preserve upstream portability diagnostics even when
                // a concrete interpreter implements the extension. Only added
                // dialects use measured absence to filter snippet diagnostics.
                let upstream = Dialect::from_name(dialect).is_some_and(|d| !d.is_added());
                // A versionless dialect keeps a code if another version reproduces it.
                let reproduces = recorded.row.iter().any(|row| {
                    row.code == code
                        && row.outcome == Outcome::Reproduces
                        && Dialect::from_name(&row.shell).is_some_and(|d| d.name() == dialect)
                });
                !reports || upstream || reproduces
            }
        };
        snippet_agrees && !on_fixed.contains(&code)
    }
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
        return Verdict::Claim(Claim::Reproduces);
    }
    if a_fixed && b_fixed {
        return Verdict::Claim(Claim::Absent);
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

fn port_check_claim(
    cell: &Cell,
    spec: &Spec,
    snippet: &str,
    fixed: &str,
    claim: Claim,
    baseline: Baseline,
    recorded: &Outcomes,
) -> Result<(Outcome, String), String> {
    if baseline == Baseline::Record {
        // The table is built from shell evidence, not from its previous rules.
        return Ok((claim.outcome(), String::new()));
    }
    let Some(dialect) = port_dialect(cell, spec) else {
        return Ok((claim.outcome(), String::new()));
    };
    if claim == Claim::Reproduces && spec.shell.as_deref().is_some_and(|s| !speaks(dialect, s)) {
        return Ok((claim.outcome(), String::new()));
    }
    let codes = |script: &str| -> Result<Vec<i64>, String> {
        Ok(port_keys(script, "-", Some(dialect))?
            .iter()
            .map(|k| k.code)
            .collect())
    };
    let on_snippet = codes(snippet)?;
    let on_fixed = codes(fixed)?;
    if claim.agrees(spec.code, dialect, recorded, &on_snippet, &on_fixed) {
        return Ok((claim.outcome(), String::new()));
    }
    Ok((
        Outcome::PortMiss,
        format!("port as {dialect}: snippet {on_snippet:?} fixed {on_fixed:?}"),
    ))
}

fn port_dialect<'a>(cell: &'a Cell, spec: &Spec) -> Option<&'a str> {
    let own = Dialect::from_name(&cell.shell).map(Dialect::name);
    if own.is_some() && spec.shell.as_deref() == own {
        own
    } else {
        cell.port_shell()
    }
}

fn speaks(port_shell: &str, spec_shell: &str) -> bool {
    port_shell == spec_shell
        || Dialect::from_name(port_shell)
            .is_some_and(|d| Dialect::from(d.floor()).name() == spec_shell)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn port_check(
        cell: &Cell,
        spec: &Spec,
        snippet: &str,
        fixed: &str,
    ) -> Result<(Outcome, String), String> {
        port_check_claim(
            cell,
            spec,
            snippet,
            fixed,
            Claim::Reproduces,
            Baseline::Verify,
            &Outcomes::default(),
        )
    }

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
        assert_eq!(
            verdict(&spec, &parsed, &ran),
            Verdict::Claim(Claim::Reproduces)
        );
    }

    #[test]
    fn a_parse_observe_is_absent_when_both_scripts_parse() {
        let spec = parse_spec();
        let parsed = [run_with(0, "", ""), run_with(0, "", "")];
        assert_eq!(parse_verdict(&spec, &parsed), None);
        let ran = [run_with(0, "hi\n", ""), run_with(0, "hi\n", "")];
        assert_eq!(verdict(&spec, &parsed, &ran), Verdict::Claim(Claim::Absent));
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
        assert_eq!(
            verdict(&spec, &parsed, &ran),
            Verdict::Claim(Claim::Reproduces)
        );
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
            &recorded,
            &rows,
            &[],
            Coverage::Matrix,
            Baseline::Record,
        );
        assert_eq!(failures, Vec::<String>::new());
        assert_eq!(drift.len(), 2);
        assert!(drift[0].starts_with("SC2086 bash:1 absent (recorded reproduces)"));
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
    fn absent_claims_check_added_dialects_and_every_fixed_script() {
        let mut spec = parse_spec();
        spec.code = 2086;
        let snippet = "x=\"a b\"; printf '<%s>' $x\n";
        let fixed = "x=\"a b\"; printf '<%s>' \"$x\"\n";
        // Even a spec on another floor must not bypass an absent assertion.
        assert_eq!(spec.shell.as_deref(), Some("sh"));
        let check = |shell, a, b| {
            port_check_claim(
                &cell(shell, None),
                &spec,
                a,
                b,
                Claim::Absent,
                Baseline::Verify,
                &Outcomes::default(),
            )
        };
        assert!(matches!(
            check("mksh", snippet, fixed),
            Ok((Outcome::PortMiss, _))
        ));
        assert_eq!(
            check("bash", snippet, fixed),
            Ok((Outcome::Absent, String::new()))
        );
        assert!(matches!(
            check("bash", fixed, snippet),
            Ok((Outcome::PortMiss, _))
        ));
        assert_eq!(
            check("bash", fixed, fixed),
            Ok((Outcome::Absent, String::new()))
        );
        assert_eq!(
            check("zsh", snippet, fixed),
            Ok((Outcome::Absent, String::new()))
        );
        assert_eq!(
            check("tcsh", snippet, fixed),
            Ok((Outcome::Absent, String::new()))
        );
    }

    #[test]
    fn dash_smoke_absence_preserves_upstream_portability_checks_for_all_seven_specs() {
        let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
        // CI's dash 0.5.13 run matched these fixed observables on both scripts.
        // That does not invalidate their diagnostics in generic POSIX sh mode.
        let observations = [
            (3012, "y\n"),
            (3026, "y\n"),
            (3043, "g\n"),
            (3049, "caught\ndone\n"),
            (3065, "y\n"),
            (3066, "y\n"),
            (3067, "y\n"),
        ];
        let codes: Vec<i64> = observations.iter().map(|(code, _)| *code).collect();
        let specs = spec::load_from(&root.join(crate::validity::SPECS), &codes).unwrap();
        let matrix = matrix::load_from(&root.join(crate::validity::MATRIX)).unwrap();
        let recorded = outcomes::load_from(&root.join(crate::validity::OUTCOMES)).unwrap();
        let dash = matrix.find("dash", "0.5.13").unwrap();
        assert_eq!(specs.len(), observations.len());
        let actual: Vec<_> = specs
            .iter()
            .zip(observations)
            .map(|(spec, (code, stdout))| {
                assert_eq!(spec.code, code);
                assert_eq!(port_dialect(dash, spec), Some("sh"));
                let parsed = [run_with(0, "", ""), run_with(0, "", "")];
                let ran = [run_with(0, stdout, ""), run_with(0, stdout, "")];
                assert_eq!(parse_verdict(spec, &parsed), None);
                let result = match verdict(spec, &parsed, &ran) {
                    Verdict::Claim(claim) => {
                        assert_eq!(claim, Claim::Absent);
                        assert!(
                            matches!(
                                port_check_claim(
                                    dash,
                                    spec,
                                    &spec.snippet.script,
                                    &spec.snippet.script,
                                    claim,
                                    Baseline::Verify,
                                    &recorded,
                                ),
                                Ok((Outcome::PortMiss, _))
                            ),
                            "SC{code}: a diagnostic on the fixed script must still fail"
                        );
                        port_check_claim(
                            dash,
                            spec,
                            &spec.snippet.script,
                            &spec.fixed.script,
                            claim,
                            Baseline::Verify,
                            &recorded,
                        )
                    }
                    other @ Verdict::Outcome(..) => panic!("SC{code}: {other:?}"),
                };
                (code, result)
            })
            .collect();
        let expected: Vec<_> = codes
            .into_iter()
            .map(|code| (code, Ok((Outcome::Absent, String::new()))))
            .collect();
        assert_eq!(actual, expected);
    }

    #[test]
    fn recording_shell_evidence_does_not_depend_on_the_previous_rules() {
        let mut spec = parse_spec();
        spec.code = 2086;
        spec.shell = None;
        let snippet = "x=\"a b\"; printf '<%s>' $x\n";
        let fixed = "x=\"a b\"; printf '<%s>' \"$x\"\n";
        for (shell, claim) in [("mksh", Claim::Absent), ("zsh", Claim::Reproduces)] {
            assert!(matches!(
                port_check_claim(
                    &cell(shell, None),
                    &spec,
                    snippet,
                    fixed,
                    claim,
                    Baseline::Verify,
                    &Outcomes::default(),
                ),
                Ok((Outcome::PortMiss, _))
            ));
            assert_eq!(
                port_check_claim(
                    &cell(shell, None),
                    &spec,
                    snippet,
                    fixed,
                    claim,
                    Baseline::Record,
                    &Outcomes::default(),
                ),
                Ok((claim.outcome(), String::new()))
            );
        }
    }

    #[test]
    fn absent_verification_respects_other_versions_but_not_other_dialects_or_codes() {
        let row = |code, shell: &str, version: &str, outcome| Row {
            code,
            shell: shell.to_string(),
            version: version.to_string(),
            outcome,
            observed: String::new(),
        };
        let mut recorded = Outcomes::default();
        recorded.merge(&[
            row(2086, "zsh", "5.9", Outcome::Absent),
            row(2086, "bash", "5.3", Outcome::Reproduces),
            row(2046, "zsh", "5.9", Outcome::Reproduces),
        ]);
        // Independent evidence must catch a port regression that emits a suppressed code.
        assert!(!Claim::Absent.agrees(2086, "zsh", &recorded, &[2086], &[]));
        assert!(Claim::Absent.agrees(2086, "zsh", &recorded, &[], &[]));
        recorded.merge(&[row(2086, "zsh", "5.8", Outcome::Reproduces)]);
        assert!(Claim::Absent.agrees(2086, "zsh", &recorded, &[2086], &[]));
        assert!(!Claim::Absent.agrees(2086, "zsh", &recorded, &[2086], &[2086]));

        recorded.merge(&[
            row(2086, "mksh", "1", Outcome::Absent),
            row(2086, "mksh", "2", Outcome::Reproduces),
        ]);
        let mut spec = parse_spec();
        spec.code = 2086;
        let snippet = "x=\"a b\"; printf '<%s>' $x\n";
        let fixed = "x=\"a b\"; printf '<%s>' \"$x\"\n";
        assert_eq!(
            port_check_claim(
                &cell("mksh", None),
                &spec,
                snippet,
                fixed,
                Claim::Absent,
                Baseline::Verify,
                &recorded,
            ),
            Ok((Outcome::Absent, String::new()))
        );
        assert!(matches!(
            port_check_claim(
                &cell("mksh", None),
                &spec,
                snippet,
                snippet,
                Claim::Absent,
                Baseline::Verify,
                &recorded,
            ),
            Ok((Outcome::PortMiss, _))
        ));
    }

    #[test]
    fn partial_recording_prunes_retired_rows_and_preserves_other_current_rows() {
        let matrix = matrix::Matrix {
            cell: vec![cell("bash", None), cell("zsh", None)],
        };
        let mut other_spec = parse_spec();
        other_spec.code = 3010;
        let specs = [parse_spec(), other_spec];
        let row = |code, shell: &str, version: &str| Row {
            code,
            shell: shell.to_string(),
            version: version.to_string(),
            outcome: Outcome::Reproduces,
            observed: String::new(),
        };
        let mut all = Outcomes::default();
        all.merge(&[
            row(3001, "bash", "1"),
            row(3001, "zsh", "1"),
            row(3010, "zsh", "1"),
            row(3001, "zsh", "retired-version"),
            row(3001, "retired-shell", "1"),
            row(9999, "zsh", "1"),
        ]);
        all.merge(&[Row {
            outcome: Outcome::Absent,
            ..row(3001, "bash", "1")
        }]);
        all.retain_current(&specs, &matrix);
        assert_eq!(all.row.len(), 3);
        assert_eq!(
            all.find(&row(3001, "bash", "1")).unwrap().outcome,
            Outcome::Absent
        );
        assert_eq!(
            all.find(&row(3001, "zsh", "1")).unwrap().outcome,
            Outcome::Reproduces
        );
        assert_eq!(
            all.find(&row(3010, "zsh", "1")).unwrap().outcome,
            Outcome::Reproduces
        );
        let rules = super::super::rules::render(&all, &matrix).unwrap();
        assert!(rules.contains("code: 3001,"));
        assert!(rules.contains("code: 3010,"));
        assert!(!rules.contains("9999"));
        assert!(!rules.contains("retired"));
        let report = outcomes::report(&all, &specs);
        assert!(report.contains("## SC3001"));
        assert!(report.contains("## SC3010"));
    }

    #[test]
    fn a_floor_spec_runs_the_port_in_the_dialects_on_that_floor() {
        let spec = |snippet: &str| Spec {
            code: 3010,
            claim: String::new(),
            shell: Some("sh".to_string()),
            snippet: spec::Script {
                script: snippet.to_string(),
            },
            fixed: spec::Script {
                script: String::new(),
            },
            observe: vec![],
        };
        let bashism = spec("[[ -n $1 ]]\n");
        let fixed = "[ -n \"$1\" ]\n";
        assert_eq!(
            port_check(&cell("posh", None), &bashism, "[[ -n $1 ]]\n", fixed),
            Ok((Outcome::Reproduces, String::new()))
        );
        let silent = spec("echo hi\n");
        for shell in ["posh", "yash", "netbsd-sh"] {
            assert!(
                matches!(
                    port_check(&cell(shell, None), &silent, "echo hi\n", fixed),
                    Ok((Outcome::PortMiss, _))
                ),
                "{shell}"
            );
        }
        for shell in ["zsh", "mksh", "osh"] {
            assert_eq!(
                port_check(&cell(shell, None), &silent, "echo hi\n", fixed),
                Ok((Outcome::Reproduces, String::new())),
                "{shell}"
            );
        }
        assert!(speaks("sh", "sh"));
        assert!(speaks("posh", "sh"));
        assert!(speaks("zsh", "bash"));
        assert!(!speaks("zsh", "sh"));
        assert!(!speaks("bash", "sh"));
    }

    #[test]
    fn a_spec_for_the_cells_own_shell_runs_the_port_as_that_shell() {
        let spec = |shell: &str| Spec {
            code: 3036,
            claim: String::new(),
            shell: Some(shell.to_string()),
            snippet: spec::Script {
                script: String::new(),
            },
            fixed: spec::Script {
                script: String::new(),
            },
            observe: vec![],
        };
        let dash = cell("dash", Some("sh"));
        assert_eq!(port_dialect(&dash, &spec("dash")), Some("dash"));
        assert_eq!(port_dialect(&dash, &spec("sh")), Some("sh"));
        assert_eq!(
            port_dialect(&cell("zsh-sh", Some("sh")), &spec("sh")),
            Some("sh")
        );
        let fixed = "printf 'a\\n'\n";
        assert_eq!(
            port_check(&dash, &spec("dash"), "echo -e 'a'\n", fixed),
            Ok((Outcome::Reproduces, String::new()))
        );
        assert!(matches!(
            port_check(&dash, &spec("dash"), "echo hi\n", fixed),
            Ok((Outcome::PortMiss, _))
        ));
    }

    #[test]
    fn a_full_verification_with_missing_images_fails() {
        let missing = ["zsh:5.9".to_string(), "tcsh:6.24.16".to_string()];
        assert_eq!(
            unrun_cells(&[], &missing, Baseline::Verify),
            Some("full matrix ran without zsh:5.9, tcsh:6.24.16".to_string())
        );
        assert_eq!(unrun_cells(&[], &missing, Baseline::Record), None);
        assert_eq!(
            unrun_cells(&["zsh".to_string()], &missing, Baseline::Verify),
            None
        );
        assert_eq!(unrun_cells(&[], &[], Baseline::Verify), None);
    }

    #[test]
    fn a_parse_only_spec_decides_from_the_parse_step() {
        let spec = parse_spec();
        assert!(!spec.observes_runtime());
        assert!(spec_with(Kind::Stdout, "", "hi\n").observes_runtime());
        let parsed = [run_with(2, "", "sh: 1: Syntax error"), run_with(0, "", "")];
        assert_eq!(parse_verdict(&spec, &parsed), None);
        assert_eq!(
            verdict(&spec, &parsed, &parsed.clone()),
            Verdict::Claim(Claim::Reproduces)
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
        let dash = ["dash:1".to_string()];
        assert_eq!(Coverage::of(&[], &[]), Coverage::Matrix);
        assert_eq!(Coverage::of(&dash, &[]), Coverage::Cells);
        assert_eq!(Coverage::of(&[], &dash), Coverage::Cells);
        let record = Baseline::Record;
        let (failures, _) = compare(&m, &none, &absent, &specs, Coverage::Cells, record);
        assert_eq!(failures, Vec::<String>::new());
        let (failures, _) = compare(&m, &none, &absent, &specs, Coverage::Matrix, record);
        assert_eq!(failures, vec!["SC3001 reproduces in no cell".to_string()]);
        let (failures, _) = compare(&m, &none, &reproduces, &specs, Coverage::Matrix, record);
        assert_eq!(failures, Vec::<String>::new());
    }
}
