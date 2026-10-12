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
    let (failures, drift) = compare(&matrix, &recorded, &rows, &specs);
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
            None => drift.push(format!("{id} (new)")),
        }
    }
    for s in specs {
        let mine: Vec<&Row> = rows.iter().filter(|r| r.code == s.code).collect();
        if !mine.is_empty() && mine.iter().all(|r| r.outcome != Outcome::Reproduces) {
            failures.push(format!("SC{} reproduces in no cell", s.code));
        }
    }
    (failures, drift)
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
    for script in [&snippet, &fixed] {
        let r = container.exec(&dirs[0], &parse_argv, script)?;
        if r.timed_out {
            return Ok((Outcome::Timeout, "parse".to_string()));
        }
        if r.status != 0 {
            return Ok((Outcome::Unparsable, first_line(&r.stderr)));
        }
    }
    let a = container.exec(&dirs[0], &cell.argv, &snippet)?;
    let b = container.exec(&dirs[1], &cell.argv, &fixed)?;
    if a.timed_out || b.timed_out {
        return Ok((Outcome::Timeout, String::new()));
    }
    let a_snippet = spec.observe.iter().all(|o| matches(&a, o.kind, &o.snippet));
    let a_fixed = spec.observe.iter().all(|o| matches(&a, o.kind, &o.fixed));
    let b_fixed = spec.observe.iter().all(|o| matches(&b, o.kind, &o.fixed));
    if a_snippet && b_fixed {
        return port_check(cell, spec, &snippet, &fixed);
    }
    if a_fixed && b_fixed {
        return Ok((Outcome::Absent, String::new()));
    }
    Ok((
        Outcome::Differs,
        format!("snippet {} fixed {}", render(&a), render(&b)),
    ))
}

fn matches(run: &Run, kind: Kind, expected: &str) -> bool {
    match kind {
        Kind::Stdout => run.stdout == expected,
        Kind::Status => run.status.to_string() == expected,
        Kind::StderrContains => run.stderr.contains(expected),
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
    let Some(dialect) = cell.dialect.as_deref() else {
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
        assert!(matches(&r, Kind::Stdout, "a\n"));
        assert!(!matches(&r, Kind::Stdout, "a"));
        assert!(matches(&r, Kind::Status, "3"));
        assert!(matches(&r, Kind::StderrContains, "bad"));
        assert_eq!(first_line(&r.stderr), "oops: bad");
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
        let (failures, drift) = compare(&m, &recorded, &rows, &[]);
        assert_eq!(failures.len(), 1);
        assert!(failures[0].starts_with("SC2086 bash:1 absent"));
        assert_eq!(drift.len(), 1);
        assert!(drift[0].starts_with("SC2086 zsh:1 absent"));
        let (failures, drift) = compare(&m, &Outcomes::default(), &rows, &[]);
        assert_eq!(failures, Vec::<String>::new());
        assert_eq!(drift.len(), 2);
    }
}
