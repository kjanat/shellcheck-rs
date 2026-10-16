//! External validity: do the tools agree with the shells they lint for?
//!
//! `gate` and `fuzz` establish *internal* validity — the port says what the
//! Haskell says. Both could be wrong together, and on a parse decision that is
//! not hypothetical: ShellCheck rejects `! # comment`, which bash runs.
//!
//! This mode asks the shells instead. For each script it compares two verdicts
//! per dialect:
//!
//! * the shell's: `<shell> -n`, which parses without running anything;
//! * each tool's: whether it reported the fatal parse trio (SC1073/SC1009/
//!   SC1072), which is exactly when it refuses to analyse the file.
//!
//! and sorts the disagreements into the two that matter:
//!
//! * **rejects-valid** — the shell accepts the script, the tool refuses to
//!   parse it. The expensive direction: the user gets no analysis at all for a
//!   script that runs.
//! * **accepts-invalid** — the shell rejects it, the tool analyses it happily.
//!   A syntax error the user is not told about.
//!
//! Both tools are measured the same way, so the oracle's own numbers are the
//! baseline: the port should be no worse, and where it is better that is a
//! sanctioned deviation (see [`crate::deviations`]).
//!
//! The shells are the validity matrix's cells (`validity/matrix.toml`), each
//! run in the same isolated container the validity runner uses. The port
//! checks a cell as its shell, or as the cell's `dialect` for an emulation
//! cell such as `zsh --emulate sh`. The oracle checks a cell only when it has
//! a `dialect`; upstream has no `--shell` for the others. A VM cell is
//! skipped. Host binaries, where installed, give the four-dialect summary at
//! the end.
//!
//! ## What this does not prove
//!
//! `-n` is a syntax check. A script can parse and still be nonsense at runtime,
//! and shells differ in what they defer to runtime, so "accepts" here is a
//! weaker claim than "works". The host dialect mapping is also a judgement
//! call: `sh` is checked with dash, which is a POSIX shell but not *the* POSIX
//! shell, and `busybox` with `busybox sh`. Where a shell is not installed its
//! dialect is skipped and the report says so rather than quietly passing.

use std::cell::RefCell;
use std::collections::BTreeMap;
use std::io::Write;
use std::process::{Command, Stdio};

use shellcheck_rs::Dialect;

use crate::corpus;
use crate::fuzz::{Rng, generate};
use crate::oracle::Oracle;
use crate::validity::docker::{self, Container};
use crate::validity::matrix::{self, Cell, version_cmp};
use crate::{Args, port_keys};

/// ShellCheck's dialects, and the interpreter that speaks each one.
///
/// `ksh` is AT&T ksh93, the shell ShellCheck's ksh support is written against —
/// mksh is a different shell and is deliberately not used as a stand-in.
const DIALECTS: [(&str, &str, &[&str]); 4] = [
    ("bash", "bash", &["-n"]),
    ("sh", "dash", &["-n"]),
    ("ksh", "ksh93", &["-n"]),
    ("busybox", "busybox", &["sh", "-n"]),
];

/// The codes that mean "this file does not parse, so nothing was analysed".
const FATAL: [i64; 3] = [1073, 1009, 1072];

/// The scratch directory each cell's scripts are parsed from.
const DIR: &str = "/tmp/shells";

#[derive(Default)]
struct Tally {
    checked: usize,
    rejects_valid: usize,
    accepts_invalid: usize,
    /// One smallest example of each disagreement, to make the number actionable.
    example_rejects_valid: Option<String>,
    example_accepts_invalid: Option<String>,
}

/// One cell's numbers: the port's, and the oracle's where the cell has an
/// upstream dialect.
struct CellTally {
    id: String,
    port: Tally,
    oracle: Option<Tally>,
}

/// The oracle's codes per script, `None` where it crashed.
type OracleCodes = Vec<Option<Vec<i64>>>;

/// The oracle run for a dialect over a list of scripts.
type AskOracle<'a> = &'a dyn Fn(&str, &[String]) -> Result<OracleCodes, String>;

/// Ask a shell whether a script parses. `None` when the shell cannot be run at
/// all, which the caller reports rather than silently treating as agreement.
fn shell_parses(program: &str, args: &[&str], script: &str) -> Option<bool> {
    let mut child = Command::new(program)
        .args(args)
        .stdin(Stdio::piped())
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .spawn()
        .ok()?;
    child.stdin.as_mut()?.write_all(script.as_bytes()).ok()?;
    Some(child.wait().ok()?.success())
}

fn tool_parses(codes: &[i64]) -> bool {
    !codes.iter().any(|c| FATAL.contains(c))
}

fn note(slot: &mut Option<String>, script: &str) {
    match slot {
        Some(existing) if existing.len() <= script.len() => {}
        _ => *slot = Some(script.to_string()),
    }
}

fn record(tally: &mut Tally, shell_ok: bool, codes: &[i64], script: &str) {
    tally.checked += 1;
    match (shell_ok, tool_parses(codes)) {
        (true, false) => {
            tally.rejects_valid += 1;
            note(&mut tally.example_rejects_valid, script);
        }
        (false, true) => {
            tally.accepts_invalid += 1;
            note(&mut tally.example_accepts_invalid, script);
        }
        _ => {}
    }
}

fn codes(keys: &[crate::CommentKey]) -> Vec<i64> {
    keys.iter().map(|k| k.code).collect()
}

/// The `--shell` the port checks a cell as: the cell's shell when the port
/// knows it, else the upstream dialect the cell stands in for.
fn port_dialect(cell: &Cell) -> Option<&str> {
    Dialect::from_name(&cell.shell)
        .map(Dialect::name)
        .or(cell.dialect.as_deref())
}

fn ordered<'a>(cells: impl Iterator<Item = &'a Cell>) -> Vec<&'a Cell> {
    let mut cells: Vec<&Cell> = cells.collect();
    cells.sort_by(|a, b| {
        a.shell
            .cmp(&b.shell)
            .then_with(|| version_cmp(&a.version, &b.version))
    });
    cells
}

/// The image to run a cell in, or why the cell is skipped.
fn plan(cell: &Cell, locate: impl Fn(&Cell) -> Option<String>) -> Result<String, &'static str> {
    if cell.vm {
        return Err("vm cell, skipped");
    }
    if port_dialect(cell).is_none() {
        return Err("no port dialect");
    }
    locate(cell).ok_or("no image")
}

fn measure_cell(
    cell: &Cell,
    scripts: &[String],
    shell: &mut dyn FnMut(&str) -> Result<Option<bool>, String>,
    oracle: AskOracle<'_>,
) -> Result<CellTally, String> {
    let dialect = port_dialect(cell).ok_or_else(|| format!("{}: no port dialect", cell.id()))?;
    let oracle_codes = match cell.dialect.as_deref() {
        Some(upstream) => Some(oracle(upstream, scripts)?),
        None => None,
    };
    let mut port = Tally::default();
    let mut oracle_tally = oracle_codes.as_ref().map(|_| Tally::default());
    for (i, script) in scripts.iter().enumerate() {
        let Some(shell_ok) = shell(script)? else {
            continue;
        };
        let pcodes = codes(&port_keys(script, "-", Some(dialect))?);
        record(&mut port, shell_ok, &pcodes, script);
        if let (Some(tally), Some(all)) = (&mut oracle_tally, &oracle_codes)
            && let Some(ocodes) = &all[i]
        {
            record(tally, shell_ok, ocodes, script);
        }
    }
    Ok(CellTally {
        id: cell.id(),
        port,
        oracle: oracle_tally,
    })
}

fn in_container(
    container: &Container,
    cell: &Cell,
    scripts: &[String],
    oracle: AskOracle<'_>,
) -> Result<CellTally, String> {
    container.mkdir(DIR)?;
    let mut argv = cell.argv.clone();
    argv.extend(cell.parse.iter().cloned());
    let mut shell = |script: &str| -> Result<Option<bool>, String> {
        let run = container.exec(DIR, &argv, script)?;
        Ok((!run.timed_out).then_some(run.status == 0))
    };
    measure_cell(cell, scripts, &mut shell, oracle)
}

fn oracle_codes(oracle: &Oracle, dialect: &str, scripts: &[String]) -> Result<OracleCodes, String> {
    let named: Vec<(String, String)> = scripts.iter().map(|s| (oracle.name(), s.clone())).collect();
    let by_name = oracle.check(&named, Some(dialect))?;
    Ok(named
        .iter()
        .map(|(name, _)| by_name.get(name).map(|c| codes(&crate::oracle_keys(c))))
        .collect())
}

const CELL_HEADER: &str = "cell                  scripts       rejects-valid     accepts-invalid";

fn skip_line(cell: &Cell, why: &str) -> String {
    format!("{:<20} {why}", cell.id())
}

fn cell_line(t: &CellTally) -> String {
    let oracle = |count: fn(&Tally) -> usize| {
        t.oracle
            .as_ref()
            .map_or_else(|| "-".to_string(), |o| format!("o:{}", count(o)))
    };
    let mut line = format!(
        "{:<20} {:>8}  {:>8} / {:<7} {:>8} / {:<7}",
        t.id,
        t.port.checked,
        t.port.rejects_valid,
        oracle(|o| o.rejects_valid),
        t.port.accepts_invalid,
        oracle(|o| o.accepts_invalid),
    );
    if t.oracle.is_none() {
        line.push_str("  no upstream dialect");
    }
    line.trim_end().to_string()
}

pub fn run(args: &Args) -> Result<bool, String> {
    let oracle = Oracle::new(args.oracle())?;
    println!(
        "{}",
        crate::oracle::verify(&oracle, &args.repo, args.any_oracle_version())?
    );

    // The same inputs the fuzzer uses: upstream's property scripts, plus
    // generated and mutated shell.
    let src = std::path::Path::new(&args.repo).join("src/ShellCheck");
    let seeds: Vec<String> = corpus::extract(&src)
        .map(|e| e.into_iter().map(|x| x.script).collect())
        .unwrap_or_default();
    let mut rng = Rng::new(args.fuzzing.seed.wrapping_add(7));
    let mut scripts: Vec<String> = seeds.clone();
    for _ in 0..args.fuzzing.iterations {
        scripts.push(generate(&mut rng, &seeds));
    }

    let matrix = matrix::load()?;
    let cells = ordered(matrix.cells(&args.validity.cell));
    let cached: RefCell<BTreeMap<String, OracleCodes>> = RefCell::new(BTreeMap::new());
    let ask = |dialect: &str, scripts: &[String]| -> Result<OracleCodes, String> {
        if let Some(found) = cached.borrow().get(dialect) {
            return Ok(found.clone());
        }
        let fresh = oracle_codes(&oracle, dialect, scripts)?;
        cached
            .borrow_mut()
            .insert(dialect.to_string(), fresh.clone());
        Ok(fresh)
    };
    println!("\n{CELL_HEADER}");
    for cell in cells {
        let reference = match plan(cell, docker::locate) {
            Ok(reference) => reference,
            Err(why) => {
                println!("{}", skip_line(cell, why));
                continue;
            }
        };
        let container = Container::start(cell, &reference)?;
        let measured = in_container(&container, cell, &scripts, &ask);
        container.stop();
        println!("{}", cell_line(&measured?));
    }

    let mut tallies: Tallies = BTreeMap::new();
    let mut missing: Vec<&str> = Vec::new();

    for (dialect, program, flags) in DIALECTS {
        if shell_parses(program, flags, ":\n").is_none() {
            missing.push(dialect);
            continue;
        }
        // One oracle invocation per batch of scripts, as everywhere else.
        for chunk in scripts.chunks(crate::oracle::BATCH) {
            let named: Vec<(String, String)> =
                chunk.iter().map(|s| (oracle.name(), s.clone())).collect();
            let by_name = oracle.check(&named, Some(dialect))?;
            for (name, script) in &named {
                let Some(ocomments) = by_name.get(name) else {
                    continue;
                };
                let Some(shell_ok) = shell_parses(program, flags, script) else {
                    continue;
                };
                let ocodes = codes(&crate::oracle_keys(ocomments));
                let path = oracle.dir().join(name);
                let pcodes = codes(&port_keys(script, &path.to_string_lossy(), Some(dialect))?);

                let (oracle_tally, port_tally) = tallies.entry(dialect).or_default();
                record(oracle_tally, shell_ok, &ocodes, script);
                record(port_tally, shell_ok, &pcodes, script);
            }
        }
    }

    report(&tallies, &missing);

    // This mode reports; it does not gate. Both tools disagree with the shells
    // in both directions today, by design in places (ShellCheck rejects some
    // valid-but-awful syntax on purpose), so a threshold would be arbitrary
    // until the numbers have been read and triaged.
    Ok(true)
}

/// Per dialect: the oracle's tally, then the port's.
type Tallies<'a> = BTreeMap<&'a str, (Tally, Tally)>;

fn report(tallies: &Tallies<'_>, missing: &[&str]) {
    println!(
        "\nexternal validity: does each tool's idea of \"this parses\" match the shell's?\n\
         (rejects-valid = shell runs it, tool refuses to analyse; \
         accepts-invalid = shell rejects it, tool analyses anyway)\n"
    );
    println!(
        "{:<9} {:>8}  {:>18} {:>18}",
        "dialect", "scripts", "rejects-valid", "accepts-invalid"
    );
    for (dialect, _, _) in DIALECTS {
        let Some((o, p)) = tallies.get(dialect) else {
            continue;
        };
        println!(
            "{dialect:<9} {:>8}  {:>8} / {:<7} {:>8} / {:<7}",
            p.checked,
            format!("{}", p.rejects_valid),
            format!("o:{}", o.rejects_valid),
            format!("{}", p.accepts_invalid),
            format!("o:{}", o.accepts_invalid),
        );
    }
    if !missing.is_empty() {
        println!(
            "\nnot measured (interpreter not installed): {}",
            missing.join(", ")
        );
    }
    for (dialect, _, _) in DIALECTS {
        let Some((_, p)) = tallies.get(dialect) else {
            continue;
        };
        if let Some(s) = &p.example_rejects_valid {
            println!("\n{dialect}: port rejects, {dialect} runs it:\n  {s:?}");
        }
        if let Some(s) = &p.example_accepts_invalid {
            println!("\n{dialect}: port analyses, {dialect} rejects it:\n  {s:?}");
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::validity::matrix::SourcePin;

    fn cell(shell: &str, version: &str, dialect: Option<&str>) -> Cell {
        Cell {
            shell: shell.to_string(),
            version: version.to_string(),
            image: format!("ghcr.io/x/shell-{shell}:{version}"),
            digest: String::new(),
            base: String::new(),
            dockerfile: shell.to_string(),
            argv: vec![shell.to_string()],
            parse: vec!["-n".to_string()],
            shipped: false,
            vm: false,
            dialect: dialect.map(str::to_string),
            source: SourcePin::Crate {
                version: version.to_string(),
            },
        }
    }

    fn scripts(list: &[&str]) -> Vec<String> {
        list.iter().map(ToString::to_string).collect()
    }

    #[test]
    fn a_tally_counts_each_disagreement_once_and_keeps_the_smallest_example() {
        let mut t = Tally::default();
        record(&mut t, true, &[2086], "ok");
        record(&mut t, false, &[1073], "both reject");
        record(&mut t, true, &[1073, 1072], "longer rejected");
        record(&mut t, true, &[1009], "{}");
        record(&mut t, false, &[], "shell says no");
        assert_eq!(t.checked, 5);
        assert_eq!(t.rejects_valid, 2);
        assert_eq!(t.accepts_invalid, 1);
        assert_eq!(t.example_rejects_valid.as_deref(), Some("{}"));
        assert_eq!(t.example_accepts_invalid.as_deref(), Some("shell says no"));
    }

    #[test]
    fn cells_report_in_shell_then_version_order() {
        let cells = [
            cell("zsh-sh", "5.9", Some("sh")),
            cell("dash", "0.5.10.2", Some("sh")),
            cell("zsh", "5.9", None),
            cell("dash", "0.5.9.1", Some("sh")),
            cell("bash", "5.3", Some("bash")),
        ];
        let ids: Vec<String> = ordered(cells.iter()).iter().map(|c| c.id()).collect();
        assert_eq!(
            ids,
            [
                "bash:5.3",
                "dash:0.5.9.1",
                "dash:0.5.10.2",
                "zsh:5.9",
                "zsh-sh:5.9"
            ]
        );
    }

    #[test]
    fn a_vm_cell_is_skipped_before_any_image_lookup() {
        let mut guest = cell("netbsd-sh", "10.2", None);
        guest.vm = true;
        let why = plan(&guest, |_| panic!("a vm cell asks docker for nothing")).unwrap_err();
        assert_eq!(why, "vm cell, skipped");
        assert_eq!(
            skip_line(&guest, why),
            "netbsd-sh:10.2       vm cell, skipped"
        );
    }

    #[test]
    fn a_cell_without_a_port_dialect_is_skipped_and_a_missing_image_is_named() {
        let tcsh = cell("tcsh", "6.24.16", None);
        assert_eq!(plan(&tcsh, |_| None), Err("no port dialect"));
        let dash = cell("dash", "0.5.12", Some("sh"));
        assert_eq!(plan(&dash, |_| None), Err("no image"));
        assert_eq!(
            plan(&dash, |c| Some(c.image.clone())),
            Ok("ghcr.io/x/shell-dash:0.5.12".to_string())
        );
    }

    #[test]
    fn the_port_checks_a_cell_as_its_shell_or_as_its_stand_in() {
        assert_eq!(port_dialect(&cell("zsh", "5.9", None)), Some("zsh"));
        assert_eq!(port_dialect(&cell("zsh-sh", "5.9", Some("sh"))), Some("sh"));
        assert_eq!(
            port_dialect(&cell("busybox", "1.37.0", Some("busybox"))),
            Some("busybox")
        );
        assert_eq!(port_dialect(&cell("tcsh", "6.24.16", None)), None);
    }

    #[test]
    fn a_cell_without_dialect_yields_no_oracle_number() {
        let zsh = cell("zsh", "5.9", None);
        let list = scripts(&["echo hi\n", "if\n"]);
        let mut shell = |script: &str| Ok(Some(script.starts_with("echo")));
        let oracle = |_: &str, _: &[String]| panic!("no upstream dialect, no oracle run");
        let t = measure_cell(&zsh, &list, &mut shell, &oracle).unwrap();
        assert!(t.oracle.is_none());
        assert_eq!(t.port.checked, 2);
        assert_eq!(t.port.rejects_valid, 0);
        assert_eq!(t.port.accepts_invalid, 0);
        let line = cell_line(&t);
        assert!(line.starts_with("zsh:5.9 "), "{line}");
        assert!(line.contains(" 0 / -"), "{line}");
        assert!(line.ends_with("no upstream dialect"), "{line}");
    }

    #[test]
    fn a_cell_with_dialect_tallies_the_oracle_and_skips_its_crashes() {
        let dash = cell("dash", "0.5.12", Some("sh"));
        let list = scripts(&["echo hi\n", "if\n", "{}\n"]);
        let mut shell = |script: &str| Ok(Some(script != "if\n"));
        let oracle = |dialect: &str, scripts: &[String]| {
            assert_eq!(dialect, "sh");
            assert_eq!(scripts.len(), 3);
            Ok(vec![Some(vec![]), None, Some(vec![1073])])
        };
        let t = measure_cell(&dash, &list, &mut shell, &oracle).unwrap();
        let o = t
            .oracle
            .as_ref()
            .expect("an upstream dialect has an oracle tally");
        assert_eq!(t.port.checked, 3);
        assert_eq!(o.checked, 2);
        assert_eq!(o.rejects_valid, 1);
        assert_eq!(o.example_rejects_valid.as_deref(), Some("{}\n"));
        let line = cell_line(&t);
        assert!(line.contains("/ o:1"), "{line}");
        assert!(!line.contains("no upstream dialect"), "{line}");
        assert_eq!(line, line.trim_end());
    }

    #[test]
    fn a_timed_out_script_counts_for_neither_tool() {
        let dash = cell("dash", "0.5.12", Some("sh"));
        let list = scripts(&["echo hi\n", "sleep 9\n"]);
        let mut shell = |script: &str| Ok(script.starts_with("echo").then_some(true));
        let oracle = |_: &str, _: &[String]| Ok(vec![Some(vec![]), Some(vec![])]);
        let t = measure_cell(&dash, &list, &mut shell, &oracle).unwrap();
        assert_eq!(t.port.checked, 1);
        assert_eq!(t.oracle.unwrap().checked, 1);
    }
}
