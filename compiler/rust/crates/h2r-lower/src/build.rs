use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::Instant;

use h2r_core_ir::Module;

use crate::emit::{Driver, emit_entry_split};

const MANIFEST: &str = "crates.txt";

fn at(path: &Path) -> impl Fn(std::io::Error) -> String + '_ {
    move |error| format!("{}: {error}", path.display())
}

pub fn emit(
    modules: &[Module],
    entries: &[&str],
    out: &Path,
    budget: usize,
    driver: Driver,
) -> Result<(), String> {
    let program = emit_entry_split(modules, entries, budget, driver)?;
    fs::create_dir_all(out).map_err(at(out))?;
    let write = |name: &str, source: &str| {
        let path = out.join(format!("{name}.rs"));
        fs::write(&path, source).map_err(at(&path))
    };
    let mut manifest = String::from("h2r_rt lib\n");
    write("h2r_rt", &program.runtime)?;
    for unit in &program.crates {
        write(&unit.name, &unit.source)?;
        manifest.push_str(&format!(
            "{} lib {}\n",
            unit.name,
            unit.dependencies.join(" ")
        ));
    }
    let (name, kind) = if driver == Driver::Api {
        ("h2r_entry", "lib")
    } else {
        ("program", "bin")
    };
    write(name, &program.main)?;
    manifest.push_str(&format!(
        "{name} {kind} {}\n",
        program.main_dependencies.join(" ")
    ));
    let path = out.join(MANIFEST);
    fs::write(&path, manifest).map_err(at(&path))
}

pub fn compile(out: &Path, opt_level: &str) -> Result<PathBuf, String> {
    let path = out.join(MANIFEST);
    let manifest = fs::read_to_string(&path).map_err(at(&path))?;
    let mut built = None;
    for line in manifest.lines() {
        let mut words = line.split_whitespace();
        let (Some(name), Some(kind)) = (words.next(), words.next()) else {
            return Err(format!("malformed crate line {line:?}"));
        };
        let dependencies: Vec<&str> = words.collect();
        let level = if name == "h2r_rt" { "3" } else { opt_level };
        rustc(out, name, kind, &dependencies, level)?;
        built = Some(out.join(if kind == "bin" {
            name.to_string()
        } else {
            format!("lib{name}.rlib")
        }));
    }
    let built = built.ok_or("the manifest lists no crates")?;
    println!("built {}", built.display());
    Ok(built)
}

fn rustc(
    out: &Path,
    name: &str,
    kind: &str,
    dependencies: &[&str],
    opt_level: &str,
) -> Result<(), String> {
    let source = out.join(format!("{name}.rs"));
    let mut command = Command::new("rustc");
    command
        .arg("--edition=2024")
        .args(["--crate-type", kind, "--crate-name", name])
        .args(["-C", &format!("opt-level={opt_level}"), "-C", "debuginfo=0"])
        .arg("-L")
        .arg(format!("dependency={}", out.display()))
        .arg("--out-dir")
        .arg(out);
    for dependency in std::iter::once("h2r_rt").chain(dependencies.iter().copied()) {
        if dependency == name {
            continue;
        }
        command.arg("--extern").arg(format!(
            "{dependency}={}",
            out.join(format!("lib{dependency}.rlib")).display()
        ));
    }
    command.arg(&source);
    let started = Instant::now();
    let output = command
        .output()
        .map_err(|error| format!("running rustc: {error}"))?;
    let diagnostics = String::from_utf8_lossy(&output.stderr);
    let log = out.join(format!("{name}.log"));
    fs::write(&log, diagnostics.as_bytes()).map_err(at(&log))?;
    let warnings = diagnostics
        .lines()
        .filter(|line| line.starts_with("warning"))
        .count();
    println!(
        "{name}: {} bytes, {:.1} s, {warnings} warning lines",
        fs::metadata(&source).map_err(at(&source))?.len(),
        started.elapsed().as_secs_f64()
    );
    if !output.status.success() {
        return Err(format!(
            "rustc rejected {}:\n{diagnostics}",
            source.display()
        ));
    }
    Ok(())
}
