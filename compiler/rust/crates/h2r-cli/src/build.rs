use std::fs;
use std::path::Path;
use std::process::Command;
use std::time::Instant;

use anyhow::{Context, Result, bail};
use h2r_core_ir::Module;

const MANIFEST: &str = "crates.txt";

pub fn emit(
    modules: &[Module],
    entry: &str,
    out: &Path,
    budget: usize,
    driver: h2r_lower::emit::Driver,
) -> Result<()> {
    let program = h2r_lower::emit::emit_entry_split(modules, entry, budget, driver)
        .map_err(anyhow::Error::msg)?;
    fs::create_dir_all(out)?;
    let mut manifest = String::from("h2r_rt lib\n");
    fs::write(out.join("h2r_rt.rs"), &program.runtime)?;
    for unit in &program.crates {
        fs::write(out.join(format!("{}.rs", unit.name)), &unit.source)?;
        manifest.push_str(&format!(
            "{} lib {}\n",
            unit.name,
            unit.dependencies.join(" ")
        ));
    }
    fs::write(out.join("program.rs"), &program.main)?;
    manifest.push_str(&format!(
        "program bin {}\n",
        program.main_dependencies.join(" ")
    ));
    fs::write(out.join(MANIFEST), manifest)?;
    Ok(())
}

pub fn compile(out: &Path, opt_level: &str) -> Result<()> {
    let manifest = fs::read_to_string(out.join(MANIFEST))
        .with_context(|| format!("reading {}", out.join(MANIFEST).display()))?;
    for line in manifest.lines() {
        let mut words = line.split_whitespace();
        let (Some(name), Some(kind)) = (words.next(), words.next()) else {
            bail!("malformed crate line {line:?}");
        };
        let dependencies: Vec<&str> = words.collect();
        let level = if name == "h2r_rt" { "3" } else { opt_level };
        rustc(out, name, kind, &dependencies, level)?;
    }
    println!("built {}", out.join("program").display());
    Ok(())
}

fn rustc(out: &Path, name: &str, kind: &str, dependencies: &[&str], opt_level: &str) -> Result<()> {
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
    let output = command.output()?;
    let diagnostics = String::from_utf8_lossy(&output.stderr);
    fs::write(out.join(format!("{name}.log")), diagnostics.as_bytes())?;
    let warnings = diagnostics
        .lines()
        .filter(|line| line.starts_with("warning"))
        .count();
    println!(
        "{name}: {} bytes, {:.1} s, {warnings} warning lines",
        fs::metadata(&source)?.len(),
        started.elapsed().as_secs_f64()
    );
    if !output.status.success() {
        bail!("rustc rejected {}:\n{diagnostics}", source.display());
    }
    Ok(())
}
