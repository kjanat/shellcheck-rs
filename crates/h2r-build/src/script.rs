use std::ffi::OsString;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, ExitCode};

use anyhow::{Context, Result, anyhow, bail};
use h2r_lower::build::Rustc;
use h2r_lower::emit::Driver;

use crate::Checkout;
use crate::extract::{self, Tools, sha256_hex, sha256sum_line};

const EMIT: &str = "emit";
const BUDGET: usize = 4_000_000;
const OPT_LEVEL: &str = "1";
const EMITTED: &str = "emitted.sha256";
const COMPILED: &str = "compiled.sha256";

pub fn build_script(entries: &[&str]) -> ExitCode {
    let mut args = std::env::args_os().skip(1);
    let outcome = match args.next() {
        Some(stage) if stage == EMIT => emit(args),
        _ => build(entries),
    };
    match outcome {
        Ok(()) => ExitCode::SUCCESS,
        Err(error) => {
            eprintln!("{error:#}");
            ExitCode::FAILURE
        }
    }
}

fn build(entries: &[&str]) -> Result<()> {
    let checkout = checkout()?;
    for input in extract::inputs(&checkout) {
        println!("cargo::rerun-if-changed={}", input.display());
    }
    let _lock = checkout.lock()?;
    extract::world(&Tools::new()?, &checkout)?;

    let out = checkout.build().join("rshellcheck");
    let emitted = emitted(&checkout, entries)?;
    if !recorded(&out, EMITTED, &emitted) {
        forget(&out, EMITTED)?;
        let status = Command::new(std::env::current_exe()?)
            .arg(EMIT)
            .arg(&out)
            .args(entries)
            .status()
            .context("running the emit stage")?;
        if !status.success() {
            bail!("emitting into {} failed with {status}", out.display());
        }
        record(&out, EMITTED, &emitted)?;
    }

    let target = variable("TARGET")?;
    let rustc = Rustc {
        wrapper: std::env::var_os("RUSTC_WRAPPER").filter(|wrapper| !wrapper.is_empty()),
        program: std::env::var_os("RUSTC").unwrap_or_else(|| OsString::from("rustc")),
        target: (target != variable("HOST")?).then_some(target),
    };
    let compiled = compiled(&out, &rustc)?;
    if !recorded(&out, COMPILED, &compiled) {
        forget(&out, COMPILED)?;
        h2r_lower::build::compile(&out, OPT_LEVEL, &rustc).map_err(anyhow::Error::msg)?;
        record(&out, COMPILED, &compiled)?;
    }
    println!("cargo::rustc-link-search=all={}", out.display());
    Ok(())
}

fn emit(mut args: impl Iterator<Item = OsString>) -> Result<()> {
    let out = PathBuf::from(args.next().context("the emit stage takes a directory")?);
    let entries = args
        .map(|entry| {
            entry
                .into_string()
                .map_err(|entry| anyhow!("entry {entry:?} is not UTF-8"))
        })
        .collect::<Result<Vec<String>>>()?;
    let checkout = checkout()?;
    h2r_core_ir::with_big_stack(move || {
        let (dir, with) = checkout.world();
        let modules = h2r_core_ir::load_dirs(&dir, &with)?.modules;
        let entries: Vec<&str> = entries.iter().map(String::as_str).collect();
        h2r_lower::build::emit(&modules, &entries, &out, BUDGET, Driver::Api)
            .map_err(anyhow::Error::msg)
    })?
}

fn emitted(checkout: &Checkout, entries: &[&str]) -> Result<String> {
    let executable = std::env::current_exe()?;
    let mut fingerprint = sha256sum_line(&executable, "emitter")?;
    for entry in entries {
        fingerprint.push_str(&format!("{entry}\n"));
    }
    fingerprint.push_str(&format!("{BUDGET}\n"));
    let (dir, with) = checkout.world();
    for dir in std::iter::once(dir).chain(with) {
        fingerprint.push_str(&sha256sum_line(
            &dir.join("outputs.sha256"),
            &dir.display().to_string(),
        )?);
    }
    Ok(sha256_hex(fingerprint.as_bytes()))
}

fn compiled(out: &Path, rustc: &Rustc) -> Result<String> {
    let manifest = out.join("crates.txt");
    let crates =
        fs::read_to_string(&manifest).with_context(|| format!("reading {}", manifest.display()))?;
    let mut fingerprint = crates.clone();
    for line in crates.lines() {
        let name = line.split_whitespace().next().unwrap_or_default();
        fingerprint.push_str(&sha256sum_line(
            &out.join(format!("{name}.rs")),
            &format!("{name}.rs"),
        )?);
    }
    let version = Command::new(&rustc.program)
        .arg("-vV")
        .output()
        .context("running rustc -vV")?;
    if !version.status.success() {
        bail!("rustc -vV failed with {}", version.status);
    }
    fingerprint.push_str(&String::from_utf8_lossy(&version.stdout));
    fingerprint.push_str(&format!(
        "{}\n{OPT_LEVEL}\n",
        rustc.target.as_deref().unwrap_or("host")
    ));
    Ok(sha256_hex(fingerprint.as_bytes()))
}

fn recorded(out: &Path, record: &str, fingerprint: &str) -> bool {
    fs::read_to_string(out.join(record)).is_ok_and(|recorded| recorded.trim_end() == fingerprint)
        && fs::read_to_string(out.join("crates.txt")).is_ok_and(|crates| {
            crates.lines().all(|line| {
                let name = line.split_whitespace().next().unwrap_or_default();
                let built = if record == COMPILED {
                    format!("lib{name}.rlib")
                } else {
                    format!("{name}.rs")
                };
                out.join(built).is_file()
            })
        })
}

fn record(out: &Path, record: &str, fingerprint: &str) -> Result<()> {
    let path = out.join(record);
    fs::write(&path, format!("{fingerprint}\n"))
        .with_context(|| format!("writing {}", path.display()))
}

fn forget(out: &Path, record: &str) -> Result<()> {
    match fs::remove_file(out.join(record)) {
        Ok(()) => Ok(()),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => Ok(()),
        Err(error) => Err(error).with_context(|| format!("removing {record}")),
    }
}

fn checkout() -> Result<Checkout> {
    Checkout::containing(Path::new(&variable("CARGO_MANIFEST_DIR")?))
}

fn variable(name: &str) -> Result<String> {
    std::env::var(name).with_context(|| format!("cargo sets {name} for build scripts"))
}

#[cfg(test)]
mod tests {
    use super::{EMITTED, forget, record, recorded};

    #[test]
    fn a_record_counts_only_while_its_outputs_exist() {
        let out = std::env::temp_dir().join(format!("h2r-build-record-{}", std::process::id()));
        std::fs::create_dir_all(&out).expect("a scratch directory");
        std::fs::write(out.join("crates.txt"), "h2r_rt lib\nh2r_entry lib h2r_c0\n")
            .expect("a manifest");
        std::fs::write(out.join("h2r_rt.rs"), "").expect("a source");
        record(&out, EMITTED, "abc").expect("a record");
        assert!(!recorded(&out, EMITTED, "abc"));
        std::fs::write(out.join("h2r_entry.rs"), "").expect("a source");
        assert!(recorded(&out, EMITTED, "abc"));
        assert!(!recorded(&out, EMITTED, "abd"));
        forget(&out, EMITTED).expect("forgetting");
        assert!(!recorded(&out, EMITTED, "abc"));
        std::fs::remove_dir_all(&out).expect("removing the scratch directory");
    }
}
