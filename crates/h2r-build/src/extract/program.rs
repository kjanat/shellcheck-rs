use std::fs;
use std::path::{Path, PathBuf};
use std::process::Stdio;
use std::time::SystemTime;

use anyhow::{Context, Result, bail};

use super::{
    Tools, dump_checksums, dumps, extractor_sources, remove_dir, sha256_file, sha256_hex,
    sha256sum_line, top_level, unchanged,
};
use crate::Checkout;

const SOURCE_ITEMS: [&str; 9] = [
    "src",
    "shellcheck.hs",
    "ShellCheck.cabal",
    "striptests",
    "LICENSE",
    "README.md",
    "CHANGELOG.md",
    "shellcheck.1.md",
    "manpage",
];

pub const PROFILES: [(&str, &str); 6] = [
    ("A", "-O1"),
    ("B", "-O2"),
    ("C", "-O2 -fno-full-laziness"),
    (
        "D",
        "-O2 -fno-full-laziness -fspecialise-aggressively -fexpose-all-unfoldings -fcross-module-specialise",
    ),
    (
        "E",
        "-O2 -fno-full-laziness -fspecialise-aggressively -fexpose-all-unfoldings -fcross-module-specialise -fstatic-argument-transformation",
    ),
    (
        "F",
        "-O2 -fno-full-laziness -fspecialise-aggressively -fexpose-all-unfoldings -fcross-module-specialise -fstatic-argument-transformation -fstrictness-before=2",
    ),
];

pub struct Options {
    pub opt: String,
    pub build_dir: PathBuf,
    pub core_dir: PathBuf,
    pub keep_dir: Option<PathBuf>,
    pub jobs: Option<usize>,
    pub source_ref: Option<String>,
    pub constraints: Option<String>,
}

pub fn inputs(checkout: &Checkout) -> Vec<PathBuf> {
    SOURCE_ITEMS
        .iter()
        .map(|item| checkout.root().join(item))
        .chain([
            checkout.plugin().join("src"),
            checkout.plugin().join("h2r-plugin.cabal"),
        ])
        .collect()
}

pub fn package_db(tools: &Tools, build: &Path) -> PathBuf {
    build
        .join("dist-newstyle/packagedb")
        .join(format!("ghc-{}", tools.ghc_version))
}

pub fn extract(tools: &Tools, checkout: &Checkout, options: &Options) -> Result<()> {
    let repo = checkout.root().to_path_buf();
    let build = options.build_dir.clone();
    let out = options.core_dir.clone();
    let keep = options.keep_dir.clone();
    let git = |args: &[&str]| tools.output(tools.command("git").arg("-C").arg(&repo).args(args));
    let source_ref = match &options.source_ref {
        Some(reference) => Some(
            git(&["rev-parse", "--verify", &format!("{reference}^{{commit}}")])?
                .trim()
                .to_string(),
        ),
        None => None,
    };
    let plugin_dir = match source_ref {
        Some(_) => build.join("compiler/h2r-plugin"),
        None => repo.join("compiler/h2r-plugin"),
    };
    let cabal_version = tools
        .output(tools.command("cabal").arg("--numeric-version"))
        .context("cabal is not on PATH")?
        .trim()
        .to_string();

    let mut fingerprint = String::new();
    for line in [
        options.opt.clone(),
        out.display().to_string(),
        keep.as_ref()
            .map(|dir| dir.display().to_string())
            .unwrap_or_default(),
        tools.ghc_version.clone(),
        cabal_version.clone(),
        source_ref.clone().unwrap_or_default(),
    ] {
        fingerprint.push_str(&line);
        fingerprint.push('\n');
    }
    if let Some(constraints) = &options.constraints {
        fingerprint.push_str(&format!(
            "{}  constraints\n",
            sha256_hex(constraints.as_bytes())
        ));
    }
    match &source_ref {
        Some(reference) => {
            let archive = tools
                .command("git")
                .arg("-C")
                .arg(&repo)
                .args(["archive", reference, "--"])
                .args(SOURCE_ITEMS)
                .arg("compiler/h2r-plugin")
                .stderr(Stdio::inherit())
                .output()?;
            if !archive.status.success() {
                bail!("git archive {reference} failed with {}", archive.status);
            }
            fingerprint.push_str(&format!("{}  -\n", sha256_hex(&archive.stdout)));
        }
        None => {
            let mut inputs: Vec<PathBuf> = Vec::new();
            for dir in ["src", "compiler/h2r-plugin/src"] {
                inputs.extend(super::files_under(&repo.join(dir))?);
            }
            inputs.extend(
                SOURCE_ITEMS[1..]
                    .iter()
                    .chain(["compiler/h2r-plugin/h2r-plugin.cabal"].iter())
                    .map(|item| repo.join(item)),
            );
            let mut shown: Vec<(String, PathBuf)> = inputs
                .into_iter()
                .map(|path| {
                    Ok((
                        path.strip_prefix(&repo)?.display().to_string(),
                        path.clone(),
                    ))
                })
                .collect::<Result<_>>()?;
            shown.sort_by(|left, right| left.0.as_bytes().cmp(right.0.as_bytes()));
            for (name, path) in shown {
                fingerprint.push_str(&sha256sum_line(&path, &name)?);
            }
        }
    }
    fingerprint.push_str(&extractor_sources());
    let fingerprint = sha256_hex(fingerprint.as_bytes());

    if unchanged(&out, &fingerprint)? {
        println!("==> extraction unchanged: {}", out.display());
        return Ok(());
    }

    let resuming = fs::read_to_string(build.join("inputs.sha256"))
        .is_ok_and(|recorded| recorded.trim_end() == fingerprint)
        && !out.join("outputs.sha256").is_file();
    if resuming {
        println!("==> resuming extraction in {}", build.display());
    } else {
        println!("==> staging sources in {}", build.display());
        remove_dir(&build)?;
        remove_dir(&out)?;
        fs::create_dir_all(&build)?;
        fs::create_dir_all(&out)?;
        match &source_ref {
            Some(reference) => untar(tools, &repo, reference, &SOURCE_ITEMS, &build)?,
            None => {
                for item in SOURCE_ITEMS {
                    tools.run(
                        tools
                            .command("cp")
                            .arg("-r")
                            .arg(repo.join(item))
                            .arg(&build),
                    )?;
                }
            }
        }

        println!("==> stripping tests (removes Template Haskell and QuickCheck)");
        tools.run(
            tools
                .command(&build.join("striptests").display().to_string())
                .current_dir(&build),
        )?;
        if let Some(reference) = &source_ref {
            untar(tools, &repo, reference, &["compiler/h2r-plugin"], &build)?;
        }

        println!("==> wiring in the Core dump plugin");
        let cabal_file = build.join("ShellCheck.cabal");
        let wired: String = fs::read_to_string(&cabal_file)?
            .lines()
            .map(|line| {
                let indent = &line[..line.len() - line.trim_start_matches(' ').len()];
                match line[indent.len()..].strip_prefix("build-depends:") {
                    Some(rest) => {
                        format!("{indent}build-depends:\n{indent}  h2r-plugin,{rest}\n")
                    }
                    None => format!("{line}\n"),
                }
            })
            .collect();
        fs::write(&cabal_file, wired)?;
        fs::write(
            build.join("cabal.project"),
            format!(
                "packages:\n  .\n  {}\n\npackage ShellCheck\n  ghc-options: {} -fplugin=H2R.CorePlugin -fplugin-opt=H2R.CorePlugin:outdir={}\n",
                plugin_dir.display(),
                options.opt,
                out.display()
            ),
        )?;
        if let Some(constraints) = &options.constraints {
            fs::write(build.join("cabal.project.local"), constraints)?;
        }
        fs::write(build.join("inputs.sha256"), format!("{fingerprint}\n"))?;
    }

    println!("==> building (this runs the full optimisation pipeline)");
    let jobs = match options.jobs {
        Some(jobs) => jobs,
        None => std::thread::available_parallelism()?.get(),
    };
    tools.run(
        tools
            .command("cabal")
            .current_dir(&build)
            .arg("build")
            .arg(format!("-j{jobs}"))
            .arg("shellcheck"),
    )?;

    println!();
    println!(
        "==> wrote {} module dumps to {}",
        dumps(&out)?.len(),
        out.display()
    );
    tools.run(tools.command("du").arg("-sh").arg(&out))?;
    let binary = PathBuf::from(
        tools
            .output(
                tools
                    .command("cabal")
                    .current_dir(&build)
                    .args(["list-bin", "shellcheck"]),
            )?
            .trim(),
    );
    println!("==> binary: {}", binary.display());
    let plan_json = build.join("dist-newstyle/cache/plan.json");

    if let Some(keep) = &keep {
        println!(
            "==> keeping binary, build plan and provenance in {}",
            keep.display()
        );
        fs::create_dir_all(keep)?;
        fs::copy(&binary, keep.join("shellcheck"))?;
        fs::copy(&plan_json, keep.join("plan.json"))?;
        let modules: String = top_level(&out, ".core.json")?
            .into_iter()
            .map(|name| format!("{name}\n"))
            .collect();
        fs::write(keep.join("modules"), &modules)?;
        let dirty = git(&[
            "status",
            "--porcelain",
            "--",
            "src",
            "shellcheck.hs",
            "ShellCheck.cabal",
            "striptests",
            "compiler/h2r-plugin",
        ])?
        .lines()
        .count();
        let mut plugin_text = fs::read(plugin_dir.join("h2r-plugin.cabal"))?;
        for name in top_level(&plugin_dir.join("src/H2R"), ".hs")? {
            plugin_text.extend(fs::read(plugin_dir.join("src/H2R").join(name))?);
        }
        let mut stripped: Vec<PathBuf> = super::files_under(&build.join("src"))?;
        stripped.extend(["shellcheck.hs", "ShellCheck.cabal"].map(|item| build.join(item)));
        stripped.sort_by(|left, right| left.as_os_str().cmp(right.as_os_str()));
        let mut stripped_text = Vec::new();
        for file in &stripped {
            stripped_text.extend(fs::read(file)?);
        }
        let version = tools
            .output(
                tools
                    .command(&keep.join("shellcheck").display().to_string())
                    .arg("--version"),
            )?
            .replace('\n', " ");
        let provenance = [
            format!("date={}", utc_now()),
            format!("flags={}", options.opt),
            "flags_scope=package ShellCheck only; dependencies at Hackage defaults".to_string(),
            format!("repo_head={}", git(&["rev-parse", "HEAD"])?.trim()),
            format!(
                "source_ref={}",
                source_ref.as_deref().unwrap_or("working-tree")
            ),
            format!("repo_dirty_inputs={dirty}"),
            format!("plugin_sha256={}", sha256_hex(&plugin_text)),
            format!("stripped_source_sha256={}", sha256_hex(&stripped_text)),
            format!("ghc={}", tools.ghc_version),
            format!("cabal={cabal_version}"),
            format!("modules={}", modules.lines().count()),
            format!("binary_sha256={}", sha256_file(&keep.join("shellcheck"))?),
            format!("binary_version={version}"),
        ]
        .map(|line| format!("{line}\n"))
        .concat();
        fs::write(keep.join("provenance"), &provenance)?;
        print!("{provenance}");
    }

    if fs::metadata(out.join("Main.core.json")).map_or(true, |metadata| metadata.len() == 0) {
        bail!("{} has no Main.core.json", out.display());
    }
    let mut checksums = dump_checksums(&out)?;
    let artifacts: Vec<PathBuf> = match &keep {
        Some(keep) => ["shellcheck", "plan.json", "modules", "provenance"]
            .map(|name| keep.join(name))
            .to_vec(),
        None => vec![binary, plan_json],
    };
    for artifact in artifacts {
        checksums.push_str(&sha256sum_line(&artifact, &artifact.display().to_string())?);
    }
    fs::write(out.join("outputs.sha256.tmp"), checksums)?;
    fs::rename(out.join("outputs.sha256.tmp"), out.join("outputs.sha256"))?;
    fs::write(out.join("inputs.sha256"), format!("{fingerprint}\n"))?;
    Ok(())
}

fn untar(tools: &Tools, repo: &Path, reference: &str, items: &[&str], into: &Path) -> Result<()> {
    let archive = tools
        .command("git")
        .arg("-C")
        .arg(repo)
        .args(["archive", reference, "--"])
        .args(items)
        .stderr(Stdio::inherit())
        .output()?;
    if !archive.status.success() {
        bail!("git archive {reference} failed with {}", archive.status);
    }
    let mut tar = tools
        .command("tar")
        .arg("-x")
        .arg("-C")
        .arg(into)
        .stdin(Stdio::piped())
        .spawn()?;
    std::io::Write::write_all(
        tar.stdin.as_mut().context("tar has a stdin")?,
        &archive.stdout,
    )?;
    let status = tar.wait()?;
    if !status.success() {
        bail!("tar -x failed with {status}");
    }
    Ok(())
}

fn utc_now() -> String {
    let seconds = SystemTime::now()
        .duration_since(SystemTime::UNIX_EPOCH)
        .map_or(0, |elapsed| elapsed.as_secs());
    let days = (seconds / 86_400) as i64;
    let rest = seconds % 86_400;
    let shifted = days + 719_468;
    let era = shifted.div_euclid(146_097);
    let day_of_era = shifted.rem_euclid(146_097);
    let year_of_era =
        (day_of_era - day_of_era / 1_460 + day_of_era / 36_524 - day_of_era / 146_096) / 365;
    let day_of_year = day_of_era - (365 * year_of_era + year_of_era / 4 - year_of_era / 100);
    let month_index = (5 * day_of_year + 2) / 153;
    let day = day_of_year - (153 * month_index + 2) / 5 + 1;
    let month = if month_index < 10 {
        month_index + 3
    } else {
        month_index - 9
    };
    let year = year_of_era + era * 400 + i64::from(month <= 2);
    format!(
        "{year:04}-{month:02}-{day:02}T{:02}:{:02}:{:02}Z",
        rest / 3_600,
        rest % 3_600 / 60,
        rest % 60
    )
}

pub fn entry(
    tools: &Tools,
    checkout: &Checkout,
    out: &Path,
    build: &Path,
    shellcheck_db: &Path,
    store_db: Option<PathBuf>,
) -> Result<()> {
    let out = out.to_path_buf();
    let work = build.join("work");
    let source = checkout.entry_source();
    let store_db = tools.store_db(store_db)?;
    let mut fingerprint = format!(
        "{}\n{}\n{}\n",
        tools.ghc_version,
        store_db.display(),
        shellcheck_db.display()
    );
    for file in super::files_under(shellcheck_db)? {
        fingerprint.push_str(&sha256sum_line(&file, &file.display().to_string())?);
    }
    for file in
        std::iter::once(source.clone()).chain(super::files_under(&checkout.plugin().join("src"))?)
    {
        let shown = file.strip_prefix(checkout.root())?.display().to_string();
        fingerprint.push_str(&sha256sum_line(&file, &shown)?);
    }
    fingerprint.push_str(&extractor_sources());
    let fingerprint = sha256_hex(fingerprint.as_bytes());
    if unchanged(&out, &fingerprint)? {
        println!("==> entry unchanged: {}", out.display());
        return Ok(());
    }

    let plugin = tools.plugin(checkout, build)?;
    remove_dir(&out)?;
    remove_dir(&work)?;
    fs::create_dir_all(&out)?;
    fs::create_dir_all(&work)?;
    tools.run(
        tools
            .command("ghc")
            .args([
                "-c",
                "-O1",
                "-this-unit-id",
                "h2r-entry",
                "-package-env",
                "-",
            ])
            .arg("-package-db")
            .arg(&store_db)
            .arg("-package-db")
            .arg(shellcheck_db)
            .args(["-package", "ShellCheck"])
            .arg(plugin.flag(&out))
            .arg("-fplugin-trustworthy")
            .arg("-odir")
            .arg(&work)
            .arg("-hidir")
            .arg(&work)
            .arg(&source),
    )?;
    println!(
        "==> wrote {} module dumps to {}",
        dumps(&out)?.len(),
        out.display()
    );
    fs::write(out.join("outputs.sha256"), dump_checksums(&out)?)?;
    fs::write(out.join("inputs.sha256"), format!("{fingerprint}\n"))?;
    Ok(())
}

pub fn canary(tools: &Tools, checkout: &Checkout) -> Result<()> {
    let repo = checkout.root().to_path_buf();
    let source = repo.join("compiler/canary");
    let build = repo.join("compiler/build/canary");
    let builddir = format!("--builddir={}", build.join("cabal").display());
    tools.run(tools.command("cabal").current_dir(&source).args([
        "build",
        "--offline",
        &builddir,
        "h2r-canary",
    ]))?;
    for (optimization, out, extra) in [
        ("-O1", build.clone(), None),
        (
            "-O0",
            build.join("unoptimized"),
            Some("-fmax-simplifier-iterations=0"),
        ),
    ] {
        let objects = out.join("oracle-build");
        let core = out.join("core");
        remove_dir(&core)?;
        fs::create_dir_all(&objects)?;
        tools.run(
            tools
                .command("cabal")
                .current_dir(&source)
                .args([
                    "exec",
                    &builddir,
                    "--",
                    "ghc",
                    "--make",
                    "Main.hs",
                    optimization,
                ])
                .args(extra)
                .args([
                    "-fno-worker-wrapper",
                    "-fforce-recomp",
                    "-package",
                    "h2r-plugin",
                    "-fplugin=H2R.CorePlugin",
                ])
                .arg(format!(
                    "-fplugin-opt=H2R.CorePlugin:outdir={}",
                    core.display()
                ))
                .arg("-odir")
                .arg(&objects)
                .arg("-hidir")
                .arg(&objects)
                .arg("-o")
                .arg(out.join("oracle")),
        )?;
        println!(
            "==> {optimization}: wrote {} module dumps to {}",
            dumps(&core)?.len(),
            core.display()
        );
    }
    Ok(())
}

pub fn oracle(tools: &Tools, checkout: &Checkout) -> Result<()> {
    let repo = checkout.root().to_path_buf();
    let source = repo.join("compiler/canary/shellcheck");
    let build = repo.join("compiler/build/shellcheck-oracle");
    let builddir = format!("--builddir={}", build.join("cabal").display());
    tools.run(tools.command("cabal").current_dir(&source).args([
        "build",
        "--offline",
        &builddir,
        "shellcheck-oracle",
    ]))?;
    let built = tools.output(tools.command("cabal").current_dir(&source).args([
        "list-bin",
        &builddir,
        "shellcheck-oracle",
    ]))?;
    let oracle = build.join("oracle");
    fs::copy(built.trim(), &oracle)
        .with_context(|| format!("copying {} to {}", built.trim(), oracle.display()))?;
    println!("==> wrote {}", oracle.display());
    Ok(())
}
