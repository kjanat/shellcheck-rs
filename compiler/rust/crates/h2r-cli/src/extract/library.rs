use std::fs;
use std::path::{Path, PathBuf};

use anyhow::{Context, Result, bail};

use super::{
    Tools, compare_interfaces, dump_checksums, dumps, extractor_sources, paths, remove_dir,
    repo_root, sha256_hex, sha256sum_line, unchanged,
};

pub struct Layout {
    pub package: &'static str,
    pub hadrian_path: &'static str,
    pub source_dirs: &'static [&'static str],
    pub include_dirs: &'static [&'static str],
    pub flags: &'static [&'static str],
    pub unit: Option<&'static str>,
    pub virtual_modules: &'static [&'static str],
    pub omitted: &'static [&'static str],
    pub ghc_tree: Option<&'static str>,
    pub store: bool,
    pub differs: &'static [&'static str],
}

const BOOT: Layout = Layout {
    package: "",
    hadrian_path: ".",
    source_dirs: &["."],
    include_dirs: &[],
    flags: &["-O2", "-XHaskell2010"],
    unit: None,
    virtual_modules: &[],
    omitted: &[],
    ghc_tree: None,
    store: false,
    differs: &[],
};

pub const LAYOUTS: &[Layout] = &[
    Layout {
        package: "containers",
        hadrian_path: "libraries/containers/containers",
        source_dirs: &["src"],
        include_dirs: &["include"],
        ..BOOT
    },
    Layout {
        package: "transformers",
        hadrian_path: "libraries/transformers",
        ..BOOT
    },
    Layout {
        package: "array",
        hadrian_path: "libraries/array",
        ..BOOT
    },
    Layout {
        package: "mtl",
        hadrian_path: "libraries/mtl",
        ..BOOT
    },
    Layout {
        package: "base",
        hadrian_path: "libraries/base",
        include_dirs: &["include"],
        unit: Some("base"),
        ..BOOT
    },
    Layout {
        package: "parsec",
        hadrian_path: "libraries/parsec",
        source_dirs: &["src"],
        ..BOOT
    },
    Layout {
        package: "ghc-prim",
        hadrian_path: "libraries/ghc-prim",
        unit: Some("ghc-prim"),
        virtual_modules: &["GHC.Prim"],
        ..BOOT
    },
    Layout {
        package: "ghc-bignum",
        hadrian_path: "libraries/ghc-bignum",
        source_dirs: &["src"],
        include_dirs: &["include"],
        flags: &["-O2", "-XHaskell2010", "-DBIGNUM_NATIVE"],
        unit: Some("ghc-bignum"),
        ghc_tree: Some("libraries/ghc-bignum"),
        omitted: &["GHC.Num.Backend.GMP"],
        differs: &[
            "GHC/Num/Backend.hi",
            "GHC/Num/Backend/GMP.hi",
            "GHC/Num/Backend/Native.hi",
            "GHC/Num/Backend/Selected.hi",
            "GHC/Num/BigNat.hi",
            "GHC/Num/Integer.hi",
            "GHC/Num/Natural.hi",
        ],
        ..BOOT
    },
    Layout {
        package: "regex-base",
        store: true,
        source_dirs: &["src"],
        flags: &[
            "-O",
            "-XHaskell2010",
            "-XNoImplicitPrelude",
            "-XSafe",
            "-XMultiParamTypeClasses",
            "-XFunctionalDependencies",
            "-XTypeSynonymInstances",
            "-XFlexibleInstances",
            "-XFlexibleContexts",
        ],
        ..BOOT
    },
    Layout {
        package: "regex-tdfa",
        store: true,
        source_dirs: &["lib"],
        flags: &[
            "-O",
            "-XHaskell2010",
            "-XBangPatterns",
            "-XExistentialQuantification",
            "-XFlexibleContexts",
            "-XFlexibleInstances",
            "-XForeignFunctionInterface",
            "-XFunctionalDependencies",
            "-XMagicHash",
            "-XMultiParamTypeClasses",
            "-XNondecreasingIndentation",
            "-XRecursiveDo",
            "-XScopedTypeVariables",
            "-XTypeOperators",
            "-XTypeSynonymInstances",
            "-XUnboxedTuples",
            "-XUnliftedFFITypes",
            "-funbox-strict-fields",
            "-fspec-constr-count=10",
        ],
        ..BOOT
    },
    Layout {
        package: "fgl",
        store: true,
        flags: &["-O", "-XHaskell98"],
        ..BOOT
    },
    Layout {
        package: "Diff",
        store: true,
        source_dirs: &["src"],
        flags: &["-O", "-XHaskell2010", "-funbox-strict-fields"],
        ..BOOT
    },
];

impl Layout {
    fn under(&self, dir: &str) -> String {
        match (self.hadrian_path, dir) {
            (".", dir) => dir.to_string(),
            (hadrian, ".") => hadrian.to_string(),
            (hadrian, dir) => format!("{hadrian}/{dir}"),
        }
    }
}

struct Package<'t> {
    tools: &'t Tools,
    db: Option<PathBuf>,
    name: &'static str,
}

impl Package<'_> {
    fn field(&self, field: &str) -> Result<String> {
        let mut command = self.tools.command("ghc-pkg");
        if let Some(db) = &self.db {
            command.arg(format!("--package-db={}", db.display()));
        }
        self.tools
            .output(command.args(["field", self.name, field, "--simple-output"]))
    }

    fn words(&self, field: &str) -> Result<Vec<String>> {
        Ok(self
            .field(field)?
            .split_whitespace()
            .map(str::to_string)
            .collect())
    }
}

fn modules(listing: &str) -> Vec<String> {
    let words: Vec<&str> = listing
        .split([',', '\n', ' ', '\t'])
        .filter(|word| !word.is_empty())
        .collect();
    let mut modules = Vec::new();
    let mut index = 0;
    while index < words.len() {
        if words.get(index + 1) == Some(&"from") {
            index += 3;
            continue;
        }
        modules.push(words[index].to_string());
        index += 1;
    }
    modules
}

pub fn extract(
    tools: &Tools,
    package: &str,
    out: Option<PathBuf>,
    store_db: Option<PathBuf>,
) -> Result<()> {
    let Some(layout) = LAYOUTS.iter().find(|layout| layout.package == package) else {
        bail!("no source layout recorded for {package}");
    };
    let repo = repo_root();
    let build = repo.join("compiler/build/libraries");
    let out = out.unwrap_or_else(|| repo.join("compiler/library-json").join(package));
    let store_db = tools.store_db(store_db)?;
    let installed_package = Package {
        tools,
        db: layout.store.then(|| store_db.clone()),
        name: layout.package,
    };
    let mut package_flags = Vec::new();
    if layout.store {
        package_flags.extend([
            "-package-db".to_string(),
            store_db.display().to_string(),
            "-hide-all-packages".to_string(),
        ]);
        for dependency in installed_package.words("depends")? {
            package_flags.extend(["-package-id".to_string(), dependency]);
        }
    }
    let unit = match layout.unit {
        Some(unit) => unit.to_string(),
        None => installed_package.field("id")?.trim().to_string(),
    };
    let version = installed_package.field("version")?.trim().to_string();
    let installed = PathBuf::from(installed_package.field("library-dirs")?.trim());
    let installed_includes = installed_package.words("include-dirs")?;
    let rts_includes = Package {
        tools,
        db: None,
        name: "rts",
    }
    .words("include-dirs")?;
    let modules: Vec<String> = modules(&installed_package.field("exposed-modules,hidden-modules")?)
        .into_iter()
        .filter(|module| {
            !layout.virtual_modules.contains(&module.as_str())
                && !layout.omitted.contains(&module.as_str())
        })
        .collect();
    let source = build.join(format!("{package}-{version}"));

    let plugin_sources = repo.join("compiler/h2r-plugin/src");
    let mut fingerprint = String::new();
    for line in std::iter::once(unit.as_str())
        .chain([layout.hadrian_path, layout.ghc_tree.unwrap_or("")])
        .chain(layout.flags.iter().copied())
        .chain(package_flags.iter().map(String::as_str))
        .chain(modules.iter().map(String::as_str))
        .chain(layout.differs.iter().copied())
    {
        fingerprint.push_str(line);
        fingerprint.push('\n');
    }
    fingerprint.push_str(&tools.ghc_version);
    fingerprint.push('\n');
    for file in super::files_under(&plugin_sources)? {
        let shown = file.strip_prefix(&repo)?.display().to_string();
        fingerprint.push_str(&sha256sum_line(&file, &shown)?);
    }
    fingerprint.push_str(&extractor_sources());
    let fingerprint = sha256_hex(fingerprint.as_bytes());
    if unchanged(&out, &fingerprint)? {
        println!("==> {package} unchanged: {}", out.display());
        return Ok(());
    }

    if !source.is_dir() {
        fs::create_dir_all(&build)?;
        tools.run(
            tools
                .command("cabal")
                .arg("get")
                .arg(format!("--destdir={}", build.display()))
                .arg(format!("{package}-{version}")),
        )?;
        if let Some(tree) = layout.ghc_tree {
            overlay(tools, &source, tree)?;
        }
    }

    let plugin = tools.plugin(&build)?;
    let work = build.join(format!("{package}-{version}-h2r"));
    let staged = build.join(format!("{package}-{version}-root"));
    remove_dir(&out)?;
    remove_dir(&work)?;
    remove_dir(&staged)?;
    fs::create_dir_all(&out)?;
    fs::create_dir_all(&work)?;
    let root = if layout.hadrian_path == "." {
        source.clone()
    } else {
        let link = staged.join(layout.hadrian_path);
        fs::create_dir_all(link.parent().context("a hadrian path has a parent")?)?;
        std::os::unix::fs::symlink(&source, &link)?;
        staged
    };

    let mut search: Vec<String> = layout
        .source_dirs
        .iter()
        .map(|dir| format!("-i{}", layout.under(dir)))
        .chain(
            layout
                .include_dirs
                .iter()
                .map(|dir| format!("-I{}", layout.under(dir))),
        )
        .chain(installed_includes.iter().map(|dir| format!("-I{dir}")))
        .collect();

    let (major, minor) = {
        let mut parts = tools.ghc_version.split('.');
        let major: u32 = parts.next().unwrap_or("0").parse()?;
        let minor: u32 = parts.next().unwrap_or("0").parse()?;
        (major, minor)
    };
    let hsc_flags: Vec<String> = [
        format!("--cflag=-D__GLASGOW_HASKELL__={}", major * 100 + minor),
        "--cflag=-Dx86_64_HOST_ARCH=1".to_string(),
        "--cflag=-Dlinux_HOST_OS=1".to_string(),
    ]
    .into_iter()
    .chain(search.iter().filter(|flag| flag.starts_with("-I")).cloned())
    .chain(rts_includes.iter().map(|dir| format!("-I{dir}")))
    .collect();
    let hsc = work.join("hsc");
    for module in &modules {
        let path = module.replace('.', "/");
        for dir in layout.source_dirs {
            let relative = format!("{}/{path}.hsc", layout.under(dir));
            if !root.join(&relative).is_file() {
                continue;
            }
            let target = hsc.join(format!("{path}.hs"));
            fs::create_dir_all(target.parent().context("a module path has a parent")?)?;
            tools.run(
                tools
                    .command("hsc2hs")
                    .current_dir(&root)
                    .args(&hsc_flags)
                    .arg("-o")
                    .arg(&target)
                    .arg(&relative),
            )?;
            let boot = root.join(format!("{}/{path}.hs-boot", layout.under(dir)));
            if boot.is_file() {
                std::os::unix::fs::symlink(&boot, hsc.join(format!("{path}.hs-boot")))?;
            }
        }
    }
    if hsc.is_dir() {
        search.push(format!("-i{}", hsc.display()));
    }
    let autogen = work.join("autogen");
    for module in modules.iter().filter(|module| module.starts_with("Paths_")) {
        fs::create_dir_all(&autogen)?;
        let prefix = store_db
            .parent()
            .context("the store package db has a parent")?
            .join(&unit);
        fs::write(
            autogen.join(format!("{module}.hs")),
            paths::module(module, &prefix.display().to_string(), &version),
        )?;
        search.push(format!("-i{}", autogen.display()));
    }

    println!("==> compiling {unit} ({} modules)", modules.len());
    tools.run(
        tools
            .command("ghc")
            .current_dir(&root)
            .args(["--make", "-j", "-no-link", "-this-unit-id", &unit])
            .args(&package_flags)
            .args(layout.flags)
            .args(&search)
            .arg(plugin.flag(&out))
            .arg("-fplugin-trustworthy")
            .arg("-odir")
            .arg(&work)
            .arg("-hidir")
            .arg(&work)
            .args(&modules),
    )?;

    let count = dumps(&out)?.len();
    if count != modules.len() {
        bail!("{count} dumps for {} modules", modules.len());
    }
    println!("==> comparing {count} interfaces with the installed {unit}");
    let differs: Vec<String> = layout.differs.iter().map(|path| path.to_string()).collect();
    compare_interfaces(tools, &installed, &work, &differs)?;
    println!("==> wrote {count} module dumps to {}", out.display());
    fs::write(out.join("outputs.sha256"), dump_checksums(&out)?)?;
    fs::write(out.join("inputs.sha256"), format!("{fingerprint}\n"))?;
    Ok(())
}

fn overlay(tools: &Tools, source: &Path, tree: &str) -> Result<()> {
    for file in super::files_under(source)? {
        let name = file.to_string_lossy();
        if !(name.ends_with(".hs") || name.ends_with(".hs-boot") || name.ends_with(".h")) {
            continue;
        }
        let relative = file.strip_prefix(source)?.display().to_string();
        tools.run(
            tools
                .command("curl")
                .arg("-fsSL")
                .arg(format!(
                    "https://gitlab.haskell.org/ghc/ghc/-/raw/ghc-{}-release/{tree}/{relative}",
                    tools.ghc_version
                ))
                .arg("-o")
                .arg(&file),
        )?;
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::{LAYOUTS, modules};

    #[test]
    fn a_reexported_module_is_not_compiled() {
        assert_eq!(
            modules("A, B\nC from base:C, D\n"),
            ["A", "B", "D"].map(String::from)
        );
    }

    #[test]
    fn every_package_has_one_layout() {
        for layout in LAYOUTS {
            assert_eq!(
                LAYOUTS
                    .iter()
                    .filter(|other| other.package == layout.package)
                    .count(),
                1
            );
        }
    }
}
