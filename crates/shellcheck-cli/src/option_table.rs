//! The option table of the CLI, shared with the build script that generates
//! the completion scripts from it.

/// Formats the port implements. `getOpt`'s format validation lists exactly
/// these, sorted (mirroring `Map.keys` of the Haskell `formats` map).
pub const SUPPORTED_FORMATS: &[&str] =
    &["checkstyle", "diff", "gcc", "json", "json1", "quiet", "tty"];

/// The `-S`/`--severity` values, most severe first.
pub const SEVERITIES: [&str; 4] = ["error", "warning", "info", "style"];

/// Argument kind for a recognised option, following the Haskell `ArgDescr`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ArgKind {
    /// Takes no argument (`NoArg`).
    None,
    /// Requires an argument (`ReqArg`): `--opt=v`, `--opt v`, `-ov`, `-o v`.
    Required,
    /// Optional argument (`OptArg`): only `--opt=v` / `-ov` supply one; a
    /// following word is NOT consumed (matches `getOpt`).
    Optional,
}

/// One `Option` of the Haskell `options` list: its letter, long name, the
/// `Flag` key it produces, how it takes an argument, the argument's
/// placeholder, and its help text.
pub struct OptDef {
    pub short: Option<char>,
    pub long: &'static str,
    pub key: &'static str,
    pub kind: ArgKind,
    pub arg: &'static str,
    pub help: &'static str,
}

/// The recognised option table (mirrors `options` in shellcheck.hs).
pub const OPTS: &[OptDef] = &[
    OptDef {
        short: Some('a'),
        long: "check-sourced",
        key: "sourced",
        kind: ArgKind::None,
        arg: "",
        help: "Include warnings from sourced files",
    },
    OptDef {
        short: Some('C'),
        long: "color",
        key: "color",
        kind: ArgKind::Optional,
        arg: "WHEN",
        help: "Use color (auto, always, never)",
    },
    OptDef {
        short: Some('i'),
        long: "include",
        key: "include",
        kind: ArgKind::Required,
        arg: "CODE1,CODE2..",
        help: "Consider only given types of warnings",
    },
    OptDef {
        short: Some('e'),
        long: "exclude",
        key: "exclude",
        kind: ArgKind::Required,
        arg: "CODE1,CODE2..",
        help: "Exclude types of warnings",
    },
    OptDef {
        short: None,
        long: "extended-analysis",
        key: "extended-analysis",
        kind: ArgKind::Required,
        arg: "bool",
        help: "Perform dataflow analysis (default true)",
    },
    OptDef {
        short: Some('f'),
        long: "format",
        key: "format",
        kind: ArgKind::Required,
        arg: "FORMAT",
        help: "Output format (checkstyle, diff, gcc, json, json1, quiet, tty)",
    },
    OptDef {
        short: Some('j'),
        long: "jobs",
        key: "jobs",
        kind: ArgKind::Required,
        arg: "N",
        help: "Analyze files with N workers (default: up to 4 CPUs; quiet stays sequential)",
    },
    OptDef {
        short: None,
        long: "list-optional",
        key: "list-optional",
        kind: ArgKind::None,
        arg: "",
        help: "List checks disabled by default",
    },
    OptDef {
        short: None,
        long: "norc",
        key: "norc",
        kind: ArgKind::None,
        arg: "",
        help: "Don't look for .shellcheckrc and .editorconfig files",
    },
    OptDef {
        short: None,
        long: "rcfile",
        key: "rcfile",
        kind: ArgKind::Required,
        arg: "RCFILE",
        help: "Prefer the specified configuration file over searching for one",
    },
    OptDef {
        short: Some('o'),
        long: "enable",
        key: "enable",
        kind: ArgKind::Required,
        arg: "check1,check2..",
        help: "List of optional checks to enable (or 'all')",
    },
    OptDef {
        short: Some('P'),
        long: "source-path",
        key: "source-path",
        kind: ArgKind::Required,
        arg: "SOURCEPATHS",
        help: "Specify path when looking for sourced files (\"SCRIPTDIR\" for script's dir)",
    },
    OptDef {
        short: Some('s'),
        long: "shell",
        key: "shell",
        kind: ArgKind::Required,
        arg: "SHELLNAME",
        help: "Specify dialect (sh, bash, dash, ksh, busybox, zsh, mksh, oksh, loksh, yash, posh, bosh, osh, brush, freebsd-sh, netbsd-sh)",
    },
    OptDef {
        short: Some('S'),
        long: "severity",
        key: "severity",
        kind: ArgKind::Required,
        arg: "SEVERITY",
        help: "Minimum severity of errors to consider (error, warning, info, style)",
    },
    OptDef {
        short: Some('V'),
        long: "version",
        key: "version",
        kind: ArgKind::None,
        arg: "",
        help: "Print version information",
    },
    OptDef {
        short: Some('W'),
        long: "wiki-link-count",
        key: "wiki-link-count",
        kind: ArgKind::Required,
        arg: "NUM",
        help: "The number of wiki links to show, when applicable",
    },
    OptDef {
        short: Some('x'),
        long: "external-sources",
        key: "externals",
        kind: ArgKind::None,
        arg: "",
        help: "Allow 'source' outside of FILES",
    },
    OptDef {
        short: None,
        long: "help",
        key: "help",
        kind: ArgKind::None,
        arg: "",
        help: "Show this usage summary and exit",
    },
    OptDef {
        short: None,
        long: "files-from",
        key: "files-from",
        kind: ArgKind::Required,
        arg: "FILE",
        help: "Read input files from FILE (one per line, or '-' for stdin)",
    },
    #[cfg(feature = "completions")]
    OptDef {
        short: None,
        long: "generate-completions",
        key: "completions",
        kind: ArgKind::Required,
        arg: "SHELL",
        help: "Print a completion script (bash, zsh, fish, powershell)",
    },
];

/// A shell `--generate-completions` writes a script for.
#[cfg(feature = "completions")]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Shell {
    /// GNU Bash.
    Bash,
    /// Zsh.
    Zsh,
    /// Fish.
    Fish,
    /// PowerShell.
    Powershell,
}

#[cfg(feature = "completions")]
impl Shell {
    /// Every shell with a completion script.
    pub const ALL: [Self; 4] = [Self::Bash, Self::Zsh, Self::Fish, Self::Powershell];

    /// The `--generate-completions` value naming this shell.
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::Bash => "bash",
            Self::Zsh => "zsh",
            Self::Fish => "fish",
            Self::Powershell => "powershell",
        }
    }

    /// The script's file name, as each shell's completion directory expects
    /// it.
    #[must_use]
    pub const fn file_name(self) -> &'static str {
        match self {
            Self::Bash => "rshellcheck.bash",
            Self::Zsh => "_rshellcheck",
            Self::Fish => "rshellcheck.fish",
            Self::Powershell => "rshellcheck.ps1",
        }
    }
}
