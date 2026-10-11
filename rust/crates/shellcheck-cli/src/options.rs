//! Command-line option parsing for the ShellCheck CLI.
//!
//! This mirrors the Haskell `shellcheck.hs` driver (`options`/`parseArguments`/
//! `parseOption`/`statusToCode`) closely enough to reproduce its user-visible
//! behaviour: the same recognised option set, the same `getOpt Permute`
//! semantics (options and files may be interleaved, short options may be
//! clustered/glued, long options accept `--opt=val` or `--opt val`), and the
//! same exit statuses.
//!
//! Exit statuses (Haskell `statusToCode`):
//!   * 0 = no problems / informational exit (`--version`, `--help`, ...)
//!   * 1 = problems found (decided by the caller after running the analysis)
//!   * 2 = runtime/IO error (decided by the caller)
//!   * 3 = `SyntaxFailure`  (getOpt/usage error: unknown flag, missing argument,
//!     bad number, bad boolean)
//!   * 4 = `SupportFailure` (unknown format / shell / severity / color value)
//!
//! One deliberate difference: an argument that starts with `-` is a filename
//! when its first option does not exist, and also when it reads as options but
//! fails, or carries a value that its option rejects, while a file by that name
//! exists. `getOpt` rejects both (exit 3); [POSIX Utility Syntax Guideline 14]
//! only asks that arguments identifiable as options be treated as options.
//!
//! [POSIX Utility Syntax Guideline 14]: https://pubs.opengroup.org/onlinepubs/9799919799/basedefs/V1_chap12.html#tag_12_02
//!
//! The parser returns an [`Outcome`]; the binary is responsible for printing to
//! stderr/stdout and exiting. Its only IO is reading `--files-from` lists and
//! the existence check the caller passes in.

use std::ffi::OsString;
use std::fmt::Write;
use std::ops::ControlFlow;
use std::path::{Path, PathBuf};

use shellcheck_rs::interface::{CheckSpec, ColorOption, Severity, Shell};

/// Formats the port implements. `getOpt`'s format validation lists exactly
/// these, sorted (mirroring `Map.keys` of the Haskell `formats` map).
pub const SUPPORTED_FORMATS: &[&str] =
    &["checkstyle", "diff", "gcc", "json", "json1", "quiet", "tty"];

/// What the caller should do after parsing.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Outcome {
    /// Parsing succeeded; run the analysis with this configuration. Boxed: it
    /// dwarfs the other variants, which are a string at most.
    Run(Box<RunConfig>),
    /// Print the version banner to stdout and exit 0.
    PrintVersion,
    /// Print the usage summary to stdout and exit 0.
    PrintHelp,
    /// Print the (currently empty) optional-check listing to stdout and exit 0.
    ListOptional,
    /// Print `message` to stderr and exit with `code` (3 or 4).
    Error {
        /// What to print.
        message: String,
        /// The exit status.
        code: u8,
    },
}

/// Options resulting from a successful CLI argument parse.
///
/// Holds the format, input targets, and a `CheckSpec` template that the caller
/// clones per input file when setting `filename` and `script`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RunConfig {
    /// The `-f`/`--format` name, `tty` by default.
    pub format: String,
    /// Input file paths, or `"-"` for stdin.
    pub inputs: Vec<PathBuf>,
    /// The `CheckSpec` every input starts from.
    pub spec_template: CheckSpec,
    /// Resolved color setting from `-C`/`--color` (defaults to `auto`), used by tty and diff output.
    pub color: ColorOption,
    /// Max wiki link count from `-W`/`--wiki-link-count` (defaults to 3), used by tty wiki summary.
    pub wiki_link_count: usize,
    /// Maximum file-analysis workers (default 1; quiet mode stays sequential).
    pub jobs: usize,
    /// Explicit config path from `--rcfile <path>`. When `None`, standard `.shellcheckrc` discovery applies.
    pub rcfile: Option<String>,
    /// Search directories for sourced files from `-P`/`--source-path` in flag order. `SCRIPTDIR` expands to target script directory.
    pub source_paths: Vec<String>,
    /// Allows reading sourced files not included in `inputs` (`-x`/`--external-sources`).
    pub external_sources: bool,
}

/// Argument kind for a recognised option, following the Haskell `ArgDescr`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ArgKind {
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
struct OptDef {
    short: Option<char>,
    long: &'static str,
    key: &'static str,
    kind: ArgKind,
    arg: &'static str,
    help: &'static str,
}

/// The recognised option table (mirrors `options` in shellcheck.hs).
const OPTS: &[OptDef] = &[
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
        help: "Analyze files with N workers (default 1; quiet stays sequential)",
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
        help: "Specify dialect (sh, bash, dash, ksh, busybox)",
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
];

fn find_short(c: char) -> Option<&'static OptDef> {
    OPTS.iter().find(|o| o.short == Some(c))
}

impl OptDef {
    /// `fmtShort`: the letter with its argument placeholder.
    fn short_form(&self) -> String {
        self.short.map_or_else(String::new, |c| match self.kind {
            ArgKind::None => format!("-{c}"),
            ArgKind::Required => format!("-{c} {}", self.arg),
            ArgKind::Optional => format!("-{c}[{}]", self.arg),
        })
    }

    /// `fmtLong`: the long name with its argument placeholder.
    fn long_form(&self) -> String {
        match self.kind {
            ArgKind::None => format!("--{}", self.long),
            ArgKind::Required => format!("--{}={}", self.long, self.arg),
            ArgKind::Optional => format!("--{}[={}]", self.long, self.arg),
        }
    }
}

/// `usageInfo`'s table: the short and long forms, each column padded to its
/// widest entry, then the help text.
fn usage_table<'a>(opts: impl Iterator<Item = &'a OptDef> + Clone) -> String {
    let short_w = opts
        .clone()
        .map(|o| o.short_form().len())
        .max()
        .unwrap_or(0);
    let long_w = opts.clone().map(|o| o.long_form().len()).max().unwrap_or(0);
    let mut s = String::new();
    for o in opts {
        let _ = writeln!(
            s,
            "  {:<short_w$}  {:<long_w$}  {}",
            o.short_form(),
            o.long_form(),
            o.help
        );
    }
    s
}

/// The usage summary (`getUsageInfo`).
#[must_use]
pub fn usage() -> String {
    format!(
        "Usage: shellcheck [OPTIONS...] FILES...\n{}",
        usage_table(OPTS.iter())
    )
}

/// The optional checks the analyzer knows about, in the order the Haskell
/// `optionalChecks` list defines them. Each tuple is (name, description,
/// example, fix), matching the `--list-optional` catalog emitted by the oracle.
const OPTIONAL_CHECKS: &[(&str, &str, &str, &str)] = &[
    (
        "add-default-case",
        "Suggest adding a default case in `case` statements",
        "case $? in 0) echo 'Success';; esac",
        "case $? in 0) echo 'Success';; *) echo 'Fail' ;; esac",
    ),
    (
        "avoid-negated-conditions",
        "Suggest removing unnecessary comparison negations",
        "[ ! \"$var\" -eq 1 ]",
        "[ \"$var\" -ne 1 ]",
    ),
    (
        "avoid-nullary-conditions",
        "Suggest explicitly using -n in `[ $var ]`",
        "[ \"$var\" ]",
        "[ -n \"$var\" ]",
    ),
    (
        "check-extra-masked-returns",
        "Check for additional cases where exit codes are masked",
        "rm -r \"$(get_chroot_dir)/home\"",
        "set -e; dir=\"$(get_chroot_dir)\"; rm -r \"$dir/home\"",
    ),
    (
        "check-set-e-suppressed",
        "Notify when set -e is suppressed during function invocation",
        "set -e; func() { cp *.txt ~/backup; rm *.txt; }; func && echo ok",
        "set -e; func() { cp *.txt ~/backup; rm *.txt; }; func; echo ok",
    ),
    (
        "check-unassigned-uppercase",
        "Warn when uppercase variables are unassigned",
        "echo $VAR",
        "VAR=hello; echo $VAR",
    ),
    (
        "deprecate-which",
        "Suggest 'command -v' instead of 'which'",
        "which javac",
        "command -v javac",
    ),
    (
        "quote-safe-variables",
        "Suggest quoting variables without metacharacters",
        "var=hello; echo $var",
        "var=hello; echo \"$var\"",
    ),
    (
        "require-double-brackets",
        "Require [[ and warn about [ in Bash/Ksh",
        "[ -e /etc/issue ]",
        "[[ -e /etc/issue ]]",
    ),
    (
        "require-double-equals",
        "Require == and warn about = in Bash tests",
        "[[ \"$x\" = \"$y\" ]]",
        "[[ \"$x\" == \"$y\" ]]",
    ),
    (
        "require-variable-braces",
        "Suggest putting braces around all variable references",
        "var=hello; echo $var",
        "var=hello; echo ${var}",
    ),
    (
        "useless-use-of-cat",
        "Check for Useless Use Of Cat (UUOC)",
        "cat foo | grep bar",
        "grep bar foo",
    ),
];

/// Renders the `--list-optional` catalog matching upstream `printOptional`.
///
/// Outputs four `key: value` lines (`name`, `desc`, `example`, `fix`) per check,
/// separated by blank lines (`newLinesBetween`), including a trailing blank line.
#[must_use]
pub fn list_optional_text() -> String {
    let mut s = String::new();
    for (name, desc, example, fix) in OPTIONAL_CHECKS {
        let _ = writeln!(
            s,
            "name:    {name}\ndesc:    {desc}\nexample: {example}\nfix:     {fix}\n"
        );
    }
    s
}

/// The version banner (`printVersion`), using the crate version.
#[must_use]
pub fn version_banner() -> String {
    format!(
        "ShellCheck - shell script analysis tool\nversion: {}\nlicense: GNU General Public License, version 3\nwebsite: https://www.shellcheck.net",
        env!("CARGO_PKG_VERSION")
    )
}

/// A recognised flag with its (optional) argument, in argv order.
#[derive(Debug, Clone, PartialEq, Eq)]
struct Flag {
    key: &'static str,
    value: Option<String>,
}

/// One result of `getOpt`'s `getNext` for an option argument.
enum OptResult {
    /// `Opt`: a recognised option.
    Opt(Flag),
    /// `UnreqOpt`: an option nothing declares, as written.
    Unrecognized(String),
    /// `OptErr`: an ambiguous long option, or a missing or unwanted argument.
    Error(String),
}

/// Phase 1: `getOpt Permute`. Returns the flags, the files, and the error
/// messages, each ending in a newline: the argument errors first, then the
/// unrecognized options, as `getOpt` orders them.
///
/// An argument whose first option does not exist can only be a filename, and
/// is one. An argument that reads as options but fails, or carries a value
/// that its option rejects, is a filename when `exists` says so.
fn tokenize(
    argv: &[OsString],
    exists: &dyn Fn(&Path) -> bool,
) -> (Vec<Flag>, Vec<PathBuf>, Vec<String>) {
    let mut flags: Vec<Flag> = Vec::new();
    let mut files: Vec<PathBuf> = Vec::new();
    let mut errors: Vec<String> = Vec::new();
    let mut unrecognized: Vec<String> = Vec::new();
    let mut rest = argv.iter();
    while let Some(native_arg) = rest.next() {
        let arg = native_arg.to_string_lossy();
        if arg == "--" {
            files.extend(rest.by_ref().map(PathBuf::from));
            continue;
        }
        if arg == "-" || !arg.starts_with('-') {
            files.push(PathBuf::from(native_arg));
            continue;
        }
        let mut ahead = rest.clone();
        let results = get_next(&arg, &mut ahead);
        let only_a_file = matches!(results.first(), Some(OptResult::Unrecognized(_)));
        if only_a_file || (!results.iter().all(is_valid_opt) && exists(Path::new(native_arg))) {
            files.push(PathBuf::from(native_arg));
            continue;
        }
        rest = ahead;
        for result in results {
            match result {
                OptResult::Opt(flag) => flags.push(flag),
                OptResult::Unrecognized(u) => {
                    unrecognized.push(format!("unrecognized option `{u}'\n"));
                }
                OptResult::Error(e) => errors.push(e),
            }
        }
    }
    errors.extend(unrecognized);
    (flags, files, errors)
}

/// `getNext` for an argument that starts with `-` and is neither `-` nor
/// `--`. A short cluster yields one result per option, and an unrecognized
/// letter does not stop the rest of the cluster.
fn get_next(arg: &str, rest: &mut std::slice::Iter<'_, OsString>) -> Vec<OptResult> {
    if let Some(long) = arg.strip_prefix("--") {
        return vec![long_opt(long, rest)];
    }
    let mut out = Vec::new();
    let mut chars = arg[1..].chars();
    while let Some(c) = chars.next() {
        let tail = chars.as_str().to_string();
        let Some(def) = find_short(c) else {
            out.push(OptResult::Unrecognized(format!("-{c}")));
            continue;
        };
        let value = match def.kind {
            ArgKind::None => {
                out.push(OptResult::Opt(Flag {
                    key: def.key,
                    value: None,
                }));
                continue;
            }
            ArgKind::Required if tail.is_empty() => {
                let Some(v) = rest.next() else {
                    out.push(OptResult::Error(format!(
                        "option `-{c}' requires an argument {}\n",
                        def.arg
                    )));
                    return out;
                };
                Some(v.to_string_lossy().into_owned())
            }
            ArgKind::Required => Some(tail),
            ArgKind::Optional => (!tail.is_empty()).then_some(tail),
        };
        out.push(OptResult::Opt(Flag {
            key: def.key,
            value,
        }));
        return out;
    }
    out
}

/// `longOpt`: an exact name wins, otherwise any option whose name starts with
/// the one given; more than one candidate is ambiguous.
fn long_opt(long: &str, rest: &mut std::slice::Iter<'_, OsString>) -> OptResult {
    let (name, inline) = match long.split_once('=') {
        Some((name, value)) => (name, Some(value)),
        None => (long, None),
    };
    let exact: Vec<&OptDef> = OPTS.iter().filter(|o| o.long == name).collect();
    let candidates = if exact.is_empty() {
        OPTS.iter().filter(|o| o.long.starts_with(name)).collect()
    } else {
        exact
    };
    let def = match candidates.as_slice() {
        [] => return OptResult::Unrecognized(format!("--{long}")),
        [def] => def,
        many => {
            return OptResult::Error(format!(
                "option `--{name}' is ambiguous; could be one of:\n{}",
                usage_table(many.iter().copied())
            ));
        }
    };
    let value = match (def.kind, inline) {
        (ArgKind::None, None) => None,
        (ArgKind::None, Some(_)) => {
            return OptResult::Error(format!("option `--{name}' doesn't allow an argument\n"));
        }
        (ArgKind::Required, Some(v)) => Some(v.to_string()),
        (ArgKind::Required, None) => match rest.next() {
            Some(v) => Some(v.to_string_lossy().into_owned()),
            None => {
                return OptResult::Error(format!(
                    "option `--{name}' requires an argument {}\n",
                    def.arg
                ));
            }
        },
        (ArgKind::Optional, v) => v.map(str::to_string),
    };
    OptResult::Opt(Flag {
        key: def.key,
        value,
    })
}

/// A recognised option with a value that the option accepts. `parseOption`
/// and the format lookup decide, and `--enable` names must be checks that
/// exist.
fn is_valid_opt(result: &OptResult) -> bool {
    let OptResult::Opt(flag) = result else {
        return false;
    };
    match flag.key {
        "format" => flag
            .value
            .as_deref()
            .is_some_and(|f| SUPPORTED_FORMATS.contains(&f)),
        "enable" => {
            flag.value.as_deref().unwrap_or("").split(',').all(|name| {
                name == "all" || OPTIONAL_CHECKS.iter().any(|(check, ..)| *check == name)
            })
        }
        _ => !matches!(
            parse_option(flag, &mut Folded::new()),
            ControlFlow::Break(Outcome::Error { .. })
        ),
    }
}

/// Split a comma-separated list, dropping empty entries (Haskell
/// `filter (not . null) $ split ','`).
fn split_nonempty(s: &str) -> Vec<String> {
    s.split(',')
        .filter(|x| !x.is_empty())
        .map(std::string::ToString::to_string)
        .collect()
}

/// `parseNum`: strip an optional leading `SC`, require all digits.
fn parse_num(s: &str) -> Result<i64, String> {
    let digits = s.strip_prefix("SC").unwrap_or(s);
    if digits.is_empty() || !digits.bytes().all(|b| b.is_ascii_digit()) {
        return Err(format!("Invalid number: {s}"));
    }
    digits
        .parse::<i64>()
        .map_err(|_| format!("Invalid number: {s}"))
}

/// The codes of an `--include`/`--exclude` list; a bad one is a
/// `SyntaxFailure` (exit 3).
fn parse_codes(value: Option<&str>) -> ControlFlow<Outcome, Vec<i64>> {
    let mut codes = Vec::new();
    for c in split_nonempty(value.unwrap_or("")) {
        match parse_num(&c) {
            Ok(n) => codes.push(n),
            Err(message) => return ControlFlow::Break(Outcome::Error { message, code: 3 }),
        }
    }
    ControlFlow::Continue(codes)
}

/// `shellForExecutable` (ShellCheck.Data): maps interpreter names, including
/// the established aliases, to a dialect. Used for `--shell`, rc `shell=`, and
/// `# shellcheck shell=` directives.
#[must_use]
pub fn parse_shell(s: &str) -> Option<Shell> {
    Some(match s {
        "sh" => Shell::Sh,
        "bash" | "bats" => Shell::Bash,
        "busybox" | "busybox sh" | "busybox ash" => Shell::BusyboxSh,
        "dash" | "ash" => Shell::Dash,
        "ksh" | "ksh88" | "ksh93" | "oksh" => Shell::Ksh,
        _ => return None,
    })
}

fn parse_severity(s: &str) -> Option<Severity> {
    Some(match s {
        "error" => Severity::ErrorC,
        "warning" => Severity::WarningC,
        "info" => Severity::InfoC,
        "style" => Severity::StyleC,
        _ => return None,
    })
}

/// The options folded so far, flag by flag.
struct Folded {
    spec: CheckSpec,
    format: Option<String>,
    color: ColorOption,
    wiki_link_count: usize,
    jobs: usize,
    rcfile: Option<String>,
    source_paths: Vec<String>,
    external_sources: bool,
}

impl Folded {
    fn new() -> Self {
        Self {
            spec: CheckSpec::default(),
            format: None,
            color: ColorOption::ColorAuto,
            wiki_link_count: 3,
            jobs: 1,
            rcfile: None,
            source_paths: Vec::new(),
            external_sources: false,
        }
    }
}

fn parse_worker_count(value: &str) -> ControlFlow<Outcome, usize> {
    match value.parse::<usize>() {
        Ok(n) if n > 0 => ControlFlow::Continue(n),
        _ => ControlFlow::Break(Outcome::Error {
            message: format!("Invalid worker count, expected a positive integer: {value}"),
            code: 3,
        }),
    }
}

/// `parseOption` for one flag. `Break` ends the parse with that outcome.
fn parse_option(flag: &Flag, o: &mut Folded) -> ControlFlow<Outcome> {
    match flag.key {
        // --- Immediate informational exits (exit 0). ---
        "version" => return ControlFlow::Break(Outcome::PrintVersion),
        "help" => return ControlFlow::Break(Outcome::PrintHelp),
        "list-optional" => return ControlFlow::Break(Outcome::ListOptional),

        // --- Wired into CheckSpec (effective in the analysis core). ---
        "shell" => {
            let v = flag.value.as_deref().unwrap_or("");
            match parse_shell(v) {
                Some(sh) => o.spec.shell_type_override = Some(sh),
                None => {
                    return ControlFlow::Break(Outcome::Error {
                        message: format!("Unknown shell: {v}"),
                        code: 4,
                    });
                }
            }
        }
        "severity" => {
            let Some(sev) = parse_severity(flag.value.as_deref().unwrap_or("")) else {
                let valid = ["error", "warning", "info", "style"];
                return ControlFlow::Break(support_error("severity", &valid));
            };
            o.spec.min_severity = sev;
        }
        "include" => {
            let mut new = parse_codes(flag.value.as_deref())?;
            // csIncludedWarnings = if null new then old else Just new <> old
            if !new.is_empty() {
                if let Some(old) = &mut o.spec.included_warnings {
                    new.append(old);
                }
                o.spec.included_warnings = Some(new);
            }
        }
        "exclude" => {
            let mut new = parse_codes(flag.value.as_deref())?;
            // csExcludedWarnings = new ++ old
            new.extend(std::mem::take(&mut o.spec.excluded_warnings));
            o.spec.excluded_warnings = new;
        }
        "enable" => {
            // csOptionalChecks = old ++ split ',' value  (no empty-filter)
            let value = flag.value.as_deref().unwrap_or("");
            for c in value.split(',') {
                o.spec.optional_checks.push(c.to_string());
            }
        }
        "norc" => o.spec.ignore_rc = true,

        // --- Accepted and set on the spec, effective where the core supports it. ---
        "sourced" => o.spec.check_sourced = true,
        "extended-analysis" => {
            let v = flag.value.as_deref().unwrap_or("");
            match v {
                "true" => o.spec.extended_analysis = Some(true),
                "false" => o.spec.extended_analysis = Some(false),
                _ => {
                    return ControlFlow::Break(Outcome::Error {
                        message: format!("Invalid boolean, expected true/false: {v}"),
                        code: 3,
                    });
                }
            }
        }

        // --- Validated but not yet effective in the core. ---
        "color" => {
            // Default value when no argument is given is "always" (matches
            // the Haskell OptArg default), then validated.
            o.color = match flag.value.as_deref().unwrap_or("always") {
                "auto" => ColorOption::ColorAuto,
                "always" => ColorOption::ColorAlways,
                "never" => ColorOption::ColorNever,
                _ => {
                    return ControlFlow::Break(support_error(
                        "color",
                        &["auto", "always", "never"],
                    ));
                }
            };
        }
        "jobs" => o.jobs = parse_worker_count(flag.value.as_deref().unwrap_or(""))?,
        "wiki-link-count" => {
            // Parsed as a number; invalid -> SyntaxFailure (exit 3).
            match parse_num(flag.value.as_deref().unwrap_or("")) {
                Ok(n) => o.wiki_link_count = usize::try_from(n).unwrap_or(usize::MAX),
                Err(message) => return ControlFlow::Break(Outcome::Error { message, code: 3 }),
            }
        }

        // -P/--source-path: `sourcePaths = sourcePaths options ++ paths`,
        // where each flag's value is one search path (`splitSearchPath`).
        "source-path" => {
            o.source_paths
                .extend(split_search_path(flag.value.as_deref().unwrap_or("")));
        }
        // -x/--external-sources: allow 'source' outside of FILES.
        "externals" => o.external_sources = true,
        // --rcfile: captured here; resolved per input in the driver.
        // A later flag overwrites an earlier one (last-wins, matching the
        // Haskell fold `options { rcfile = Just str }`).
        "rcfile" => o.rcfile.clone_from(&flag.value),
        // --files-from: handled by `files_from` (expands into the input list).
        "files-from" => {}

        // --format: validated after the fold (handled specially, like Haskell).
        // getOption returns the FIRST matching flag, so `-f json -f tty`
        // keeps json. Only set when not already set.
        "format" => {
            if o.format.is_none() {
                o.format.clone_from(&flag.value);
            }
        }

        other => {
            // Should be unreachable: every OPTS key is handled above.
            return ControlFlow::Break(Outcome::Error {
                message: format!("Internal error for --{other}. Please file a bug :("),
                code: 3,
            });
        }
    }
    ControlFlow::Continue(())
}

/// The inputs every `--files-from` lists, in flag order: one path per line,
/// '#' comments and blanks skipped.
fn files_from(flags: &[Flag]) -> Result<Vec<String>, Outcome> {
    let mut inputs: Vec<String> = Vec::new();
    for flag in flags.iter().filter(|f| f.key == "files-from") {
        let path = flag.value.as_deref().unwrap_or("");
        let contents = if path == "-" {
            use std::io::Read;
            let mut s = String::new();
            if std::io::stdin().read_to_string(&mut s).is_err() {
                return Err(Outcome::Error {
                    message: "Could not read file list from stdin".to_string(),
                    code: 2,
                });
            }
            s
        } else {
            std::fs::read_to_string(path).map_err(|e| Outcome::Error {
                message: format!("Could not read file list: {path}: {e}"),
                code: 2,
            })?
        };
        inputs.extend(
            contents
                .lines()
                .map(str::trim)
                .filter(|line| !line.is_empty() && !line.starts_with('#'))
                .map(str::to_string),
        );
    }
    Ok(inputs)
}

/// Parses CLI arguments following upstream's two-phase process.
///
/// - **Phase 1 (`parseArguments`)**: Tokenizes flags; exits with code 3 on `getOpt` errors.
/// - **Phase 2 (`process` / `parseOption`)**: Folds flags in order:
///   - Exits 0 immediately for `--version`, `--help`, and `--list-optional`.
///   - Exits 4 on option value validation errors.
///   - Validates format last.
///
/// `exists` says whether a file by a given name exists.
#[must_use]
pub fn parse(argv: &[String], exists: &dyn Fn(&str) -> bool) -> Outcome {
    let argv: Vec<OsString> = argv.iter().map(OsString::from).collect();
    parse_os(&argv, &|path| path.to_str().is_some_and(exists))
}

/// Parse native CLI arguments without using their display text as file identity.
///
/// Option names and values are textual; input filenames retain their exact
/// platform representation, including filenames beginning with a dash.
#[must_use]
pub fn parse_os(argv: &[OsString], exists: &dyn Fn(&Path) -> bool) -> Outcome {
    // Phase 1: getOpt-level recognition.
    let (flags, files, errors) = tokenize(argv, exists);
    if !errors.is_empty() {
        return Outcome::Error {
            message: format!("{}\n{}", errors.concat(), usage()),
            code: 3,
        };
    }

    // Phase 2: fold over flags in order.
    let mut o = Folded::new();
    for flag in &flags {
        if let ControlFlow::Break(outcome) = parse_option(flag, &mut o) {
            return outcome;
        }
    }

    let inputs = match files_from(&flags) {
        Ok(inputs) => inputs,
        Err(e) => return e,
    };
    let mut inputs: Vec<PathBuf> = inputs.into_iter().map(PathBuf::from).collect();
    inputs.extend(files);

    // An empty input list with NO --files-from is a usage error (exit 3), NOT
    // an implicit stdin read: the oracle requires one or more filenames or an
    // explicit `-` and prints "No files specified." with the usage summary
    // (shellcheck.hs `parseArguments`). Reading stdin here would turn a common
    // invocation mistake into a hang on an interactive terminal.
    //
    // An explicit but empty --files-from (e.g. `--files-from=/dev/null`) is
    // deliberately permitted: the oracle checks zero files and exits 0. In that
    // case we fall through with an empty input list, which renders nothing.
    if inputs.is_empty() && !flags.iter().any(|f| f.key == "files-from") {
        return Outcome::Error {
            message: format!("No files specified.\n\n{}", usage()),
            code: 3,
        };
    }

    // Validate format last (mirrors `process`: fold, then format lookup).
    let format = o.format.unwrap_or_else(|| "tty".to_string());
    if !SUPPORTED_FORMATS.contains(&format.as_str()) {
        let mut message = format!("Unknown format {format}\nSupported formats:");
        for f in SUPPORTED_FORMATS {
            let _ = write!(message, "\n  {f}");
        }
        return Outcome::Error { message, code: 4 };
    }

    Outcome::Run(Box::new(RunConfig {
        format,
        inputs,
        spec_template: o.spec,
        color: o.color,
        wiki_link_count: o.wiki_link_count,
        jobs: o.jobs,
        rcfile: o.rcfile,
        source_paths: o.source_paths,
        external_sources: o.external_sources,
    }))
}

/// `System.FilePath.splitSearchPath` on POSIX: split on `:`, and an empty entry
/// means the working directory.
fn split_search_path(value: &str) -> Vec<String> {
    value
        .split(':')
        .map(|p| if p.is_empty() { "." } else { p }.to_string())
        .collect()
}

/// Build a `SupportFailure` (exit 4) error mirroring `parseEnum`.
fn support_error(name: &str, valid: &[&str]) -> Outcome {
    Outcome::Error {
        message: format!(
            "Unknown value for --{name}. Valid options are: {}",
            valid.join(", ")
        ),
        code: 4,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn args(a: &[&str]) -> Vec<String> {
        a.iter().map(std::string::ToString::to_string).collect()
    }

    /// `parse` in a directory with no files in it.
    fn parse(argv: &[String]) -> Outcome {
        super::parse(argv, &|_| false)
    }

    #[test]
    fn a_dash_argument_whose_first_option_does_not_exist_is_a_file() {
        let c = run(&["-.sh", "-nope.sh", "--bogus"]);
        assert_eq!(c.inputs, ["-.sh", "-nope.sh", "--bogus"].map(PathBuf::from));
        assert_eq!(c.spec_template.optional_checks, Vec::<String>::new());
    }

    #[test]
    fn a_failing_option_argument_is_a_file_only_when_the_file_exists() {
        let exists = |name: &str| matches!(name, "-fope.sh" | "-ope.sh" | "-xZ" | "-xa");
        match super::parse(&args(&["-fope.sh", "-ope.sh", "-xZ"]), &exists) {
            Outcome::Run(c) => {
                assert_eq!(c.inputs, ["-fope.sh", "-ope.sh", "-xZ"].map(PathBuf::from));
            }
            other => panic!("expected Run, got {other:?}"),
        }
        // Without the files they stay options, with their errors.
        match parse(&args(&["-fope.sh", "x"])) {
            Outcome::Error { code, message } => {
                assert_eq!(code, 4);
                assert!(message.starts_with("Unknown format ope.sh"));
            }
            other => panic!("expected Error(4), got {other:?}"),
        }
        match parse(&args(&["-xZ", "x"])) {
            Outcome::Error { code, message } => {
                assert_eq!(code, 3);
                assert!(message.starts_with("unrecognized option `-Z'\n\nUsage:"));
            }
            other => panic!("expected Error(3), got {other:?}"),
        }
        // A valid option stays an option, whatever files exist.
        match super::parse(&args(&["-xa", "f.sh"]), &exists) {
            Outcome::Run(c) => {
                assert!(c.external_sources);
                assert!(c.spec_template.check_sourced);
                assert_eq!(c.inputs, [PathBuf::from("f.sh")]);
            }
            other => panic!("expected Run, got {other:?}"),
        }
    }

    #[test]
    fn a_long_option_may_be_abbreviated_to_a_unique_prefix() {
        assert_eq!(parse(&args(&["--vers"])), Outcome::PrintVersion);
        assert_eq!(
            run(&["--exten=false", "-"]).spec_template.extended_analysis,
            Some(false)
        );
    }

    #[test]
    fn an_ambiguous_prefix_lists_its_candidates() {
        match parse(&args(&["--e", "x"])) {
            Outcome::Error { code, message } => {
                assert_eq!(code, 3);
                let candidates = "option `--e' is ambiguous; could be one of:\n  \
                    -e CODE1,CODE2..    --exclude=CODE1,CODE2..   Exclude types of warnings\n  \
                    \x20                   --extended-analysis=bool  Perform dataflow analysis (default true)\n  \
                    -o check1,check2..  --enable=check1,check2..  List of optional checks to enable (or 'all')\n  \
                    -x                  --external-sources        Allow 'source' outside of FILES\n\nUsage:";
                assert!(message.starts_with(candidates), "{message}");
            }
            other => panic!("expected Error(3), got {other:?}"),
        }
    }

    #[test]
    fn every_option_error_is_reported_argument_errors_first() {
        match parse(&args(&["-xZ", "--norc=1", "--shell"])) {
            Outcome::Error { code, message } => {
                assert_eq!(code, 3);
                assert!(
                    message.starts_with(
                        "option `--norc' doesn't allow an argument\n\
                         option `--shell' requires an argument SHELLNAME\n\
                         unrecognized option `-Z'\n\nUsage:"
                    ),
                    "{message}"
                );
            }
            other => panic!("expected Error(3), got {other:?}"),
        }
    }

    /// Every optional check upstream lists is implemented and reachable.
    #[test]
    fn list_optional_has_all_twelve_checks() {
        assert_eq!(list_optional_text().matches("name:").count(), 12);
    }

    fn run(a: &[&str]) -> RunConfig {
        match parse(&args(a)) {
            Outcome::Run(c) => *c,
            other => panic!("expected Run, got {other:?}"),
        }
    }

    #[test]
    fn explicit_stdin_tty() {
        let c = run(&["-"]);
        assert_eq!(c.inputs, vec![PathBuf::from("-")]);
        assert_eq!(c.format, "tty");
    }

    #[test]
    fn no_files_is_syntax_error() {
        // No filenames and no explicit `-`: usage error (exit 3), never an
        // implicit stdin read. Matches the oracle's "No files specified."
        match parse(&args(&[])) {
            Outcome::Error { code, message } => {
                assert_eq!(code, 3);
                assert!(message.contains("No files specified."));
            }
            other => panic!("expected Error(3), got {other:?}"),
        }
        // Options-only, still no input target: same error.
        match parse(&args(&["-s", "bash"])) {
            Outcome::Error { code, .. } => assert_eq!(code, 3),
            other => panic!("expected Error(3), got {other:?}"),
        }
    }

    #[test]
    fn empty_files_from_is_ok_not_error() {
        // An explicit but empty --files-from is permitted and yields an empty
        // input list (the oracle exits 0 having checked nothing), unlike the
        // no-arguments case which is a usage error.
        let c = run(&["--files-from=/dev/null"]);
        assert_eq!(c.inputs, [] as [PathBuf; 0]);
    }

    #[test]
    fn format_first_wins() {
        // getOption returns the first match: `-f json -f tty` keeps json.
        let c = run(&["-f", "json", "-f", "tty", "-"]);
        assert_eq!(c.format, "json");
    }

    #[test]
    fn version_exits_zero() {
        assert_eq!(parse(&args(&["-V"])), Outcome::PrintVersion);
        assert_eq!(parse(&args(&["--version"])), Outcome::PrintVersion);
    }

    #[test]
    fn version_wins_over_later_bad_value() {
        // Fold is left-to-right: version exits before shell is validated.
        assert_eq!(
            parse(&args(&["--version", "--shell=zsh"])),
            Outcome::PrintVersion
        );
    }

    #[test]
    fn an_option_error_beats_version() {
        // getOpt recognition (phase 1) runs before the fold, so an option
        // error anywhere is exit 3 even with --version present.
        match parse(&args(&["--version", "--shell"])) {
            Outcome::Error { code, .. } => assert_eq!(code, 3),
            other => panic!("expected Error(3), got {other:?}"),
        }
    }

    #[test]
    fn help_exits_zero() {
        assert_eq!(parse(&args(&["--help"])), Outcome::PrintHelp);
    }

    #[test]
    fn unknown_format_is_support_error() {
        // With a valid input target, format is validated last (exit 4).
        match parse(&args(&["--format=bogus", "-"])) {
            Outcome::Error { code, message } => {
                assert_eq!(code, 4);
                assert!(message.contains("Unknown format bogus"));
                assert!(message.contains("json1"));
            }
            other => panic!("expected Error(4), got {other:?}"),
        }
    }

    #[test]
    fn json1_format_ok() {
        assert_eq!(run(&["--format=json1", "-"]).format, "json1");
        assert_eq!(run(&["-f", "json1", "-"]).format, "json1");
        assert_eq!(run(&["--format", "json1", "-"]).format, "json1");
    }

    #[test]
    fn unknown_shell_is_support_error() {
        for a in [
            vec!["--shell=zsh"],
            vec!["-s", "zsh"],
            vec!["--shell", "zsh"],
        ] {
            match parse(&args(&a)) {
                Outcome::Error { code, .. } => assert_eq!(code, 4, "for {a:?}"),
                other => panic!("expected Error(4) for {a:?}, got {other:?}"),
            }
        }
    }

    #[test]
    fn valid_shell_both_forms() {
        // Separate-arg form must set the shell, not be treated as a filename.
        let c = run(&["-s", "bash", "-"]);
        assert_eq!(c.spec_template.shell_type_override, Some(Shell::Bash));
        assert_eq!(c.inputs, vec![PathBuf::from("-")]);

        let c = run(&["--shell=ksh", "-"]);
        assert_eq!(c.spec_template.shell_type_override, Some(Shell::Ksh));

        let c = run(&["-sdash", "-"]); // glued short
        assert_eq!(c.spec_template.shell_type_override, Some(Shell::Dash));

        assert_eq!(
            run(&["-s", "busybox", "-"])
                .spec_template
                .shell_type_override,
            Some(Shell::BusyboxSh)
        );
        assert_eq!(
            run(&["-s", "sh", "-"]).spec_template.shell_type_override,
            Some(Shell::Sh)
        );
    }

    #[test]
    fn severity_wired() {
        let c = run(&["-S", "error", "-"]);
        assert_eq!(c.spec_template.min_severity, Severity::ErrorC);
        let c = run(&["--severity=warning", "-"]);
        assert_eq!(c.spec_template.min_severity, Severity::WarningC);
    }

    #[test]
    fn bad_severity_is_support_error() {
        match parse(&args(&["-S", "bogus"])) {
            Outcome::Error { code, .. } => assert_eq!(code, 4),
            other => panic!("expected Error(4), got {other:?}"),
        }
    }

    #[test]
    fn include_wired_and_accumulates() {
        let c = run(&["-i", "SC2086,2154", "--include=SC1000", "-"]);
        // include: Just new <> old, so later flags prepend.
        assert_eq!(
            c.spec_template.included_warnings,
            Some(vec![1000, 2086, 2154])
        );
    }

    #[test]
    fn exclude_wired_and_accumulates() {
        let c = run(&["-e", "SC2086", "-e", "2154", "-"]);
        // exclude: new ++ old, later flags prepend.
        assert_eq!(c.spec_template.excluded_warnings, vec![2154, 2086]);
    }

    #[test]
    fn bad_include_number_is_syntax_error() {
        match parse(&args(&["-i", "notanumber"])) {
            Outcome::Error { code, .. } => assert_eq!(code, 3),
            other => panic!("expected Error(3), got {other:?}"),
        }
    }

    #[test]
    fn enable_wired() {
        let c = run(&[
            "-o",
            "avoid-nullary-conditions,check-extra-masked-returns",
            "-",
        ]);
        assert_eq!(
            c.spec_template.optional_checks,
            vec![
                "avoid-nullary-conditions".to_string(),
                "check-extra-masked-returns".to_string()
            ]
        );
    }

    #[test]
    fn norc_wired() {
        assert!(run(&["--norc", "-"]).spec_template.ignore_rc);
    }

    #[test]
    fn missing_required_arg_is_syntax_error() {
        match parse(&args(&["--shell"])) {
            Outcome::Error { code, .. } => assert_eq!(code, 3),
            other => panic!("expected Error(3), got {other:?}"),
        }
    }

    #[test]
    fn source_following_flags_are_wired() {
        // -P, -x, -a parse without error and do not become filenames.
        // --rcfile is captured into RunConfig (last-wins) but still does not
        // become a filename.
        let c = run(&["-x", "-a", "-P", "src", "--rcfile", "my.rc", "-"]);
        assert_eq!(c.inputs, vec![PathBuf::from("-")]);
        assert!(c.spec_template.check_sourced);
        assert!(c.external_sources);
        assert_eq!(c.source_paths, vec!["src".to_string()]);
        assert_eq!(c.rcfile, Some("my.rc".to_string()));
        // Neither is on by default.
        let c = run(&["-"]);
        assert!(!c.external_sources);
        assert_eq!(c.source_paths, [] as [std::string::String; 0]);
        assert!(!c.spec_template.check_sourced);
    }

    #[test]
    fn source_paths_accumulate_in_flag_order() {
        // `sourcePaths options ++ paths`, one flag's value split on ':'.
        let c = run(&["-P", "a:b", "--source-path=c", "-P", "SCRIPTDIR/d", "-"]);
        assert_eq!(
            c.source_paths,
            vec![
                "a".to_string(),
                "b".to_string(),
                "c".to_string(),
                "SCRIPTDIR/d".to_string()
            ]
        );
    }

    #[test]
    fn split_search_path_turns_empty_entries_into_dot() {
        // POSIX `splitSearchPath`.
        assert_eq!(split_search_path("a:b"), vec!["a", "b"]);
        assert_eq!(split_search_path(""), vec!["."]);
        assert_eq!(split_search_path("a::b"), vec!["a", ".", "b"]);
        assert_eq!(split_search_path(":a"), vec![".", "a"]);
    }

    #[test]
    fn rcfile_last_wins() {
        let c = run(&["--rcfile", "a.rc", "--rcfile=b.rc", "-"]);
        assert_eq!(c.rcfile, Some("b.rc".to_string()));
    }

    #[test]
    fn no_rcfile_is_none() {
        assert_eq!(run(&["-"]).rcfile, None);
    }

    #[test]
    fn color_invalid_is_support_error() {
        match parse(&args(&["--color=purple"])) {
            Outcome::Error { code, .. } => assert_eq!(code, 4),
            other => panic!("expected Error(4), got {other:?}"),
        }
        // Bare --color defaults to "always" and is accepted.
        assert!(matches!(parse(&args(&["--color", "-"])), Outcome::Run(_)));
    }

    #[test]
    fn files_and_options_interleave() {
        let c = run(&["a.sh", "-s", "bash", "b.sh"]);
        assert_eq!(c.inputs, vec![PathBuf::from("a.sh"), PathBuf::from("b.sh")]);
        assert_eq!(c.spec_template.shell_type_override, Some(Shell::Bash));
    }

    #[test]
    fn double_dash_stops_option_parsing() {
        let c = run(&["--", "-s", "bash"]);
        assert_eq!(c.inputs, vec![PathBuf::from("-s"), PathBuf::from("bash")]);
    }
}
