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
//!   * 3 = SyntaxFailure  (getOpt/usage error: unknown flag, missing argument,
//!         bad number, bad boolean)
//!   * 4 = SupportFailure (unknown format / shell / severity / color value)
//!
//! The parser is intentionally IO-free and returns an [`Outcome`]; the binary
//! is responsible for printing to stderr/stdout and exiting. This keeps the
//! parser unit-testable without shelling out.

use shellcheck_rs::interface::{CheckSpec, ColorOption, Severity, Shell};

/// Formats the port implements. `getOpt`'s format validation lists exactly
/// these, sorted (mirroring `Map.keys` of the Haskell `formats` map).
pub const SUPPORTED_FORMATS: &[&str] =
    &["checkstyle", "diff", "gcc", "json", "json1", "quiet", "tty"];

/// What the caller should do after parsing.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Outcome {
    /// Parsing succeeded; run the analysis with this configuration.
    Run(RunConfig),
    /// Print the version banner to stdout and exit 0.
    PrintVersion,
    /// Print the usage summary to stdout and exit 0.
    PrintHelp,
    /// Print the (currently empty) optional-check listing to stdout and exit 0.
    ListOptional,
    /// Print `message` to stderr and exit with `code` (3 or 4).
    Error { message: String, code: u8 },
}

/// A successful parse: the format to render, the input files (`-` == stdin),
/// and a `CheckSpec` template carrying the wired analysis options. The caller
/// clones the template per input, filling in `filename`/`script`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RunConfig {
    pub format: String,
    pub inputs: Vec<String>,
    pub spec_template: CheckSpec,
    /// Resolved from `-C/--color` (default `auto`), used by tty/diff.
    pub color: ColorOption,
    /// `-W/--wiki-link-count` (default 3), used by tty's wiki summary.
    pub wiki_link_count: usize,
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

/// Internal option key (the Haskell `Flag var` name) plus how it takes an arg.
struct OptDef {
    short: Option<char>,
    long: &'static str,
    key: &'static str,
    kind: ArgKind,
}

/// The recognised option table (mirrors `options` in shellcheck.hs).
const OPTS: &[OptDef] = &[
    OptDef { short: Some('a'), long: "check-sourced",     key: "sourced",           kind: ArgKind::None },
    OptDef { short: Some('C'), long: "color",             key: "color",             kind: ArgKind::Optional },
    OptDef { short: Some('i'), long: "include",           key: "include",           kind: ArgKind::Required },
    OptDef { short: Some('e'), long: "exclude",           key: "exclude",           kind: ArgKind::Required },
    OptDef { short: None,      long: "extended-analysis", key: "extended-analysis", kind: ArgKind::Required },
    OptDef { short: Some('f'), long: "format",            key: "format",            kind: ArgKind::Required },
    OptDef { short: None,      long: "list-optional",     key: "list-optional",     kind: ArgKind::None },
    OptDef { short: None,      long: "norc",              key: "norc",              kind: ArgKind::None },
    OptDef { short: None,      long: "rcfile",            key: "rcfile",            kind: ArgKind::Required },
    OptDef { short: Some('o'), long: "enable",            key: "enable",            kind: ArgKind::Required },
    OptDef { short: Some('P'), long: "source-path",       key: "source-path",       kind: ArgKind::Required },
    OptDef { short: Some('s'), long: "shell",             key: "shell",             kind: ArgKind::Required },
    OptDef { short: Some('S'), long: "severity",          key: "severity",          kind: ArgKind::Required },
    OptDef { short: Some('V'), long: "version",           key: "version",           kind: ArgKind::None },
    OptDef { short: Some('W'), long: "wiki-link-count",   key: "wiki-link-count",   kind: ArgKind::Required },
    OptDef { short: Some('x'), long: "external-sources",  key: "externals",         kind: ArgKind::None },
    OptDef { short: None,      long: "help",              key: "help",              kind: ArgKind::None },
    OptDef { short: None,      long: "files-from",        key: "files-from",        kind: ArgKind::Required },
];

fn find_long(name: &str) -> Option<&'static OptDef> {
    OPTS.iter().find(|o| o.long == name)
}
fn find_short(c: char) -> Option<&'static OptDef> {
    OPTS.iter().find(|o| o.short == Some(c))
}

/// The usage summary (`getUsageInfo`). Faithful in spirit to `usageInfo`; the
/// exact column layout is not load-bearing.
pub fn usage() -> String {
    // Mirrors GHC getOpt's `usageInfo`: two left columns (short-with-arg,
    // long-with-arg) padded to the widest entry, then the description. The
    // wording/placeholders match shellcheck.hs so `--help` and the
    // "No files specified." error read like the oracle's.
    let mut s = String::from("Usage: shellcheck [OPTIONS...] FILES...\n");
    let lines = [
        ("-a",                 "--check-sourced",           "Include warnings from sourced files"),
        ("-C[WHEN]",           "--color[=WHEN]",            "Use color (auto, always, never)"),
        ("-i CODE1,CODE2..",   "--include=CODE1,CODE2..",   "Consider only given types of warnings"),
        ("-e CODE1,CODE2..",   "--exclude=CODE1,CODE2..",   "Exclude types of warnings"),
        ("",                   "--extended-analysis=bool",  "Perform dataflow analysis (default true)"),
        ("-f FORMAT",          "--format=FORMAT",           "Output format (checkstyle, diff, gcc, json, json1, quiet, tty)"),
        ("",                   "--list-optional",           "List checks disabled by default"),
        ("",                   "--norc",                    "Don't look for .shellcheckrc files"),
        ("",                   "--rcfile=RCFILE",           "Prefer the specified configuration file over searching for one"),
        ("-o check1,check2..", "--enable=check1,check2..",  "List of optional checks to enable (or 'all')"),
        ("-P SOURCEPATHS",     "--source-path=SOURCEPATHS", "Specify path when looking for sourced files (\"SCRIPTDIR\" for script's dir)"),
        ("-s SHELLNAME",       "--shell=SHELLNAME",         "Specify dialect (sh, bash, dash, ksh, busybox)"),
        ("-S SEVERITY",        "--severity=SEVERITY",       "Minimum severity of errors to consider (error, warning, info, style)"),
        ("-V",                 "--version",                 "Print version information"),
        ("-W NUM",             "--wiki-link-count=NUM",     "The number of wiki links to show, when applicable"),
        ("-x",                 "--external-sources",        "Allow 'source' outside of FILES"),
        ("",                   "--help",                    "Show this usage summary and exit"),
        ("",                   "--files-from=FILE",         "Read input files from FILE (one per line, or '-' for stdin)"),
    ];
    let short_w = lines.iter().map(|(sh, _, _)| sh.len()).max().unwrap_or(0);
    let long_w = lines.iter().map(|(_, lo, _)| lo.len()).max().unwrap_or(0);
    for (short, long, desc) in lines {
        s.push_str(&format!("  {short:<short_w$}  {long:<long_w$}  {desc}\n"));
    }
    s
}

/// The optional checks the analyzer knows about, in the order the Haskell
/// `optionalChecks` list defines them. Each tuple is (name, description,
/// example, fix), matching the `--list-optional` catalog emitted by the oracle.
const OPTIONAL_CHECKS: &[(&str, &str, &str, &str)] = &[
    ("add-default-case",
     "Suggest adding a default case in `case` statements",
     "case $? in 0) echo 'Success';; esac",
     "case $? in 0) echo 'Success';; *) echo 'Fail' ;; esac"),
    ("avoid-negated-conditions",
     "Suggest removing unnecessary comparison negations",
     "[ ! \"$var\" -eq 1 ]",
     "[ \"$var\" -ne 1 ]"),
    ("avoid-nullary-conditions",
     "Suggest explicitly using -n in `[ $var ]`",
     "[ \"$var\" ]",
     "[ -n \"$var\" ]"),
    ("check-extra-masked-returns",
     "Check for additional cases where exit codes are masked",
     "rm -r \"$(get_chroot_dir)/home\"",
     "set -e; dir=\"$(get_chroot_dir)\"; rm -r \"$dir/home\""),
    ("check-set-e-suppressed",
     "Notify when set -e is suppressed during function invocation",
     "set -e; func() { cp *.txt ~/backup; rm *.txt; }; func && echo ok",
     "set -e; func() { cp *.txt ~/backup; rm *.txt; }; func; echo ok"),
    ("check-unassigned-uppercase",
     "Warn when uppercase variables are unassigned",
     "echo $VAR",
     "VAR=hello; echo $VAR"),
    ("deprecate-which",
     "Suggest 'command -v' instead of 'which'",
     "which javac",
     "command -v javac"),
    ("quote-safe-variables",
     "Suggest quoting variables without metacharacters",
     "var=hello; echo $var",
     "var=hello; echo \"$var\""),
    ("require-double-brackets",
     "Require [[ and warn about [ in Bash/Ksh",
     "[ -e /etc/issue ]",
     "[[ -e /etc/issue ]]"),
    ("require-variable-braces",
     "Suggest putting braces around all variable references",
     "var=hello; echo $var",
     "var=hello; echo ${var}"),
    ("useless-use-of-cat",
     "Check for Useless Use Of Cat (UUOC)",
     "cat foo | grep bar",
     "grep bar foo"),
];

/// Render the `--list-optional` catalog exactly as the oracle does: for each
/// check, four `key: value` lines followed by a blank line (`newLinesBetween`
/// in `printOptional`), including a trailing blank line after the last entry.
pub fn list_optional_text() -> String {
    let mut s = String::new();
    for (name, desc, example, fix) in OPTIONAL_CHECKS {
        s.push_str(&format!("name:    {name}\n"));
        s.push_str(&format!("desc:    {desc}\n"));
        s.push_str(&format!("example: {example}\n"));
        s.push_str(&format!("fix:     {fix}\n"));
        s.push('\n');
    }
    s
}

/// The version banner (`printVersion`), using the crate version.
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

/// Phase 1: tokenise argv into flags + files, mirroring `getOpt Permute`.
/// Returns `Err(message)` for a getOpt-level error (SyntaxFailure / exit 3):
/// unknown option or a missing required argument.
fn tokenize(argv: &[String]) -> Result<(Vec<Flag>, Vec<String>), String> {
    let mut flags: Vec<Flag> = Vec::new();
    let mut files: Vec<String> = Vec::new();
    let mut i = 0;
    while i < argv.len() {
        let arg = &argv[i];
        if arg == "--" {
            // Everything after `--` is a non-option.
            files.extend(argv[i + 1..].iter().cloned());
            break;
        } else if arg == "-" {
            // stdin: a filename, not an option.
            files.push("-".to_string());
        } else if let Some(long) = arg.strip_prefix("--") {
            let (name, inline_val) = match long.split_once('=') {
                Some((n, v)) => (n, Some(v.to_string())),
                None => (long, None),
            };
            let def = match find_long(name) {
                Some(d) => d,
                None => return Err(format!("unrecognized option `--{name}'")),
            };
            match def.kind {
                ArgKind::None => {
                    if inline_val.is_some() {
                        return Err(format!("option `--{name}' doesn't allow an argument"));
                    }
                    flags.push(Flag { key: def.key, value: None });
                }
                ArgKind::Required => {
                    let v = if let Some(v) = inline_val {
                        v
                    } else {
                        i += 1;
                        match argv.get(i) {
                            Some(v) => v.clone(),
                            None => {
                                return Err(format!("option `--{name}' requires an argument"));
                            }
                        }
                    };
                    flags.push(Flag { key: def.key, value: Some(v) });
                }
                ArgKind::Optional => {
                    // OptArg: only an inline `=value` supplies an argument.
                    flags.push(Flag { key: def.key, value: inline_val });
                }
            }
        } else if arg.starts_with('-') && arg.len() > 1 {
            // Short option cluster, e.g. `-ax`, `-sbash`, `-s bash`.
            let chars: Vec<char> = arg.chars().collect();
            let mut j = 1; // skip leading '-'
            while j < chars.len() {
                let c = chars[j];
                let def = match find_short(c) {
                    Some(d) => d,
                    None => return Err(format!("unrecognized option `-{c}'")),
                };
                match def.kind {
                    ArgKind::None => {
                        flags.push(Flag { key: def.key, value: None });
                        j += 1;
                    }
                    ArgKind::Required => {
                        let rest: String = chars[j + 1..].iter().collect();
                        let v = if !rest.is_empty() {
                            rest
                        } else {
                            i += 1;
                            match argv.get(i) {
                                Some(v) => v.clone(),
                                None => {
                                    return Err(format!("option `-{c}' requires an argument"));
                                }
                            }
                        };
                        flags.push(Flag { key: def.key, value: Some(v) });
                        break; // rest of cluster consumed as the argument
                    }
                    ArgKind::Optional => {
                        let rest: String = chars[j + 1..].iter().collect();
                        let v = if rest.is_empty() { None } else { Some(rest) };
                        flags.push(Flag { key: def.key, value: v });
                        break;
                    }
                }
            }
        } else {
            files.push(arg.clone());
        }
        i += 1;
    }
    Ok((flags, files))
}

/// Split a comma-separated list, dropping empty entries (Haskell
/// `filter (not . null) $ split ','`).
fn split_nonempty(s: &str) -> Vec<String> {
    s.split(',').filter(|x| !x.is_empty()).map(|x| x.to_string()).collect()
}

/// `parseNum`: strip an optional leading `SC`, require all digits.
fn parse_num(s: &str) -> Result<i64, String> {
    let digits = s.strip_prefix("SC").unwrap_or(s);
    if digits.is_empty() || !digits.bytes().all(|b| b.is_ascii_digit()) {
        return Err(format!("Invalid number: {s}"));
    }
    digits.parse::<i64>().map_err(|_| format!("Invalid number: {s}"))
}

/// `shellForExecutable` restricted to the values the port accepts.
pub fn parse_shell(s: &str) -> Option<Shell> {
    Some(match s {
        "sh" => Shell::Sh,
        "bash" => Shell::Bash,
        "dash" => Shell::Dash,
        "ksh" => Shell::Ksh,
        "busybox" => Shell::BusyboxSh,
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

/// Full argument parse. Mirrors `parseArguments` (phase 1, exit 3 on getOpt
/// errors) followed by `process`/`parseOption` (phase 2: fold over flags in
/// order, with `--version`/`--help`/`--list-optional` exiting 0 immediately,
/// value validation failing with exit 4, and format validated last).
pub fn parse(argv: &[String]) -> Outcome {
    // Phase 1: getOpt-level recognition.
    let (flags, files) = match tokenize(argv) {
        Ok(x) => x,
        Err(msg) => {
            return Outcome::Error {
                message: format!("{msg}\n\n{}", usage()),
                code: 3,
            };
        }
    };

    // Phase 2: fold over flags in order.
    let mut spec = CheckSpec::default();
    let mut format: Option<String> = None;
    let mut color = ColorOption::ColorAuto;
    let mut wiki_link_count: usize = 3;

    for flag in &flags {
        match flag.key {
            // --- Immediate informational exits (exit 0). ---
            "version" => return Outcome::PrintVersion,
            "help" => return Outcome::PrintHelp,
            "list-optional" => return Outcome::ListOptional,

            // --- Wired into CheckSpec (effective in the analysis core). ---
            "shell" => {
                let v = flag.value.as_deref().unwrap_or("");
                match parse_shell(v) {
                    Some(sh) => spec.shell_type_override = Some(sh),
                    None => {
                        return Outcome::Error {
                            message: format!("Unknown shell: {v}"),
                            code: 4,
                        };
                    }
                }
            }
            "severity" => {
                let v = flag.value.as_deref().unwrap_or("");
                match parse_severity(v) {
                    Some(sev) => spec.min_severity = sev,
                    None => return support_error("severity", &["error", "warning", "info", "style"]),
                }
            }
            "include" => {
                let mut new = Vec::new();
                for c in split_nonempty(flag.value.as_deref().unwrap_or("")) {
                    match parse_num(&c) {
                        Ok(n) => new.push(n),
                        Err(m) => return Outcome::Error { message: m, code: 3 },
                    }
                }
                // csIncludedWarnings = if null new then old else Just new <> old
                if !new.is_empty() {
                    match &mut spec.included_warnings {
                        Some(old) => new.append(old),
                        None => {}
                    }
                    spec.included_warnings = Some(new);
                }
            }
            "exclude" => {
                let mut new = Vec::new();
                for c in split_nonempty(flag.value.as_deref().unwrap_or("")) {
                    match parse_num(&c) {
                        Ok(n) => new.push(n),
                        Err(m) => return Outcome::Error { message: m, code: 3 },
                    }
                }
                // csExcludedWarnings = new ++ old
                new.extend(std::mem::take(&mut spec.excluded_warnings));
                spec.excluded_warnings = new;
            }
            "enable" => {
                // csOptionalChecks = old ++ split ',' value  (no empty-filter)
                let value = flag.value.as_deref().unwrap_or("");
                for c in value.split(',') {
                    spec.optional_checks.push(c.to_string());
                }
            }
            "norc" => spec.ignore_rc = true,

            // --- Accepted and set on the spec, effective where the core supports it. ---
            "sourced" => spec.check_sourced = true,
            "extended-analysis" => {
                let v = flag.value.as_deref().unwrap_or("");
                match v {
                    "true" => spec.extended_analysis = Some(true),
                    "false" => spec.extended_analysis = Some(false),
                    _ => {
                        return Outcome::Error {
                            message: format!("Invalid boolean, expected true/false: {v}"),
                            code: 3,
                        };
                    }
                }
            }

            // --- Validated but not yet effective in the core. ---
            "color" => {
                // Default value when no argument is given is "always" (matches
                // the Haskell OptArg default), then validated.
                let v = flag.value.clone().unwrap_or_else(|| "always".to_string());
                color = match v.as_str() {
                    "auto" => ColorOption::ColorAuto,
                    "always" => ColorOption::ColorAlways,
                    "never" => ColorOption::ColorNever,
                    _ => return support_error("color", &["auto", "always", "never"]),
                };
            }
            "wiki-link-count" => {
                // Parsed as a number; invalid -> SyntaxFailure (exit 3).
                let v = flag.value.as_deref().unwrap_or("");
                match parse_num(v) {
                    Ok(n) => wiki_link_count = n.max(0) as usize,
                    Err(m) => return Outcome::Error { message: m, code: 3 },
                }
            }

            // --- Accepted-but-not-yet-effective (parsed, no core support yet). ---
            // -P/--source-path: the source resolver is not ported.
            "source-path" => {}
            // -x/--external-sources: reading sources outside FILES is not ported.
            "externals" => {}
            // --rcfile: rc-file resolution is not ported.
            "rcfile" => {}
            // --files-from: handled below (expands into the input list).
            "files-from" => {}

            // --format: validated after the fold (handled specially, like Haskell).
            // getOption returns the FIRST matching flag, so `-f json -f tty`
            // keeps json. Only set when not already set.
            "format" => {
                if format.is_none() {
                    format = flag.value.clone();
                }
            }

            other => {
                // Should be unreachable: every OPTS key is handled above.
                return Outcome::Error {
                    message: format!("Internal error for --{other}. Please file a bug :("),
                    code: 3,
                };
            }
        }
    }

    // Expand --files-from (one path per line, '#' comments and blanks skipped).
    let mut inputs: Vec<String> = Vec::new();
    let mut had_files_from = false;
    for flag in &flags {
        if flag.key == "files-from" {
            had_files_from = true;
            let path = flag.value.as_deref().unwrap_or("");
            let contents = if path == "-" {
                use std::io::Read;
                let mut s = String::new();
                if std::io::stdin().read_to_string(&mut s).is_err() {
                    return Outcome::Error {
                        message: "Could not read file list from stdin".to_string(),
                        code: 2,
                    };
                }
                s
            } else {
                match std::fs::read_to_string(path) {
                    Ok(s) => s,
                    Err(e) => {
                        return Outcome::Error {
                            message: format!("Could not read file list: {path}: {e}"),
                            code: 2,
                        };
                    }
                }
            };
            for line in contents.lines() {
                let line = line.trim();
                if line.is_empty() || line.starts_with('#') {
                    continue;
                }
                inputs.push(line.to_string());
            }
        }
    }
    inputs.extend(files);

    // An empty final input list is a usage error (exit 3), NOT an implicit
    // stdin read: the oracle requires one or more filenames or an explicit `-`
    // and prints "No files specified." with the usage summary
    // (shellcheck.hs `parseArguments`). Reading stdin here would turn a common
    // invocation mistake into a hang on an interactive terminal.
    let _ = had_files_from;
    if inputs.is_empty() {
        return Outcome::Error {
            message: format!("No files specified.\n\n{}", usage()),
            code: 3,
        };
    }

    // Validate format last (mirrors `process`: fold, then format lookup).
    let format = format.unwrap_or_else(|| "tty".to_string());
    if !SUPPORTED_FORMATS.contains(&format.as_str()) {
        let mut message = format!("Unknown format {format}\nSupported formats:");
        for f in SUPPORTED_FORMATS {
            message.push_str(&format!("\n  {f}"));
        }
        return Outcome::Error { message, code: 4 };
    }

    Outcome::Run(RunConfig { format, inputs, spec_template: spec, color, wiki_link_count })
}

/// Build a SupportFailure (exit 4) error mirroring `parseEnum`.
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
        a.iter().map(|s| s.to_string()).collect()
    }

    fn run(a: &[&str]) -> RunConfig {
        match parse(&args(a)) {
            Outcome::Run(c) => c,
            other => panic!("expected Run, got {other:?}"),
        }
    }

    #[test]
    fn explicit_stdin_tty() {
        let c = run(&["-"]);
        assert_eq!(c.inputs, vec!["-".to_string()]);
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
    fn format_first_wins() {
        // getOption returns the first match: `-f json -f tty` keeps json.
        let c = run(&["-f", "json", "-f", "tty", "-"]);
        assert_eq!(c.format, "json");
    }

    #[test]
    fn unknown_flag_is_syntax_error() {
        match parse(&args(&["--bogusflag"])) {
            Outcome::Error { code, .. } => assert_eq!(code, 3),
            other => panic!("expected Error(3), got {other:?}"),
        }
    }

    #[test]
    fn unknown_short_flag_is_syntax_error() {
        match parse(&args(&["-Z"])) {
            Outcome::Error { code, .. } => assert_eq!(code, 3),
            other => panic!("expected Error(3), got {other:?}"),
        }
    }

    #[test]
    fn version_exits_zero() {
        assert_eq!(parse(&args(&["-V"])), Outcome::PrintVersion);
        assert_eq!(parse(&args(&["--version"])), Outcome::PrintVersion);
    }

    #[test]
    fn version_wins_over_later_bad_value() {
        // Fold is left-to-right: version exits before shell is validated.
        assert_eq!(parse(&args(&["--version", "--shell=zsh"])), Outcome::PrintVersion);
    }

    #[test]
    fn unknown_flag_beats_version() {
        // getOpt recognition (phase 1) runs before the fold, so an unknown
        // flag anywhere is exit 3 even with --version present.
        match parse(&args(&["--version", "--bogusflag"])) {
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
        for a in [vec!["--shell=zsh"], vec!["-s", "zsh"], vec!["--shell", "zsh"]] {
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
        assert_eq!(c.inputs, vec!["-".to_string()]);

        let c = run(&["--shell=ksh", "-"]);
        assert_eq!(c.spec_template.shell_type_override, Some(Shell::Ksh));

        let c = run(&["-sdash", "-"]); // glued short
        assert_eq!(c.spec_template.shell_type_override, Some(Shell::Dash));

        assert_eq!(run(&["-s", "busybox", "-"]).spec_template.shell_type_override, Some(Shell::BusyboxSh));
        assert_eq!(run(&["-s", "sh", "-"]).spec_template.shell_type_override, Some(Shell::Sh));
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
        assert_eq!(c.spec_template.included_warnings, Some(vec![1000, 2086, 2154]));
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
        let c = run(&["-o", "avoid-nullary-conditions,check-extra-masked-returns", "-"]);
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
    fn accepted_but_inert_flags_parse() {
        // -P, -x, --rcfile, -a parse without error and do not become filenames.
        let c = run(&["-x", "-a", "-P", "src", "--rcfile", "my.rc", "-"]);
        assert_eq!(c.inputs, vec!["-".to_string()]);
        assert!(c.spec_template.check_sourced);
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
        assert_eq!(c.inputs, vec!["a.sh".to_string(), "b.sh".to_string()]);
        assert_eq!(c.spec_template.shell_type_override, Some(Shell::Bash));
    }

    #[test]
    fn double_dash_stops_option_parsing() {
        let c = run(&["--", "-s", "bash"]);
        assert_eq!(c.inputs, vec!["-s".to_string(), "bash".to_string()]);
    }
}
