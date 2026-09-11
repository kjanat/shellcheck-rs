//! `.shellcheckrc` / `--rcfile` configuration support.
//!
//! Mirrors the discovery and directive handling of the Haskell driver
//! (`shellcheck.hs`: `getConfig`, `findConfig`, `getConfigPaths`, `defaultPaths`,
//! `readConfig`) and the rc-directive subset of the core annotation parser
//! (`ShellCheck.Parser.readAnnotationWithoutPrefix`).
//!
//! An rc file has one directive per line, `key=value`. `#` starts a comment
//! (whole-line or trailing) which is stripped, blank lines are ignored, and
//! unknown keys are silently ignored. Lines repeating a key accumulate. Only
//! the "annotation" directive set is recognised:
//!
//!   * `disable=SC2086,SC2181` / `disable=all` -> add codes to excluded warnings
//!   * `enable=check-name,other` -> append to optional checks
//!   * `shell=bash` -> shell dialect override (if valid)
//!   * `extended-analysis=true|false` -> dataflow analysis toggle
//!   * `external-sources=true|false` -> parsed, inert (source resolver not ported)
//!   * `source-path=...` -> parsed, inert (source resolver not ported)
//!   * `source=...` -> parsed, inert
//!
//! The parser is IO-free where it can be; discovery reads the filesystem via
//! `std` only (no external dependencies).

use std::path::{Path, PathBuf};

use shellcheck_rs::interface::Shell;

use crate::options::parse_shell;

/// Parsed rc directives from one config file (directives accumulate across
/// lines). `shell`/`extended_analysis` keep only the last value seen, matching
/// the core annotation semantics where a later `ShellOverride` supersedes.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct RcConfig {
    /// Individual codes from `disable=` directives (ranges expanded).
    pub disabled_codes: Vec<i64>,
    /// `disable=all` was seen: exclude every warning.
    pub disable_all: bool,
    /// Names from `enable=` directives, in order.
    pub enabled_checks: Vec<String>,
    /// The `shell=` override, if a recognised dialect was given.
    pub shell: Option<Shell>,
    /// The `extended-analysis=` toggle, if given.
    pub extended_analysis: Option<bool>,
}

/// Parse the contents of an rc file into an [`RcConfig`]. Never fails: lines
/// that do not parse are ignored, mirroring the oracle's tolerant handling.
pub fn parse_contents(contents: &str) -> RcConfig {
    let mut cfg = RcConfig::default();
    for raw in contents.lines() {
        // Strip a `#` comment (whole-line or trailing).
        let line = match raw.split_once('#') {
            Some((before, _)) => before,
            None => raw,
        };
        let line = line.trim();
        if line.is_empty() {
            continue;
        }
        let (key, value) = match line.split_once('=') {
            Some((k, v)) => (k.trim(), v.trim()),
            None => continue, // no '=' : not a directive, ignore
        };
        // The established annotation parser accepts quoted directive values,
        // e.g. `disable='SC2086,SC2181'` or `shell="bash"`; strip a matching
        // surrounding quote pair before applying.
        apply_directive(&mut cfg, key, unquote(value));
    }
    cfg
}

fn apply_directive(cfg: &mut RcConfig, key: &str, value: &str) {
    match key {
        "disable" => {
            for elem in value.split(',') {
                let elem = elem.trim();
                if elem.is_empty() {
                    continue;
                }
                if elem == "all" {
                    cfg.disable_all = true;
                    continue;
                }
                // `from` or `from-to`; a bare code disables just that code
                // (DisableComment from (from+1)); a range disables [from, to).
                match elem.split_once('-') {
                    Some((from, to)) => {
                        if let (Some(from), Some(to)) = (parse_code(from), parse_code(to)) {
                            for c in from..to {
                                cfg.disabled_codes.push(c);
                            }
                        }
                    }
                    None => {
                        if let Some(c) = parse_code(elem) {
                            cfg.disabled_codes.push(c);
                        }
                    }
                }
            }
        }
        "enable" => {
            for name in value.split(',') {
                let name = name.trim();
                if !name.is_empty() {
                    cfg.enabled_checks.push(name.to_string());
                }
            }
        }
        "shell" => {
            // Keep the FIRST recognised shell override: `determineShell` selects
            // the first `ShellOverride` (headOrDefault), so a later `shell=`
            // line does not supersede an earlier valid one. An unknown value is
            // ignored (the oracle emits SC1103 but proceeds without override).
            if cfg.shell.is_none() {
                if let Some(sh) = parse_shell(value) {
                    cfg.shell = Some(sh);
                }
            }
        }
        "extended-analysis" => match value {
            "true" => cfg.extended_analysis = Some(true),
            "false" => cfg.extended_analysis = Some(false),
            _ => {}
        },
        // Recognised but inert (the source resolver is not ported). Parsed so
        // that a present directive is not mistaken for an error.
        "external-sources" | "source-path" | "source" => {}
        // Unknown keys are silently ignored.
        _ => {}
    }
}

/// Strip a single matching pair of surrounding single or double quotes.
/// `'SC2086,SC2181'` -> `SC2086,SC2181`, `"bash"` -> `bash`; unquoted or
/// mismatched values are returned unchanged.
fn unquote(s: &str) -> &str {
    let b = s.as_bytes();
    if b.len() >= 2 && (b[0] == b'\'' || b[0] == b'"') && b[b.len() - 1] == b[0] {
        &s[1..s.len() - 1]
    } else {
        s
    }
}

/// Parse a warning code, tolerating an optional `SC` prefix.
fn parse_code(s: &str) -> Option<i64> {
    let digits = s.trim().strip_prefix("SC").unwrap_or_else(|| s.trim());
    if digits.is_empty() || !digits.bytes().all(|b| b.is_ascii_digit()) {
        return None;
    }
    digits.parse::<i64>().ok()
}

/// Read and parse an explicit `--rcfile`. Returns `None` if the file cannot be
/// read (the caller prints the warning), mirroring `readConfig` returning
/// `Nothing`.
pub fn read_config_file(path: &Path) -> Option<RcConfig> {
    let contents = std::fs::read_to_string(path).ok()?;
    Some(parse_contents(&contents))
}

/// Discover the applicable rc config for a single input by walking up from the
/// input's directory to the filesystem root, then the user config dirs. Uses
/// the first candidate that exists and is readable (`findConfig`).
///
/// For stdin (`-`) the current working directory is used as the starting point
/// (`getConfig` normalises `-` to the CWD via `canonicalizePath`).
pub fn discover(input_name: &str) -> Option<RcConfig> {
    let dir = starting_dir(input_name)?;
    for candidate in candidate_paths(&dir) {
        // `findConfig`/`readConfig` select the FIRST candidate that EXISTS
        // (doesFileExist). A nearer existing-but-unreadable file is still
        // selected: the oracle reports the read error and uses an empty config,
        // rather than silently falling through to a parent or user config.
        if candidate.is_file() {
            match std::fs::read_to_string(&candidate) {
                Ok(contents) => return Some(parse_contents(&contents)),
                Err(e) => {
                    eprintln!("{}: {}", candidate.display(), e);
                    return Some(RcConfig::default());
                }
            }
        }
    }
    None
}

/// The directory to begin the upward search from for a given input.
fn starting_dir(input_name: &str) -> Option<PathBuf> {
    if input_name == "-" {
        return std::env::current_dir().ok();
    }
    // Normalise like `canonicalizePath`, falling back to the given path if it
    // cannot be canonicalised (e.g. the file does not exist yet).
    let path = std::fs::canonicalize(input_name).unwrap_or_else(|_| PathBuf::from(input_name));
    let dir = path.parent().map(|p| p.to_path_buf());
    match dir {
        Some(d) if !d.as_os_str().is_empty() => Some(d),
        // A bare relative filename has no parent component: use the CWD.
        _ => std::env::current_dir().ok(),
    }
}

/// The ordered list of candidate rc file paths for a starting directory:
/// `<dir>/.shellcheckrc` then `<dir>/shellcheckrc` at each level from `dir` up
/// to the root, followed by the user home and XDG config paths (`defaultPaths`).
fn candidate_paths(dir: &Path) -> Vec<PathBuf> {
    let mut paths = Vec::new();
    for ancestor in dir.ancestors() {
        paths.push(ancestor.join(".shellcheckrc"));
        paths.push(ancestor.join("shellcheckrc"));
    }
    paths.extend(default_paths());
    paths
}

/// `defaultPaths`: the user home rc (`getAppUserDataDirectory "shellcheckrc"`,
/// i.e. `$HOME/.shellcheckrc` on Unix) and the XDG config rc
/// (`getXdgDirectory XdgConfig "shellcheckrc"`, i.e.
/// `$XDG_CONFIG_HOME/shellcheckrc` or `$HOME/.config/shellcheckrc`).
fn default_paths() -> Vec<PathBuf> {
    let mut paths = Vec::new();
    let home = std::env::var_os("HOME").map(PathBuf::from);
    if let Some(home) = &home {
        paths.push(home.join(".shellcheckrc"));
    }
    if let Some(xdg) = std::env::var_os("XDG_CONFIG_HOME").map(PathBuf::from) {
        paths.push(xdg.join("shellcheckrc"));
    } else if let Some(home) = &home {
        paths.push(home.join(".config").join("shellcheckrc"));
    }
    paths
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_single_disable() {
        let c = parse_contents("disable=SC1234");
        assert_eq!(c.disabled_codes, vec![1234]);
        assert!(!c.disable_all);
    }

    #[test]
    fn strips_whole_line_and_trailing_comments() {
        let c = parse_contents("# a comment\ndisable=SC2148 # trailing comment\n");
        assert_eq!(c.disabled_codes, vec![2148]);
    }

    #[test]
    fn ignores_blank_lines() {
        let c = parse_contents("\n\n   \n\t\n");
        assert_eq!(c, RcConfig::default());
    }

    #[test]
    fn disable_list_splits_and_accepts_sc_prefix_or_bare() {
        let c = parse_contents("disable=SC2086,2181");
        assert_eq!(c.disabled_codes, vec![2086, 2181]);
    }

    #[test]
    fn disable_all_sets_flag() {
        let c = parse_contents("disable=all");
        assert!(c.disable_all);
        assert!(c.disabled_codes.is_empty());
    }

    #[test]
    fn disable_range_expands() {
        let c = parse_contents("disable=2086-2089");
        assert_eq!(c.disabled_codes, vec![2086, 2087, 2088]);
    }

    #[test]
    fn multiple_disable_lines_accumulate() {
        let c = parse_contents("disable=SC2148\ndisable=SC2086\n");
        assert_eq!(c.disabled_codes, vec![2148, 2086]);
    }

    #[test]
    fn enable_appends_names() {
        let c = parse_contents("enable=avoid-nullary-conditions,check-extra-masked-returns");
        assert_eq!(
            c.enabled_checks,
            vec![
                "avoid-nullary-conditions".to_string(),
                "check-extra-masked-returns".to_string()
            ]
        );
    }

    #[test]
    fn shell_valid_and_invalid() {
        assert_eq!(parse_contents("shell=bash").shell, Some(Shell::Bash));
        assert_eq!(parse_contents("shell=sh").shell, Some(Shell::Sh));
        // Unknown dialect is ignored (no override), not an error.
        assert_eq!(parse_contents("shell=zsh").shell, None);
        // Aliases route through parse_shell (shellForExecutable).
        assert_eq!(parse_contents("shell=ksh93").shell, Some(Shell::Ksh));
    }

    #[test]
    fn shell_keeps_first_override() {
        // determineShell selects the first ShellOverride, so a later shell=
        // does not supersede an earlier valid one.
        assert_eq!(
            parse_contents("shell=sh\nshell=bash\n").shell,
            Some(Shell::Sh)
        );
    }

    #[test]
    fn quoted_values_are_unquoted() {
        assert_eq!(
            parse_contents("disable='SC2086,SC2181'").disabled_codes,
            vec![2086, 2181]
        );
        assert_eq!(parse_contents("shell=\"bash\"").shell, Some(Shell::Bash));
        // A mismatched/again-unquoted value is left as-is (and then rejected).
        assert_eq!(parse_contents("shell='bash\"").shell, None);
    }

    #[test]
    fn extended_analysis_toggle() {
        assert_eq!(
            parse_contents("extended-analysis=true").extended_analysis,
            Some(true)
        );
        assert_eq!(
            parse_contents("extended-analysis=false").extended_analysis,
            Some(false)
        );
        // Unrecognised value is ignored.
        assert_eq!(
            parse_contents("extended-analysis=maybe").extended_analysis,
            None
        );
    }

    #[test]
    fn unknown_keys_are_ignored() {
        let c = parse_contents("severity=error\ninclude=SC1000\nbogus=stuff\ndisable=SC2148");
        // severity/include/bogus are not rc directives -> ignored; disable applies.
        assert_eq!(c.disabled_codes, vec![2148]);
        assert!(!c.disable_all);
        assert_eq!(c.enabled_checks.len(), 0);
    }

    #[test]
    fn inert_directives_parse_without_error() {
        let c = parse_contents("external-sources=true\nsource-path=/x\nsource=lib.sh");
        assert_eq!(c, RcConfig::default());
    }

    #[test]
    fn lines_without_equals_are_ignored() {
        let c = parse_contents("this is not a directive\ndisable=SC2148");
        assert_eq!(c.disabled_codes, vec![2148]);
    }
}
