//! Port of `ShellCheck.EditorConfig`.
//!
//! Minimal support for reading shellcheck directives from EditorConfig style files (<https://editorconfig.org/>).
//!
//! Only the `shellcheck.*` keys of sections whose glob matches the file being checked are extracted,
//! and turned into the same "key=value" directive syntax that is used in .shellcheckrc files.

use crate::data::shell_for_executable;
use std::fmt::Write;

const REJECTED: &str = "invalid editorconfig value";

/// A `shellcheck.*` directive: its 1-based line, the key without the prefix,
/// and the trimmed value.
type Directive = (usize, String, String);

/// `parseEditorConfig`: the shellcheck directives in matching sections.
///
/// Given the contents of an EditorConfig style file and the name of the file
/// being checked, return the shellcheck directives (as a "key=value\n"
/// delimited blob, suitable for feeding into the same parser as .shellcheckrc)
/// found in matching sections.
///
/// As per the EditorConfig spec, files are read top to bottom and properties
/// from later sections override those from earlier ones (for the same key),
/// so on conflicts the last matching section wins.
#[must_use]
pub fn parse(contents: &str, name: &str) -> String {
    let usable: Vec<Directive> = all_directives(contents, name)
        .into_iter()
        .filter(|(_, key, value)| is_usable_directive(key, value))
        .collect();
    // Render each directive at its original line in the config file, so that
    // any parse error (SC1134) is reported at the correct line.
    let mut out = String::new();
    let mut previous = 0;
    for (line, key, value) in last_wins(usable) {
        out.push_str(&"\n".repeat(line.saturating_sub(previous + 1)));
        let _ = writeln!(out, "{key}={value}");
        previous = line;
    }
    out
}

/// `invalidDirectiveLines`: returns the 1-based line numbers of invalid
/// `shellcheck.*` directives, i.e.:
///   * `shellcheck.shell=<x>` where `<x>` is a non-empty, unknown shell
///     (e.g. `zsh`), which would otherwise silently suppress the SC2148
///     "unknown shell" warning;
///   * any `shellcheck.<key>=<value>` whose (trimmed) value contains `#` or
///     `;` anywhere, since EditorConfig does not allow inline comments and
///     such a value is otherwise silently truncated by the .shellcheckrc
///     parser's trailing-comment handling (e.g. both `disable=#abc` and
///     `disable=SC2148 #abc` would silently lose the part from `#` onwards).
///     Plain empty values are not reported here: they are simply no-ops.
///
/// Only directives in sections whose glob matches the file are reported.
#[must_use]
pub fn invalid_directive_lines(contents: &str, name: &str) -> Vec<usize> {
    all_directives(contents, name)
        .into_iter()
        .filter(|(_, key, value)| {
            if key == "shell" {
                !value.is_empty() && shell_for_executable(value).is_none()
            } else {
                has_comment_marker(value)
            }
        })
        .map(|(line, _, _)| line)
        .collect()
}

/// `editorConfigDirectives`: build the directive blob contributed by a single
/// EditorConfig file for the given file being checked.
///
/// Returns `None` if the file contributes nothing (no matching section, or
/// only empty values). Returns a blob of "key=value\n" directives when the matching sections are
/// valid, or a single rejected line at the position of any invalid
/// `shellcheck.*` directive so that the .shellcheckrc parser reports it as
/// SC1134.
#[must_use]
pub fn directives(contents: &str, name: &str) -> Option<String> {
    let mut bad = invalid_directive_lines(contents, name);
    if !bad.is_empty() {
        bad.sort_unstable();
        bad.dedup();
        return Some(bad.iter().fold(String::new(), |mut out, n| {
            let _ = writeln!(out, "{}{REJECTED}", "\n".repeat(n.saturating_sub(1)));
            out
        }));
    }
    let result = parse(contents, name);
    (!result.is_empty()).then_some(result)
}

/// A blob that only says an EditorConfig file was rejected:
/// `isEditorConfigRejection`.
#[must_use]
pub fn is_rejection(blob: &str) -> bool {
    lines(blob)
        .iter()
        .all(|l| trim(l).is_empty() || *l == REJECTED)
}

/// The blob `getEditorConfig` builds for an invalid `root` declaration.
#[must_use]
pub fn rejected_root(line: usize) -> String {
    format!("{}{REJECTED}\n", "\n".repeat(line.saturating_sub(1)))
}

/// `isEditorConfigRoot`: does the top-level (pre-section) part of an
/// EditorConfig file declare "root = true"? Per the spec, this stops the
/// search for further EditorConfig files in parent directories.
#[must_use]
pub fn is_editor_config_root(contents: &str) -> bool {
    pre_section_lines(contents)
        .iter()
        .any(|l| root_value(l).as_deref() == Some("true"))
}

/// `invalidRootLines`: returns the 1-based line numbers of invalid `root`
/// declarations, i.e. root values other than true/false (such as `root =`).
#[must_use]
pub fn invalid_root_lines(contents: &str) -> Vec<usize> {
    pre_section_lines(contents)
        .iter()
        .enumerate()
        .filter_map(|(i, l)| match root_value(l) {
            Some(value) if value != "true" && value != "false" => Some(i + 1),
            _ => None,
        })
        .collect()
}

/// `globToRegexString`: translate an EditorConfig glob pattern into an
/// anchored regex string.
///
/// Per the spec, patterns without a path separator are matched against the
/// file at any depth (as if prefixed with "**/").
#[must_use]
pub fn glob_to_regex_string(pattern: &str) -> String {
    let prefix = if pattern.contains('/') { "" } else { "(.*/)?" };
    let chars: Vec<char> = pattern.chars().collect();
    format!("^{prefix}{}$", glob_body(&chars))
}

/// `matchesGlob`: does the (relative path of the) file match the given
/// EditorConfig glob? A pattern that does not translate into a valid regex
/// matches nothing.
fn matches_glob(pattern: &str, name: &str) -> bool {
    regex::Regex::new(&format!("(?m){}", glob_to_regex_string(pattern)))
        .is_ok_and(|re| re.is_match(name))
}

fn glob_body(pattern: &[char]) -> String {
    let mut out = String::new();
    let mut i = 0;
    while i < pattern.len() {
        let c = pattern[i];
        let rest = &pattern[i + 1..];
        match c {
            '*' if rest.first() == Some(&'*') => {
                out.push_str(".*");
                i += 2;
                continue;
            }
            '*' => out.push_str("[^/]*"),
            '?' => out.push_str("[^/]"),
            '[' => match rest.iter().position(|&c| c == ']') {
                Some(end) => {
                    out.push('[');
                    out.push_str(&translate_class(&rest[..end]));
                    out.push(']');
                    i += end + 2;
                    continue;
                }
                None => out.push_str("\\["),
            },
            '{' => match find_matching_brace(rest) {
                Some((body, after)) => {
                    let alternatives: Vec<String> = brace_alternatives(&body)
                        .iter()
                        .map(|alt| glob_body(&alt.chars().collect::<Vec<_>>()))
                        .collect();
                    out.push_str(&build_alternation(&alternatives));
                    i += 1 + after;
                    continue;
                }
                None => out.push_str("\\{"),
            },
            c if ".\\+()^$|".contains(c) => {
                out.push('\\');
                out.push(c);
            }
            c => out.push(c),
        }
        i += 1;
    }
    out
}

/// `translateClass`: `!` negates, and a backslash is escaped.
fn translate_class(class: &[char]) -> String {
    let (negated, body) = match class.split_first() {
        Some(('!', body)) => (true, body),
        _ => (false, class),
    };
    let mut out = String::from(if negated { "^" } else { "" });
    for &c in body {
        if c == '\\' {
            out.push_str("\\\\");
        } else {
            out.push(c);
        }
    }
    out
}

/// `findMatchingBrace`: scan past a balanced `{` ... `}` pair, returning the
/// contents of the braces (with any nested braces verbatim) and how many
/// characters of `input` it used. Returns `None` if the braces are unbalanced.
fn find_matching_brace(input: &[char]) -> Option<(String, usize)> {
    let mut depth = 1;
    let mut body = String::new();
    for (i, &c) in input.iter().enumerate() {
        match c {
            '}' if depth == 1 => return Some((body, i + 1)),
            '}' => depth -= 1,
            '{' => depth += 1,
            _ => {}
        }
        body.push(c);
    }
    None
}

/// `buildAlternation`: wrap a list of regex alternatives in an anchored group.
/// Empty alternatives are handled so the result is always a valid regex:
///   * all empty  -> "" (the whole group matches the empty string)
///   * some empty -> "(a|b)?" (the group is optional)
///   * none empty -> "(a|b|c)"
fn build_alternation(alternatives: &[String]) -> String {
    if alternatives.iter().all(String::is_empty) {
        return String::new();
    }
    let non_empty: Vec<&str> = alternatives
        .iter()
        .filter(|a| !a.is_empty())
        .map(String::as_str)
        .collect();
    if non_empty.len() < alternatives.len() {
        format!("({})?", non_empty.join("|"))
    } else {
        format!("({})", non_empty.join("|"))
    }
}

/// `braceAlternatives`: expand EditorConfig brace alternatives. Besides the
/// comma separated form, EditorConfig supports numeric ranges like `{1..3}`
/// which match any integer in the range (none when the start is not below the
/// end). Commas inside nested braces (e.g. `ba{r,z}`) are not treated as
/// separators.
fn brace_alternatives(body: &str) -> Vec<String> {
    if let Some(dot) = body.find('.') {
        let (from, rest) = body.split_at(dot);
        if let Some(to) = rest.strip_prefix("..")
            && let (Some(from), Some(to)) = (read_int(from), read_int(to))
        {
            return if from < to {
                (from..=to).map(|n| n.to_string()).collect()
            } else {
                Vec::new()
            };
        }
    }
    split_top_level_commas(body)
}

/// `splitTopLevelCommas`: split on commas, but ignore commas that appear inside
/// nested `{...}` pairs so that `a,b{c,d}` yields `["a", "b{c,d}"]`.
fn split_top_level_commas(body: &str) -> Vec<String> {
    let mut parts = Vec::new();
    let mut current = String::new();
    let mut depth: usize = 0;
    for c in body.chars() {
        match c {
            '{' => depth += 1,
            '}' => depth = depth.saturating_sub(1),
            ',' if depth == 0 => {
                parts.push(std::mem::take(&mut current));
                continue;
            }
            _ => {}
        }
        current.push(c);
    }
    parts.push(current);
    parts
}

/// `reads s :: [(Int, String)]` with nothing left over: leading space, an
/// optional minus sign, digits.
fn read_int(s: &str) -> Option<i64> {
    let s = s.trim_start_matches(is_space);
    let (negative, digits) = s
        .strip_prefix('-')
        .map_or((false, s), |rest| (true, rest.trim_start_matches(is_space)));
    if digits.is_empty() || !digits.chars().all(|c| c.is_ascii_digit()) {
        return None;
    }
    let magnitude: i64 = digits.parse().ok()?;
    Some(if negative { -magnitude } else { magnitude })
}

/// `allDirectives name sections`: all `shellcheck.*` directives (as
/// (line, key, value) tuples) found in sections whose glob matches the file
/// being checked, in file order.
fn all_directives(contents: &str, name: &str) -> Vec<Directive> {
    sections(contents)
        .into_iter()
        .filter(|(pattern, _)| matches_glob(pattern, name))
        .flat_map(|(_, body)| body.into_iter().filter_map(|(n, l)| directive(n, l)))
        .collect()
}

/// `splitSections 1 (lines contents)`: each section header's pattern with the
/// numbered lines up to the next header. Lines before the first header
/// belong to no section.
fn sections(contents: &str) -> Vec<(String, Vec<(usize, &str)>)> {
    let mut out: Vec<(String, Vec<(usize, &str)>)> = Vec::new();
    for (i, l) in lines(contents).into_iter().enumerate() {
        match parse_header(l) {
            Some(pattern) => out.push((pattern, Vec::new())),
            None => {
                if let Some((_, body)) = out.last_mut() {
                    body.push((i + 1, l));
                }
            }
        }
    }
    out
}

/// `parseHeader`: `[pattern]`, after a full-line comment is dropped.
fn parse_header(l: &str) -> Option<String> {
    let t = trim(drop_line_comment(l));
    let inner = t.strip_prefix('[')?;
    let pattern = inner.strip_suffix(']')?;
    (!inner.is_empty()).then(|| pattern.to_string())
}

/// `toDirectivePair`: a `shellcheck.<key> = <value>` line.
fn directive(line: usize, l: &str) -> Option<Directive> {
    let t = trim(drop_line_comment(l));
    let (key, value) = t.split_once('=')?;
    let key = trim(key);
    let key = key.strip_prefix("shellcheck.")?;
    Some((line, key.to_string(), trim(value).to_string()))
}

/// `isUsableDirective`: only emit directives that the .shellcheckrc parser can
/// handle unambiguously. Unknown shells (e.g. `shellcheck.shell=zsh`) would
/// otherwise silently suppress the SC2148 "unknown shell" warning, so they are
/// dropped here and reported via `invalidDirectiveLines`. Values containing
/// `#` or `;` anywhere (not just at the start) are also dropped and reported:
/// EditorConfig has no inline comments, so such a value is otherwise silently
/// truncated by the .shellcheckrc parser's trailing-comment handling (e.g.
/// both `disable=#abc` and `disable=SC2148 #abc` would silently lose the part
/// from `#` onwards). Empty values for other keys are simply skipped (no-op):
/// the rc parser would silently accept them anyway.
fn is_usable_directive(key: &str, value: &str) -> bool {
    if key == "shell" {
        value.is_empty() || shell_for_executable(value).is_some()
    } else {
        !value.is_empty() && !has_comment_marker(value)
    }
}

fn has_comment_marker(value: &str) -> bool {
    value.contains(['#', ';'])
}

/// `lastWins`: keep only the last occurrence of each key, preserving the
/// relative order of the remaining (first-seen) entries.
fn last_wins(directives: Vec<Directive>) -> Vec<Directive> {
    let mut kept: Vec<Directive> = Vec::new();
    for d in directives.into_iter().rev() {
        if !kept.iter().any(|k| k.1 == d.1) {
            kept.push(d);
        }
    }
    kept.reverse();
    kept
}

/// The lines before the first section header.
fn pre_section_lines(contents: &str) -> Vec<&str> {
    lines(contents)
        .into_iter()
        .take_while(|l| parse_header(l).is_none())
        .collect()
}

/// `rootValue`: the lowercased value of a `root = ...` line.
fn root_value(l: &str) -> Option<String> {
    let t = trim(drop_line_comment(l));
    let (key, value) = t.split_once('=')?;
    if trim(key).to_lowercase() != "root" {
        return None;
    }
    Some(trim(value).to_lowercase())
}

/// `dropLineComment`: EditorConfig does not allow inline comments; `#` and `;`
/// starting on the first non-whitespace character denote a full-line comment.
/// Lines not starting with `#` or `;` must be returned verbatim.
fn drop_line_comment(l: &str) -> &str {
    match l.trim_start_matches(is_space).chars().next() {
        Some('#' | ';') => "",
        _ => l,
    }
}

fn trim(s: &str) -> &str {
    s.trim_matches(is_space)
}

/// `Data.Char.isSpace`: the ASCII spaces and controls `\t`..`\r`, the Latin-1
/// no-break space, and the Unicode space separators above it.
const fn is_space(c: char) -> bool {
    match c {
        ' ' | '\t'..='\r' | '\u{a0}' => true,
        c if c > '\u{377}' => matches!(
            c,
            '\u{1680}' | '\u{2000}'..='\u{200a}' | '\u{202f}' | '\u{205f}' | '\u{3000}'
        ),
        _ => false,
    }
}

/// `lines`: split on `\n`, with no empty line after a trailing one and none
/// at all for empty input. A `\r` stays where it was.
fn lines(s: &str) -> Vec<&str> {
    if s.is_empty() {
        return Vec::new();
    }
    s.strip_suffix('\n').unwrap_or(s).split('\n').collect()
}

#[cfg(test)]
#[allow(non_snake_case)]
mod tests {
    use super::*;

    #[test]
    fn prop_globStar() {
        assert!(matches_glob("*.ebuild", "foo.ebuild"));
    }

    #[test]
    fn prop_globBraceExt() {
        assert!(matches_glob("*.{ebuild,eclass}", "foo.eclass"));
    }

    #[test]
    fn prop_globBraceExt2() {
        assert!(matches_glob("*.{ebuild,eclass}", "foo.ebuild"));
    }

    #[test]
    fn prop_globBraceName() {
        assert!(matches_glob("{PKGBUILD,APKBUILD}", "PKGBUILD"));
    }

    #[test]
    fn prop_globBraceName2() {
        assert!(matches_glob("{PKGBUILD,APKBUILD}", "APKBUILD"));
    }

    #[test]
    fn prop_globNoMatch() {
        assert!(!matches_glob("*.ebuild", "foo.txt"));
    }

    #[test]
    fn prop_globQuestion() {
        assert!(matches_glob("foo?.sh", "food.sh"));
    }

    #[test]
    fn prop_globClass() {
        assert!(matches_glob("foo[0-9].sh", "foo1.sh"));
    }

    #[test]
    fn prop_globClassNeg() {
        assert!(!matches_glob("foo[!0-9].sh", "foo1.sh"));
    }

    // Patterns without a path separator should match at any depth.
    #[test]
    fn prop_globAnyDepth() {
        assert!(matches_glob("*.sh", "sub/dir/foo.sh"));
    }

    #[test]
    fn prop_globAnyDepthPlain() {
        assert!(matches_glob("foo", "sub/foo"));
    }

    // Patterns with a path separator are only matched against the full
    // relative path.
    #[test]
    fn prop_globWithSlashNoMatch() {
        assert!(!matches_glob("sub/*.sh", "other/foo.sh"));
    }

    #[test]
    fn prop_globWithSlashMatch() {
        assert!(matches_glob("sub/*.sh", "sub/foo.sh"));
    }

    // Numeric range expansion
    #[test]
    fn prop_globRange() {
        assert!(matches_glob("file{1..3}.sh", "file2.sh"));
    }

    #[test]
    fn prop_globRangeStart() {
        assert!(matches_glob("file{1..3}.sh", "file1.sh"));
    }

    #[test]
    fn prop_globRangeEnd() {
        assert!(matches_glob("file{1..3}.sh", "file3.sh"));
    }

    #[test]
    fn prop_globRangeNoMatch() {
        assert!(!matches_glob("file{1..3}.sh", "file4.sh"));
    }

    #[test]
    fn prop_globRangeNegative() {
        assert!(matches_glob("file{-2..0}.sh", "file-1.sh"));
    }

    #[test]
    fn prop_globRangeDescending() {
        assert!(!matches_glob("file{3..1}.sh", "file2.sh"));
    }

    #[test]
    fn prop_globLiteralDots() {
        assert!(!matches_glob("file{1..3}.sh", "file1..3.sh"));
    }

    // Empty brace alternatives (e.g. 'foo{,bar}') make the group optional:
    // 'foo' and 'foobar' both match.
    #[test]
    fn prop_globBraceEmptyAlt() {
        assert!(matches_glob("foo{,bar}", "foo"));
    }

    #[test]
    fn prop_globBraceEmptyAlt2() {
        assert!(matches_glob("foo{,bar}", "foobar"));
    }

    #[test]
    fn prop_globBraceEmptyAltNoMatch() {
        assert!(!matches_glob("foo{,bar}", "foobaz"));
    }

    // Nested braces: '{foo,ba{r,z}}' matches foo, bar and baz.
    #[test]
    fn prop_globBraceNested1() {
        assert!(matches_glob("{foo,ba{r,z}}", "foo"));
    }

    #[test]
    fn prop_globBraceNested2() {
        assert!(matches_glob("{foo,ba{r,z}}", "bar"));
    }

    #[test]
    fn prop_globBraceNested3() {
        assert!(matches_glob("{foo,ba{r,z}}", "baz"));
    }

    #[test]
    fn prop_globBraceNestedNoMatch() {
        assert!(!matches_glob("{foo,ba{r,z}}", "baq"));
    }

    #[test]
    fn prop_parseEditorConfig1() {
        assert_eq!(
            parse(
                "[*.{ebuild,eclass}]\nshellcheck.shell=bash\nshellcheck.disable=SC2034\n",
                "foo.ebuild"
            ),
            "\nshell=bash\ndisable=SC2034\n"
        );
    }

    #[test]
    fn prop_parseEditorConfig2() {
        assert_eq!(
            parse("[*.{ebuild,eclass}]\nshellcheck.shell=bash\n", "foo.txt"),
            ""
        );
    }

    #[test]
    fn prop_parseEditorConfig3() {
        assert_eq!(
            parse(
                "[{PKGBUILD,APKBUILD}]\nshellcheck.disable=SC2034\n",
                "PKGBUILD"
            ),
            "\ndisable=SC2034\n"
        );
    }

    #[test]
    fn prop_parseEditorConfig4() {
        assert_eq!(
            parse(
                "root = true\n[*.sh]\nindent_style = space\nshellcheck.shell=bash\n",
                "foo.sh"
            ),
            "\n\n\nshell=bash\n"
        );
    }

    // A later, more specific section overrides an earlier, more general
    // one for the same key.
    #[test]
    fn prop_parseEditorConfig5() {
        assert_eq!(
            parse(
                "[*]\nshellcheck.shell=sh\n\n[foo]\nshellcheck.shell=bash\n",
                "foo"
            ),
            "\n\n\n\nshell=bash\n"
        );
    }

    // Non-conflicting keys from earlier and later sections are all kept.
    #[test]
    fn prop_parseEditorConfig6() {
        assert_eq!(
            parse(
                "[*]\nshellcheck.shell=sh\n\n[foo]\nshellcheck.disable=SC2034\n",
                "foo"
            ),
            "\nshell=sh\n\n\ndisable=SC2034\n"
        );
    }

    // An unsupported shell is not emitted as a usable directive; instead its
    // line is reported via invalidDirectiveLines so the caller can reject it.
    #[test]
    fn prop_parseEditorConfigUnknownShell() {
        assert_eq!(parse("[*]\nshellcheck.shell=zsh\n", "foo"), "");
    }

    #[test]
    fn prop_parseEditorConfigEmptyShell() {
        assert_eq!(parse("[*]\nshellcheck.shell=\n", "foo"), "\nshell=\n");
    }

    #[test]
    fn prop_parseEditorConfigEmptyDisable() {
        assert_eq!(parse("[*]\nshellcheck.disable=\n", "foo"), "");
    }

    // A '#' embedded anywhere in the value (not just at the start) makes it
    // invalid too, since EditorConfig has no inline comments and the
    // .shellcheckrc parser would otherwise silently truncate it at the '#'.
    #[test]
    fn prop_parseEditorConfigEmbeddedComment() {
        assert_eq!(parse("[*]\nshellcheck.disable=SC2148 #abc\n", "foo"), "");
    }

    // EditorConfig does not allow inline comments, so a trailing '# ...'
    // makes the value invalid (the .shellcheckrc parser's
    // shellForExecutable lookup fails on the embedded text), and the
    // directive is dropped. It is reported via invalidDirectiveLines.
    #[test]
    fn prop_parseEditorConfigInlineComment() {
        assert_eq!(parse("[*]\nshellcheck.shell=bash # inline\n", "foo"), "");
    }

    // Full-line comments starting on first non-ws char are stripped.
    #[test]
    fn prop_parseEditorConfigLineComment() {
        assert_eq!(parse("[*]\n# shellcheck.shell=bash\n", "foo"), "");
    }

    #[test]
    fn prop_parseEditorConfigSemicolonComment() {
        assert_eq!(parse("[*]\n; shellcheck.shell=bash\n", "foo"), "");
    }

    // Empty brace alternative makes the glob group optional; 'foo' matches
    // '[foo{,bar}]'.
    #[test]
    fn prop_parseEditorConfigBraceEmpty() {
        assert_eq!(
            parse("[foo{,bar}]\nshellcheck.shell=sh\n", "foo"),
            "\nshell=sh\n"
        );
    }

    // Nested braces are expanded correctly; 'baz' matches
    // '[{foo,ba{r,z}}]'.
    #[test]
    fn prop_parseEditorConfigBraceNested() {
        assert_eq!(
            parse("[{foo,ba{r,z}}]\nshellcheck.shell=sh\n", "baz"),
            "\nshell=sh\n"
        );
    }

    #[test]
    fn prop_isEditorConfigRootEmpty() {
        assert!(!is_editor_config_root("root =\n"));
    }

    #[test]
    fn prop_isEditorConfigRootFalse() {
        assert!(!is_editor_config_root("root = false\n"));
    }

    #[test]
    fn prop_isEditorConfigRootTrue() {
        assert!(is_editor_config_root("root = TRUE\n"));
    }

    #[test]
    fn prop_invalidRootLinesEmpty() {
        assert_eq!(invalid_root_lines("root =\n"), vec![1]);
    }

    #[test]
    fn prop_invalidRootLinesTrue() {
        assert_eq!(invalid_root_lines("root = true\n"), Vec::<usize>::new());
    }

    #[test]
    fn prop_invalidRootLinesFalse() {
        assert_eq!(invalid_root_lines("root = false\n"), Vec::<usize>::new());
    }

    #[test]
    fn prop_invalidRootLinesInSection() {
        assert_eq!(
            invalid_root_lines("[*]\nroot = true\n"),
            Vec::<usize>::new()
        );
    }

    // An unsupported non-empty shell is reported at its line.
    #[test]
    fn prop_invalidDirectiveLinesUnknownShell() {
        assert_eq!(
            invalid_directive_lines("[*]\nshellcheck.shell=zsh\n", "foo"),
            vec![2]
        );
    }

    // An empty shell is valid (the rc parser rejects it), so no error.
    #[test]
    fn prop_invalidDirectiveLinesEmptyShell() {
        assert_eq!(
            invalid_directive_lines("[*]\nshellcheck.shell=\n", "foo"),
            Vec::<usize>::new()
        );
    }

    // A known shell is fine.
    #[test]
    fn prop_invalidDirectiveLinesKnownShell() {
        assert_eq!(
            invalid_directive_lines("[*]\nshellcheck.shell=bash\n", "foo"),
            Vec::<usize>::new()
        );
    }

    // A '#'-prefixed value is reported (EditorConfig has no inline comments).
    #[test]
    fn prop_invalidDirectiveLinesHashValue() {
        assert_eq!(
            invalid_directive_lines("[foo]\nshellcheck.disable = #abc\n", "foo"),
            vec![2]
        );
    }

    // A ';'-prefixed value is reported too.
    #[test]
    fn prop_invalidDirectiveLinesSemicolonValue() {
        assert_eq!(
            invalid_directive_lines("[foo]\nshellcheck.disable = ;abc\n", "foo"),
            vec![2]
        );
    }

    // A '#' embedded anywhere in the value (not just at the start) is
    // reported too: previously this was silently accepted, since the
    // .shellcheckrc parser would treat everything from the '#' onwards as a
    // trailing comment (e.g. this used to disable SC2148 without warning).
    #[test]
    fn prop_invalidDirectiveLinesEmbeddedHashValue() {
        assert_eq!(
            invalid_directive_lines("[foo]\nshellcheck.disable = SC2148 #abc\n", "foo"),
            vec![2]
        );
    }

    #[test]
    fn prop_invalidDirectiveLinesEmbeddedSemicolonValue() {
        assert_eq!(
            invalid_directive_lines("[foo]\nshellcheck.disable = SC2148 ;abc\n", "foo"),
            vec![2]
        );
    }

    // A plain empty value (no comment marker) is not reported: it is simply
    // a no-op, unlike a value that was truncated down to empty by a leading
    // comment marker.
    #[test]
    fn prop_invalidDirectiveLinesEmptyValueNotInvalid() {
        assert_eq!(
            invalid_directive_lines("[foo]\nshellcheck.disable =\n", "foo"),
            Vec::<usize>::new()
        );
    }

    // A plain invalid value (no comment marker) is not reported here; it is
    // rejected by the .shellcheckrc parser as SC1134 instead.
    #[test]
    fn prop_invalidDirectiveLinesPlainValue() {
        assert_eq!(
            invalid_directive_lines("[foo]\nshellcheck.disable = abc\n", "foo"),
            Vec::<usize>::new()
        );
    }

    // Directives in non-matching sections are ignored.
    #[test]
    fn prop_invalidDirectiveLinesNoMatch() {
        assert_eq!(
            invalid_directive_lines("[*.txt]\nshellcheck.shell=zsh\n", "foo"),
            Vec::<usize>::new()
        );
    }

    // Only the matching section's invalid directive is reported.
    #[test]
    fn prop_invalidDirectiveLinesMatchingSection() {
        assert_eq!(
            invalid_directive_lines(
                "[*.txt]\nshellcheck.shell=zsh\n[foo]\nshellcheck.shell=bash\n",
                "foo"
            ),
            Vec::<usize>::new()
        );
    }

    #[test]
    fn editor_config_directives_rejects_each_invalid_line_at_its_position() {
        assert_eq!(
            directives("[foo]\nshellcheck.shell=zsh\n", "foo").as_deref(),
            Some("\ninvalid editorconfig value\n")
        );
        assert!(is_rejection("\ninvalid editorconfig value\n"));
        assert!(!is_rejection("\nshell=bash\n"));
        assert_eq!(directives("[bar]\nshellcheck.shell=sh\n", "foo"), None);
        assert_eq!(rejected_root(3), "\n\ninvalid editorconfig value\n");
    }

    #[test]
    fn haskell_lines_and_spaces() {
        assert_eq!(lines(""), Vec::<&str>::new());
        assert_eq!(lines("a\n"), vec!["a"]);
        assert_eq!(lines("a\r\nb"), vec!["a\r", "b"]);
        assert!(is_space('\u{a0}'));
        assert!(!is_space('\u{85}'));
        assert!(!is_space('\u{2028}'));
        assert_eq!(read_int(" -2"), Some(-2));
        assert_eq!(read_int("2 "), None);
        assert_eq!(read_int("+2"), None);
    }
}
