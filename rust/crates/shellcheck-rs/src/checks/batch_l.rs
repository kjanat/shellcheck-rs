//! Ported check batch l. See rust/PORTING.md.
//!
//! Self-contained pattern checks:
//! - SC2004  checkArithmeticDeref  (Analytics.hs) — `$`/`${}` unnecessary on
//!   variables inside `$((..))` / `(( ))` arithmetic.
//! - SC2219  checkLetUsage         (Checks/Commands.hs) — `let expr` -> `(( expr ))`.
//! - SC2209  checkAssignAteCommand (Analytics.hs) — `x=command` (assigning the
//!   literal name of a common command instead of its output). Also carries the
//!   SC2037 branch of the same Haskell function.
//! - SC2211  checkGlobAsCommand    (Analytics.hs) — a glob used as a command name.
//! - SC2065  checkTestRedirects    (Analytics.hs) — `>`/`<` in `test` args read
//!   as a redirection, not a comparison.
use crate::analyzer_lib::*;
use crate::ast::*;
use crate::astlib::get_literal_string;
use crate::astlib::is_glob;
use crate::astlib::is_unquoted_flag;
use crate::astlib::oversimplify_concat;
use crate::cfg::get_unquoted_literal;
use crate::interface::Shell;

/// Register this batch's checks.
pub fn register(c: &mut Checker) {
    c.node(check_arithmetic_deref);
    c.node(check_let_usage);
    c.node(check_assign_ate_command);
    c.node(check_glob_as_command);
    c.node(check_test_redirects);
}

// ===========================================================================
// Shared helpers (ported privately; parallel agents own other .rs files).
// ===========================================================================

// ===========================================================================
// SC2004 — checkArithmeticDeref
// ===========================================================================

fn arith_deref_is_exception(s: &str) -> bool {
    const SPECIAL: &str = "/.:#%?*@$-!+=^,";
    match s.chars().next() {
        None => true,
        Some(h) => s.chars().any(|c| SPECIAL.contains(c)) || h.is_ascii_digit(),
    }
}

fn check_arithmetic_deref(params: &Parameters, t: &Token, out: &mut Out) {
    let list = match &*t.inner {
        InnerToken::TA_Expansion(l) => l,
        _ => return,
    };
    if list.len() != 1 {
        return;
    }
    let (id, op) = match &*list[0].inner {
        InnerToken::T_DollarBraced { op, .. } => (list[0].id(), op),
        _ => return,
    };
    if arith_deref_is_exception(&oversimplify_concat(op)) {
        return;
    }
    // fromMaybe noWarning . msum . map warningFor $ parents params t
    // parents = the token itself followed by its ancestors up to the root.
    let mut cur = t.clone();
    loop {
        match &*cur.inner {
            InnerToken::T_Arithmetic(_)
            | InnerToken::T_DollarArithmetic(_)
            | InnerToken::T_ForArithmetic { .. }
            | InnerToken::T_Assignment { .. } => {
                style(
                    out,
                    id,
                    2004,
                    "$/${} is unnecessary on arithmetic variables.",
                );
                return;
            }
            InnerToken::T_SimpleCommand { .. } => return,
            _ => {}
        }
        match params.parent(&cur) {
            Some(p) => cur = p.clone(),
            None => return,
        }
    }
}

// ===========================================================================
// SC2219 — checkLetUsage
// ===========================================================================

fn simple_command_name(t: &Token) -> Option<String> {
    match &*t.inner {
        InnerToken::T_SimpleCommand { words, .. } => words.first().and_then(get_literal_string),
        _ => None,
    }
}

fn check_let_usage(params: &Parameters, t: &Token, out: &mut Out) {
    if simple_command_name(t).as_deref() != Some("let") {
        return;
    }
    if matches!(params.shell, Shell::Bash | Shell::Ksh) {
        style(
            out,
            t.id(),
            2219,
            "Instead of 'let expr', prefer (( expr )) .",
        );
    }
}

// ===========================================================================
// SC2209 / SC2037 — checkAssignAteCommand
// ===========================================================================

fn is_common_command(s: &Option<String>) -> bool {
    match s {
        Some(x) => COMMON_COMMANDS.contains(&x.as_str()),
        None => false,
    }
}

fn first_word_is_arg(list: &[Token]) -> bool {
    match list.first() {
        Some(head) => is_glob(head) || is_unquoted_flag(head),
        None => false,
    }
}

fn check_assign_ate_command(_params: &Parameters, t: &Token, out: &mut Out) {
    let (assignments, words) = match &*t.inner {
        InnerToken::T_SimpleCommand { assignments, words } => (assignments, words),
        _ => return,
    };
    if assignments.len() != 1 {
        return;
    }
    let assignment_term = match &*assignments[0].inner {
        InnerToken::T_Assignment { value, .. } => value,
        _ => return,
    };
    if first_word_is_arg(words) {
        err(
            out,
            t.id(),
            2037,
            "To assign the output of a command, use var=$(cmd) .",
        );
    } else if is_common_command(&get_unquoted_literal(assignment_term)) {
        warn(
            out,
            t.id(),
            2209,
            "Use var=$(command) to assign output (or quote to assign string).",
        );
    }
}

// ===========================================================================
// SC2211 — checkGlobAsCommand
// ===========================================================================

/// Parser-gap guard. The Rust parser does not yet parse every `[ .. ]` /
/// `[[ .. ]]` test (e.g. operators like `-a`, `-o`, `<`, `\>`, `=~ (..)`);
/// when it gives up it collapses the bracket expression into a `T_Glob`
/// spanning the whole (or nearly whole) test, e.g. `T_Glob("[ -a foo ]")` or
/// `T_Glob("[[ 3 \\< 4 ]")`. This check would otherwise report those as
/// SC2211. The Haskell parser produces a `T_Condition` there instead, so the
/// oracle never fires. A well-formed `T_Glob` token never contains an unquoted
/// space or tab (that would split the word), so a glob part carrying one is
/// always this fallback artifact — suppressing it drops the parser noise
/// without hiding any real glob-as-command.
fn is_condition_fallback_glob(first: &Token) -> bool {
    fn has_spaced_glob(t: &Token) -> bool {
        match &*t.inner {
            InnerToken::T_Glob(s) => s.chars().any(|c| c == ' ' || c == '\t'),
            InnerToken::T_NormalWord(l) | InnerToken::T_DoubleQuoted(l) => {
                l.iter().any(has_spaced_glob)
            }
            _ => false,
        }
    }
    has_spaced_glob(first)
}

fn check_glob_as_command(_params: &Parameters, t: &Token, out: &mut Out) {
    if let InnerToken::T_SimpleCommand { words, .. } = &*t.inner {
        if let Some(first) = words.first() {
            if is_glob(first) && !is_condition_fallback_glob(first) {
                warn(
                    out,
                    first.id(),
                    2211,
                    "This is a glob used as a command name. Was it supposed to be in ${..}, array, or is it missing quoting?",
                );
            }
        }
    }
}

// ===========================================================================
// SC2065 — checkTestRedirects
// ===========================================================================

fn redirect_is_comparison(op: &Token) -> bool {
    matches!(&*op.inner, InnerToken::T_Greater | InnerToken::T_Less)
}

fn redirect_is_suspicious(t: &Token) -> bool {
    match &*t.inner {
        InnerToken::T_FdRedirect { fd, target } => match &*target.inner {
            InnerToken::T_IoFile { op, .. } => fd != "2" && redirect_is_comparison(op),
            _ => false,
        },
        _ => false,
    }
}

fn check_test_redirects(_params: &Parameters, t: &Token, out: &mut Out) {
    let (redirs, cmd) = match &*t.inner {
        InnerToken::T_Redirecting { redirs, cmd } => (redirs, cmd),
        _ => return,
    };
    if !crate::analyzer_lib::is_command(cmd, "test") {
        return;
    }
    for r in redirs {
        if redirect_is_suspicious(r) {
            warn(
                out,
                r.id(),
                2065,
                "This is interpreted as a shell file redirection, not a comparison.",
            );
        }
    }
}

// ShellCheck.Data.commonCommands
const COMMON_COMMANDS: &[&str] = &[
    "admin",
    "alias",
    "ar",
    "asa",
    "at",
    "awk",
    "basename",
    "batch",
    "bc",
    "bg",
    "break",
    "c99",
    "cal",
    "cat",
    "cd",
    "cflow",
    "chgrp",
    "chmod",
    "chown",
    "cksum",
    "cmp",
    "colon",
    "comm",
    "command",
    "compress",
    "continue",
    "cp",
    "crontab",
    "csplit",
    "ctags",
    "cut",
    "cxref",
    "date",
    "dd",
    "delta",
    "df",
    "diff",
    "dirname",
    "dot",
    "du",
    "echo",
    "ed",
    "env",
    "eval",
    "ex",
    "exec",
    "exit",
    "expand",
    "export",
    "expr",
    "fc",
    "fg",
    "file",
    "find",
    "fold",
    "fuser",
    "gencat",
    "get",
    "getconf",
    "getopts",
    "gettext",
    "grep",
    "hash",
    "head",
    "iconv",
    "ipcrm",
    "ipcs",
    "jobs",
    "join",
    "kill",
    "lex",
    "link",
    "ln",
    "locale",
    "localedef",
    "logger",
    "logname",
    "lp",
    "ls",
    "m4",
    "mailx",
    "make",
    "man",
    "mesg",
    "mkdir",
    "mkfifo",
    "more",
    "msgfmt",
    "mv",
    "newgrp",
    "ngettext",
    "nice",
    "nl",
    "nm",
    "nohup",
    "od",
    "paste",
    "patch",
    "pathchk",
    "pax",
    "pr",
    "printf",
    "prs",
    "ps",
    "pwd",
    "read",
    "readlink",
    "readonly",
    "realpath",
    "renice",
    "return",
    "rm",
    "rmdel",
    "rmdir",
    "sact",
    "sccs",
    "sed",
    "set",
    "sh",
    "shift",
    "sleep",
    "sort",
    "split",
    "strings",
    "strip",
    "stty",
    "tabs",
    "tail",
    "talk",
    "tee",
    "test",
    "time",
    "timeout",
    "times",
    "touch",
    "tput",
    "tr",
    "trap",
    "tsort",
    "tty",
    "type",
    "ulimit",
    "umask",
    "unalias",
    "uname",
    "uncompress",
    "unexpand",
    "unget",
    "uniq",
    "unlink",
    "unset",
    "uucp",
    "uudecode",
    "uuencode",
    "uustat",
    "uux",
    "val",
    "vi",
    "wait",
    "wc",
    "what",
    "who",
    "write",
    "xargs",
    "xgettext",
    "yacc",
    "zcat",
];

#[cfg(test)]
#[allow(non_snake_case)]
mod tests {
    use super::*;
    use crate::analyzer_lib::make_parameters;
    use crate::interface::Shell;
    use crate::parser::parse_script;

    fn params_for(script: &str) -> Parameters {
        let p = parse_script("test", script);
        let root = p.root.expect("parse produced no root");
        make_parameters(root, p.positions, None, None)
    }
    fn params_for_shell(script: &str, shell: Shell) -> Parameters {
        let p = parse_script("test", script);
        let root = p.root.expect("parse produced no root");
        make_parameters(root, p.positions, Some(shell), None)
    }
    fn emits_code_shell(
        f: fn(&Parameters, &Token, &mut Out),
        s: &str,
        code: i64,
        shell: Shell,
    ) -> bool {
        let params = params_for_shell(s, shell);
        let mut out = Out::new();
        params.root.visit_preorder(&mut |t| f(&params, t, &mut out));
        out.iter().any(|c| c.comment.code == code)
    }
    fn emits(f: fn(&Parameters, &Token, &mut Out), s: &str) -> bool {
        let params = params_for(s);
        let mut out = Out::new();
        params.root.visit_preorder(&mut |t| f(&params, t, &mut out));
        !out.is_empty()
    }

    // ---- SC2004 checkArithmeticDeref ----
    #[test]
    fn prop_checkArithmeticDeref1() {
        assert!(emits(check_arithmetic_deref, "echo $((3+$foo))"));
    }
    #[test]
    fn prop_checkArithmeticDeref2() {
        assert!(emits(check_arithmetic_deref, "cow=14; (( s+= $cow ))"));
    }
    #[test]
    fn prop_checkArithmeticDeref3() {
        assert!(!emits(
            check_arithmetic_deref,
            "cow=1/40; (( s+= ${cow%%/*} ))"
        ));
    }
    #[test]
    fn prop_checkArithmeticDeref4() {
        assert!(!emits(check_arithmetic_deref, "(( ! $? ))"));
    }
    #[test]
    fn prop_checkArithmeticDeref5() {
        assert!(!emits(check_arithmetic_deref, "(($1))"));
    }
    #[test]
    fn prop_checkArithmeticDeref6() {
        assert!(emits(check_arithmetic_deref, "(( a[$i] ))"));
    }
    #[test]
    fn prop_checkArithmeticDeref7() {
        assert!(!emits(check_arithmetic_deref, "(( 10#$n ))"));
    }
    #[test]
    fn prop_checkArithmeticDeref8() {
        assert!(!emits(check_arithmetic_deref, "let i=$i+1"));
    }
    #[test]
    fn prop_checkArithmeticDeref9() {
        assert!(!emits(check_arithmetic_deref, "(( a[foo] ))"));
    }
    #[test]
    fn prop_checkArithmeticDeref10() {
        assert!(!emits(check_arithmetic_deref, "(( a[\\$foo] ))"));
    }
    #[test]
    fn prop_checkArithmeticDeref11() {
        assert!(emits(check_arithmetic_deref, "a[$foo]=wee"));
    }
    #[test]
    fn prop_checkArithmeticDeref11b() {
        assert!(!emits(check_arithmetic_deref, "declare -A a; a[$foo]=wee"));
    }
    #[test]
    fn prop_checkArithmeticDeref12() {
        assert!(emits(
            check_arithmetic_deref,
            "for ((i=0; $i < 3; i)); do true; done"
        ));
    }
    #[test]
    fn prop_checkArithmeticDeref13() {
        assert!(!emits(check_arithmetic_deref, "(( $$ ))"));
    }
    #[test]
    fn prop_checkArithmeticDeref14() {
        assert!(!emits(check_arithmetic_deref, "(( $! ))"));
    }
    #[test]
    fn prop_checkArithmeticDeref15() {
        assert!(!emits(check_arithmetic_deref, "(( ${!var} ))"));
    }
    #[test]
    fn prop_checkArithmeticDeref16() {
        assert!(!emits(check_arithmetic_deref, "(( ${x+1} + ${x=42} ))"));
    }

    // ---- SC2219 checkLetUsage ----
    #[test]
    fn prop_checkLetUsage1() {
        assert!(emits_code_shell(
            check_let_usage,
            "let a=1",
            2219i64,
            Shell::Bash
        ));
    }
    #[test]
    fn prop_checkLetUsage2() {
        assert!(!emits_code_shell(
            check_let_usage,
            "(( a=1 ))",
            2219i64,
            Shell::Bash
        ));
    }

    // ---- SC2209 / SC2037 checkAssignAteCommand ----
    #[test]
    fn prop_checkAssignAteCommand1() {
        assert!(emits(check_assign_ate_command, "A=ls -l"));
    }
    #[test]
    fn prop_checkAssignAteCommand2() {
        assert!(emits(check_assign_ate_command, "A=ls --sort=$foo"));
    }
    #[test]
    fn prop_checkAssignAteCommand3() {
        assert!(emits(check_assign_ate_command, "A=cat foo | grep bar"));
    }
    #[test]
    fn prop_checkAssignAteCommand4() {
        assert!(!emits(check_assign_ate_command, "A=foo ls -l"));
    }
    #[test]
    fn prop_checkAssignAteCommand5() {
        assert!(emits(check_assign_ate_command, "PAGER=cat grep bar"));
    }
    #[test]
    fn prop_checkAssignAteCommand6() {
        assert!(!emits(check_assign_ate_command, "PAGER=\"cat\" grep bar"));
    }
    #[test]
    fn prop_checkAssignAteCommand7() {
        assert!(emits(check_assign_ate_command, "here=pwd"));
    }

    // ---- SC2211 checkGlobAsCommand ----
    #[test]
    fn prop_checkGlobAsCommand1() {
        assert!(emits(check_glob_as_command, "foo*"));
    }
    #[test]
    fn prop_checkGlobAsCommand2() {
        assert!(emits(check_glob_as_command, "$(var[i])"));
    }
    #[test]
    fn prop_checkGlobAsCommand3() {
        assert!(!emits(check_glob_as_command, "echo foo*"));
    }

    // ---- SC2065 checkTestRedirects ----
    #[test]
    fn prop_checkTestRedirects1() {
        assert!(emits(check_test_redirects, "test 3 > 1"));
    }
    #[test]
    fn prop_checkTestRedirects2() {
        assert!(!emits(check_test_redirects, "test 3 \\> 1"));
    }
    #[test]
    fn prop_checkTestRedirects3() {
        assert!(emits(check_test_redirects, "/usr/bin/test $var > $foo"));
    }
    #[test]
    fn prop_checkTestRedirects4() {
        assert!(!emits(check_test_redirects, "test 1 -eq 2 2> file"));
    }
}
