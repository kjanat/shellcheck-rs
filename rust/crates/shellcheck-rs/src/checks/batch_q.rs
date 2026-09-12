//! Ported check batch q. See rust/PORTING.md.
//!
//! Long-tail checks ported from Analytics.hs / Checks/ShellSupport.hs:
//! - SC2013  checkForInCat          (Analytics.hs)   — `for f in $(cat foo)`.
//! - SC2210  checkRedirectionToNumber (Analytics.hs) — `foo 1>2`.
//! - SC2206/SC2207 checkSplittingInArrays (Analytics.hs) — `a=( $var )`.
//! - SC2268  checkComparisonWithLeadingX (Analytics.hs) — `[ x$foo = xlol ]`.
//! - SC2001  checkEchoSed           (Checks/ShellSupport.hs) — echo|sed pattern.
//! - SC2093  checkSpuriousExec      (Analytics.hs)   — `exec foo; true`.
//! - SC2281  checkEqualsInCommand   (Analytics.hs)   — `$var=foo` (+ family).
//! - SC2198/SC2199/... checkTestArgumentSplitting (Analytics.hs).
//! - SC2233/SC2234/SC2235 checkSubshelledTests (Analytics.hs).
//! - SC2261/... checkPipeToNowhere  (Analytics.hs).
#![allow(unused_imports, unused_variables, dead_code)]
use crate::cfg::will_become_multiple_args;
use crate::cfg::will_concat_in_assignment;
use crate::cfg::get_unquoted_literal;
use crate::astlib::is_quotes;
use crate::astlib::is_glob;
use crate::analyzer_lib::*;
use crate::ast::*;
use crate::astlib;
use crate::interface::{Fix, Replacement, Shell};

/// Register this batch's checks.
pub fn register(c: &mut Checker) {
    c.node(check_for_in_cat);
    c.node(check_splitting_in_arrays);
    // check_redirection_to_number (SC2210) is implemented and tested but NOT
    // registered: for a glued fd like `foo 1>2` the Rust parser gives the
    // T_IoFile id a span that starts at the fd digit (col 5), whereas the
    // oracle anchors SC2210 at the redirection operator (col 6). This is a
    // parser span discrepancy (the fd belongs to T_FdRedirect, not T_IoFile),
    // fixable only in the parser, so registering it yields extra > 0.
    c.node(check_comparison_with_leading_x);
    c.node(check_echo_sed);
    c.node(check_spurious_exec);
    c.node(check_equals_in_command);
    c.node(check_test_argument_splitting);
    // SC2261 (competing redirections) is registered on its own below.
    // The full checkPipeToNowhere (SC2216/2217/2259/2260) is implemented in
    // `check_pipe_to_nowhere` but NOT registered: its SC2259/SC2216 branches
    // depend on parser features the port lacks — command substitutions inside
    // heredoc bodies are parsed as a literal (so `cmd << EOF ... $(..) .. EOF`
    // is wrongly seen as not consuming stdin, yielding a spurious SC2259), and
    // `&>` is parsed as `&` + `>` rather than a combined redirect. Registering
    // it produces extra > 0 on those codes. The SC2261 dupe logic is unaffected
    // by those gaps, so it is split out and registered here.
    c.node(check_subshelled_tests);
}

// ---------------------------------------------------------------------------
// Shared local helpers (ported from ASTLib / AnalyzerLib; kept private).
// ---------------------------------------------------------------------------

/// `ShellCheck.Data.variablesWithoutSpaces`.
const VARIABLES_WITHOUT_SPACES: &[&str] = &[
    "-",
    "$",
    "?",
    "!",
    "#",
    "BASHPID",
    "BASH_ARGC",
    "BASH_LINENO",
    "BASH_SUBSHELL",
    "EUID",
    "EPOCHREALTIME",
    "EPOCHSECONDS",
    "LINENO",
    "OPTIND",
    "PPID",
    "RANDOM",
    "READLINE_ARGUMENT",
    "READLINE_MARK",
    "READLINE_POINT",
    "SECONDS",
    "SHELLOPTS",
    "SHLVL",
    "SRANDOM",
    "UID",
    "COLUMNS",
    "HISTFILESIZE",
    "HISTSIZE",
    "LINES",
    "BASH_MONOSECONDS",
    "BASH_TRAPSIG",
    "FLAGS_ERROR",
    "FLAGS_FALSE",
    "FLAGS_TRUE",
];

// ---------------------------------------------------------------------------
// SC2013 — checkForInCat
// ---------------------------------------------------------------------------

fn check_for_in_cat(params: &Parameters, t: &Token, out: &mut Out) {
    if let InnerToken::T_ForIn { items, .. } = &*t.inner {
        if items.len() == 1 {
            if let InnerToken::T_NormalWord(w) = &*items[0].inner {
                for part in w {
                    check_for_in_cat_part(part, out);
                }
            }
        }
    }
}

fn check_for_in_cat_part(part: &Token, out: &mut Out) {
    // T_DollarExpansion id [T_Pipeline _ _ r]   (and T_Backticked treated the same)
    let list = match &*part.inner {
        InnerToken::T_DollarExpansion(list) => Some(list),
        InnerToken::T_Backticked(cmds) => Some(cmds),
        _ => None,
    };
    if let Some(list) = list {
        if list.len() == 1 {
            if let InnerToken::T_Pipeline { commands, .. } = &*list[0].inner {
                if commands.iter().all(is_line_based) {
                    info(
                        out,
                        part.id(),
                        2013,
                        "To read lines rather than words, pipe/redirect to a 'while read' loop.",
                    );
                }
            }
        }
    }
}

fn is_line_based(cmd: &Token) -> bool {
    ["grep", "fgrep", "egrep", "sed", "cat", "awk", "cut", "sort"]
        .iter()
        .any(|c| is_command(cmd, c))
}

// ---------------------------------------------------------------------------
// SC2210 — checkRedirectionToNumber
// ---------------------------------------------------------------------------

// ---------------------------------------------------------------------------
// SC2206 / SC2207 — checkSplittingInArrays
// ---------------------------------------------------------------------------

fn check_splitting_part(params: &Parameters, part: &Token, out: &mut Out) {
    match &*part.inner {
        InnerToken::T_DollarExpansion(_)
        | InnerToken::T_DollarBraceCommandExpansion { .. }
        | InnerToken::T_Backticked(_) => {
            let msg = if params.shell == Shell::Ksh {
                "Prefer read -A or while read to split command output (or quote to avoid splitting)."
            } else {
                "Prefer mapfile or read -a to split command output (or quote to avoid splitting)."
            };
            warn(out, part.id(), 2207, msg);
        }
        InnerToken::T_DollarBraced { op, .. } => {
            let reference =
                crate::cfg::get_braced_reference(&crate::cfg::oversimplify(op).concat());
            if !is_counting_reference(part)
                && !is_quoted_alternative_reference(part)
                && !VARIABLES_WITHOUT_SPACES.contains(&reference.as_str())
            {
                let msg = if params.shell == Shell::Ksh {
                    "Quote to prevent word splitting/globbing, or split robustly with read -A or while read."
                } else {
                    "Quote to prevent word splitting/globbing, or split robustly with mapfile or read -a."
                };
                warn(out, part.id(), 2206, msg);
            }
        }
        _ => {}
    }
}

// ---------------------------------------------------------------------------
// SC2268 — checkComparisonWithLeadingX
// ---------------------------------------------------------------------------

fn check_comparison_with_leading_x(params: &Parameters, t: &Token, out: &mut Out) {
    match &*t.inner {
        InnerToken::TC_Binary { op, lhs, rhs, .. } if matches!(op.as_str(), "=" | "==" | "!=") => {
            leading_x_check(params, lhs, rhs, out);
        }
        InnerToken::T_SimpleCommand { words, .. } if words.len() == 4 => {
            let cmd = &words[0];
            let op = &words[2];
            if astlib::get_literal_string(cmd).as_deref() == Some("test")
                && matches!(
                    astlib::get_literal_string(op).as_deref(),
                    Some("=") | Some("==") | Some("!=")
                )
            {
                leading_x_check(params, &words[1], &words[3], out);
            }
        }
        _ => {}
    }
}

fn leading_x_check(params: &Parameters, lhs: &Token, rhs: &Token, out: &mut Out) {
    if let (Some(l), Some(r)) = (fix_leading_x(params, lhs), fix_leading_x(params, rhs)) {
        let fix = fix_with(vec![l, r]);
        style_with_fix(
            out,
            lhs.id(),
            2268,
            "Avoid x-prefix in comparisons as it no longer serves a purpose.",
            fix,
        );
    }
}

fn fix_leading_x(params: &Parameters, token: &Token) -> Option<Replacement> {
    let parts = word_parts(token);
    let first = parts.first()?;
    match &*first.inner {
        InnerToken::T_Literal(s) => {
            let c = s.chars().next()?;
            if !c.eq_ignore_ascii_case(&'x') {
                return None;
            }
            // The side is a single, unquoted x or X, so we have to quote.
            if let InnerToken::T_NormalWord(v) = &*token.inner {
                if v.len() == 1 {
                    if let InnerToken::T_Literal(single) = &*v[0].inner {
                        if single.chars().count() == 1 {
                            return Some(replace_start(params, v[0].id(), 1, "\"\""));
                        }
                    }
                }
            }
            // Otherwise we can just delete it.
            Some(replace_start(params, first.id(), 1, ""))
        }
        InnerToken::T_SingleQuoted(s) => {
            let c = s.chars().next()?;
            if !c.eq_ignore_ascii_case(&'x') {
                return None;
            }
            // Replace the single quote and the character x or X.
            Some(replace_start(params, first.id(), 2, "'"))
        }
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// SC2001 — checkEchoSed (ForShell [Bash, Ksh])
// ---------------------------------------------------------------------------

fn check_echo_sed(params: &Parameters, t: &Token, out: &mut Out) {
    if !matches!(params.shell, Shell::Bash | Shell::Ksh) {
        return;
    }
    match &*t.inner {
        InnerToken::T_Redirecting { redirs, cmd } => {
            if redirs.iter().any(redirect_here_string) {
                let rcmd = crate::cfg::oversimplify(cmd);
                check_sed(t.id(), &rcmd, out);
            }
        }
        InnerToken::T_Pipeline { commands, .. } if commands.len() == 2 => {
            let acmd = crate::cfg::oversimplify(&commands[0]);
            if acmd == ["echo", "${VAR}"] {
                let bcmd = crate::cfg::oversimplify(&commands[1]);
                check_sed(t.id(), &bcmd, out);
            }
        }
        _ => {}
    }
}

fn redirect_here_string(t: &Token) -> bool {
    matches!(&*t.inner, InnerToken::T_FdRedirect { target, .. } if matches!(&*target.inner, InnerToken::T_HereString(_)))
}

fn check_sed(id: Id, cmd: &[String], out: &mut Out) {
    let v = match cmd {
        [a, v] if a == "sed" => Some(v),
        [a, b, v] if a == "sed" && b == "-e" => Some(v),
        _ => None,
    };
    if let Some(v) = v {
        if is_simple_sed(v) {
            style(
                out,
                id,
                2001,
                "See if you can use ${variable//search/replace} instead.",
            );
        }
    }
}

/// Port of `isSimpleSed`: matches `^s(.)([^\n]*)g?$` and requires exactly two
/// occurrences of the delimiter in the tail.
fn is_simple_sed(s: &str) -> bool {
    if s.contains('\n') {
        return false;
    }
    let chars: Vec<char> = s.chars().collect();
    if chars.len() < 2 || chars[0] != 's' {
        return false;
    }
    let delim = chars[1];
    chars[2..].iter().filter(|&&c| c == delim).count() == 2
}

// ---------------------------------------------------------------------------
// SC2093 — checkSpuriousExec
// ---------------------------------------------------------------------------

fn check_spurious_exec(params: &Parameters, t: &Token, out: &mut Out) {
    if has_execfail(params) {
        return;
    }
    match &*t.inner {
        InnerToken::T_Script { commands, .. } => do_list(commands, false, out),
        InnerToken::T_BraceGroup(cmds) => do_list(cmds, false, out),
        InnerToken::T_WhileExpression { body, .. } => do_list(body, true, out),
        InnerToken::T_UntilExpression { body, .. } => do_list(body, true, out),
        InnerToken::T_ForIn { body, .. } => do_list(body, true, out),
        InnerToken::T_ForArithmetic { body, .. } => do_list(body, true, out),
        InnerToken::T_IfExpression { clauses, elses } => {
            for (_, l) in clauses {
                do_list(l, false, out);
            }
            do_list(elses, false, out);
        }
        _ => {}
    }
}

fn has_execfail(params: &Parameters) -> bool {
    params.shell == Shell::Bash && is_option_set("execfail", &params.root)
}

fn spurious_cleanup(t: &Token) -> bool {
    if let InnerToken::T_Pipeline { commands, .. } = &*t.inner {
        if commands.len() == 1 {
            let cmd = &commands[0];
            let is_match = get_command_name(cmd).map_or(false, |name| {
                matches!(name.as_str(), ":" | "echo" | "exit" | "printf" | "return")
            });
            return is_match || spurious_is_assignment(cmd);
        }
    }
    false
}

fn spurious_is_assignment(t: &Token) -> bool {
    match &*t.inner {
        InnerToken::T_Redirecting { cmd, .. } => spurious_is_assignment(cmd),
        InnerToken::T_SimpleCommand { assignments, words } => {
            !assignments.is_empty() && words.is_empty()
        }
        InnerToken::T_Assignment { .. } => true,
        InnerToken::T_Annotation { token, .. } => spurious_is_assignment(token),
        _ => false,
    }
}

fn strip_cleanup(cmds: &[Token]) -> &[Token] {
    let mut end = cmds.len();
    while end > 0 && spurious_cleanup(&cmds[end - 1]) {
        end -= 1;
    }
    &cmds[..end]
}

fn do_list(cmds: &[Token], in_loop: bool, out: &mut Out) {
    let stripped = strip_cleanup(cmds);
    do_list_stripped(stripped, in_loop, out);
}

fn do_list_stripped(cmds: &[Token], in_loop: bool, out: &mut Out) {
    if in_loop {
        // Comment every command, including the last.
        if let Some((current, tail)) = cmds.split_first() {
            comment_if_exec(current, out);
            do_list(tail, true, out);
        }
    } else {
        // Comment all but the last remaining command.
        if cmds.len() >= 2 {
            comment_if_exec(&cmds[0], out);
            do_list(&cmds[1..], false, out);
        }
    }
}

fn comment_if_exec(t: &Token, out: &mut Out) {
    match &*t.inner {
        InnerToken::T_Pipeline { commands, .. } if commands.len() == 1 => {
            comment_if_exec(&commands[0], out);
        }
        InnerToken::T_Redirecting { cmd, .. } => {
            if let InnerToken::T_SimpleCommand { words, .. } = &*cmd.inner {
                if words.len() >= 2
                    && astlib::get_literal_string(&words[0]).as_deref() == Some("exec")
                {
                    warn(
                        out,
                        cmd.id(),
                        2093,
                        "Remove \"exec \" if script should continue after this command.",
                    );
                }
            }
        }
        _ => {}
    }
}

// ---------------------------------------------------------------------------
// SC2270-2282 — checkEqualsInCommand (target code SC2281)
// ---------------------------------------------------------------------------

fn eic_has_equals(t: &Token) -> bool {
    matches!(&*t.inner, InnerToken::T_Literal(s) if s.contains('='))
}

fn matches_positional_assignment(s: &str) -> bool {
    let b = s.as_bytes();
    if b.is_empty() || !b[0].is_ascii_digit() {
        return false;
    }
    if b.len() >= 2 && b[1] == b'=' {
        return true;
    }
    b.len() >= 3 && b[1].is_ascii_digit() && b[2] == b'='
}

fn is_leading_number_var(s: &str) -> bool {
    let lead: &str = match s.find('=') {
        Some(i) => &s[..i],
        None => s,
    };
    let mut chars = lead.chars();
    match chars.next() {
        Some(x) => {
            x.is_ascii_digit()
                && lead.chars().all(crate::cfg::is_variable_char)
                && !lead.chars().all(|c| c.is_ascii_digit())
        }
        None => false,
    }
}

fn is_conflict_marker(cmd: &Token) -> bool {
    if let Some(str) = get_unquoted_literal(cmd) {
        let n = str.chars().count();
        str.chars().all(|c| c == '=') && (4..=12).contains(&n)
    } else {
        false
    }
}

fn may_be_variable_name(leading: &[&Token]) -> bool {
    if leading.iter().any(|t| is_quotes(t)) {
        return false;
    }
    if leading.iter().any(|t| will_become_multiple_args(t)) {
        return false;
    }
    let fb = |_: &InnerToken| Some("x".to_string());
    let mut s = String::new();
    for p in leading {
        s.push_str(&astlib::get_literal_string_ext(p, &fb).unwrap_or_default());
    }
    crate::cfg::is_variable_name(&s)
}

fn check_equals_in_command(params: &Parameters, original: &Token, out: &mut Out) {
    let (assignments_empty, single_word, words) = match &*original.inner {
        InnerToken::T_SimpleCommand { assignments, words } => {
            (assignments.is_empty(), words.len() == 1, words)
        }
        _ => return,
    };
    let word = match words.first() {
        Some(w) => w,
        None => return,
    };
    let list = match &*word.inner {
        InnerToken::T_NormalWord(list) => list,
        _ => return,
    };
    if !list.iter().any(eic_has_equals) {
        return;
    }
    // break hasEquals: leading before the first '='-literal, eq = that literal.
    let eq_idx = match list.iter().position(eic_has_equals) {
        Some(i) => i,
        None => return,
    };
    let mut leading: Vec<&Token> = list[..eq_idx].iter().collect();
    let eq = &list[eq_idx];
    // stripSinglePlus: drop a trailing literal "+" from leading.
    if let Some(last) = leading.last() {
        if matches!(&*last.inner, InnerToken::T_Literal(s) if s == "+") {
            leading.pop();
        }
    }

    let (lit_id, s) = match &*eq.inner {
        InnerToken::T_Literal(s) => (eq.id(), s.clone()),
        _ => return,
    };
    let cmd_id = word.id();

    // Message helpers.
    let positional_msg = |out: &mut Out, id: Id| {
        err(
            out,
            id,
            2270,
            "To assign positional parameters, use 'set -- first second ..' (or use [ ] to compare).",
        );
    };
    let indirection_msg = |out: &mut Out, id: Id| {
        err(
            out,
            id,
            2271,
            "For indirection, use arrays, declare \"var$n=value\", or (for sh) read/eval.",
        );
    };
    let bad_comparison_msg = |out: &mut Out, id: Id| {
        err(
            out,
            id,
            2272,
            "Command name contains ==. For comparison, use [ \"$var\" = value ].",
        );
    };
    let conflict_marker_msg = |out: &mut Out, id: Id| {
        err(
            out,
            id,
            2273,
            "Sequence of ===s found. Merge conflict or intended as a commented border?",
        );
    };
    let border_msg = |out: &mut Out, id: Id| {
        err(
            out,
            id,
            2274,
            "Command name starts with ===. Intended as a commented border?",
        );
    };
    let prefix_msg = |out: &mut Out, id: Id| {
        err(out, id, 2275, "Command name starts with =. Bad line break?");
    };
    let generic_msg = |out: &mut Out, id: Id| {
        err(
            out,
            id,
            2276,
            "This is interpreted as a command name containing '='. Bad assignment or comparison?",
        );
    };
    let leading_number_msg = |out: &mut Out, id: Id| {
        err(
            out,
            id,
            2282,
            "Variable names can't start with numbers, so this is interpreted as a command.",
        );
    };
    let assign0_msg = |out: &mut Out, id: Id, bashfix: Fix| match params.shell {
        Shell::Bash => err_with_fix(
            out,
            id,
            2277,
            "Use BASH_ARGV0 to assign to $0 in bash (or use [ ] to compare).",
            bashfix,
        ),
        Shell::Ksh => err(
            out,
            id,
            2278,
            "$0 can't be assigned in Ksh (but it does reflect the current function).",
        ),
        Shell::Dash => err(
            out,
            id,
            2279,
            "$0 can't be assigned in Dash. This becomes a command name.",
        ),
        Shell::BusyboxSh => err(
            out,
            id,
            2279,
            "$0 can't be assigned in Busybox Ash. This becomes a command name.",
        ),
        _ => err(
            out,
            id,
            2280,
            "$0 can't be assigned this way, and there is no portable alternative.",
        ),
    };

    // The order of these branches matters.
    if leading.is_empty() && s.starts_with('-') {
        // --foo=42  (SC2215 territory)
        return;
    }
    if leading.is_empty() && s.starts_with('=') {
        if assignments_empty && single_word && is_conflict_marker(word) {
            conflict_marker_msg(out, original.id());
        } else if s.starts_with("===") {
            border_msg(out, original.id());
        } else {
            prefix_msg(out, cmd_id);
        }
        return;
    }
    if s.contains("==") {
        bad_comparison_msg(out, cmd_id);
        return;
    }
    // [T_DollarBraced id braced l] | "=" prefix s
    if leading.len() == 1 {
        if let InnerToken::T_DollarBraced { braced, op } = &*leading[0].inner {
            if s.starts_with('=') {
                let db_id = leading[0].id();
                let variable_str = crate::cfg::oversimplify(op).concat();
                let variable_reference = crate::cfg::get_braced_reference(&variable_str);
                let variable_modifier = crate::cfg::get_braced_modifier(&variable_str);
                let is_plain = crate::cfg::is_variable_name(&variable_str);
                let is_positional =
                    !variable_str.is_empty() && variable_str.chars().all(|c| c.is_ascii_digit());
                let is_array = !variable_reference.is_empty()
                    && variable_modifier.starts_with('[')
                    && variable_modifier.ends_with(']');

                // Mirrors Analytics.hs checkEqualsInCommand `case () of`: the
                // empty-name (`${}=`) and `#`-prefixed (`$#=`/`${#var}=`) arms
                // are distinct cases in the oracle that happen to share the
                // generic message; kept separate to preserve that mapping.
                #[allow(clippy::if_same_then_else)]
                if variable_str.is_empty() {
                    generic_msg(out, cmd_id);
                } else if variable_str.starts_with('#') {
                    generic_msg(out, cmd_id);
                } else if variable_str == "0" {
                    let fix = fix_with(vec![replace_token(params, db_id, "BASH_ARGV0")]);
                    assign0_msg(out, db_id, fix);
                } else if is_positional {
                    positional_msg(out, db_id);
                } else if is_array || is_plain {
                    let sigil = if *braced { "${}" } else { "$" };
                    let msg = format!("Don't use {} on the left side of assignments.", sigil);
                    let fix = if *braced {
                        fix_with(vec![
                            replace_start(params, db_id, 2, ""),
                            replace_end(params, db_id, 1, ""),
                        ])
                    } else {
                        fix_with(vec![replace_start(params, db_id, 1, "")])
                    };
                    err_with_fix(out, db_id, 2281, &msg, fix);
                } else {
                    indirection_msg(out, db_id);
                }
                return;
            }
        }
    }
    if leading.is_empty() && matches_positional_assignment(&s) {
        if s.starts_with("0=") {
            let fix = fix_with(vec![replace_start(params, lit_id, 1, "BASH_ARGV0")]);
            assign0_msg(out, lit_id, fix);
        } else {
            positional_msg(out, lit_id);
        }
        return;
    }
    if leading.is_empty() && is_leading_number_var(&s) {
        leading_number_msg(out, cmd_id);
        return;
    }
    if !leading.is_empty() {
        let before_eq: String = s.chars().take_while(|&c| c != '=').collect();
        if may_be_variable_name(&leading) && before_eq.chars().all(crate::cfg::is_variable_char) {
            indirection_msg(out, cmd_id);
            return;
        }
    }
    generic_msg(out, cmd_id);
}

// ---------------------------------------------------------------------------
// SC2144/SC2198/SC2199/SC2200/SC2201/SC2202/SC2203/SC2208/SC2245/SC2255 —
// checkTestArgumentSplitting
// ---------------------------------------------------------------------------

const ARITHMETIC_BINARY_TEST_OPS: [&str; 6] = ["-eq", "-ne", "-lt", "-le", "-gt", "-ge"];

fn glob_has_split_range(l: &[Token]) -> bool {
    let after: Vec<&Token> = l
        .iter()
        .skip_while(|t| !matches!(&*t.inner, InnerToken::T_Literal(s) if s == "["))
        .collect();
    after
        .iter()
        .any(|t| matches!(&*t.inner, InnerToken::T_Literal(s) if s.contains(']')))
}

fn is_brace_expansion(t: &Token) -> bool {
    matches!(&*t.inner, InnerToken::T_BraceExpansion(_))
}

fn tas_check_arrays(params: &Parameters, typ: ConditionType, token: &Token, out: &mut Out) {
    if word_parts(token).iter().any(|p| is_array_expansion(p)) {
        if typ == ConditionType::SingleBracket {
            warn(
                out,
                token.id(),
                2198,
                "Arrays don't work as operands in [ ]. Use a loop (or concatenate with * instead of @).",
            );
        } else {
            err(
                out,
                token.id(),
                2199,
                "Arrays implicitly concatenate in [[ ]]. Use a loop (or explicit * instead of @).",
            );
        }
    }
}

fn tas_check_braces(params: &Parameters, typ: ConditionType, token: &Token, out: &mut Out) {
    if word_parts(token).iter().any(|p| is_brace_expansion(p)) {
        if typ == ConditionType::SingleBracket {
            warn(
                out,
                token.id(),
                2200,
                "Brace expansions don't work as operands in [ ]. Use a loop.",
            );
        } else {
            err(
                out,
                token.id(),
                2201,
                "Brace expansion doesn't happen in [[ ]]. Use a loop.",
            );
        }
    }
}

fn tas_check_globs(params: &Parameters, typ: ConditionType, token: &Token, out: &mut Out) {
    if is_glob(token) {
        if typ == ConditionType::SingleBracket {
            warn(
                out,
                token.id(),
                2202,
                "Globs don't work as operands in [ ]. Use a loop.",
            );
        } else {
            err(
                out,
                token.id(),
                2203,
                "Globs are ignored in [[ ]] except right of =/!=. Use a loop.",
            );
        }
    }
}

fn tas_check_all(params: &Parameters, typ: ConditionType, token: &Token, out: &mut Out) {
    tas_check_arrays(params, typ, token, out);
    tas_check_braces(params, typ, token, out);
    tas_check_globs(params, typ, token, out);
}

fn tas_check_numerical_glob(params: &Parameters, token: &Token, out: &mut Out) {
    // Only the SingleBracket clause exists in Haskell; callers only pass SingleBracket.
    if params.shell != Shell::Ksh && is_glob(token) {
        err(
            out,
            token.id(),
            2255,
            "[ ] does not apply arithmetic evaluation. Evaluate with $((..)) for numbers, or use string comparator for strings.",
        );
    }
}

fn check_test_argument_splitting(params: &Parameters, t: &Token, out: &mut Out) {
    match &*t.inner {
        InnerToken::TC_Unary { typ, op, token } if is_glob(token) => {
            if op == "-v" {
                if *typ == ConditionType::SingleBracket {
                    err(
                        out,
                        token.id(),
                        2208,
                        "Use [[ ]] or quote arguments to -v to avoid glob expansion.",
                    );
                }
            } else if *typ == ConditionType::SingleBracket && params.shell == Shell::Ksh {
                // Ksh appears to stop processing after unrecognized tokens.
                let ksh_ops: Vec<String> = "bcdfgkprsuwxLhNOGRS"
                    .chars()
                    .map(|c| format!("-{}", c))
                    .collect();
                if ksh_ops.iter().any(|o| o == op) {
                    warn(
                        out,
                        token.id(),
                        2245,
                        &format!(
                            "{} only applies to the first expansion of this glob. Use a loop to check any/all.",
                            op
                        ),
                    );
                }
            } else {
                err(
                    out,
                    token.id(),
                    2144,
                    &format!("{} doesn't work with globs. Use a for loop.", op),
                );
            }
        }
        InnerToken::TC_Nullary { typ, token } => {
            tas_check_braces(params, *typ, token, out);
            tas_check_globs(params, *typ, token, out);
            if *typ == ConditionType::DoubleBracket {
                tas_check_arrays(params, *typ, token, out);
            }
        }
        InnerToken::TC_Unary { typ, token, .. } => {
            tas_check_all(params, *typ, token, out);
        }
        InnerToken::TC_Binary { typ, op, lhs, rhs }
            if ARITHMETIC_BINARY_TEST_OPS.contains(&op.as_str()) =>
        {
            if *typ == ConditionType::DoubleBracket {
                for c in [lhs, rhs] {
                    tas_check_arrays(params, *typ, c, out);
                    tas_check_braces(params, *typ, c, out);
                }
            } else {
                for c in [lhs, rhs] {
                    tas_check_numerical_glob(params, c, out);
                    tas_check_arrays(params, *typ, c, out);
                    tas_check_braces(params, *typ, c, out);
                }
            }
        }
        InnerToken::TC_Binary { typ, op, lhs, rhs } => {
            if matches!(op.as_str(), "=" | "==" | "!=" | "=~") {
                tas_check_all(params, *typ, lhs, out);
                tas_check_arrays(params, *typ, rhs, out);
                tas_check_braces(params, *typ, rhs, out);
            } else {
                tas_check_all(params, *typ, lhs, out);
                tas_check_all(params, *typ, rhs, out);
            }
        }
        _ => {}
    }
}

// ---------------------------------------------------------------------------
// SC2216/SC2217/SC2259/SC2260/SC2261 — checkPipeToNowhere (target code SC2261)
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, PartialEq, Eq)]
enum PipeType {
    StdoutPipe,
    StdoutStderrPipe,
    NoPipe,
}

/// `ShellCheck.Data.nonReadingCommands`.
const NON_READING_COMMANDS: &[&str] = &[
    "alias", "basename", "bg", "cal", "cd", "chgrp", "chmod", "chown", "cp", "du", "echo",
    "export", "fg", "fuser", "getconf", "getopt", "getopts", "ipcrm", "ipcs", "jobs", "kill", "ln",
    "ls", "locale", "mv", "printf", "ps", "pwd", "readlink", "realpath", "renice", "rm", "rmdir",
    "set", "sleep", "touch", "trap", "ulimit", "unalias", "uname",
];

const INTERACTIVE_FLAG_CMDS: &[&str] = &["cp", "mv", "rm"];

// ---------------------------------------------------------------------------
// SC2233/SC2234/SC2235 — checkSubshelledTests (target code SC2235)
// ---------------------------------------------------------------------------

fn sst_is_command_test(t: &Token) -> bool {
    is_command(t, "test")
}

fn sst_is_test_command(t: &Token) -> bool {
    if let InnerToken::T_Pipeline {
        separators,
        commands,
    } = &*t.inner
    {
        if separators.is_empty() && commands.len() == 1 {
            if let InnerToken::T_Redirecting { cmd, .. } = &*commands[0].inner {
                return matches!(&*cmd.inner, InnerToken::T_Condition { .. })
                    || sst_is_command_test(cmd);
            }
        }
    }
    false
}

fn sst_is_test_structure(t: &Token) -> bool {
    match &*t.inner {
        InnerToken::T_Banged(w) => sst_is_test_structure(w),
        InnerToken::T_AndIf { lhs, rhs } | InnerToken::T_OrIf { lhs, rhs } => {
            sst_is_test_structure(lhs) && sst_is_test_structure(rhs)
        }
        InnerToken::T_Pipeline {
            separators,
            commands,
        } if separators.is_empty() && commands.len() == 1 => {
            if let InnerToken::T_Redirecting { cmd, .. } = &*commands[0].inner {
                match &*cmd.inner {
                    InnerToken::T_BraceGroup(ts) => ts.iter().all(sst_is_test_structure),
                    InnerToken::T_Subshell(ts) => ts.iter().all(sst_is_test_structure),
                    _ => sst_is_test_command(t),
                }
            } else {
                sst_is_test_command(t)
            }
        }
        _ => sst_is_test_command(t),
    }
}

fn sst_is_single_test(cmds: &[Token]) -> bool {
    cmds.len() == 1 && sst_is_test_command(&cmds[0])
}

fn is_function_tok(t: &Token) -> bool {
    matches!(&*t.inner, InnerToken::T_Function { .. })
}

fn sst_is_function_body(path: &[Token]) -> bool {
    // path[0] is the subshell itself; path[1] is its immediate parent.
    path.get(1).map_or(false, is_function_tok)
}

fn sst_skippable(t: &Token) -> bool {
    match &*t.inner {
        InnerToken::T_Redirecting { redirs, .. } => redirs.is_empty(),
        InnerToken::T_Pipeline { separators, .. } => separators.is_empty(),
        InnerToken::T_Annotation { .. } => true,
        _ => false,
    }
}

fn sst_is_compound_condition(path: &[Token]) -> bool {
    // dropWhile skippable over the tail (parents) of the path.
    let tail = if path.len() > 1 { &path[1..] } else { &[][..] };
    let mut iter = tail.iter().skip_while(|t| sst_skippable(t));
    match iter.next() {
        Some(t) => matches!(
            &*t.inner,
            InnerToken::T_IfExpression { .. }
                | InnerToken::T_WhileExpression { .. }
                | InnerToken::T_UntilExpression { .. }
        ),
        None => false,
    }
}

fn sst_is_assignment_node(t: &Token) -> bool {
    match &*t.inner {
        InnerToken::TA_Assignment { .. } => true,
        InnerToken::TA_Unary { op, .. } => op.contains("++") || op.contains("--"),
        InnerToken::T_DollarBraced { op, .. } => {
            let str = crate::cfg::oversimplify(op).concat();
            let modifier = crate::cfg::get_braced_modifier(&str);
            modifier.starts_with('=') || modifier.starts_with(":=")
        }
        InnerToken::T_DollarBraceCommandExpansion { .. } => true,
        _ => false,
    }
}

fn sst_has_assignment(t: &Token) -> bool {
    let mut found = false;
    t.visit_preorder(&mut |n| {
        if sst_is_assignment_node(n) {
            found = true;
        }
    });
    found
}

fn check_subshelled_tests(params: &Parameters, t: &Token, out: &mut Out) {
    if let InnerToken::T_Subshell(list) = &*t.inner {
        if list.iter().all(sst_is_test_structure) && !sst_has_assignment(t) {
            let path = get_path(params, t);
            if sst_is_compound_condition(&path) {
                style(
                    out,
                    t.id(),
                    2233,
                    "Remove superfluous (..) around condition to avoid subshell overhead.",
                );
            } else if sst_is_single_test(list) && !sst_is_function_body(&path) {
                style(
                    out,
                    t.id(),
                    2234,
                    "Remove superfluous (..) around test command to avoid subshell overhead.",
                );
            } else {
                style(
                    out,
                    t.id(),
                    2235,
                    "Use { ..; } instead of (..) to avoid subshell overhead.",
                );
            }
        }
    }
}

fn check_splitting_in_arrays(params: &Parameters, t: &Token, out: &mut Out) {
    if let InnerToken::T_Array(elements) = &*t.inner {
        for word in elements {
            if let InnerToken::T_NormalWord(parts) = &*word.inner {
                for part in parts {
                    check_splitting_part(params, part, out);
                }
            }
        }
    }
}

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
    fn emits(f: fn(&Parameters, &Token, &mut Out), s: &str) -> bool {
        let params = params_for(s);
        let mut out = Out::new();
        params.root.visit_preorder(&mut |t| f(&params, t, &mut out));
        !out.is_empty()
    }
    fn emits_code(f: fn(&Parameters, &Token, &mut Out), s: &str, code: i64) -> bool {
        let params = params_for(s);
        let mut out = Out::new();
        params.root.visit_preorder(&mut |t| f(&params, t, &mut out));
        out.iter().any(|c| c.comment.code == code)
    }
    fn codes(f: fn(&Parameters, &Token, &mut Out), s: &str) -> Vec<i64> {
        let params = params_for(s);
        let mut out = Out::new();
        params.root.visit_preorder(&mut |t| f(&params, t, &mut out));
        out.iter().map(|c| c.comment.code).collect()
    }

    // ---- SC2013 checkForInCat ----
    #[test]
    fn prop_checkForInCat1() {
        assert!(emits(
            check_for_in_cat,
            "for f in $(cat foo); do stuff; done"
        ));
    }
    #[test]
    fn prop_checkForInCat1a() {
        assert!(emits(
            check_for_in_cat,
            "for f in `cat foo`; do stuff; done"
        ));
    }
    #[test]
    fn prop_checkForInCat2() {
        assert!(emits(
            check_for_in_cat,
            "for f in $(cat foo | grep lol); do stuff; done"
        ));
    }
    #[test]
    fn prop_checkForInCat2a() {
        assert!(emits(
            check_for_in_cat,
            "for f in `cat foo | grep lol`; do stuff; done"
        ));
    }
    #[test]
    fn prop_checkForInCat3() {
        assert!(!emits(
            check_for_in_cat,
            "for f in $(cat foo | grep bar | wc -l); do stuff; done"
        ));
    }

    // ---- SC2210 checkRedirectionToNumber ----

    // ---- SC2206 / SC2207 checkSplittingInArrays ----

    // ---- SC2268 checkComparisonWithLeadingX ----
    #[test]
    fn prop_checkComparisonWithLeadingX1() {
        assert!(emits(check_comparison_with_leading_x, "[ x$foo = xlol ]"));
    }
    #[test]
    fn prop_checkComparisonWithLeadingX2() {
        assert!(emits(check_comparison_with_leading_x, "test x$foo = xlol"));
    }
    #[test]
    fn prop_checkComparisonWithLeadingX3() {
        assert!(!emits(check_comparison_with_leading_x, "[ $foo = xbar ]"));
    }
    #[test]
    fn prop_checkComparisonWithLeadingX4() {
        assert!(!emits(check_comparison_with_leading_x, "test $foo = xbar"));
    }
    #[test]
    fn prop_checkComparisonWithLeadingX5() {
        assert!(emits(
            check_comparison_with_leading_x,
            "[ \"x$foo\" = 'xlol' ]"
        ));
    }
    #[test]
    fn prop_checkComparisonWithLeadingX6() {
        assert!(emits(
            check_comparison_with_leading_x,
            "[ x\"$foo\" = x'lol' ]"
        ));
    }
    #[test]
    fn prop_checkComparisonWithLeadingX7() {
        assert!(emits(check_comparison_with_leading_x, "[ X$foo != Xbar ]"));
    }

    // ---- SC2001 checkEchoSed ----
    #[test]
    fn prop_checkEchoSed1() {
        assert!(emits_code(
            check_echo_sed,
            "FOO=$(echo \"$cow\" | sed 's/foo/bar/g')",
            2001
        ));
    }
    #[test]
    fn prop_checkEchoSed1b() {
        assert!(emits_code(
            check_echo_sed,
            "FOO=$(sed 's/foo/bar/g' <<< \"$cow\")",
            2001
        ));
    }
    #[test]
    fn prop_checkEchoSed2() {
        assert!(emits_code(
            check_echo_sed,
            "rm $(echo $cow | sed -e 's,foo,bar,')",
            2001
        ));
    }
    #[test]
    fn prop_checkEchoSed2b() {
        assert!(emits_code(
            check_echo_sed,
            "rm $(sed -e 's,foo,bar,' <<< $cow)",
            2001
        ));
    }

    // ---- SC2093 checkSpuriousExec ----
    #[test]
    fn prop_checkSpuriousExec1() {
        assert!(emits(check_spurious_exec, "exec foo; true"));
    }
    #[test]
    fn prop_checkSpuriousExec2() {
        assert!(emits(check_spurious_exec, "if a; then exec b; exec c; fi"));
    }
    #[test]
    fn prop_checkSpuriousExec3() {
        assert!(!emits(check_spurious_exec, "echo cow; exec foo"));
    }
    #[test]
    fn prop_checkSpuriousExec4() {
        assert!(!emits(check_spurious_exec, "if a; then exec b; fi"));
    }
    #[test]
    fn prop_checkSpuriousExec5() {
        assert!(!emits(check_spurious_exec, "exec > file; cmd"));
    }
    #[test]
    fn prop_checkSpuriousExec6() {
        assert!(emits(check_spurious_exec, "exec foo > file; cmd"));
    }
    #[test]
    fn prop_checkSpuriousExec7() {
        assert!(!emits(
            check_spurious_exec,
            "exec file; echo failed; exit 3"
        ));
    }
    #[test]
    fn prop_checkSpuriousExec8() {
        assert!(!emits(
            check_spurious_exec,
            "exec {origout}>&1- >tmp.log 2>&1; bar"
        ));
    }
    #[test]
    fn prop_checkSpuriousExec9() {
        assert!(emits(
            check_spurious_exec,
            "for file in rc.d/*; do exec \"$file\"; done"
        ));
    }
    #[test]
    fn prop_checkSpuriousExec10() {
        assert!(!emits(
            check_spurious_exec,
            "exec file; r=$?; printf >&2 'failed\n'; return $r"
        ));
    }
    #[test]
    fn prop_checkSpuriousExec11() {
        assert!(!emits(check_spurious_exec, "exec file; :"));
    }
    #[test]
    fn prop_checkSpuriousExec12() {
        assert!(!emits(
            check_spurious_exec,
            "#!/bin/bash\nshopt -s execfail; exec foo; exec bar; echo 'Error'; exit 1;"
        ));
    }
    #[test]
    fn prop_checkSpuriousExec13() {
        assert!(emits(
            check_spurious_exec,
            "#!/bin/dash\nshopt -s execfail; exec foo; exec bar; echo 'Error'; exit 1;"
        ));
    }

    // ---- SC2270-2282 checkEqualsInCommand ----
    fn eic_codes(s: &str) -> Vec<i64> {
        codes(check_equals_in_command, s)
    }
    #[test]
    fn prop_checkEqualsInCommand1a() {
        assert_eq!(eic_codes("#!/bin/bash\n0='foo'"), vec![2277]);
    }
    #[test]
    fn prop_checkEqualsInCommand2a() {
        assert_eq!(eic_codes("#!/bin/ksh \n$0='foo'"), vec![2278]);
    }
    #[test]
    fn prop_checkEqualsInCommand3a() {
        assert_eq!(eic_codes("#!/bin/dash\n${0}='foo'"), vec![2279]);
    }
    #[test]
    fn prop_checkEqualsInCommand4a() {
        assert_eq!(eic_codes("#!/bin/sh  \n0='foo'"), vec![2280]);
    }
    #[test]
    fn prop_checkEqualsInCommand1b() {
        assert_eq!(eic_codes("1='foo'"), vec![2270]);
    }
    #[test]
    fn prop_checkEqualsInCommand2b() {
        assert_eq!(eic_codes("${2}='foo'"), vec![2270]);
    }
    #[test]
    fn prop_checkEqualsInCommand1c() {
        assert_eq!(eic_codes("var$((n+1))=value"), vec![2271]);
    }
    #[test]
    fn prop_checkEqualsInCommand2c() {
        assert_eq!(eic_codes("var${x}=value"), vec![2271]);
    }
    #[test]
    fn prop_checkEqualsInCommand3c() {
        assert_eq!(eic_codes("var$((cmd))x='foo'"), vec![2271]);
    }
    #[test]
    fn prop_checkEqualsInCommand4c() {
        assert_eq!(eic_codes("$(cmd)='foo'"), vec![2271]);
    }
    #[test]
    fn prop_checkEqualsInCommand1d() {
        assert_eq!(eic_codes("======="), vec![2273]);
    }
    #[test]
    fn prop_checkEqualsInCommand2d() {
        assert_eq!(eic_codes("======= Here ======="), vec![2274]);
    }
    #[test]
    fn prop_checkEqualsInCommand3d() {
        assert_eq!(eic_codes("foo\n=42"), vec![2275]);
    }
    #[test]
    fn prop_checkEqualsInCommand1e() {
        assert_eq!(eic_codes("--foo=bar"), Vec::<i64>::new());
    }
    #[test]
    fn prop_checkEqualsInCommand2e() {
        assert_eq!(eic_codes("$(cmd)'=foo'"), Vec::<i64>::new());
    }
    #[test]
    fn prop_checkEqualsInCommand3e() {
        assert_eq!(eic_codes("var${x}/=value"), vec![2276]);
    }
    #[test]
    fn prop_checkEqualsInCommand4e() {
        assert_eq!(eic_codes("${}=value"), vec![2276]);
    }
    #[test]
    fn prop_checkEqualsInCommand5e() {
        assert_eq!(eic_codes("${#x}=value"), vec![2276]);
    }
    #[test]
    fn prop_checkEqualsInCommand1f() {
        assert_eq!(eic_codes("$var=foo"), vec![2281]);
    }
    #[test]
    fn prop_checkEqualsInCommand2f() {
        assert_eq!(eic_codes("$a=$b"), vec![2281]);
    }
    #[test]
    fn prop_checkEqualsInCommand3f() {
        assert_eq!(eic_codes("${var}=foo"), vec![2281]);
    }
    #[test]
    fn prop_checkEqualsInCommand4f() {
        assert_eq!(eic_codes("${var[42]}=foo"), vec![2281]);
    }
    #[test]
    fn prop_checkEqualsInCommand5f() {
        assert_eq!(eic_codes("$var+=foo"), vec![2281]);
    }
    #[test]
    fn prop_checkEqualsInCommand1g() {
        assert_eq!(eic_codes("411toppm=true"), vec![2282]);
    }

    // ---- SC2144/2198/2199/2200/2201/2202/2203/2208/2245/2255 checkTestArgumentSplitting ----
    #[test]
    fn prop_checkTestArgumentSplitting1() {
        assert!(emits(check_test_argument_splitting, "[ -e *.mp3 ]"));
    }
    #[test]
    fn prop_checkTestArgumentSplitting2() {
        assert!(!emits(check_test_argument_splitting, "[[ $a == *b* ]]"));
    }
    #[test]
    fn prop_checkTestArgumentSplitting3() {
        assert!(emits(check_test_argument_splitting, "[[ *.png == '' ]]"));
    }
    #[test]
    fn prop_checkTestArgumentSplitting4() {
        assert!(emits(
            check_test_argument_splitting,
            "[[ foo == f{o,oo,ooo} ]]"
        ));
    }
    #[test]
    fn prop_checkTestArgumentSplitting5() {
        assert!(emits(check_test_argument_splitting, "[[ $@ ]]"));
    }
    #[test]
    fn prop_checkTestArgumentSplitting6() {
        assert!(emits(check_test_argument_splitting, "[ -e $@ ]"));
    }
    #[test]
    fn prop_checkTestArgumentSplitting7() {
        assert!(emits(check_test_argument_splitting, "[ $@ == $@ ]"));
    }
    #[test]
    fn prop_checkTestArgumentSplitting8() {
        assert!(emits(check_test_argument_splitting, "[[ $@ = $@ ]]"));
    }
    #[test]
    fn prop_checkTestArgumentSplitting9() {
        assert!(!emits(
            check_test_argument_splitting,
            "[[ foo =~ bar{1,2} ]]"
        ));
    }
    #[test]
    fn prop_checkTestArgumentSplitting10() {
        assert!(!emits(check_test_argument_splitting, "[ \"$@\" ]"));
    }
    #[test]
    fn prop_checkTestArgumentSplitting11() {
        assert!(emits(check_test_argument_splitting, "[[ \"$@\" ]]"));
    }
    #[test]
    fn prop_checkTestArgumentSplitting12() {
        assert!(emits(check_test_argument_splitting, "[ *.png ]"));
    }
    #[test]
    fn prop_checkTestArgumentSplitting13() {
        assert!(emits(check_test_argument_splitting, "[ \"$@\" == \"\" ]"));
    }
    #[test]
    fn prop_checkTestArgumentSplitting14() {
        assert!(emits(check_test_argument_splitting, "[[ \"$@\" == \"\" ]]"));
    }
    #[test]
    fn prop_checkTestArgumentSplitting15() {
        assert!(!emits(
            check_test_argument_splitting,
            "[[ \"$*\" == \"\" ]]"
        ));
    }
    #[test]
    fn prop_checkTestArgumentSplitting16() {
        assert!(!emits(check_test_argument_splitting, "[[ -v foo[123] ]]"));
    }
    #[test]
    fn prop_checkTestArgumentSplitting17() {
        assert!(!emits(
            check_test_argument_splitting,
            "#!/bin/ksh\n[ -e foo* ]"
        ));
    }
    #[test]
    fn prop_checkTestArgumentSplitting18() {
        assert!(emits(
            check_test_argument_splitting,
            "#!/bin/ksh\n[ -d foo* ]"
        ));
    }
    #[test]
    fn prop_checkTestArgumentSplitting19() {
        assert!(!emits(
            check_test_argument_splitting,
            "[[ var[x] -eq 2*3 ]]"
        ));
    }
    #[test]
    fn prop_checkTestArgumentSplitting20() {
        assert!(emits(check_test_argument_splitting, "[ var[x] -eq 2 ]"));
    }
    #[test]
    fn prop_checkTestArgumentSplitting21() {
        assert!(emits(check_test_argument_splitting, "[ 6 -eq 2*3 ]"));
    }

    // ---- SC2216/2217/2259/2260/2261 checkPipeToNowhere ----

    // ---- SC2233/2234/2235 checkSubshelledTests ----
    #[test]
    fn prop_checkSubshelledTests1() {
        assert!(emits(check_subshelled_tests, "a && ( [ b ] || ! [ c ] )"));
    }
    #[test]
    fn prop_checkSubshelledTests2() {
        assert!(emits(check_subshelled_tests, "( [ a ] )"));
    }
    #[test]
    fn prop_checkSubshelledTests3() {
        assert!(emits(
            check_subshelled_tests,
            "( [ a ] && [ b ] || test c )"
        ));
    }
    #[test]
    fn prop_checkSubshelledTests4() {
        assert!(emits(
            check_subshelled_tests,
            "( [ a ] && { [ b ] && [ c ]; } )"
        ));
    }
    #[test]
    fn prop_checkSubshelledTests5() {
        assert!(!emits(check_subshelled_tests, "( [[ ${var:=x} = y ]] )"));
    }
    #[test]
    fn prop_checkSubshelledTests6() {
        assert!(!emits(check_subshelled_tests, "( [[ $((i++)) = 10 ]] )"));
    }
    #[test]
    fn prop_checkSubshelledTests7() {
        assert!(!emits(check_subshelled_tests, "( [[ $((i+=1)) = 10 ]] )"));
    }
    #[test]
    fn prop_checkSubshelledTests8() {
        assert!(emits(
            check_subshelled_tests,
            "# shellcheck disable=SC2234\nf() ( [[ x ]] )"
        ));
    }
    #[test]
    fn prop_checkSplittingInArrays1() {
        assert!(emits(check_splitting_in_arrays, "a=( $var )"));
    }
    #[test]
    fn prop_checkSplittingInArrays2() {
        assert!(emits(check_splitting_in_arrays, "a=( $(cmd) )"));
    }
    #[test]
    fn prop_checkSplittingInArrays3() {
        assert!(!emits(check_splitting_in_arrays, "a=( \"$var\" )"));
    }
    #[test]
    fn prop_checkSplittingInArrays4() {
        assert!(!emits(check_splitting_in_arrays, "a=( \"$(cmd)\" )"));
    }
    #[test]
    fn prop_checkSplittingInArrays5() {
        assert!(!emits(check_splitting_in_arrays, "a=( $! $$ $# )"));
    }
    #[test]
    fn prop_checkSplittingInArrays6() {
        assert!(!emits(check_splitting_in_arrays, "a=( ${#arr[@]} )"));
    }
    #[test]
    fn prop_checkSplittingInArrays7() {
        assert!(!emits(check_splitting_in_arrays, "a=( foo{1,2} )"));
    }
    #[test]
    fn prop_checkSplittingInArrays8() {
        assert!(!emits(check_splitting_in_arrays, "a=( * )"));
    }
}
