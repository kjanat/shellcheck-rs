//! Checks on how commands are invoked, from `ShellCheck.Analytics`.
use crate::analyzer_lib::condition_children;
use crate::analyzer_lib::get_all_flags;
use crate::analyzer_lib::get_command_name;
use crate::analyzer_lib::is_command;
use crate::analyzer_lib::is_unqualified_command;
use crate::analyzer_lib::*;
use crate::ast::*;
use crate::ast_lib::get_command_sequences;
use crate::ast_lib::get_literal_string_def;
use crate::ast_lib::is_glob;
use crate::ast_lib::is_quotes;
use crate::ast_lib::is_unquoted_flag;
use crate::ast_lib::only_literal_string;
use crate::ast_lib::oversimplify;

use crate::ast_lib;
use crate::cfg::get_unquoted_literal;
use crate::cfg::will_become_multiple_args;
use crate::data::COMMON_COMMANDS;
use crate::interface::Fix;
use crate::interface::Shell;

pub(super) fn check_unchecked_cd_pushd_popd(params: &Parameters, t: &Token, out: &mut Out) {
    if has_set_e(params) {
        return;
    }
    if !matches!(&*t.inner, InnerToken::T_SimpleCommand { .. }) {
        return;
    }
    let name = match get_command_name(t) {
        Some(n) => n,
        None => return,
    };
    if !matches!(name.as_str(), "cd" | "pushd" | "popd") {
        return;
    }
    if is_safe_dir(t) {
        return;
    }
    if matches!(name.as_str(), "pushd" | "popd") && get_all_flags(t).iter().any(|(_, f)| f == "n") {
        return;
    }
    if is_last_command_in_function(params, t) {
        return;
    }
    if is_condition_path(params, t) {
        return;
    }
    warn_with_fix(
        out,
        t.id(),
        2164,
        &format!(
            "Use '{n} ... || exit' or '{n} ... || return' in case {n} fails.",
            n = name
        ),
        fix_with(vec![replace_end(params, t.id(), 0, " || exit")]),
    );
}

pub(super) fn check_assign_ate_command(_params: &Parameters, t: &Token, out: &mut Out) {
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

pub(super) fn check_uuoe_var(_params: &Parameters, t: &Token, out: &mut Out) {
    let (id, cmds) = match &*t.inner {
        InnerToken::T_Backticked(cmds) => (t.id(), cmds),
        InnerToken::T_DollarExpansion(cmds) => (t.id(), cmds),
        _ => return,
    };
    // check id (T_Pipeline _ _ [T_Redirecting _ _ c]) = warnForEcho id c
    if cmds.len() != 1 {
        return;
    }
    let pipeline = &cmds[0];
    let commands = match &*pipeline.inner {
        InnerToken::T_Pipeline { commands, .. } if commands.len() == 1 => commands,
        _ => return,
    };
    let c = match &*commands[0].inner {
        InnerToken::T_Redirecting { cmd, .. } => cmd,
        _ => return,
    };
    // checkUnqualifiedCommand "echo": first word literal (unqualified) == "echo".
    let words = match &*c.inner {
        InnerToken::T_SimpleCommand { words, .. } if !words.is_empty() => words,
        _ => return,
    };
    let cmd_name = match ast_lib::get_literal_string(&words[0]) {
        Some(n) => n,
        None => return,
    };
    if cmd_name != "echo" {
        return;
    }
    let vars = &words[1..];
    let (first, rest) = match vars.split_first() {
        Some(x) => x,
        None => return,
    };
    let is_covered = rest.is_empty() && token_is_just_command_output(first);
    if is_covered || only_literal_string(first).starts_with('-') {
        return;
    }
    // Conformance-safety guard: an escaped nested backtick (`echo \`cmd\``) is
    // not reassembled into a `T_Backticked` by the current parser — it leaves
    // literal backtick characters in the arguments, which defeats the
    // `is_covered` (SC2005) detection above and would over-fire here. A
    // correctly parsed command substitution never appears as a literal
    // backtick, so treat any such argument as unreliable and withhold.
    if vars.iter().any(|v| only_literal_string(v).contains('`')) {
        return;
    }
    if vars.iter().all(could_be_optimized) {
        style(
            out,
            id,
            2116,
            "Useless echo? Instead of 'cmd $(echo foo)', just use 'cmd foo'.",
        );
    }
}

pub(super) fn check_find_exec(_params: &Parameters, t: &Token, out: &mut Out) {
    let InnerToken::T_SimpleCommand { words, .. } = &*t.inner else {
        return;
    };
    if words.is_empty() || !is_command(t, "find") {
        return;
    }

    fn should_warn(x: &Token) -> bool {
        matches!(
            &*x.inner,
            InnerToken::T_DollarExpansion(_)
                | InnerToken::T_Backticked(_)
                | InnerToken::T_Glob(_)
                | InnerToken::T_Extglob { .. }
        )
    }
    fn from_word(x: &Token) -> &[Token] {
        match &*x.inner {
            InnerToken::T_NormalWord(l) => l,
            _ => &[],
        }
    }

    // broken over words[1..]
    let r = &words[1..];
    let mut v = false;
    for w in r {
        if v {
            for part in from_word(w) {
                if should_warn(part) {
                    info(
                        out,
                        part.id(),
                        2014,
                        "This will expand once before find runs, not per file found.",
                    );
                }
            }
        }
        v = match ast_lib::get_literal_string(w).as_deref() {
            Some("-exec") | Some("-execdir") | Some("-ok") | Some("-okdir") => true,
            Some("+") | Some(";") => false,
            _ => v,
        };
    }
    if v {
        // last of t (== words, since assignments precede words but Haskell `t`
        // here is the words list `(h:r)`).
        let last = words.last().unwrap();
        err(
            out,
            last.id(),
            2067,
            "Missing ';' or + terminating -exec. You can't use |/||/&&, and ';' has to be a separate, quoted argument.",
        );
    }
}

pub(super) fn check_lonely_dot_dash(_params: &Parameters, t: &Token, out: &mut Out) {
    if let InnerToken::T_Redirecting { .. } = &*t.inner {
        if is_unqualified_command(t, "./") {
            err(
                out,
                t.id(),
                2083,
                "Don't add spaces after the slash in './file'.",
            );
        }
    }
}

pub(super) fn check_spurious_exec(params: &Parameters, t: &Token, out: &mut Out) {
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

/// `checkGlobsAsOptions` (SC2035): a leading `*`/`?` glob argument can be
/// mistaken for options; suggest `./*` or `-- *`.
pub(super) fn check_globs_as_options(params: &Parameters, t: &Token, out: &mut Out) {
    if let InnerToken::T_SimpleCommand { words, .. } = &*t.inner {
        let base = command_basename(words);
        if matches!(base.as_deref(), Some("echo") | Some("printf")) || params.has_noglob {
            return;
        }
        for w in words.iter().skip(1) {
            // stop at end-of-args markers
            if let Some(lit) = ast_lib::get_literal_string(w) {
                if lit == "--" || lit == ":::" || lit == "::::" {
                    break;
                }
            }
            if let InnerToken::T_NormalWord(parts) = &*w.inner {
                if let Some(first) = parts.first() {
                    if let InnerToken::T_Glob(s) = &*first.inner {
                        if s == "*" || s == "?" {
                            info(
                                out,
                                first.id(),
                                2035,
                                "Use ./*glob* or -- *glob* so names with dashes won't become options.",
                            );
                        }
                    }
                }
            }
        }
    }
}

pub(super) fn check_cd_and_back(params: &Parameters, t: &Token, out: &mut Out) {
    if has_set_e(params) {
        return;
    }
    for seq in get_command_sequences(t) {
        let candidates: Vec<&Token> = seq.iter().filter_map(|x| cd_candidate(x)).collect();
        if let Some(id) = find_cd_pair(&candidates) {
            info(
                out,
                id,
                2103,
                "Use a ( subshell ) to avoid having to cd back.",
            );
        }
    }
}

pub(super) fn check_unsupported(params: &Parameters, t: &Token, out: &mut Out) {
    let (name, support) = shell_support(t);
    if support.is_empty() || support.contains(&params.shell) {
        return;
    }
    let shells: Vec<&str> = support.iter().map(|s| shell_lower(*s)).collect();
    err(
        out,
        t.id(),
        2127,
        &format!(
            "To use {}, specify #!/usr/bin/env {}",
            name,
            shells.join(" or ")
        ),
    );
}

pub(super) fn check_cp_legacy_r(params: &Parameters, t: &Token, out: &mut Out) {
    if !matches!(&*t.inner, InnerToken::T_SimpleCommand { .. }) || !is_unqualified_command(t, "cp")
    {
        return;
    }
    let flags = get_all_flags(t);
    if let Some((flag_token, _)) = flags.iter().find(|(_, s)| s == "r") {
        warn_with_fix(
            out,
            flag_token.id(),
            2336,
            "cp -r behavior is implementation-defined",
            fix_with(vec![replace_token(params, flag_token.id(), "-R")]),
        );
    }
}

pub(super) fn check_glob_as_command(_params: &Parameters, t: &Token, out: &mut Out) {
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

pub(super) fn check_flag_as_command(_params: &Parameters, t: &Token, out: &mut Out) {
    if let InnerToken::T_SimpleCommand { assignments, words } = &*t.inner {
        if assignments.is_empty() {
            if let Some(first) = words.first() {
                if is_unquoted_flag(first) {
                    warn(
                        out,
                        first.id(),
                        2215,
                        "This flag is used as a command name. Bad line break or missing [ .. ]?",
                    );
                }
            }
        }
    }
}

pub(super) fn check_equals_in_command(params: &Parameters, original: &Token, out: &mut Out) {
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
                let variable_str = crate::ast_lib::oversimplify(op).concat();
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

pub(super) fn check_command_with_trailing_symbol(_params: &Parameters, t: &Token, out: &mut Out) {
    let InnerToken::T_SimpleCommand { words, .. } = &*t.inner else {
        return;
    };
    let Some(cmd) = words.first() else {
        return;
    };
    let str = get_literal_string_def("x", cmd);
    let last = str.chars().last().unwrap_or('x');
    match str.as_str() {
        "." | ":" | " " | "//" => {}
        "" => err(
            out,
            cmd.id(),
            2286,
            "This empty string is interpreted as a command name. Double check syntax (or use 'true' as a no-op).",
        ),
        _ if last == '/' => err(
            out,
            cmd.id(),
            2287,
            "This is interpreted as a command name ending with '/'. Double check syntax.",
        ),
        _ if "\\.,([{<>}])#\"'% ".contains(last) => warn(
            out,
            cmd.id(),
            2288,
            &format!(
                "This is interpreted as a command name ending with {}. Double check syntax.",
                trailing_symbol_format(last)
            ),
        ),
        _ if str.contains('\t') => err(
            out,
            cmd.id(),
            2289,
            "This is interpreted as a command name containing a tab. Double check syntax.",
        ),
        _ if str.contains('\n') => err(
            out,
            cmd.id(),
            2289,
            "This is interpreted as a command name containing a linefeed. Double check syntax.",
        ),
        _ => {}
    }
}

pub(super) fn check_bats_test_does_not_use_negation(params: &Parameters, t: &Token, out: &mut Out) {
    let InnerToken::T_BatsTest { body, .. } = &*t.inner else {
        return;
    };
    let InnerToken::T_BraceGroup(commands) = &*body.inner else {
        return;
    };
    let is_last = |x: &Token| commands.last().map(|c| c == x).unwrap_or(false);
    for cmd in commands {
        if let InnerToken::T_Banged(inner) = &*cmd.inner {
            // T_Banged (T_Pipeline _ _ [T_Redirecting _ _ (T_Condition ..)])
            let is_condition = matches!(&*inner.inner, InnerToken::T_Pipeline { commands, .. }
                if commands.len() == 1
                    && matches!(&*commands[0].inner, InnerToken::T_Redirecting { cmd, .. }
                        if matches!(&*cmd.inner, InnerToken::T_Condition { .. })));
            if is_condition {
                if is_last(cmd) {
                    style(
                        out,
                        cmd.id(),
                        2315,
                        "In Bats, ! will not fail the test if it is not the last command anymore. Fold the `!` into the conditional!",
                    );
                } else {
                    err(
                        out,
                        cmd.id(),
                        2315,
                        "In Bats, ! does not cause a test failure. Fold the `!` into the conditional!",
                    );
                }
            } else {
                if is_last(cmd) {
                    style_with_fix(
                        out,
                        cmd.id(),
                        2314,
                        "In Bats, ! will not fail the test if it is not the last command anymore. Use `run ! ` (on Bats >= 1.5.0) instead.",
                        fix_with(vec![replace_start(params, cmd.id(), 0, "run ")]),
                    );
                } else {
                    err_with_fix(
                        out,
                        cmd.id(),
                        2314,
                        "In Bats, ! does not cause a test failure. Use 'run ! ' (on Bats >= 1.5.0) instead.",
                        fix_with(vec![replace_start(params, cmd.id(), 0, "run ")]),
                    );
                }
            }
        }
    }
}

// ===========================================================================
// Tests
// ===========================================================================

/// `couldBeOptimized`: the argument won't be re-split/globbed if inlined.
fn could_be_optimized(t: &Token) -> bool {
    match &*t.inner {
        InnerToken::T_Glob(_) | InnerToken::T_Extglob { .. } | InnerToken::T_BraceExpansion(_) => {
            false
        }
        InnerToken::T_NormalWord(l) | InnerToken::T_DoubleQuoted(l) => {
            l.iter().all(could_be_optimized)
        }
        _ => true,
    }
}

/// `containsSetE`: `params.has_set_e` (which covers `set -e` commands) plus the
/// shebang check `T_Script _ (T_Literal _ str) _ -> str matches "[[:space:]]-[^-]*e"`
/// that the shared `contains_set_e` does not perform.
fn has_set_e(params: &Parameters) -> bool {
    if params.has_set_e {
        return true;
    }
    let mut node = &params.root;
    while let InnerToken::T_Annotation { token, .. } = &*node.inner {
        node = token;
    }
    if let InnerToken::T_Script { shebang, .. } = &*node.inner {
        if let InnerToken::T_Literal(s) = &*shebang.inner {
            return shebang_flag_matches(s, b'e');
        }
    }
    false
}

/// Matches the regex `[[:space:]]-[^-]*<c>`: whitespace, `-`, non-dashes, then `c`.
fn shebang_flag_matches(s: &str, c: u8) -> bool {
    let b = s.as_bytes();
    let mut i = 0;
    while i < b.len() {
        if b[i].is_ascii_whitespace() && i + 1 < b.len() && b[i + 1] == b'-' {
            let mut j = i + 2;
            while j < b.len() && b[j] != b'-' {
                if b[j] == c {
                    return true;
                }
                j += 1;
            }
        }
        i += 1;
    }
    false
}

fn is_cd_revert(t: &Token) -> bool {
    let o = oversimplify(t);
    o.len() == 2 && (o[1] == ".." || o[1] == "-")
}

fn cd_candidate(t: &Token) -> Option<&Token> {
    match &*t.inner {
        InnerToken::T_Annotation { token, .. } => cd_candidate(token),
        InnerToken::T_Pipeline { commands, .. } if commands.len() == 1 => {
            if is_command(&commands[0], "cd") {
                Some(&commands[0])
            } else {
                None
            }
        }
        _ => None,
    }
}

fn find_cd_pair(list: &[&Token]) -> Option<Id> {
    let mut i = 0;
    while i + 1 < list.len() {
        let a = list[i];
        let b = list[i + 1];
        if is_cd_revert(b) && !is_cd_revert(a) {
            return Some(b.id());
        }
        i += 1;
    }
    None
}

/// `^/*((\.|\.\.)/+)*(\.|\.\.)?$`
fn matches_safe_dir(s: &str) -> bool {
    let b = s.as_bytes();
    let mut i = 0;
    while i < b.len() && b[i] == b'/' {
        i += 1;
    }
    loop {
        let start = i;
        if i < b.len() && b[i] == b'.' {
            i += 1;
            if i < b.len() && b[i] == b'.' {
                i += 1;
            }
        } else {
            break;
        }
        if i < b.len() && b[i] == b'/' {
            while i < b.len() && b[i] == b'/' {
                i += 1;
            }
        } else {
            i = start;
            break;
        }
    }
    if i < b.len() && b[i] == b'.' {
        i += 1;
        if i < b.len() && b[i] == b'.' {
            i += 1;
        }
    }
    i == b.len()
}

fn is_safe_dir(t: &Token) -> bool {
    let o = oversimplify(t);
    o.len() == 2 && matches_safe_dir(&o[1])
}

fn is_condition_path(params: &Parameters, t: &Token) -> bool {
    let mut child = t;
    loop {
        if matches!(&*child.inner, InnerToken::T_BatsTest { .. }) {
            return true;
        }
        let parent = match params.parent(child) {
            Some(p) => p,
            None => return false,
        };
        if condition_children(parent)
            .iter()
            .any(|c| c.id() == child.id())
        {
            return true;
        }
        child = parent;
    }
}

fn is_last_command_in_function(params: &Parameters, t: &Token) -> bool {
    let mut cur = t;
    while let Some(c) = params.parent(cur) {
        if let Some(bg) = params.parent(c) {
            if let InnerToken::T_BraceGroup(commands) = &*bg.inner {
                // In Haskell a function body is a bare T_BraceGroup; this port
                // wraps every compound command in a T_Redirecting, so the brace
                // group's parent may be that wrapper before the T_Function.
                let mut p = params.parent(bg);
                if let Some(rp) = p {
                    if matches!(&*rp.inner, InnerToken::T_Redirecting { .. }) {
                        p = params.parent(rp);
                    }
                }
                if let Some(func) = p {
                    if matches!(&*func.inner, InnerToken::T_Function { .. }) {
                        if let Some(last) = commands.last() {
                            if last.id() == c.id() {
                                return true;
                            }
                        }
                    }
                }
            }
        }
        cur = c;
    }
    false
}

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

fn has_execfail(params: &Parameters) -> bool {
    params.shell == Shell::Bash && is_option_set("execfail", &params.root)
}

fn spurious_cleanup(t: &Token) -> bool {
    if let InnerToken::T_Pipeline { commands, .. } = &*t.inner {
        if commands.len() == 1 {
            let cmd = &commands[0];
            let is_match = get_command_name(cmd).is_some_and(|name| {
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
                    && ast_lib::get_literal_string(&words[0]).as_deref() == Some("exec")
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
        s.push_str(&ast_lib::get_literal_string_ext(p, &fb).unwrap_or_default());
    }
    crate::cfg::is_variable_name(&s)
}

fn shell_lower(s: Shell) -> &'static str {
    match s {
        Shell::Ksh => "ksh",
        Shell::Sh => "sh",
        Shell::Bash => "bash",
        Shell::Dash => "dash",
        Shell::BusyboxSh => "busyboxsh",
    }
}

/// `shellSupport t` -> (name, supported shells).
fn shell_support(t: &Token) -> (&'static str, Vec<Shell>) {
    match &*t.inner {
        InnerToken::T_CaseExpression { cases, .. } => {
            let seps: Vec<CaseType> = cases.iter().map(|(a, _, _)| *a).collect();
            if seps.contains(&CaseType::CaseContinue) {
                ("cases with ;;&", vec![Shell::Bash])
            } else if seps.contains(&CaseType::CaseFallThrough) {
                ("cases with ;&", vec![Shell::Bash, Shell::Ksh])
            } else {
                ("", vec![])
            }
        }
        InnerToken::T_DollarBraceCommandExpansion { .. } => {
            ("${ ..; } command expansion", vec![Shell::Bash, Shell::Ksh])
        }
        _ => ("", vec![]),
    }
}

fn trailing_symbol_format(x: char) -> String {
    match x {
        ' ' => "space".to_string(),
        '\'' => "apostrophe".to_string(),
        '"' => "doublequote".to_string(),
        _ => format!("'{}'", x),
    }
}

/// Basename of a simple command's command word (first word), if literal.
fn command_basename(words: &[Token]) -> Option<String> {
    let first = words.first()?;
    let s = ast_lib::get_literal_string(first)?;
    Some(s.rsplit('/').next().unwrap_or(&s).to_string())
}

#[cfg(test)]
#[allow(non_snake_case)]
mod tests {
    use super::*;
    use crate::test_support::*;

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
    fn prop_checkFlagAsCommand1() {
        assert!(emits(check_flag_as_command, "-e file"));
    }

    #[test]
    fn prop_checkFlagAsCommand2() {
        assert!(emits(check_flag_as_command, "foo\n  --bar=baz"));
    }

    #[test]
    fn prop_checkFlagAsCommand3() {
        assert!(!emits(check_flag_as_command, "'--myexec--' args"));
    }

    #[test]
    fn prop_checkFlagAsCommand4() {
        assert!(!emits(check_flag_as_command, "var=cmd --arg"));
    }

    // SC2283 — spaces around =

    // SC2288 — trailing symbol
    // Fully-literal guard: parser-gap fallbacks with expansions/globs must not fire.

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
    fn prop_checkLonelyDotDash1() {
        assert!(node_emits(check_lonely_dot_dash, "./ file"));
    }

    #[test]
    fn prop_checkLonelyDotDash2() {
        assert!(!node_emits(check_lonely_dot_dash, "./file"));
    }

    // ---- SC2084/2091/2092 checkSpuriousExpansion ----

    #[test]
    fn prop_checkFindExec1() {
        assert!(emits(check_find_exec, "find / -name '*.php' -exec rm {};"));
    }

    #[test]
    fn prop_checkFindExec2() {
        assert!(emits(check_find_exec, "find / -exec touch {} && ls {} \\;"));
    }

    #[test]
    fn prop_checkFindExec3() {
        assert!(emits(
            check_find_exec,
            "find / -execdir cat {} | grep lol +"
        ));
    }

    #[test]
    fn prop_checkFindExec4() {
        assert!(!emits(
            check_find_exec,
            "find / -name '*.php' -exec foo {} +"
        ));
    }

    #[test]
    fn prop_checkFindExec5() {
        assert!(!emits(
            check_find_exec,
            "find / -execdir bash -c 'a && b' \\;"
        ));
    }

    #[test]
    fn prop_checkFindExec6() {
        assert!(emits(
            check_find_exec,
            "find / -type d -execdir rm *.jpg \\;"
        ));
    }

    // ---- checkLoopKeywordScope ----

    #[test]
    fn prop_checkUnsupported3() {
        assert!(emits(
            check_unsupported,
            "#!/bin/sh\ncase foo in bar) baz ;& esac"
        ));
    }

    #[test]
    fn prop_checkUnsupported4() {
        assert!(emits(
            check_unsupported,
            "#!/bin/ksh\ncase foo in bar) baz ;;& esac"
        ));
    }

    #[test]
    fn prop_checkUnsupported5() {
        assert!(!emits(check_unsupported, "#!/bin/bash\necho \"${ ls; }\""));
    }

    #[test]
    fn prop_checkUnsupported6() {
        assert!(emits(check_unsupported, "#!/bin/ash\necho \"${ ls; }\""));
    }

    // ---- checkSuspiciousIFS ----

    #[test]
    fn prop_checkCpLegacyR1() {
        assert!(emits(check_cp_legacy_r, "cp -r foo bar"));
    }

    #[test]
    fn prop_checkCpLegacyR2() {
        assert!(!emits(check_cp_legacy_r, "cp -R foo bar"));
    }

    // ---- checkLoopVariableReassignment ----

    #[test]
    fn prop_checkCommandWithTrailingSymbol1() {
        assert!(emits(check_command_with_trailing_symbol, "/"));
    }

    #[test]
    fn prop_checkCommandWithTrailingSymbol2() {
        assert!(emits(check_command_with_trailing_symbol, "/foo/ bar/baz"));
    }

    #[test]
    fn prop_checkCommandWithTrailingSymbol3() {
        assert!(emits(check_command_with_trailing_symbol, "/"));
    }

    #[test]
    fn prop_checkCommandWithTrailingSymbol4() {
        assert!(!emits(check_command_with_trailing_symbol, "/*"));
    }

    #[test]
    fn prop_checkCommandWithTrailingSymbol5() {
        assert!(!emits(check_command_with_trailing_symbol, "$foo/$bar"));
    }

    #[test]
    fn prop_checkCommandWithTrailingSymbol6() {
        assert!(emits(check_command_with_trailing_symbol, "foo, bar"));
    }

    #[test]
    fn prop_checkCommandWithTrailingSymbol7() {
        assert!(!emits(check_command_with_trailing_symbol, ". foo.sh"));
    }

    #[test]
    fn prop_checkCommandWithTrailingSymbol8() {
        assert!(!emits(check_command_with_trailing_symbol, ": foo"));
    }

    #[test]
    fn prop_checkCommandWithTrailingSymbol9() {
        assert!(!emits(
            check_command_with_trailing_symbol,
            "/usr/bin/python[23] file.py"
        ));
    }

    #[test]
    fn prop_sc2287_registered() {
        assert!(emits_code(check_command_with_trailing_symbol, "/", 2287));
    }

    // ---- checkBatsTestDoesNotUseNegation ----

    #[test]
    fn prop_checkBatsTestDoesNotUseNegation1() {
        assert!(emits(
            check_bats_test_does_not_use_negation,
            "#!/usr/bin/env/bats\n@test \"name\" { ! true;  false; }"
        ));
    }

    #[test]
    fn prop_checkBatsTestDoesNotUseNegation2() {
        assert!(emits(
            check_bats_test_does_not_use_negation,
            "#!/usr/bin/env/bats\n@test \"name\" { ! [[ -e test ]]; false; }"
        ));
    }

    #[test]
    fn prop_checkBatsTestDoesNotUseNegation3() {
        assert!(emits(
            check_bats_test_does_not_use_negation,
            "#!/usr/bin/env/bats\n@test \"name\" { ! [ -e test ]; false; }"
        ));
    }

    #[test]
    fn prop_checkBatsTestDoesNotUseNegation4() {
        assert!(!emits(
            check_bats_test_does_not_use_negation,
            "#!/usr/bin/env/bats\n@test \"name\" { run ! true; }"
        ));
    }

    #[test]
    fn prop_checkBatsTestDoesNotUseNegation5() {
        assert!(!emits(
            check_bats_test_does_not_use_negation,
            "#!/usr/bin/env/bats\n@test \"name\" { ! [[ -e test ]] || false; }"
        ));
    }

    #[test]
    fn prop_checkBatsTestDoesNotUseNegation6() {
        assert!(!emits(
            check_bats_test_does_not_use_negation,
            "#!/usr/bin/env/bats\n@test \"name\" { ! [ -e test ] || false; }"
        ));
    }

    #[test]
    fn prop_checkBatsTestDoesNotUseNegation7() {
        assert_eq!(
            codes(
                check_bats_test_does_not_use_negation,
                "#!/usr/bin/env/bats\n@test \"name\" { ! true; }"
            ),
            vec![2314]
        );
    }

    #[test]
    fn prop_checkBatsTestDoesNotUseNegation8() {
        assert_eq!(
            codes(
                check_bats_test_does_not_use_negation,
                "#!/usr/bin/env/bats\n@test \"name\" { ! [[ -e test ]]; }"
            ),
            vec![2315]
        );
    }

    #[test]
    fn prop_checkBatsTestDoesNotUseNegation9() {
        assert_eq!(
            codes(
                check_bats_test_does_not_use_negation,
                "#!/usr/bin/env/bats\n@test \"name\" { ! [ -e test ]; }"
            ),
            vec![2315]
        );
    }
}
