//! Loop checks from `ShellCheck.Analytics`.
use crate::analyzer_lib::arguments;
use crate::analyzer_lib::get_all_flags;
use crate::analyzer_lib::get_command_name;
use crate::analyzer_lib::is_command;
use crate::analyzer_lib::is_unqualified_command;
use crate::analyzer_lib::*;
use crate::ast::*;

use crate::ast_lib;
use crate::ast_lib::get_literal_string;
use crate::ast_lib::is_function;
use crate::ast_lib::is_glob;
use crate::ast_lib::oversimplify;
use crate::ast_lib::{is_quoteable_expansion, will_split};
use crate::cfg::get_gnu_opts;
use crate::cfg::get_unquoted_literal;
use crate::cfg::may_become_multiple_args;
use crate::data::FLAGS_FOR_READ;
use crate::interface::Fix;

pub(super) fn check_for_in_quoted(params: &Parameters, t: &Token, out: &mut Out) {
    let InnerToken::T_ForIn { items, .. } = &*t.inner else {
        return;
    };

    // Equation 1: [T_NormalWord [word@(T_DoubleQuoted id list)]]
    if items.len() == 1 {
        if let InnerToken::T_NormalWord(nw) = &*items[0].inner {
            if nw.len() == 1 {
                if let InnerToken::T_DoubleQuoted(list) = &*nw[0].inner {
                    let word = &nw[0];
                    let guard1 = (list.iter().any(will_split) && !may_become_multiple_args(word))
                        || ast_lib::get_literal_string(word)
                            .map(|s| would_have_been_glob(&s))
                            .unwrap_or(false);
                    if guard1 {
                        err(
                            out,
                            word.id(),
                            2066,
                            "Since you double quoted this, it will not word split, and the loop will only run once.",
                        );
                        return;
                    }
                }
            }
        }
    }

    // Equation 2: [T_NormalWord [T_SingleQuoted id _]]
    if items.len() == 1 {
        if let InnerToken::T_NormalWord(nw) = &*items[0].inner {
            if nw.len() == 1 {
                if let InnerToken::T_SingleQuoted(_) = &*nw[0].inner {
                    warn(
                        out,
                        nw[0].id(),
                        2041,
                        "This is a literal string. To run as a command, use $(..) instead of '..' . ",
                    );
                    return;
                }
            }
        }
    }

    // Equation 3: [single]
    if items.len() == 1 {
        let single = &items[0];
        if get_unquoted_literal(single)
            .map(|s| s.contains(','))
            .unwrap_or(false)
        {
            warn(
                out,
                single.id(),
                2042,
                "Use spaces, not commas, to separate loop elements.",
            );
            return;
        }
        if !(will_split(single) || may_become_multiple_args(single)) {
            warn(
                out,
                single.id(),
                2043,
                "This loop will only ever run once. Bad quoting or missing glob/expansion?",
            );
            return;
        }
        // Guards failed: fall through to Equation 4 over [single].
    }

    // Equation 4: multiple (or a single item that fell through) -> SC2258
    for arg in items {
        if let Some(suffix) = crate::ast_lib::get_trailing_unquoted_literal(arg) {
            if let Some(string) = ast_lib::get_literal_string(suffix) {
                if string.ends_with(',') {
                    warn_with_fix(
                        out,
                        arg.id(),
                        2258,
                        "The trailing comma is part of the value, not a separator. Delete or quote it.",
                        fix_with(vec![replace_end(params, suffix.id(), 1, "")]),
                    );
                }
            }
        }
    }
}

pub(super) fn check_for_in_ls(_params: &Parameters, t: &Token, out: &mut Out) {
    if let InnerToken::T_ForIn { items, .. } = &*t.inner {
        if items.len() != 1 {
            return;
        }
        if let InnerToken::T_NormalWord(parts) = &*items[0].inner {
            if parts.len() != 1 {
                return;
            }
            match &*parts[0].inner {
                InnerToken::T_DollarExpansion(cmds) if cmds.len() == 1 => {
                    check_flls(out, parts[0].id(), &cmds[0]);
                }
                InnerToken::T_Backticked(cmds) if cmds.len() == 1 => {
                    check_flls(out, parts[0].id(), &cmds[0]);
                }
                _ => {}
            }
        }
    }
}

pub(super) fn check_for_in_cat(_params: &Parameters, t: &Token, out: &mut Out) {
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

pub(super) fn check_while_read_pitfalls(params: &Parameters, t: &Token, out: &mut Out) {
    let (while_id, command, contents) = match &*t.inner {
        InnerToken::T_WhileExpression { condition, body } if condition.len() == 1 => {
            (t.id(), &condition[0], body)
        }
        _ => return,
    };
    if !is_stdin_read_command(command) {
        return;
    }
    for c in contents {
        check_muncher(params, while_id, c, out);
    }
}

pub(super) fn check_loop_keyword_scope(params: &Parameters, t: &Token, out: &mut Out) {
    let Some(name) = get_command_name(t) else {
        return;
    };
    if name != "continue" && name != "break" {
        return;
    }
    let full_path = get_path(params, t);
    // relevant = isLoop || isFunction || subshellType isJust
    let path: Vec<&Token> = full_path
        .iter()
        .filter(|x| is_loop(x) || is_function(x) || subshell_type(params, x).is_some())
        .collect();

    if path.iter().any(|x| is_loop(x)) {
        // map subshellType (filter (not . isFunction) path); if head is Just -> 2106
        let filtered: Vec<&&Token> = path.iter().filter(|x| !is_function(x)).collect();
        if let Some(first) = filtered.first() {
            if let Some(str) = subshell_type(params, first) {
                warn(
                    out,
                    t.id(),
                    2106,
                    &format!("This only exits the subshell caused by the {}.", str),
                );
            }
        }
    } else {
        match path.first() {
            Some(h) if is_function(h) => {
                err(
                    out,
                    t.id(),
                    2104,
                    &format!("In functions, use return instead of {}.", name),
                );
            }
            _ => {
                err(
                    out,
                    t.id(),
                    2105,
                    &format!("{} is only valid in loops.", name),
                );
            }
        }
    }
}

pub(super) fn check_read_without_r(_params: &Parameters, t: &Token, out: &mut Out) {
    if !matches!(&*t.inner, InnerToken::T_SimpleCommand { .. }) {
        return;
    }
    if !is_unqualified_command(t, "read") {
        return;
    }
    let flags = get_all_flags(t);
    if flags.iter().any(|(_, f)| f == "r") {
        return;
    }
    // has_t0: getGnuOpts flagsForRead (arguments t) has "t" mapped to literal "0".
    let has_t0 = get_gnu_opts(FLAGS_FOR_READ, arguments(t))
        .and_then(|parsed| {
            parsed
                .iter()
                .find(|(name, _)| name == "t")
                .and_then(|(_, (_, arg))| get_literal_string(arg))
        })
        .as_deref()
        == Some("0");
    if has_t0 {
        return;
    }
    info(
        out,
        get_command_token_or_this(t).id(),
        2162,
        "read without -r will mangle backslashes.",
    );
}

pub(super) fn check_loop_variable_reassignment(params: &Parameters, token: &Token, out: &mut Out) {
    if !matches!(
        &*token.inner,
        InnerToken::T_ForIn { .. } | InnerToken::T_ForArithmetic { .. }
    ) {
        return;
    }
    let Some(str) = loop_variable(token) else {
        return;
    };
    if str == "_" {
        return;
    }
    let full = get_path(params, token);
    // NE.tail: ancestors
    let path = &full[1..];
    if let Some(next) = path
        .iter()
        .find(|x| loop_variable(x).as_deref() == Some(str.as_str()))
    {
        warn(
            out,
            token.id(),
            2165,
            "This nested loop overrides the index variable of its parent.",
        );
        warn(
            out,
            next.id(),
            2167,
            "This parent loop has its index variable overridden.",
        );
    }
}

pub(super) fn check_for_loop_glob_variables(_params: &Parameters, t: &Token, out: &mut Out) {
    let InnerToken::T_ForIn { items, .. } = &*t.inner else {
        return;
    };
    for word in items {
        if let InnerToken::T_NormalWord(parts) = &*word.inner {
            if parts.iter().any(is_glob) {
                for p in parts.iter().filter(|x| is_quoteable_expansion(x)) {
                    info(
                        out,
                        p.id(),
                        2231,
                        "Quote expansions in this for loop glob to prevent wordsplitting, e.g. \"$dir\"/*.txt .",
                    );
                }
            }
        }
    }
}

fn check_flls(out: &mut Out, id: Id, x: &Token) {
    let words = oversimplify(x);
    let head = match words.first() {
        Some(h) => h.as_str(),
        None => return,
    };
    match head {
        "ls" => {
            let rest = &words[1..];
            if rest.iter().any(|w| w.starts_with('-')) {
                warn(
                    out,
                    id,
                    2045,
                    "Iterating over ls output is fragile. Use globs.",
                );
            } else {
                err(
                    out,
                    id,
                    2045,
                    "Iterating over ls output is fragile. Use globs.",
                );
            }
        }
        "find" => {
            warn(
                out,
                id,
                2044,
                "For loops over find output are fragile. Use find -exec or a while read loop.",
            );
        }
        _ => {}
    }
}

#[derive(Clone, Copy)]
enum MunchCheck {
    HasFlag,
    HasArgument,
    Never,
}

#[derive(Clone, Copy)]
enum MunchFix {
    AddFlag,
    AddRedirect,
}

/// `munchers` map: command basename -> (check, fix, flag/redirect string).
fn muncher(name: &str) -> Option<(MunchCheck, MunchFix, &'static str)> {
    match name {
        "ssh" => Some((MunchCheck::HasFlag, MunchFix::AddFlag, "-n")),
        "ffmpeg" => Some((MunchCheck::HasArgument, MunchFix::AddFlag, "-nostdin")),
        "mplayer" => Some((
            MunchCheck::HasArgument,
            MunchFix::AddFlag,
            "-noconsolecontrols",
        )),
        "HandBrakeCLI" => Some((MunchCheck::Never, MunchFix::AddRedirect, "< /dev/null")),
        _ => None,
    }
}

fn is_stdin_read_command(t: &Token) -> bool {
    if let InnerToken::T_Pipeline { commands, .. } = &*t.inner {
        if commands.len() == 1 {
            if let InnerToken::T_Redirecting { redirs, cmd } = &*commands[0].inner {
                let plaintext = oversimplify(cmd);
                return plaintext.first().map(|s| s.as_str()) == Some("read")
                    && !plaintext.iter().any(|s| s == "-u")
                    && !redirs.iter().any(stdin_redirect);
            }
        }
    }
    false
}

fn stdin_redirect(r: &Token) -> bool {
    if let InnerToken::T_FdRedirect { fd, target } = &*r.inner {
        if fd == "0" {
            return true;
        }
        if fd.is_empty() {
            return match &*target.inner {
                InnerToken::T_IoFile { op, .. } => matches!(&*op.inner, InnerToken::T_Less),
                InnerToken::T_IoDuplicate { op, .. } => matches!(&*op.inner, InnerToken::T_LESSAND),
                InnerToken::T_HereString(_) => true,
                InnerToken::T_HereDoc { .. } => true,
                _ => false,
            };
        }
    }
    false
}

fn check_muncher(params: &Parameters, while_id: Id, t: &Token, out: &mut Out) {
    match &*t.inner {
        InnerToken::T_Pipeline { commands, .. } if !commands.is_empty() => {
            if let InnerToken::T_Redirecting { redirs, cmd } = &*commands[0].inner {
                // Check command substitutions regardless of the command.
                if let InnerToken::T_SimpleCommand { assignments, words } = &*cmd.inner {
                    for w in assignments.iter().chain(words.iter()) {
                        for part in get_words(w) {
                            for seq in get_command_sequences(part) {
                                for c in &seq {
                                    check_muncher(params, while_id, c, out);
                                }
                            }
                        }
                    }
                }

                if !redirs.iter().any(stdin_redirect) {
                    // Recurse into ifs/loops/groups/etc if this doesn't redirect.
                    for seq in get_command_sequences(cmd) {
                        for c in &seq {
                            check_muncher(params, while_id, c, out);
                        }
                    }

                    // Check the actual command.
                    if let Some(name) = get_command_basename(cmd) {
                        if let Some((check, fixkind, flag)) = muncher(&name) {
                            if !run_munch_check(check, flag, cmd) {
                                info(
                                    out,
                                    while_id,
                                    2095,
                                    &format!(
                                        "{} may swallow stdin, preventing this loop from working properly.",
                                        name
                                    ),
                                );
                                let fix = build_munch_fix(params, fixkind, flag, cmd);
                                warn_with_fix(
                                    out,
                                    cmd.id(),
                                    2095,
                                    &format!(
                                        "Use {} {} to prevent {} from swallowing stdin.",
                                        name, flag, name
                                    ),
                                    fix,
                                );
                            }
                        }
                    }
                }
            }
        }
        InnerToken::T_Backgrounded(inner) => check_muncher(params, while_id, inner, out),
        _ => {}
    }
}

fn run_munch_check(kind: MunchCheck, flag: &str, cmd: &Token) -> bool {
    match kind {
        // hasFlag ('-':flag) = elem flag . map snd . getAllFlags
        MunchCheck::HasFlag => {
            let f = flag.strip_prefix('-').unwrap_or(flag);
            get_all_flags(cmd).iter().any(|(_, s)| s == f)
        }
        // hasArgument arg = elem arg . mapMaybe getLiteralString . fromJust . getCommandArgv
        MunchCheck::HasArgument => get_command_argv(cmd)
            .map(|argv| {
                argv.iter()
                    .filter_map(ast_lib::get_literal_string)
                    .any(|s| s == flag)
            })
            .unwrap_or(false),
        MunchCheck::Never => false,
    }
}

fn build_munch_fix(params: &Parameters, fixkind: MunchFix, flag: &str, cmd: &Token) -> Fix {
    match fixkind {
        // addFlag: replaceEnd (getId $ getCommandTokenOrThis cmd) params 0 (' ':string)
        MunchFix::AddFlag => {
            let tok = get_command_token_or_this(cmd);
            fix_with(vec![replace_end(
                params,
                tok.id(),
                0,
                &format!(" {}", flag),
            )])
        }
        // addRedirect: replaceEnd (getId cmd) params 0 (' ':string)
        MunchFix::AddRedirect => fix_with(vec![replace_end(
            params,
            cmd.id(),
            0,
            &format!(" {}", flag),
        )]),
    }
}

/// `getWords`: for a T_Assignment, its value's word parts; else its own.
fn get_words(t: &Token) -> Vec<&Token> {
    match &*t.inner {
        InnerToken::T_Assignment { value, .. } => ast_lib::get_word_parts(value),
        _ => ast_lib::get_word_parts(t),
    }
}

/// `getCommandArgv t`: the name+arguments of a command.
fn get_command_argv(t: &Token) -> Option<Vec<Token>> {
    let cmd = get_command(t)?;
    if let InnerToken::T_SimpleCommand { words, .. } = &*cmd.inner {
        if !words.is_empty() {
            return Some(words.clone());
        }
    }
    None
}

/// `getCommandSequences`: command lists inside compound tokens.
fn get_command_sequences(t: &Token) -> Vec<Vec<Token>> {
    use InnerToken::*;
    match &*t.inner {
        T_Script { commands, .. } => vec![commands.clone()],
        T_BraceGroup(cmds) => vec![cmds.clone()],
        T_Subshell(cmds) => vec![cmds.clone()],
        T_WhileExpression { condition, body } => vec![condition.clone(), body.clone()],
        T_UntilExpression { condition, body } => vec![condition.clone(), body.clone()],
        T_ForIn { body, .. } => vec![body.clone()],
        T_ForArithmetic { body, .. } => vec![body.clone()],
        T_IfExpression { clauses, elses } => {
            let mut out: Vec<Vec<Token>> = Vec::new();
            for (a, b) in clauses {
                out.push(a.clone());
                out.push(b.clone());
            }
            out.push(elses.clone());
            out
        }
        T_Annotation { token, .. } => get_command_sequences(token),
        T_DollarExpansion(cmds) => vec![cmds.clone()],
        T_DollarBraceCommandExpansion { list, .. } => vec![list.clone()],
        T_Backticked(cmds) => vec![cmds.clone()],
        _ => vec![],
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

fn is_loop(t: &Token) -> bool {
    matches!(
        &*t.inner,
        InnerToken::T_WhileExpression { .. }
            | InnerToken::T_UntilExpression { .. }
            | InnerToken::T_ForIn { .. }
            | InnerToken::T_ForArithmetic { .. }
            | InnerToken::T_SelectIn { .. }
    )
}

/// `wouldHaveBeenGlob s = '*' `elem` s`.
fn would_have_been_glob(s: &str) -> bool {
    s.contains('*')
}

/// `leadType`/`subshellType` for a token (returns the subshell scope string).
fn subshell_type(params: &Parameters, t: &Token) -> Option<String> {
    use InnerToken::*;
    let s = |x: &str| Some(x.to_string());
    match &*t.inner {
        T_DollarExpansion(_) => s("$(..) expansion"),
        T_Backticked(_) => s("`..` expansion"),
        T_Backgrounded(_) => s("backgrounding &"),
        T_Subshell(_) => s("(..) group"),
        T_BatsTest { .. } => s("@bats test"),
        T_CoProcBody(_) => s("coproc"),
        T_Redirecting { .. } => {
            if causes_subshell(params, t) {
                s("pipeline")
            } else {
                None
            }
        }
        _ => None,
    }
}

fn causes_subshell(params: &Parameters, t: &Token) -> bool {
    let Some(parent) = params.parent(t) else {
        return false;
    };
    let InnerToken::T_Pipeline { commands, .. } = &*parent.inner else {
        return false;
    };
    if commands.len() >= 2 {
        !params.has_lastpipe || commands.last().map(|x| x.id()) != Some(t.id())
    } else {
        false
    }
}

fn loop_variable(t: &Token) -> Option<String> {
    match &*t.inner {
        InnerToken::T_ForIn { var, .. } => Some(var.clone()),
        InnerToken::T_ForArithmetic { init, .. } => {
            // TA_Sequence [TA_Assignment "=" (TA_Variable var _) _]
            if let InnerToken::TA_Sequence(seq) = &*init.inner {
                if seq.len() == 1 {
                    if let InnerToken::TA_Assignment { op, lhs, .. } = &*seq[0].inner {
                        if op == "=" {
                            if let InnerToken::TA_Variable { name, .. } = &*lhs.inner {
                                return Some(name.clone());
                            }
                        }
                    }
                }
            }
            None
        }
        _ => None,
    }
}

#[cfg(test)]
#[allow(non_snake_case)]
mod tests {
    use super::*;
    use crate::test_support::*;

    #[test]
    fn prop_checkWhileReadPitfalls1() {
        assert!(node_emits(
            check_while_read_pitfalls,
            "while read foo; do ssh $foo uptime; done < file"
        ));
    }

    #[test]
    fn prop_checkWhileReadPitfalls2() {
        assert!(!node_emits(
            check_while_read_pitfalls,
            "while read -u 3 foo; do ssh $foo uptime; done 3< file"
        ));
    }

    #[test]
    fn prop_checkWhileReadPitfalls3() {
        assert!(!node_emits(
            check_while_read_pitfalls,
            "while true; do ssh host uptime; done"
        ));
    }

    #[test]
    fn prop_checkWhileReadPitfalls4() {
        assert!(!node_emits(
            check_while_read_pitfalls,
            "while read foo; do ssh $foo hostname < /dev/null; done"
        ));
    }

    #[test]
    fn prop_checkWhileReadPitfalls5() {
        assert!(!node_emits(
            check_while_read_pitfalls,
            "while read foo; do echo ls | ssh $foo; done"
        ));
    }

    #[test]
    fn prop_checkWhileReadPitfalls6() {
        assert!(!node_emits(
            check_while_read_pitfalls,
            "while read foo <&3; do ssh $foo; done 3< foo"
        ));
    }

    #[test]
    fn prop_checkWhileReadPitfalls7() {
        assert!(node_emits(
            check_while_read_pitfalls,
            "while read foo; do if true; then ssh $foo uptime; fi; done < file"
        ));
    }

    #[test]
    fn prop_checkWhileReadPitfalls8() {
        assert!(!node_emits(
            check_while_read_pitfalls,
            "while read foo; do ssh -n $foo uptime; done < file"
        ));
    }

    #[test]
    fn prop_checkWhileReadPitfalls9() {
        assert!(node_emits(
            check_while_read_pitfalls,
            "while read foo; do ffmpeg -i foo.mkv bar.mkv -an; done"
        ));
    }

    #[test]
    fn prop_checkWhileReadPitfalls10() {
        assert!(node_emits(
            check_while_read_pitfalls,
            "while read foo; do mplayer foo.ogv > file; done"
        ));
    }

    #[test]
    fn prop_checkWhileReadPitfalls11() {
        assert!(!node_emits(
            check_while_read_pitfalls,
            "while read foo; do mplayer foo.ogv <<< q; done"
        ));
    }

    #[test]
    fn prop_checkWhileReadPitfalls12() {
        assert!(!node_emits(
            check_while_read_pitfalls,
            "while read foo\ndo\nmplayer foo.ogv << EOF\nq\nEOF\ndone"
        ));
    }

    #[test]
    fn prop_checkWhileReadPitfalls13() {
        assert!(node_emits(
            check_while_read_pitfalls,
            "while read foo; do x=$(ssh host cmd); done"
        ));
    }

    #[test]
    fn prop_checkWhileReadPitfalls14() {
        assert!(node_emits(
            check_while_read_pitfalls,
            "while read foo; do echo $(ssh host cmd) < /dev/null; done"
        ));
    }

    #[test]
    fn prop_checkWhileReadPitfalls15() {
        assert!(node_emits(
            check_while_read_pitfalls,
            "while read foo; do ssh $foo cmd & done"
        ));
    }

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
    fn prop_checkForInQuoted() {
        assert!(emits(
            check_for_in_quoted,
            "for f in \"$(ls)\"; do echo foo; done"
        ));
    }

    #[test]
    fn prop_checkForInQuoted2() {
        assert!(!emits(
            check_for_in_quoted,
            "for f in \"$@\"; do echo foo; done"
        ));
    }

    #[test]
    fn prop_checkForInQuoted2a() {
        assert!(!emits(
            check_for_in_quoted,
            "for f in *.mp3; do echo foo; done"
        ));
    }

    #[test]
    fn prop_checkForInQuoted2b() {
        assert!(emits(
            check_for_in_quoted,
            "for f in \"*.mp3\"; do echo foo; done"
        ));
    }

    #[test]
    fn prop_checkForInQuoted3() {
        assert!(emits(
            check_for_in_quoted,
            "for f in 'find /'; do true; done"
        ));
    }

    #[test]
    fn prop_checkForInQuoted4() {
        assert!(emits(check_for_in_quoted, "for f in 1,2,3; do true; done"));
    }

    #[test]
    fn prop_checkForInQuoted4a() {
        assert!(!emits(
            check_for_in_quoted,
            "for f in foo{1,2,3}; do true; done"
        ));
    }

    #[test]
    fn prop_checkForInQuoted5() {
        assert!(emits(check_for_in_quoted, "for f in ls; do true; done"));
    }

    #[test]
    fn prop_checkForInQuoted6() {
        assert!(!emits(
            check_for_in_quoted,
            "for f in \"${!arr}\"; do true; done"
        ));
    }

    #[test]
    fn prop_checkForInQuoted7() {
        assert!(emits(
            check_for_in_quoted,
            "for f in ls, grep, mv; do true; done"
        ));
    }

    #[test]
    fn prop_checkForInQuoted8() {
        assert!(emits(
            check_for_in_quoted,
            "for f in 'ls', 'grep', 'mv'; do true; done"
        ));
    }

    #[test]
    fn prop_checkForInQuoted9() {
        assert!(!emits(
            check_for_in_quoted,
            "for f in 'ls,' 'grep,' 'mv'; do true; done"
        ));
    }

    // ---- checkFindExec ----

    #[test]
    fn prop_lks_break_toplevel() {
        assert!(emits_code(check_loop_keyword_scope, "break", 2105));
    }

    #[test]
    fn prop_lks_continue_toplevel() {
        assert!(emits_code(check_loop_keyword_scope, "continue", 2105));
    }

    #[test]
    fn prop_lks_in_function() {
        assert!(emits_code(
            check_loop_keyword_scope,
            "foo() { break; }",
            2104
        ));
    }

    #[test]
    fn prop_lks_in_loop() {
        assert!(!emits(
            check_loop_keyword_scope,
            "while true; do break; done"
        ));
    }

    #[test]
    fn prop_lks_subshell_in_loop() {
        assert!(emits_code(
            check_loop_keyword_scope,
            "while true; do ( break ); done",
            2106
        ));
    }

    // ---- checkFunctionDeclarations ----

    #[test]
    fn prop_checkLoopVariableReassignment1() {
        assert!(emits(
            check_loop_variable_reassignment,
            "for i in *; do for i in *.bar; do true; done; done"
        ));
    }

    #[test]
    fn prop_checkLoopVariableReassignment2() {
        assert!(emits(
            check_loop_variable_reassignment,
            "for i in *; do for((i=0; i<3; i++)); do true; done; done"
        ));
    }

    #[test]
    fn prop_checkLoopVariableReassignment3() {
        assert!(!emits(
            check_loop_variable_reassignment,
            "for i in *; do for j in *.bar; do true; done; done"
        ));
    }

    #[test]
    fn prop_checkLoopVariableReassignment4() {
        assert!(!emits(
            check_loop_variable_reassignment,
            "for _ in *; do for _ in *.bar; do true; done; done"
        ));
    }

    // ---- checkForLoopGlobVariables ----

    #[test]
    fn prop_checkForLoopGlobVariables1() {
        assert!(emits(
            check_for_loop_glob_variables,
            "for i in $var/*.txt; do true; done"
        ));
    }

    #[test]
    fn prop_checkForLoopGlobVariables2() {
        assert!(!emits(
            check_for_loop_glob_variables,
            "for i in \"$var\"/*.txt; do true; done"
        ));
    }

    #[test]
    fn prop_checkForLoopGlobVariables3() {
        assert!(!emits(
            check_for_loop_glob_variables,
            "for i in $var; do true; done"
        ));
    }

    // ---- checkAliasUsedInSameParsingUnit ----
}
