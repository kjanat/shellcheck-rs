//! Redirection and pipeline checks from `ShellCheck.Analytics`.
use super::common::*;
use crate::analyzer_lib::get_all_flags;
use crate::analyzer_lib::get_closest_command;
use crate::analyzer_lib::get_command_basename;
use crate::analyzer_lib::*;
use crate::ast::*;
use crate::ast_lib;
use crate::ast_lib::get_command_sequences;
use crate::ast_lib::is_assignment;
use crate::ast_lib::is_constant;
use crate::ast_lib::oversimplify;
use crate::cfg::get_unquoted_literal;
use crate::data::COMMON_COMMANDS;
use crate::interface::Shell;

pub(super) fn check_pipe_pitfalls(_params: &Parameters, t: &Token, out: &mut Out) {
    let InnerToken::T_Pipeline { commands, .. } = &*t.inner else {
        return;
    };
    let names: Vec<String> = commands
        .iter()
        .map(|c| oversimplify(c).into_iter().next().unwrap_or_default())
        .collect();

    let has_short_parameter = |args: &[String], ch: char| -> bool {
        args.iter().any(|x| x.starts_with('-') && x.contains(ch))
    };
    let has_parameter = |args: &[String], string: &str| -> bool {
        args.iter()
            .any(|x| x.trim_start_matches('-').starts_with(string))
    };

    // for ["find", "xargs"] -> SC2038
    for n in index_of_sublists(&["find", "xargs"], &names) {
        let find = &commands[n];
        let xargs = &commands[n + 1];
        let mut args = oversimplify(xargs);
        args.extend(oversimplify(find));
        let ok = has_short_parameter(&args, '0')
            || has_parameter(&args, "null")
            || has_parameter(&args, "print0")
            || has_parameter(&args, "printf");
        if !ok {
            warn(
                out,
                find.id(),
                2038,
                "Use 'find .. -print0 | xargs -0 ..' or 'find .. -exec .. +' to allow non-alphanumeric filenames.",
            );
        }
    }

    // for ["ps", "grep"] -> SC2009
    for n in index_of_sublists(&["ps", "grep"], &names) {
        let ps = &commands[n];
        let ps_flags = command_flag_strings(get_command_local(ps));
        if !ps_flags
            .iter()
            .any(|f| matches!(f.as_str(), "p" | "pid" | "q" | "quick-pid"))
        {
            info(
                out,
                ps.id(),
                2009,
                "Consider using pgrep instead of grepping ps output.",
            );
        }
    }

    // for ["grep", "wc"] -> SC2126
    for n in index_of_sublists(&["grep", "wc"], &names) {
        let grep = &commands[n];
        let wc = &commands[n + 1];
        let flags_grep = command_flag_strings(get_command_local(grep));
        let flags_wc = command_flag_strings(get_command_local(wc));
        let grep_ok = flags_grep.iter().any(|f| {
            matches!(
                f.as_str(),
                "l" | "files-with-matches"
                    | "L"
                    | "files-without-matches"
                    | "o"
                    | "only-matching"
                    | "r"
                    | "R"
                    | "recursive"
                    | "A"
                    | "after-context"
                    | "B"
                    | "before-context"
            )
        });
        let wc_ok = flags_wc.iter().any(|f| {
            matches!(
                f.as_str(),
                "m" | "chars" | "w" | "words" | "c" | "bytes" | "L" | "max-line-length"
            )
        });
        if !(grep_ok || wc_ok || flags_wc.is_empty()) {
            style(
                out,
                grep.id(),
                2126,
                "Consider using 'grep -c' instead of 'grep|wc -l'.",
            );
        }
    }

    // didLs: ls|grep (SC2010) and ls|xargs (SC2011)
    let mut did_ls = false;
    for n in index_of_sublists(&["ls", "grep"], &names) {
        let x = &commands[n];
        warn(
            out,
            get_command_token_or_this(x).id(),
            2010,
            "Don't use ls | grep. Use a glob or a for loop with a condition to allow non-alphanumeric filenames.",
        );
        did_ls = true;
    }
    for n in index_of_sublists(&["ls", "xargs"], &names) {
        let x = &commands[n];
        warn(
            out,
            get_command_token_or_this(x).id(),
            2011,
            "Use 'find .. -print0 | xargs -0 ..' or 'find .. -exec .. +' to allow non-alphanumeric filenames.",
        );
        did_ls = true;
    }

    // unless didLs: for ["ls", "?"] -> SC2012
    if !did_ls {
        for n in index_of_sublists(&["ls", "?"], &names) {
            let ls = &commands[n];
            if !has_short_parameter(&oversimplify(ls), 'N') {
                info(
                    out,
                    ls.id(),
                    2012,
                    "Use find instead of ls to better handle non-alphanumeric filenames.",
                );
            }
        }
    }
}

pub(super) fn check_stderr_redirect(params: &Parameters, redir: &Token, out: &mut Out) {
    let redirs = match &*redir.inner {
        InnerToken::T_Redirecting { redirs, .. } => redirs,
        _ => return,
    };
    if redirs.len() != 2 {
        return;
    }
    // First: T_FdRedirect id "2" (T_IoDuplicate _ (T_GREATAND _) "1")
    let first_id = match &*redirs[0].inner {
        InnerToken::T_FdRedirect { fd, target } if fd == "2" => {
            match &*target.inner {
                InnerToken::T_IoDuplicate { op, num } if num == "1" => {
                    if !matches!(&*op.inner, InnerToken::T_GREATAND) {
                        return;
                    }
                }
                _ => return,
            }
            redirs[0].id()
        }
        _ => return,
    };
    // Second: T_FdRedirect _ _ (T_IoFile _ op _) where op is > or >>
    match &*redirs[1].inner {
        InnerToken::T_FdRedirect { target, .. } => match &*target.inner {
            InnerToken::T_IoFile { op, .. } => {
                if !matches!(&*op.inner, InnerToken::T_Greater | InnerToken::T_DGREAT) {
                    return;
                }
            }
            _ => return,
        },
        _ => return,
    }

    if !is_captured(params, redir) {
        warn(
            out,
            first_id,
            2069,
            "To redirect stdout+stderr, 2>&1 must be last (or use '{ cmd > file; } 2>&1' to clarify).",
        );
    }
}

pub(super) fn check_echo_wc(_params: &Parameters, t: &Token, out: &mut Out) {
    let InnerToken::T_Pipeline { commands, .. } = &*t.inner else {
        return;
    };
    if commands.len() != 2 {
        return;
    }
    let acmd = oversimplify(&commands[0]);
    let bcmd = oversimplify(&commands[1]);
    if acmd == ["echo", "${VAR}"] && (bcmd == ["wc", "-c"] || bcmd == ["wc", "-m"]) {
        style(
            out,
            t.id(),
            2000,
            "See if you can use ${#variable} instead.",
        );
    }
}

pub(super) fn check_piped_assignment(_params: &Parameters, t: &Token, out: &mut Out) {
    let InnerToken::T_Pipeline { commands, .. } = &*t.inner else {
        return;
    };
    if commands.len() < 2 {
        return;
    }
    let InnerToken::T_Redirecting { cmd, .. } = &*commands[0].inner else {
        return;
    };
    if let InnerToken::T_SimpleCommand { assignments, words } = &*cmd.inner {
        if !assignments.is_empty() && words.is_empty() {
            warn(
                out,
                cmd.id(),
                2036,
                "If you wanted to assign the output of the pipeline, use a=$(b | c) .",
            );
        }
    }
}

pub(super) fn check_ssh_here_doc(_params: &Parameters, t: &Token, out: &mut Out) {
    if let InnerToken::T_Redirecting { redirs, cmd: _ } = &*t.inner {
        if is_command(t, "ssh") {
            for r in redirs {
                sshd_check_here_doc(r, out);
            }
        }
    }
}

pub(super) fn check_redirect_to_same(params: &Parameters, t: &Token, out: &mut Out) {
    let list = match &*t.inner {
        InnerToken::T_Pipeline { commands, .. } => commands,
        _ => return,
    };
    // getAllRedirs: files targeted by > < >> across all pipeline stages.
    let mut all_redirs: Vec<&Token> = vec![];
    for cmd in list {
        if let InnerToken::T_Redirecting { redirs, .. } = &*cmd.inner {
            for r in redirs {
                if let InnerToken::T_FdRedirect { target, .. } = &*r.inner {
                    if let InnerToken::T_IoFile { op, file } = &*target.inner {
                        if matches!(
                            &*op.inner,
                            InnerToken::T_Greater | InnerToken::T_Less | InnerToken::T_DGREAT
                        ) {
                            all_redirs.push(file);
                        }
                    }
                }
            }
        }
    }
    for l in list {
        let mut nodes: Vec<&Token> = vec![];
        all_nodes(l, &mut nodes);
        for x in &all_redirs {
            for u in &nodes {
                check_occurrences(params, x, u, out);
            }
        }
    }
}

pub(super) fn check_stderr_pipe(params: &Parameters, t: &Token, out: &mut Out) {
    if params.shell != Shell::Ksh {
        return;
    }
    if let InnerToken::T_Pipe(s) = &*t.inner {
        if s == "|&" {
            err(out, t.id(), 2118, "Ksh does not support |&. Use 2>&1 |.");
        }
    }
}

pub(super) fn check_multiple_appends(_params: &Parameters, t: &Token, out: &mut Out) {
    for list in get_command_sequences(t) {
        let targets: Vec<Option<(&Token, Id)>> = list.iter().map(get_target).collect();
        // groupWith (fmap fst): group consecutive entries by their file token
        // (structural equality, None never equal to Some).
        let mut i = 0;
        while i < targets.len() {
            let key = targets[i].map(|(f, _)| f);
            let mut j = i + 1;
            while j < targets.len() {
                let k2 = targets[j].map(|(f, _)| f);
                let same = match (key, k2) {
                    (Some(a), Some(b)) => a == b,
                    (None, None) => true,
                    _ => false,
                };
                if !same {
                    break;
                }
                j += 1;
            }
            // group is targets[i..j]; checkGroup fires when first is Just and len>=3
            if let Some((_, id)) = targets[i] {
                if j - i >= 3 {
                    style(
                        out,
                        id,
                        2129,
                        "Consider using { cmd1; cmd2; } >> file instead of individual redirects.",
                    );
                }
            }
            i = j;
        }
    }
}

pub(super) fn check_should_use_grep_q(_params: &Parameters, t: &Token, out: &mut Out) {
    let (id, bool_, token) = match &*t.inner {
        InnerToken::TC_Nullary { token, .. } => (t.id(), true, token),
        InnerToken::TC_Unary { op, token, .. } if op == "-n" => (t.id(), true, token),
        InnerToken::TC_Unary { op, token, .. } if op == "-z" => (t.id(), false, token),
        _ => return,
    };
    if let Some(name) = get_final_grep(token) {
        let op = if bool_ { "-n" } else { "-z" };
        let flip = if bool_ { "" } else { "! " };
        style(
            out,
            id,
            2143,
            &format!(
                "Use {}{} -q instead of comparing output with [ {} .. ].",
                flip, name, op
            ),
        );
    }
}

pub(super) fn check_redirected_nowhere(params: &Parameters, token: &Token, out: &mut Out) {
    if let InnerToken::T_Pipeline { commands, .. } = &*token.inner {
        if commands.len() == 1 {
            if let Some(redir) = rn_get_dangling_redirect(&commands[0]) {
                if !rn_is_in_expansion(params, token) {
                    warn(
                        out,
                        redir.id(),
                        2188,
                        "This redirection doesn't have a command. Move to its command (or use 'true' as no-op).",
                    );
                }
            }
        } else {
            for x in commands {
                if let Some(redir) = rn_get_dangling_redirect(x) {
                    err(
                        out,
                        redir.id(),
                        2189,
                        "You can't have | between this redirection and the command it should apply to.",
                    );
                }
            }
        }
    }
}

pub(super) fn check_redirection_to_number(_params: &Parameters, t: &Token, out: &mut Out) {
    if let InnerToken::T_IoFile { file, .. } = &*t.inner {
        if let Some(f) = get_unquoted_literal(file) {
            if !f.is_empty() && f.chars().all(|c| c.is_ascii_digit()) {
                warn(
                    out,
                    t.id(),
                    2210,
                    "This is a file redirection. Was it supposed to be a comparison or fd operation?",
                );
            }
        }
    }
}

/// Full checkPipeToNowhere (with warnAboutDupes / SC2261) — used by prop tests.
pub(super) fn check_pipe_to_nowhere(params: &Parameters, t: &Token, out: &mut Out) {
    ptn_impl(params, t, true, out);
}

pub(super) fn check_redirection_to_command(_params: &Parameters, t: &Token, out: &mut Out) {
    if let InnerToken::T_IoFile { file, .. } = &*t.inner {
        if let InnerToken::T_NormalWord(parts) = &*file.inner {
            if parts.len() == 1 {
                if let InnerToken::T_Literal(str) = &*parts[0].inner {
                    if COMMON_COMMANDS.contains(&str.as_str()) && str != "file" {
                        warn(
                            out,
                            file.id(),
                            2238,
                            "Redirecting to/from command name instead of file. Did you want pipes/xargs (or quote to ignore)?",
                        );
                    }
                }
            }
        }
    }
}

pub(super) fn check_expansion_with_redirection(params: &Parameters, t: &Token, out: &mut Out) {
    let list = match &*t.inner {
        InnerToken::T_DollarExpansion(l) => l,
        InnerToken::T_Backticked(l) => l,
        InnerToken::T_DollarBraceCommandExpansion { list, .. } => list,
        _ => return,
    };
    if list.len() == 1 {
        ewr_check(params, t.id(), &list[0], out);
    }
}

/// Pre-order traversal of every node in `t`'s subtree (`doAnalysis` order).
fn all_nodes<'a>(t: &'a Token, out: &mut Vec<&'a Token>) {
    out.push(t);
    for c in t.children() {
        all_nodes(c, out);
    }
}

/// `isParentOf parentMap ancestor child`: is `ancestor` on the path from `child`
/// to the root?
fn is_parent_of(params: &Parameters, ancestor: &Token, child: &Token) -> bool {
    let mut cur = Some(child);
    while let Some(node) = cur {
        if node.id() == ancestor.id() {
            return true;
        }
        cur = params.parent(node);
    }
    false
}

/// `isCaptured`: any `usesOutput` on the path from `redir` to root.
fn is_captured(params: &Parameters, redir: &Token) -> bool {
    let mut cur = Some(redir);
    while let Some(node) = cur {
        let uses = match &*node.inner {
            InnerToken::T_Pipeline { commands, .. } => {
                commands.len() > 1
                    && !commands
                        .last()
                        .map(|last| is_parent_of(params, last, redir))
                        .unwrap_or(false)
            }
            InnerToken::T_ProcSub { .. }
            | InnerToken::T_DollarExpansion(_)
            | InnerToken::T_Backticked(_) => true,
            _ => false,
        };
        if uses {
            return true;
        }
        cur = params.parent(node);
    }
    false
}

fn check_occurrences(params: &Parameters, x: &Token, u: &Token, out: &mut Out) {
    // Both must be T_NormalWord.
    if !matches!(&*x.inner, InnerToken::T_NormalWord(_))
        || !matches!(&*u.inner, InnerToken::T_NormalWord(_))
    {
        return;
    }
    if x.id() == u.id() {
        return;
    }
    if x != u {
        return;
    }
    if is_input(params, x) && is_input(params, u) {
        return;
    }
    if is_output(params, x) && is_output(params, u) {
        return;
    }
    if special(x) {
        return;
    }
    if is_harmless_command(params, x) || is_harmless_command(params, u) {
        return;
    }
    if contains_assignment(params, u) {
        return;
    }
    // addComment (note newId=u), addComment (note exceptId=x)
    info(
        out,
        u.id(),
        2094,
        "Make sure not to read and write the same file in the same pipeline.",
    );
    info(
        out,
        x.id(),
        2094,
        "Make sure not to read and write the same file in the same pipeline.",
    );
}

fn parent_io_op<'a>(params: &'a Parameters, t: &'a Token) -> Option<&'a Token> {
    let parent = params.parent(t)?;
    if let InnerToken::T_IoFile { op, .. } = &*parent.inner {
        Some(op)
    } else {
        None
    }
}

fn is_input(params: &Parameters, t: &Token) -> bool {
    match parent_io_op(params, t) {
        Some(op) => matches!(&*op.inner, InnerToken::T_Less),
        None => false,
    }
}

fn is_output(params: &Parameters, t: &Token) -> bool {
    match parent_io_op(params, t) {
        Some(op) => matches!(&*op.inner, InnerToken::T_Greater | InnerToken::T_DGREAT),
        None => false,
    }
}

fn special(t: &Token) -> bool {
    oversimplify(t).concat().starts_with("/dev/")
}

fn is_harmless_command(params: &Parameters, arg: &Token) -> bool {
    match get_closest_command(params, arg).and_then(get_command_basename) {
        Some(name) => matches!(name.as_str(), "echo" | "mapfile" | "printf" | "sponge"),
        None => false,
    }
}

fn contains_assignment(params: &Parameters, arg: &Token) -> bool {
    match get_closest_command(params, arg) {
        Some(cmd) => is_assignment(cmd),
        None => false,
    }
}

/// `getTarget`: (append-file, redirecting-id) for a command that appends (`>>`).
fn get_target(t: &Token) -> Option<(&Token, Id)> {
    match &*t.inner {
        InnerToken::T_Annotation { token, .. } => get_target(token),
        InnerToken::T_Pipeline { commands, .. } if !commands.is_empty() => {
            get_target(commands.last().unwrap())
        }
        InnerToken::T_Redirecting { redirs, .. } => {
            // file <- mapMaybe getAppend list !!! 0
            for r in redirs {
                if let InnerToken::T_FdRedirect { target, .. } = &*r.inner {
                    if let InnerToken::T_IoFile { op, file } = &*target.inner {
                        if matches!(&*op.inner, InnerToken::T_DGREAT) {
                            return Some((file, t.id()));
                        }
                    }
                }
            }
            None
        }
        _ => None,
    }
}

fn sshd_check_here_doc(r: &Token, out: &mut Out) {
    if let InnerToken::T_FdRedirect { target, .. } = &*r.inner {
        if let InnerToken::T_HereDoc {
            quoted,
            delim,
            body,
            ..
        } = &*target.inner
        {
            if *quoted == Quoted::Unquoted && !body.iter().all(is_constant) {
                warn(
                    out,
                    target.id(),
                    2087,
                    &format!(
                        "Quote '{}' to make here document expansions happen on the server side rather than on the client.",
                        delim
                    ),
                );
            }
        }
    }
}

fn rn_get_dangling_redirect(token: &Token) -> Option<&Token> {
    if let InnerToken::T_Redirecting { redirs, cmd } = &*token.inner {
        if let InnerToken::T_SimpleCommand { assignments, words } = &*cmd.inner {
            if assignments.is_empty() && words.is_empty() {
                return redirs.first();
            }
        }
    }
    None
}

fn rn_is_in_expansion(params: &Parameters, t: &Token) -> bool {
    let path = get_path(params, t);
    // NE.tail: ancestors only.
    if path.len() < 2 {
        return false;
    }
    match &*path[1].inner {
        InnerToken::T_DollarExpansion(l) if l.len() == 1 => true,
        InnerToken::T_Backticked(l) if l.len() == 1 => true,
        InnerToken::T_Annotation { .. } => rn_is_in_expansion(params, &path[1]),
        _ => false,
    }
}

#[allow(clippy::enum_variant_names)]
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

fn ptn_has_interactive_flag(cmd: &Token) -> bool {
    has_flag(cmd, "i") || has_flag(cmd, "interactive")
}

fn ptn_command_specific_exception(name: &str, cmd: &Token) -> bool {
    match name {
        "du" => get_all_flags(cmd)
            .iter()
            .any(|(_, s)| s == "exclude-from" || s == "files0-from"),
        _ if INTERACTIVE_FLAG_CMDS.contains(&name) => ptn_has_interactive_flag(cmd),
        _ => false,
    }
}

fn ptn_tree_contains(pred: fn(&Token) -> bool, t: &Token) -> bool {
    let mut found = false;
    t.visit_preorder(&mut |n| {
        if pred(n) {
            found = true;
        }
    });
    found
}

fn ptn_may_consume(t: &Token) -> bool {
    match &*t.inner {
        InnerToken::T_ProcSub { op, .. } if op == "<" => true,
        InnerToken::T_Backticked(_) => true,
        InnerToken::T_DollarExpansion(_) => true,
        _ => false,
    }
}

fn ptn_may_produce(t: &Token) -> bool {
    matches!(&*t.inner, InnerToken::T_ProcSub { op, .. } if op == ">")
}

fn ptn_get_op_id(t: &Token) -> Id {
    match &*t.inner {
        InnerToken::T_FdRedirect { target, .. } => ptn_get_op_id(target),
        InnerToken::T_IoFile { op, .. } => op.id(),
        _ => t.id(),
    }
}

fn ptn_get_default_fds(redir: &Token) -> Option<Vec<i64>> {
    match &*redir.inner {
        InnerToken::T_HereDoc { .. } => Some(vec![0]),
        InnerToken::T_HereString(_) => Some(vec![0]),
        InnerToken::T_IoFile { op, .. } => match &*op.inner {
            InnerToken::T_Less => Some(vec![0]),
            InnerToken::T_Greater => Some(vec![1]),
            InnerToken::T_DGREAT => Some(vec![1]),
            InnerToken::T_GREATAND => Some(vec![1, 2]),
            InnerToken::T_CLOBBER => Some(vec![1]),
            InnerToken::T_IoDuplicate { op: inner, num } if num == "-" => {
                ptn_get_default_fds(inner)
            }
            _ => None,
        },
        _ => None,
    }
}

fn ptn_get_redirection_fds(t: &Token) -> Option<Vec<i64>> {
    if let InnerToken::T_FdRedirect { fd, target } = &*t.inner {
        if fd.is_empty() {
            ptn_get_default_fds(target)
        } else if fd == "&" {
            Some(vec![1, 2])
        } else if fd.chars().all(|c| c.is_ascii_digit()) {
            ptn_get_default_fds(target)?;
            fd.parse::<i64>().ok().map(|n| vec![n])
        } else {
            None
        }
    } else {
        None
    }
}

fn ptn_redirects_stdin(t: &Token) -> bool {
    ptn_get_redirection_fds(t).is_some_and(|fds| fds.contains(&0))
}

fn ptn_pipe_type(t: &Token) -> PipeType {
    match &*t.inner {
        InnerToken::T_Pipe(s) if s == "|" => PipeType::StdoutPipe,
        InnerToken::T_Pipe(s) if s == "|&" => PipeType::StdoutStderrPipe,
        _ => PipeType::NoPipe,
    }
}

fn ptn_fd_str(n: i64) -> String {
    match n {
        0 => "stdin".to_string(),
        1 => "stdout".to_string(),
        2 => "stderr".to_string(),
        _ => format!("FD {}", n),
    }
}

fn ptn_impl(params: &Parameters, t: &Token, emit_dupes: bool, out: &mut Out) {
    match &*t.inner {
        InnerToken::T_Pipeline {
            separators,
            commands,
        } => {
            let pipe_types: Vec<PipeType> = separators.iter().map(ptn_pipe_type).collect();
            for (i, stage) in commands.iter().enumerate() {
                let input = if i == 0 {
                    PipeType::NoPipe
                } else {
                    pipe_types.get(i - 1).copied().unwrap_or(PipeType::NoPipe)
                };
                let output = pipe_types.get(i).copied().unwrap_or(PipeType::NoPipe);
                ptn_check_pipe(params, input, stage, output, emit_dupes, out);
            }
        }
        InnerToken::T_Redirecting { redirs, cmd } if redirs.iter().any(ptn_redirects_stdin) => {
            ptn_check_redir(params, cmd, out);
        }
        _ => {}
    }
}

fn ptn_check_pipe(
    _params: &Parameters,
    input: PipeType,
    stage: &Token,
    output: PipeType,
    emit_dupes: bool,
    out: &mut Out,
) {
    let has_consumers = ptn_tree_contains(ptn_may_consume, stage);
    let has_producers = ptn_tree_contains(ptn_may_produce, stage);

    // SC2216
    if let Some(cmd) = get_command(stage) {
        if let Some(name) = get_command_basename(cmd) {
            if NON_READING_COMMANDS.contains(&name.as_str())
                && !has_consumers
                && input != PipeType::NoPipe
                && !ptn_command_specific_exception(&name, cmd)
            {
                let suggestion = if name == "echo" {
                    "Did you want 'cat' instead?"
                } else {
                    "Wrong command or missing xargs?"
                };
                warn(
                    out,
                    cmd.id(),
                    2216,
                    &format!(
                        "Piping to '{}', a command that doesn't read stdin. {}",
                        name, suggestion
                    ),
                );
            }
        }
    }

    if let InnerToken::T_Redirecting { redirs, .. } = &*stage.inner {
        let mut all_fds: Vec<Vec<i64>> = Vec::with_capacity(redirs.len());
        for r in redirs {
            match ptn_get_redirection_fds(r) {
                Some(fds) => all_fds.push(fds),
                None => return,
            }
        }
        let mut fd_map: Vec<(i64, Vec<&Token>)> = Vec::new();
        for (fds, redir) in all_fds.iter().zip(redirs.iter()) {
            for &n in fds {
                if let Some(entry) = fd_map.iter_mut().find(|(k, _)| *k == n) {
                    entry.1.insert(0, redir);
                } else {
                    fd_map.push((n, vec![redir]));
                }
            }
        }

        // inputWarning (SC2259)
        if input != PipeType::NoPipe && !has_consumers {
            if let Some((_, list)) = fd_map.iter().find(|(k, _)| *k == 0) {
                if let Some(override_) = list.first() {
                    err(
                        out,
                        ptn_get_op_id(override_),
                        2259,
                        "This redirection overrides piped input. To use both, merge or pass filenames.",
                    );
                }
            }
        }
        // outputWarning (SC2260)
        if output == PipeType::StdoutPipe && !has_producers {
            if let Some((_, list)) = fd_map.iter().find(|(k, _)| *k == 1) {
                if let Some(override_) = list.first() {
                    err(
                        out,
                        ptn_get_op_id(override_),
                        2260,
                        "This redirection overrides the output pipe. Use 'tee' to output to both.",
                    );
                }
            }
        }
        // warnAboutDupes (SC2261)
        if emit_dupes {
            for (n, list) in &fd_map {
                if list.len() >= 2 {
                    for c in list {
                        err(
                            out,
                            ptn_get_op_id(c),
                            2261,
                            &format!(
                                "Multiple redirections compete for {}. Use cat, tee, or pass filenames instead.",
                                ptn_fd_str(*n)
                            ),
                        );
                    }
                }
            }
        }
    }
}

fn ptn_check_redir(_params: &Parameters, cmd: &Token, out: &mut Out) {
    if let Some(name) = get_command_basename(cmd) {
        if NON_READING_COMMANDS.contains(&name.as_str())
            && !ptn_tree_contains(ptn_may_consume, cmd)
            && !(INTERACTIVE_FLAG_CMDS.contains(&name.as_str()) && ptn_has_interactive_flag(cmd))
        {
            let suggestion = if name == "echo" {
                "Did you want 'cat' instead?"
            } else {
                "Bad quoting, wrong command or missing xargs?"
            };
            warn(
                out,
                cmd.id(),
                2217,
                &format!(
                    "Redirecting to '{}', a command that doesn't read stdin. {}",
                    name, suggestion
                ),
            );
        }
    }
}

fn ewr_check(params: &Parameters, capture_id: Id, pipe: &Token, out: &mut Out) {
    if let InnerToken::T_Pipeline { commands, .. } = &*pipe.inner {
        if let Some(last) = commands.last() {
            ewr_check_cmd(params, capture_id, last, out);
        }
    }
}

enum EwrStep {
    Stop,
    Emit(Id, bool),
    Continue,
}

fn ewr_walk(t: &Token) -> EwrStep {
    if let InnerToken::T_FdRedirect { fd, target } = &*t.inner {
        // T_FdRedirect _ _ (T_IoDuplicate _ _ "1") -> stop
        if let InnerToken::T_IoDuplicate { num, .. } = &*target.inner {
            if num == "1" {
                return EwrStep::Stop;
            }
        }
        // T_FdRedirect id "1" (T_IoDuplicate _ _ _) -> stop
        if fd == "1" {
            if let InnerToken::T_IoDuplicate { .. } = &*target.inner {
                return EwrStep::Stop;
            }
        }
        // T_FdRedirect id "" (T_IoDuplicate _ op _) | op in [GREATAND, Greater] -> emit True
        if fd.is_empty() {
            if let InnerToken::T_IoDuplicate { op, .. } = &*target.inner {
                if matches!(&*op.inner, InnerToken::T_GREATAND | InnerToken::T_Greater) {
                    return EwrStep::Emit(t.id(), true);
                }
            }
        }
        // T_FdRedirect id str (T_IoFile _ op file) | str in ["","1"] && op in [DGREAT, Greater]
        if fd.is_empty() || fd == "1" {
            if let InnerToken::T_IoFile { op, file } = &*target.inner {
                if matches!(&*op.inner, InnerToken::T_DGREAT | InnerToken::T_Greater) {
                    let suggest = ast_lib::get_literal_string(file).as_deref() != Some("/dev/null");
                    return EwrStep::Emit(t.id(), suggest);
                }
            }
        }
    }
    EwrStep::Continue
}

fn ewr_check_cmd(_params: &Parameters, capture_id: Id, redir_cmd: &Token, out: &mut Out) {
    if let InnerToken::T_Redirecting { redirs, .. } = &*redir_cmd.inner {
        for r in redirs {
            match ewr_walk(r) {
                EwrStep::Stop => return,
                EwrStep::Emit(redir_id, suggest_tee) => {
                    warn(
                        out,
                        capture_id,
                        2327,
                        "This command substitution will be empty because the command's output gets redirected away.",
                    );
                    let msg = if suggest_tee {
                        "This redirection takes output away from the command substitution (use tee to duplicate)."
                    } else {
                        "This redirection takes output away from the command substitution."
                    };
                    err(out, redir_id, 2328, msg);
                    return;
                }
                EwrStep::Continue => {}
            }
        }
    }
}

/// The flag strings of a command (`map snd . getAllFlags`), given a command token.
fn command_flag_strings(cmd: Option<&Token>) -> Vec<String> {
    match cmd {
        Some(c) => get_all_flags(c).into_iter().map(|(_, s)| s).collect(),
        None => vec![],
    }
}

/// `indexOfSublists sub list` with "?" wildcard matching any element.
fn index_of_sublists(sub: &[&str], list: &[String]) -> Vec<usize> {
    fn matches_at(sub: &[&str], list: &[String]) -> bool {
        match (sub.first(), list.first()) {
            (Some(&"?"), Some(_)) => matches_at(&sub[1..], &list[1..]),
            (Some(x), Some(y)) if *x == y.as_str() => matches_at(&sub[1..], &list[1..]),
            (Some(_), Some(_)) => false,
            (Some(_), None) => false,
            (None, _) => true,
        }
    }
    let mut out = vec![];
    for n in 0..list.len() {
        if matches_at(sub, &list[n..]) {
            out.push(n);
        }
    }
    out
}

const GREP_NAMES: &[&str] = &[
    "grep", "egrep", "fgrep", "bz3grep", "bzgrep", "xzgrep", "zgrep", "zipgrep", "zstdgrep",
];

fn get_pipeline(t: &Token) -> Option<Vec<Token>> {
    match &*t.inner {
        InnerToken::T_NormalWord(l) if l.len() == 1 => get_pipeline(&l[0]),
        InnerToken::T_DoubleQuoted(l) if l.len() == 1 => get_pipeline(&l[0]),
        InnerToken::T_DollarExpansion(l) if l.len() == 1 => get_pipeline(&l[0]),
        InnerToken::T_Pipeline { commands, .. } => Some(commands.clone()),
        _ => None,
    }
}

fn get_final_grep(t: &Token) -> Option<String> {
    let cmds = get_pipeline(t)?;
    if cmds.is_empty() {
        return None;
    }
    let name = get_command_basename(cmds.last().unwrap())?;
    if GREP_NAMES.contains(&name.as_str()) {
        Some(name)
    } else {
        None
    }
}

#[cfg(test)]
#[allow(non_snake_case)]
mod tests {
    use super::*;
    use crate::test_support::*;

    #[test]
    fn prop_checkSshHereDoc1() {
        assert!(node_emits(
            check_ssh_here_doc,
            "ssh host << foo\necho $PATH\nfoo"
        ));
    }

    #[test]
    fn prop_checkSshHereDoc2() {
        assert!(!node_emits(
            check_ssh_here_doc,
            "ssh host << 'foo'\necho $PATH\nfoo"
        ));
    }

    // ---- SC2097/2098 checkPrefixAssignmentReference ----

    #[test]
    fn prop_checkRedirectedNowhere1() {
        assert!(node_emits(check_redirected_nowhere, "> file"));
    }

    #[test]
    fn prop_checkRedirectedNowhere2() {
        assert!(node_emits(check_redirected_nowhere, "> file | grep foo"));
    }

    #[test]
    fn prop_checkRedirectedNowhere3() {
        assert!(node_emits(check_redirected_nowhere, "grep foo | > bar"));
    }

    #[test]
    fn prop_checkRedirectedNowhere4() {
        assert!(!node_emits(check_redirected_nowhere, "grep foo > bar"));
    }

    #[test]
    fn prop_checkRedirectedNowhere5() {
        assert!(!node_emits(
            check_redirected_nowhere,
            "foo | grep bar > baz"
        ));
    }

    #[test]
    fn prop_checkRedirectedNowhere6() {
        assert!(!node_emits(
            check_redirected_nowhere,
            "var=$(value) 2> /dev/null"
        ));
    }

    #[test]
    fn prop_checkRedirectedNowhere7() {
        assert!(!node_emits(check_redirected_nowhere, "var=$(< file)"));
    }

    #[test]
    fn prop_checkRedirectedNowhere8() {
        assert!(!node_emits(check_redirected_nowhere, "var=`< file`"));
    }

    // ---- SC2210 checkRedirectionToNumber ----

    #[test]
    fn prop_checkRedirectionToNumber1() {
        assert!(node_emits(check_redirection_to_number, "( 1 > 2 )"));
    }

    #[test]
    fn prop_checkRedirectionToNumber2() {
        assert!(node_emits(check_redirection_to_number, "foo 1>2"));
    }

    #[test]
    fn prop_checkRedirectionToNumber3() {
        assert!(!node_emits(check_redirection_to_number, "echo foo > '2'"));
    }

    #[test]
    fn prop_checkRedirectionToNumber4() {
        assert!(!node_emits(check_redirection_to_number, "foo 1>&2"));
    }

    // ---- SC2238 checkRedirectionToCommand ----

    #[test]
    fn prop_checkRedirectionToCommand1() {
        assert!(node_emits(check_redirection_to_command, "ls > rm"));
    }

    #[test]
    fn prop_checkRedirectionToCommand2() {
        assert!(!node_emits(check_redirection_to_command, "ls > 'rm'"));
    }

    #[test]
    fn prop_checkRedirectionToCommand3() {
        assert!(!node_emits(check_redirection_to_command, "ls > myfile"));
    }

    // ---- SC2216/2217/2259/2260/2261 checkPipeToNowhere (full) ----

    #[test]
    fn prop_checkPipeToNowhere1() {
        assert!(node_emits(check_pipe_to_nowhere, "foo | echo bar"));
    }

    #[test]
    fn prop_checkPipeToNowhere2() {
        assert!(node_emits(check_pipe_to_nowhere, "basename < file.txt"));
    }

    #[test]
    fn prop_checkPipeToNowhere3() {
        assert!(node_emits(check_pipe_to_nowhere, "printf 'Lol' <<< str"));
    }

    #[test]
    fn prop_checkPipeToNowhere4() {
        assert!(node_emits(
            check_pipe_to_nowhere,
            "printf 'Lol' << eof\nlol\neof\n"
        ));
    }

    #[test]
    fn prop_checkPipeToNowhere5() {
        assert!(!node_emits(check_pipe_to_nowhere, "echo foo | xargs du"));
    }

    #[test]
    fn prop_checkPipeToNowhere6() {
        assert!(!node_emits(check_pipe_to_nowhere, "ls | echo $(cat)"));
    }

    #[test]
    fn prop_checkPipeToNowhere7() {
        assert!(!node_emits(
            check_pipe_to_nowhere,
            "echo foo | var=$(cat) ls"
        ));
    }

    #[test]
    fn prop_checkPipeToNowhere9() {
        assert!(!node_emits(check_pipe_to_nowhere, "mv -i f . < /dev/stdin"));
    }

    #[test]
    fn prop_checkPipeToNowhere10() {
        assert!(node_emits(check_pipe_to_nowhere, "ls > file | grep foo"));
    }

    #[test]
    fn prop_checkPipeToNowhere11() {
        assert!(node_emits(check_pipe_to_nowhere, "ls | grep foo < file"));
    }

    #[test]
    fn prop_checkPipeToNowhere12() {
        assert!(node_emits(check_pipe_to_nowhere, "ls > foo > bar"));
    }

    #[test]
    fn prop_checkPipeToNowhere13() {
        assert!(node_emits(check_pipe_to_nowhere, "ls > foo 2> bar > baz"));
    }

    #[test]
    fn prop_checkPipeToNowhere14() {
        assert!(node_emits(check_pipe_to_nowhere, "ls > foo &> bar"));
    }

    #[test]
    fn prop_checkPipeToNowhere15() {
        assert!(!node_emits(
            check_pipe_to_nowhere,
            "ls > foo 2> bar |& grep 'No space left'"
        ));
    }

    #[test]
    fn prop_checkPipeToNowhere16() {
        assert!(!node_emits(
            check_pipe_to_nowhere,
            "echo World | cat << EOF\nhello $(cat)\nEOF\n"
        ));
    }

    #[test]
    fn prop_checkPipeToNowhere17() {
        assert!(node_emits(
            check_pipe_to_nowhere,
            "echo World | cat << 'EOF'\nhello $(cat)\nEOF\n"
        ));
    }

    #[test]
    fn prop_checkPipeToNowhere18() {
        assert!(!node_emits(
            check_pipe_to_nowhere,
            "ls 1>&3 3>&1 3>&- | wc -l"
        ));
    }

    #[test]
    fn prop_checkPipeToNowhere19() {
        assert!(!node_emits(
            check_pipe_to_nowhere,
            "find . -print0 | du --files0-from=/dev/stdin"
        ));
    }

    #[test]
    fn prop_checkPipeToNowhere20() {
        assert!(!node_emits(
            check_pipe_to_nowhere,
            "find . | du --exclude-from=/dev/fd/0"
        ));
    }

    #[test]
    fn prop_checkPipeToNowhere21() {
        assert!(!node_emits(check_pipe_to_nowhere, "yes | cp -ri foo/* bar"));
    }

    #[test]
    fn prop_checkPipeToNowhere22() {
        assert!(!node_emits(
            check_pipe_to_nowhere,
            "yes | rm --interactive *"
        ));
    }

    // ---- SC2327/2328 checkExpansionWithRedirection ----

    #[test]
    fn prop_checkExpansionWithRedirection1() {
        assert!(node_emits(
            check_expansion_with_redirection,
            "var=$(foo > bar)"
        ));
    }

    #[test]
    fn prop_checkExpansionWithRedirection2() {
        assert!(node_emits(
            check_expansion_with_redirection,
            "var=`foo 1> bar`"
        ));
    }

    #[test]
    fn prop_checkExpansionWithRedirection3() {
        assert!(node_emits(
            check_expansion_with_redirection,
            "var=${ foo >> bar; }"
        ));
    }

    #[test]
    fn prop_checkExpansionWithRedirection4() {
        assert!(node_emits(
            check_expansion_with_redirection,
            "var=$(foo | bar > baz)"
        ));
    }

    #[test]
    fn prop_checkExpansionWithRedirection5() {
        assert!(!node_emits(
            check_expansion_with_redirection,
            "stderr=$(foo 2>&1 > /dev/null)"
        ));
    }

    #[test]
    fn prop_checkExpansionWithRedirection6() {
        assert!(!node_emits(
            check_expansion_with_redirection,
            "var=$(foo; bar > baz)"
        ));
    }

    #[test]
    fn prop_checkExpansionWithRedirection7() {
        assert!(!node_emits(
            check_expansion_with_redirection,
            "var=$(foo > bar; baz)"
        ));
    }

    #[test]
    fn prop_checkExpansionWithRedirection8() {
        assert!(!node_emits(
            check_expansion_with_redirection,
            "var=$(cat <&3)"
        ));
    }

    // ---- SC2190/2191/2192 checkArrayAssignmentIndices ----

    #[test]
    fn prop_checkEchoWc3() {
        assert!(emits(check_echo_wc, "n=$(echo $foo | wc -c)"));
    }

    // ---- checkPipedAssignment ----

    #[test]
    fn prop_checkPipedAssignment1() {
        assert!(emits(check_piped_assignment, "A=ls | grep foo"));
    }

    #[test]
    fn prop_checkPipedAssignment2() {
        assert!(!emits(check_piped_assignment, "A=foo cmd | grep foo"));
    }

    #[test]
    fn prop_checkPipedAssignment3() {
        assert!(!emits(check_piped_assignment, "A=foo"));
    }

    // ---- checkArithmeticOpCommand ----

    #[test]
    fn prop_checkPipePitfalls3() {
        assert!(emits(check_pipe_pitfalls, "ls | grep -v mp3"));
    }

    #[test]
    fn prop_checkPipePitfalls4() {
        assert!(!emits(check_pipe_pitfalls, "find . -print0 | xargs -0 foo"));
    }

    #[test]
    fn prop_checkPipePitfalls5() {
        assert!(!emits(check_pipe_pitfalls, "ls -N | foo"));
    }

    #[test]
    fn prop_checkPipePitfalls6() {
        assert!(emits(check_pipe_pitfalls, "find . | xargs foo"));
    }

    #[test]
    fn prop_checkPipePitfalls7() {
        assert!(!emits(
            check_pipe_pitfalls,
            "find . -printf '%s\\n' | xargs foo"
        ));
    }

    #[test]
    fn prop_checkPipePitfalls8() {
        assert!(emits(check_pipe_pitfalls, "foo | grep bar | wc -l"));
    }

    #[test]
    fn prop_checkPipePitfalls9() {
        assert!(!emits(check_pipe_pitfalls, "foo | grep -o bar | wc -l"));
    }

    #[test]
    fn prop_checkPipePitfalls10() {
        assert!(!emits(check_pipe_pitfalls, "foo | grep -o bar | wc"));
    }

    #[test]
    fn prop_checkPipePitfalls11() {
        assert!(!emits(check_pipe_pitfalls, "foo | grep bar | wc"));
    }

    #[test]
    fn prop_checkPipePitfalls12() {
        assert!(!emits(check_pipe_pitfalls, "foo | grep -o bar | wc -c"));
    }

    #[test]
    fn prop_checkPipePitfalls13() {
        assert!(!emits(check_pipe_pitfalls, "foo | grep bar | wc -c"));
    }

    #[test]
    fn prop_checkPipePitfalls14() {
        assert!(!emits(check_pipe_pitfalls, "foo | grep -o bar | wc -cmwL"));
    }

    #[test]
    fn prop_checkPipePitfalls15() {
        assert!(!emits(check_pipe_pitfalls, "foo | grep bar | wc -cmwL"));
    }

    #[test]
    fn prop_checkPipePitfalls16() {
        assert!(!emits(check_pipe_pitfalls, "foo | grep -r bar | wc -l"));
    }

    #[test]
    fn prop_checkPipePitfalls17() {
        assert!(!emits(check_pipe_pitfalls, "foo | grep -l bar | wc -l"));
    }

    #[test]
    fn prop_checkPipePitfalls18() {
        assert!(!emits(check_pipe_pitfalls, "foo | grep -L bar | wc -l"));
    }

    #[test]
    fn prop_checkPipePitfalls19() {
        assert!(!emits(check_pipe_pitfalls, "foo | grep -A2 bar | wc -l"));
    }

    #[test]
    fn prop_checkPipePitfalls20() {
        assert!(!emits(check_pipe_pitfalls, "foo | grep -B999 bar | wc -l"));
    }

    #[test]
    fn prop_checkPipePitfalls21() {
        assert!(!emits(
            check_pipe_pitfalls,
            "foo | grep --after-context 999 bar | wc -l"
        ));
    }

    #[test]
    fn prop_checkPipePitfalls22() {
        assert!(!emits(
            check_pipe_pitfalls,
            "foo | grep -B 1 --after-context 999 bar | wc -l"
        ));
    }

    #[test]
    fn prop_checkPipePitfalls23() {
        assert!(!emits(
            check_pipe_pitfalls,
            "ps -o pid,args -p $(pgrep java) | grep -F net.shellcheck.Test"
        ));
    }

    // ---- checkShebangParameters ----

    #[test]
    fn prop_checkStderrPipe1() {
        assert!(emits(check_stderr_pipe, "#!/bin/ksh\nfoo |& bar"));
    }

    #[test]
    fn prop_checkStderrPipe2() {
        assert!(!emits(check_stderr_pipe, "#!/bin/bash\nfoo |& bar"));
    }

    // ---- checkOverridingPath ----

    #[test]
    fn prop_checkGrepQ1() {
        assert!(emits(check_should_use_grep_q, "[[ $(foo | grep bar) ]]"));
    }

    #[test]
    fn prop_checkGrepQ2() {
        assert!(emits(check_should_use_grep_q, "[ -z $(fgrep lol) ]"));
    }

    #[test]
    fn prop_checkGrepQ3() {
        assert!(emits(
            check_should_use_grep_q,
            "[ -n \"$(foo | zgrep lol)\" ]"
        ));
    }

    #[test]
    fn prop_checkGrepQ4() {
        assert!(!emits(check_should_use_grep_q, "[ -z $(grep bar | cmd) ]"));
    }

    #[test]
    fn prop_checkGrepQ5() {
        assert!(!emits(check_should_use_grep_q, "rm $(ls | grep file)"));
    }

    #[test]
    fn prop_checkGrepQ6() {
        assert!(!emits(check_should_use_grep_q, "[[ -n $(pgrep foo) ]]"));
    }

    // ---- checkCpLegacyR ----
}
