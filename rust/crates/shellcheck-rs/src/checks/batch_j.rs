//! Ported check batch j. See rust/PORTING.md.
//!
//! Ported checks (pure AST patterns; no CFG/arithmetic dependencies):
//! - SC2064  checkTrapQuotes — `trap "..."` double-quoted argument expands now
//! - SC2069  checkStderrRedirect — `2>&1 >file` ordering
//! - SC2094  checkRedirectToSame — read+write same file in a pipeline
//! - SC2129  checkMultipleAppends — 3+ individual `>>` to the same file
//! - SC2233/SC2234  checkSubshelledTests — redundant `( )` around condition/test
//!
//! Skipped:
//! - SC2145 — already ported in an earlier batch (per assignment).
//! - SC2235 (general branch of checkSubshelledTests, `{ ..; }` suggestion) is not
//!   in this assignment, so it is intentionally not emitted; the 2233/2234
//!   branches are mutually exclusive with it, so omitting it does not change
//!   their behavior.
//!
//! Notes on arithmetic: checkSubshelledTests's `hasAssignment` also looks for
//! `TA_Assignment`/`TA_Unary "++"/"--"` inside `$((..))`. Arithmetic is not yet
//! parsed into `TA_*` (it is a placeholder literal), so those sub-cases can never
//! match; the `T_DollarBraced` (`${x:=y}`) and `T_DollarBraceCommandExpansion`
//! cases (which do parse) are ported so their negative tests stay negative.
#![allow(unused_imports, unused_variables, dead_code)]
use crate::analyzer_lib::*;
use crate::ast::*;
use crate::astlib;
use crate::astlib::oversimplify;
use crate::interface::Shell;

pub fn register(c: &mut Checker) {
    c.node(check_trap_quotes);
    c.node(check_stderr_redirect);
    c.node(check_redirect_to_same);
    c.node(check_multiple_appends);
    c.node(check_subshelled_tests);
}

// ---------------------------------------------------------------------------
// Shared private helpers (ported from ASTLib/AnalyzerLib; kept local so this
// module does not touch shared files that parallel agents also edit).
// ---------------------------------------------------------------------------

fn basename(path: &str) -> String {
    match path.rsplit('/').next() {
        Some(x) => x.to_string(),
        None => path.to_string(),
    }
}

/// `getWordParts`.
fn get_word_parts(t: &Token) -> Vec<&Token> {
    use InnerToken::*;
    match &*t.inner {
        T_NormalWord(l) => l.iter().flat_map(get_word_parts).collect(),
        T_DoubleQuoted(l) => l.iter().collect(),
        TA_Expansion(l) => l.iter().flat_map(get_word_parts).collect(),
        _ => vec![t],
    }
}

/// `isFlag`: word whose first part is an unquoted `-...` literal.
fn is_flag(t: &Token) -> bool {
    match get_word_parts(t).first() {
        Some(w) => matches!(&*w.inner, InnerToken::T_Literal(s) if s.starts_with('-')),
        None => false,
    }
}

/// `getCommand`: unwrap redirections/annotations to the T_SimpleCommand.
fn get_command(t: &Token) -> Option<&Token> {
    match &*t.inner {
        InnerToken::T_Redirecting { cmd, .. } => get_command(cmd),
        InnerToken::T_Annotation { token, .. } => get_command(token),
        InnerToken::T_SimpleCommand { words, .. } if !words.is_empty() => Some(t),
        _ => None,
    }
}

fn simple_command_words(t: &Token) -> Option<&Vec<Token>> {
    let cmd = get_command(t)?;
    if let InnerToken::T_SimpleCommand { words, .. } = &*cmd.inner {
        Some(words)
    } else {
        None
    }
}

/// `getEffectiveCommandToken` for exec: parse `getBsdOpts "cla:"`.
fn exec_effective(args: &[Token]) -> Option<&Token> {
    fn needs_arg(c: char) -> Option<bool> {
        match c {
            'c' | 'l' => Some(false),
            'a' => Some(true),
            _ => None,
        }
    }
    let mut i = 0;
    while i < args.len() {
        let s = astlib::get_literal_string(&args[i]).unwrap_or_else(|| "\0".to_string());
        if s == "--" {
            return args.get(i + 1);
        } else if s.starts_with("--") {
            return None;
        } else if s.starts_with('-') && s.len() > 1 {
            let cluster: Vec<char> = s[1..].chars().collect();
            let mut ci = 0;
            loop {
                if ci >= cluster.len() {
                    i += 1;
                    break;
                }
                match needs_arg(cluster[ci]) {
                    None => return None,
                    Some(false) => ci += 1,
                    Some(true) => {
                        if ci + 1 == cluster.len() {
                            i += 2;
                        } else {
                            i += 1;
                        }
                        break;
                    }
                }
            }
        } else {
            return Some(&args[i]);
        }
    }
    None
}

/// `getCommandName`: resolving `command`/`builtin`/`busybox`/`run`/`exec`.
fn get_command_name(t: &Token) -> Option<String> {
    let words = simple_command_words(t)?;
    let w = words.first()?;
    let s = astlib::get_literal_string(w)?;
    let rest = &words[1..];
    let effective: Option<&Token> = match s.as_str() {
        "busybox" | "builtin" | "command" | "run" => rest.first().filter(|a| !is_flag(a)),
        "exec" => exec_effective(rest),
        _ => None,
    };
    match effective {
        Some(tok) => astlib::get_literal_string(tok),
        None => Some(s),
    }
}

fn get_command_basename(t: &Token) -> Option<String> {
    get_command_name(t).map(|s| basename(&s))
}

/// `getClosestCommand`: nearest enclosing T_Redirecting on the path to root.
fn get_closest_command<'a>(params: &'a Parameters, t: &'a Token) -> Option<&'a Token> {
    let mut cur = t;
    loop {
        match &*cur.inner {
            InnerToken::T_Redirecting { .. } => return Some(cur),
            InnerToken::T_Script { .. } => return None,
            _ => {}
        }
        cur = params.parent(cur)?;
    }
}

/// `isAssignment`.
fn is_assignment(t: &Token) -> bool {
    match &*t.inner {
        InnerToken::T_Redirecting { cmd, .. } => is_assignment(cmd),
        InnerToken::T_SimpleCommand { assignments, words } => {
            !assignments.is_empty() && words.is_empty()
        }
        InnerToken::T_Assignment { .. } => true,
        InnerToken::T_Annotation { token, .. } => is_assignment(token),
        _ => false,
    }
}

/// `isFunction`.
fn is_function(t: &Token) -> bool {
    matches!(&*t.inner, InnerToken::T_Function { .. })
}

/// Pre-order traversal of every node in `t`'s subtree (`doAnalysis` order).
fn all_nodes<'a>(t: &'a Token, out: &mut Vec<&'a Token>) {
    out.push(t);
    for c in t.children() {
        all_nodes(c, out);
    }
}

// ---------------------------------------------------------------------------
// SC2064 — checkTrapQuotes
// ---------------------------------------------------------------------------

fn check_trap_quotes(_params: &Parameters, t: &Token, out: &mut Out) {
    // CommandCheck (Exactly "trap"): only fire on the T_SimpleCommand itself.
    let words = match &*t.inner {
        InnerToken::T_SimpleCommand { words, .. } if !words.is_empty() => words,
        _ => return,
    };
    if get_command_name(t).as_deref() != Some("trap") {
        return;
    }
    let arg = match words.get(1) {
        Some(a) => a,
        None => return,
    };
    // checkTrap (T_NormalWord _ [T_DoubleQuoted _ rs])
    let parts = match &*arg.inner {
        InnerToken::T_NormalWord(l) => l,
        _ => return,
    };
    if parts.len() != 1 {
        return;
    }
    let rs = match &*parts[0].inner {
        InnerToken::T_DoubleQuoted(rs) => rs,
        _ => return,
    };
    for r in rs {
        let hit = matches!(
            &*r.inner,
            InnerToken::T_DollarExpansion(_)
                | InnerToken::T_Backticked(_)
                | InnerToken::T_DollarBraced { .. }
                | InnerToken::T_DollarArithmetic(_)
        );
        if hit {
            warn(
                out,
                r.id(),
                2064,
                "Use single quotes, otherwise this expands now rather than when signalled.",
            );
        }
    }
}

// ---------------------------------------------------------------------------
// SC2069 — checkStderrRedirect
// ---------------------------------------------------------------------------

fn check_stderr_redirect(params: &Parameters, redir: &Token, out: &mut Out) {
    let redirs = match &*redir.inner {
        InnerToken::T_Redirecting { redirs, .. } => redirs,
        _ => return,
    };
    if redirs.len() != 2 {
        return;
    }
    // First: T_FdRedirect id "2" (T_IoDuplicate _ (T_GREATAND _) "1")
    let first_id;
    match &*redirs[0].inner {
        InnerToken::T_FdRedirect { fd, target } if fd == "2" => {
            match &*target.inner {
                InnerToken::T_IoDuplicate { op, num } if num == "1" => {
                    if !matches!(&*op.inner, InnerToken::T_GREATAND) {
                        return;
                    }
                }
                _ => return,
            }
            first_id = redirs[0].id();
        }
        _ => return,
    }
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

// ---------------------------------------------------------------------------
// SC2094 — checkRedirectToSame
// ---------------------------------------------------------------------------

fn check_redirect_to_same(params: &Parameters, t: &Token, out: &mut Out) {
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

// ---------------------------------------------------------------------------
// SC2129 — checkMultipleAppends
// ---------------------------------------------------------------------------

/// `getCommandSequences`.
fn get_command_sequences(t: &Token) -> Vec<&[Token]> {
    use InnerToken::*;
    match &*t.inner {
        T_Script { commands, .. } => vec![&commands[..]],
        T_BraceGroup(cmds) => vec![&cmds[..]],
        T_Subshell(cmds) => vec![&cmds[..]],
        T_WhileExpression { condition, body } => vec![&condition[..], &body[..]],
        T_UntilExpression { condition, body } => vec![&condition[..], &body[..]],
        T_ForIn { body, .. } => vec![&body[..]],
        T_ForArithmetic { body, .. } => vec![&body[..]],
        T_IfExpression { clauses, elses } => {
            let mut out: Vec<&[Token]> = vec![];
            for (a, b) in clauses {
                out.push(&a[..]);
                out.push(&b[..]);
            }
            out.push(&elses[..]);
            out
        }
        T_Annotation { token, .. } => get_command_sequences(token),
        T_DollarExpansion(cmds) => vec![&cmds[..]],
        T_DollarBraceCommandExpansion { list, .. } => vec![&list[..]],
        T_Backticked(cmds) => vec![&cmds[..]],
        _ => vec![],
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

fn check_multiple_appends(_params: &Parameters, t: &Token, out: &mut Out) {
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

// ---------------------------------------------------------------------------
// SC2233 / SC2234 — checkSubshelledTests (2233/2234 branches only)
// ---------------------------------------------------------------------------

fn check_subshelled_tests(params: &Parameters, t: &Token, out: &mut Out) {
    let list = match &*t.inner {
        InnerToken::T_Subshell(list) => list,
        _ => return,
    };
    if !list.iter().all(is_test_structure) {
        return;
    }
    if has_assignment(t) {
        return;
    }
    // getPath (parentMap params) t = [t, parent, grandparent, ...]
    let mut path: Vec<&Token> = vec![t];
    let mut cur = params.parent(t);
    while let Some(node) = cur {
        path.push(node);
        cur = params.parent(node);
    }

    if is_compound_condition(&path) {
        style(
            out,
            t.id(),
            2233,
            "Remove superfluous (..) around condition to avoid subshell overhead.",
        );
    } else if is_single_test(list) && !is_function_body(&path) {
        style(
            out,
            t.id(),
            2234,
            "Remove superfluous (..) around test command to avoid subshell overhead.",
        );
    }
    // General case (SC2235) intentionally not emitted; see module docs.
}

fn is_single_test(cmds: &[Token]) -> bool {
    cmds.len() == 1 && is_test_command(&cmds[0])
}

fn is_function_body(path: &[&Token]) -> bool {
    // (_ :| f : _) -> isFunction f
    path.get(1).map(|f| is_function(f)).unwrap_or(false)
}

fn is_test_structure(t: &Token) -> bool {
    match &*t.inner {
        InnerToken::T_Banged(inner) => is_test_structure(inner),
        InnerToken::T_AndIf { lhs, rhs } | InnerToken::T_OrIf { lhs, rhs } => {
            is_test_structure(lhs) && is_test_structure(rhs)
        }
        InnerToken::T_Pipeline { separators, commands } if separators.is_empty() => {
            match commands.as_slice() {
                [only] => {
                    if let InnerToken::T_Redirecting { cmd, .. } = &*only.inner {
                        match &*cmd.inner {
                            InnerToken::T_BraceGroup(ts) | InnerToken::T_Subshell(ts) => {
                                ts.iter().all(is_test_structure)
                            }
                            _ => is_test_command(t),
                        }
                    } else {
                        is_test_command(t)
                    }
                }
                _ => is_test_command(t),
            }
        }
        _ => is_test_command(t),
    }
}

fn is_test_command(t: &Token) -> bool {
    match &*t.inner {
        InnerToken::T_Pipeline { separators, commands } if separators.is_empty() => {
            match commands.as_slice() {
                [only] => {
                    if let InnerToken::T_Redirecting { cmd, .. } = &*only.inner {
                        match &*cmd.inner {
                            InnerToken::T_Condition { .. } => true,
                            _ => is_command_test(cmd),
                        }
                    } else {
                        false
                    }
                }
                _ => false,
            }
        }
        _ => false,
    }
}

/// `cmd \`isCommand\` "test"`.
fn is_command_test(t: &Token) -> bool {
    match get_command_name(t) {
        Some(name) => name == "test" || name.ends_with("/test"),
        None => false,
    }
}

/// `isCompoundCondition`: after skipping wrappers, is the enclosing construct an
/// if/while/until?
fn is_compound_condition(path: &[&Token]) -> bool {
    // dropWhile skippable (tail path)
    let mut idx = 1;
    while idx < path.len() && skippable(path[idx]) {
        idx += 1;
    }
    match path.get(idx) {
        Some(node) => matches!(
            &*node.inner,
            InnerToken::T_IfExpression { .. }
                | InnerToken::T_WhileExpression { .. }
                | InnerToken::T_UntilExpression { .. }
        ),
        None => false,
    }
}

fn skippable(t: &Token) -> bool {
    match &*t.inner {
        InnerToken::T_Redirecting { redirs, .. } => redirs.is_empty(),
        InnerToken::T_Pipeline { separators, .. } => separators.is_empty(),
        InnerToken::T_Annotation { .. } => true,
        _ => false,
    }
}

/// `hasAssignment t = isNothing $ doAnalysis guardNotAssignment t`: true iff any
/// descendant node "is an assignment" per `guardNotAssignment`.
fn has_assignment(t: &Token) -> bool {
    let mut nodes: Vec<&Token> = vec![];
    all_nodes(t, &mut nodes);
    nodes.iter().any(|n| node_is_assignment(n))
}

fn node_is_assignment(t: &Token) -> bool {
    match &*t.inner {
        InnerToken::TA_Assignment { .. } => true,
        InnerToken::TA_Unary { op, .. } => op.contains("++") || op.contains("--"),
        InnerToken::T_DollarBraced { op, .. } => {
            let str = oversimplify(op).concat();
            let modifier = get_braced_modifier(&str);
            modifier.starts_with('=') || modifier.starts_with(":=")
        }
        InnerToken::T_DollarBraceCommandExpansion { .. } => true,
        // Arithmetic is not yet parsed into `TA_*` (the contents of `$((..))` are
        // a placeholder literal), so the `TA_Assignment`/`TA_Unary "++"/"--"`
        // cases of `guardNotAssignment` can never match structurally. Recover the
        // increment/assignment cases (e.g. `$((i++))`, `$((i+=1))`) by scanning
        // the placeholder text; this keeps `( [[ $((i++)) = 10 ]] )` from firing.
        InnerToken::T_DollarArithmetic(inner) => {
            astlib::get_literal_string(inner).map(|s| arith_has_assignment(&s)).unwrap_or(false)
        }
        _ => false,
    }
}

/// Does an arithmetic expression string contain an assignment or `++`/`--`?
/// Matches the arithmetic assignment operators (`=`, `+=`, `-=`, `*=`, `/=`,
/// `%=`, `<<=`, `>>=`, `&=`, `|=`, `^=`) and the increment/decrement operators,
/// while excluding the comparisons `==`, `!=`, `<=`, `>=`.
fn arith_has_assignment(s: &str) -> bool {
    let b = s.as_bytes();
    let mut i = 0;
    while i < b.len() {
        let c = b[i];
        if (c == b'+' || c == b'-') && i + 1 < b.len() && b[i + 1] == c {
            return true; // ++ or --
        }
        if c == b'=' {
            let next = b.get(i + 1).copied();
            let prev = if i > 0 { Some(b[i - 1]) } else { None };
            if next != Some(b'=') {
                match prev {
                    // `==` second half, or `!=`.
                    Some(b'=') | Some(b'!') => {}
                    // `<=`/`>=` comparisons unless doubled to `<<=`/`>>=`.
                    Some(b'<') | Some(b'>') => {
                        let pp = if i >= 2 { Some(b[i - 2]) } else { None };
                        if pp == prev {
                            return true;
                        }
                    }
                    _ => return true,
                }
            }
        }
        i += 1;
    }
    false
}

// ---------------------------------------------------------------------------
// getBracedModifier (ported from ASTLib; used by hasAssignment above)
// ---------------------------------------------------------------------------

fn is_variable_start_char(c: char) -> bool {
    c == '_' || c.is_ascii_lowercase() || c.is_ascii_uppercase()
}
fn is_variable_char(c: char) -> bool {
    is_variable_start_char(c) || c.is_ascii_digit()
}
fn is_special_variable_char(c: char) -> bool {
    matches!(c, '*' | '@' | '#' | '?' | '-' | '$' | '!')
}

fn drop_hashbang_prefix(s: &str) -> &str {
    match s.chars().next() {
        Some(c) if c == '!' || c == '#' => &s[c.len_utf8()..],
        _ => s,
    }
}

fn take_name(s: &str) -> Option<String> {
    let name: String = s.chars().take_while(|c| is_variable_char(*c)).collect();
    if name.is_empty() {
        None
    } else {
        Some(name)
    }
}

fn get_special(s: &str) -> Option<String> {
    match s.chars().next() {
        Some(c) if is_special_variable_char(c) => Some(c.to_string()),
        _ => None,
    }
}

fn name_expansion(s: &str) -> Option<String> {
    let mut chars = s.chars();
    if chars.next()? != '!' {
        return None;
    }
    let next = chars.next()?;
    if !is_variable_char(next) {
        return None;
    }
    let first = chars.find(|c| !is_variable_char(*c))?;
    if matches!(first, '*' | '?' | '@') {
        Some(String::new())
    } else {
        None
    }
}

fn get_braced_reference(s: &str) -> String {
    if let Some(r) = name_expansion(s) {
        return r;
    }
    let no_prefix = drop_hashbang_prefix(s);
    if let Some(r) = take_name(no_prefix) {
        return r;
    }
    if let Some(r) = get_special(no_prefix) {
        return r;
    }
    if let Some(r) = get_special(s) {
        return r;
    }
    s.to_string()
}

fn get_braced_modifier(s: &str) -> String {
    let var = get_braced_reference(s);
    let candidates: Vec<&str> = match s.chars().next() {
        Some(c) if c == '#' || c == '!' => vec![&s[c.len_utf8()..], s],
        _ => vec![s],
    };
    for a in candidates {
        if let Some(rest) = a.strip_prefix(var.as_str()) {
            return rest.to_string();
        }
    }
    String::new()
}
