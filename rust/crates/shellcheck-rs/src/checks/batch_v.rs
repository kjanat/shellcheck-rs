//! Ported check batch v. See rust/PORTING.md.
//!
//! Expansion / quoting / parameter-substitution / redirection checks ported
//! from `ShellCheck.Analytics`:
//! - SC2082/2296/2297/2298/2299/2300/2301  checkBadParameterSubstitution
//! - SC2088  checkTildeInQuotes
//! - SC2026 (+2027/2140 impl only)          checkInexplicablyUnquoted
//! - SC2083  checkLonelyDotDash
//! - SC2084 (+2091/2092 impl only)          checkSpuriousExpansion
//! - SC2007  checkDollarBrackets
//! - SC2087  checkSshHereDoc
//! - SC2097/2098  checkPrefixAssignmentReference
//! - SC2247  checkDollarQuoteParen
//! - SC2256  checkTranslatedStringVariable
//! - SC2188/2189  checkRedirectedNowhere
//! - SC2210  checkRedirectionToNumber
//! - SC2238  checkRedirectionToCommand
//! - SC2216/2217/2259/2260 (not 2261)       checkPipeToNowhere
//! - SC2327/2328  checkExpansionWithRedirection
//! - SC2190/2191/2192  checkArrayAssignmentIndices
//! - SC2295  checkUnquotedParameterExpansionPattern
//! - SC2302/2303  checkArrayValueUsedAsIndex
use crate::analyzer_lib::is_unqualified_command;
use crate::analyzer_lib::*;
use crate::ast::*;
use crate::astlib;
use crate::astlib::is_command_substitution;
use crate::astlib::is_constant;
use crate::cfg;
use crate::cfg::get_unquoted_literal;
use crate::data::COMMON_COMMANDS;
use crate::interface::Fix;
use std::collections::HashMap;

/// Register this batch's checks.
pub fn register(c: &mut Checker) {
    c.node(check_bad_parameter_substitution);
    c.node(check_tilde_in_quotes);
    c.node(check_inexplicably_unquoted);
    c.node(check_lonely_dot_dash);
    c.node(check_spurious_expansion);
    c.node(check_dollar_brackets);
    c.node(check_ssh_here_doc);
    c.node(check_prefix_assignment_reference);
    c.node(check_dollar_quote_paren);
    c.node(check_translated_string_variable);
    c.node(check_redirected_nowhere);
    c.node(check_redirection_to_number);
    c.node(check_redirection_to_command);
    c.node(check_pipe_to_nowhere);
    c.node(check_expansion_with_redirection);
    c.tree(check_array_assignment_indices);
    c.node(check_unquoted_parameter_expansion_pattern);
    c.tree(check_array_value_used_as_index);
}

// ---------------------------------------------------------------------------
// Shared local helpers (ported from ASTLib; kept private).
// ---------------------------------------------------------------------------

/// `ShellCheck.ASTLib.isUnmodifiedParameterExpansion`.
fn is_unmodified_parameter_expansion(t: &Token) -> bool {
    match &*t.inner {
        InnerToken::T_DollarBraced { braced: false, .. } => true,
        InnerToken::T_DollarBraced { op, .. } => {
            let str = astlib::oversimplify_concat(op);
            cfg::get_braced_reference(&str) == str
        }
        _ => false,
    }
}

/// `surroundWith`.
fn surround_with(params: &Parameters, id: Id, s: &str) -> Fix {
    fix_with(vec![
        replace_start(params, id, 0, s),
        replace_end(params, id, 0, s),
    ])
}

// ---------------------------------------------------------------------------
// SC2082 / SC2296 / SC2297 / SC2298 / SC2299 / SC2300 / SC2301
// checkBadParameterSubstitution
// ---------------------------------------------------------------------------

fn bps_is_indirection_part(t: &Token) -> Option<bool> {
    match &*t.inner {
        InnerToken::T_DollarExpansion(_) => Some(true),
        InnerToken::T_Backticked(_) => Some(true),
        InnerToken::T_DollarBraced { .. } => Some(true),
        InnerToken::T_DollarArithmetic(_) => Some(true),
        InnerToken::T_Literal(s) => {
            if s.chars().all(cfg::is_variable_char) {
                None
            } else {
                Some(false)
            }
        }
        _ => Some(false),
    }
}

fn bps_is_indirection(vars: &[Token]) -> bool {
    let list: Vec<bool> = vars.iter().filter_map(bps_is_indirection_part).collect();
    !list.is_empty() && list.iter().all(|&b| b)
}

fn bps_is_variable(str: &str) -> bool {
    let chars: Vec<char> = str.chars().collect();
    if chars.len() == 1 {
        let c = chars[0];
        cfg::is_variable_start_char(c) || cfg::is_special_variable_char(c) || c.is_ascii_digit()
    } else {
        cfg::is_variable_name(str)
    }
}

fn bps_name(t: &Token) -> &'static str {
    match &*t.inner {
        InnerToken::T_SingleQuoted(_) | InnerToken::T_DoubleQuoted(_) => "quotes",
        _ => "syntax",
    }
}

fn bps_check_first(first: &Token, out: &mut Out) {
    match &*first.inner {
        InnerToken::T_Literal(s) => {
            if let Some(c) = s.chars().next() {
                if !(cfg::is_variable_char(c) || cfg::is_special_variable_char(c)) {
                    err(
                        out,
                        first.id(),
                        2296,
                        &format!(
                            "Parameter expansions can't start with {}. Double check syntax.",
                            c
                        ),
                    );
                }
            }
        }
        InnerToken::T_ParamSubSpecialChar(_) => {}
        InnerToken::T_DoubleQuoted(list)
            if list.len() == 1
                && matches!(&*list[0].inner, InnerToken::T_Literal(s) if bps_is_variable(s)) =>
        {
            err(
                out,
                first.id(),
                2297,
                "Double quotes must be outside ${}: ${\"invalid\"} vs \"${valid}\".",
            );
        }
        InnerToken::T_DollarBraced { braced, .. } if is_unmodified_parameter_expansion(first) => {
            let msg = if *braced {
                "${${x}} is invalid. For expansion, use ${x}. For indirection, use arrays, ${!x} or (for sh) eval."
            } else {
                "${$x} is invalid. For expansion, use ${x}. For indirection, use arrays, ${!x} or (for sh) eval."
            };
            err(out, first.id(), 2298, msg);
        }
        InnerToken::T_DollarBraced { .. } => {
            err(
                out,
                first.id(),
                2299,
                "Parameter expansions can't be nested. Use temporary variables.",
            );
        }
        _ if is_command_substitution(first) => {
            err(
                out,
                first.id(),
                2300,
                "Parameter expansion can't be applied to command substitutions. Use temporary variables.",
            );
        }
        _ => {
            err(
                out,
                first.id(),
                2301,
                &format!(
                    "Parameter expansion starts with unexpected {}. Double check syntax.",
                    bps_name(first)
                ),
            );
        }
    }
}

fn check_bad_parameter_substitution(_params: &Parameters, t: &Token, out: &mut Out) {
    if let InnerToken::T_DollarBraced { op, .. } = &*t.inner {
        if let InnerToken::T_NormalWord(contents) = &*op.inner {
            if let Some(first) = contents.first() {
                if bps_is_indirection(contents) {
                    err(
                        out,
                        t.id(),
                        2082,
                        "To expand via indirection, use arrays, ${!name} or (for sh only) eval.",
                    );
                } else {
                    bps_check_first(first, out);
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// SC2088 — checkTildeInQuotes
// ---------------------------------------------------------------------------

fn tiq_verify(id: Id, str: &str, out: &mut Out) {
    if str.starts_with("~/") {
        warn(out, id, 2088, "Tilde does not expand in quotes. Use $HOME.");
    }
}

fn check_tilde_in_quotes(_params: &Parameters, t: &Token, out: &mut Out) {
    if let InnerToken::T_NormalWord(list) = &*t.inner {
        match list.first().map(|x| &*x.inner) {
            Some(InnerToken::T_SingleQuoted(str)) => {
                tiq_verify(list[0].id(), str, out);
            }
            Some(InnerToken::T_DoubleQuoted(inner)) => {
                if let Some(f) = inner.first() {
                    if let InnerToken::T_Literal(str) = &*f.inner {
                        tiq_verify(f.id(), str, out);
                    }
                }
            }
            _ => {}
        }
    }
}

// ---------------------------------------------------------------------------
// SC2026 / SC2027 / SC2140 — checkInexplicablyUnquoted (full function)
// ---------------------------------------------------------------------------

fn iu_quotes_single_thing(parts: &[Token]) -> bool {
    parts.len() == 1
        && matches!(
            &*parts[0].inner,
            InnerToken::T_DollarExpansion(_)
                | InnerToken::T_DollarBraced { .. }
                | InnerToken::T_Backticked(_)
        )
}

/// `isSpecial` over a getPath-list (path[0] is the trapped token).
fn iu_is_special(path: &[Token]) -> bool {
    if path.is_empty() {
        return false;
    }
    match &*path[0].inner {
        InnerToken::T_Redirecting { .. } => false,
        InnerToken::T_DollarBraced { .. } => true,
        _ => {
            // (a:(TC_Binary _ _ "=~" lhs rhs):rest) -> getId a == getId rhs
            if path.len() >= 2 {
                if let InnerToken::TC_Binary { op, rhs, .. } = &*path[1].inner {
                    if op == "=~" {
                        return path[0].id() == rhs.id();
                    }
                }
            }
            iu_is_special(&path[1..])
        }
    }
}

/// The full checkInexplicablyUnquoted (emits 2026, 2027, 2140).
fn check_inexplicably_unquoted(params: &Parameters, t: &Token, out: &mut Out) {
    if let InnerToken::T_NormalWord(tokens) = &*t.inner {
        for start in 0..tokens.len() {
            iu_check(params, &tokens[start..], out);
        }
    }
}

fn iu_check(params: &Parameters, window: &[Token], out: &mut Out) {
    // check (T_SingleQuoted _ _ : T_Literal id str : _)
    if window.len() >= 2 {
        if let InnerToken::T_SingleQuoted(_) = &*window[0].inner {
            if let InnerToken::T_Literal(str) = &*window[1].inner {
                if !str.is_empty() && str.chars().all(|c| c.is_alphanumeric()) {
                    info(
                        out,
                        window[1].id(),
                        2026,
                        "This word is outside of quotes. Did you intend to 'nest '\"'single quotes'\"' instead'? ",
                    );
                }
                return;
            }
        }
    }
    // check (T_DoubleQuoted _ a : trapped : T_DoubleQuoted _ b : _)
    if window.len() >= 3 {
        let (a, trapped, b) = (&window[0], &window[1], &window[2]);
        if let (InnerToken::T_DoubleQuoted(a_parts), InnerToken::T_DoubleQuoted(b_parts)) =
            (&*a.inner, &*b.inner)
        {
            match &*trapped.inner {
                InnerToken::T_DollarExpansion(_) => {
                    warn(
                        out,
                        trapped.id(),
                        2027,
                        "The surrounding quotes actually unquote this. Remove or escape them.",
                    );
                }
                InnerToken::T_DollarBraced { .. } => {
                    warn(
                        out,
                        trapped.id(),
                        2027,
                        "The surrounding quotes actually unquote this. Remove or escape them.",
                    );
                }
                InnerToken::T_Literal(s) => {
                    let single = iu_quotes_single_thing(a_parts) && iu_quotes_single_thing(b_parts);
                    let is_sep = s == "=" || s == ":" || s == "/";
                    let path = get_path(params, trapped);
                    if !(single || is_sep || iu_is_special(&path)) {
                        warn(
                            out,
                            trapped.id(),
                            2140,
                            "Word is of the form \"A\"B\"C\" (B indicated). Did you mean \"ABC\" or \"A\\\"B\\\"C\"?",
                        );
                    }
                }
                _ => {}
            }
        }
    }
}

// ---------------------------------------------------------------------------
// SC2083 — checkLonelyDotDash
// ---------------------------------------------------------------------------

fn check_lonely_dot_dash(_params: &Parameters, t: &Token, out: &mut Out) {
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

// ---------------------------------------------------------------------------
// SC2084 / SC2091 / SC2092 — checkSpuriousExpansion (full function)
// ---------------------------------------------------------------------------

fn se_check(word: &Token, out: &mut Out) {
    match &*word.inner {
        InnerToken::T_DollarExpansion(_) => warn(
            out,
            word.id(),
            2091,
            "Remove surrounding $() to avoid executing output (or use eval if intentional).",
        ),
        InnerToken::T_Backticked(_) => warn(
            out,
            word.id(),
            2092,
            "Remove backticks to avoid executing output (or use eval if intentional).",
        ),
        InnerToken::T_DollarArithmetic(_) => err(
            out,
            word.id(),
            2084,
            "Remove '$' or use '_=$((expr))' to avoid executing output.",
        ),
        _ => {}
    }
}

fn check_spurious_expansion(_params: &Parameters, t: &Token, out: &mut Out) {
    if let InnerToken::T_SimpleCommand { assignments, words } = &*t.inner {
        if assignments.is_empty() && words.len() == 1 {
            if let InnerToken::T_NormalWord(parts) = &*words[0].inner {
                if parts.len() == 1 {
                    se_check(&parts[0], out);
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// SC2007 — checkDollarBrackets
// ---------------------------------------------------------------------------

fn check_dollar_brackets(_params: &Parameters, t: &Token, out: &mut Out) {
    if let InnerToken::T_DollarBracket(_) = &*t.inner {
        style(out, t.id(), 2007, "Use $((..)) instead of deprecated $[..]");
    }
}

// ---------------------------------------------------------------------------
// SC2087 — checkSshHereDoc
// ---------------------------------------------------------------------------

fn check_ssh_here_doc(_params: &Parameters, t: &Token, out: &mut Out) {
    if let InnerToken::T_Redirecting { redirs, cmd: _ } = &*t.inner {
        if is_command(t, "ssh") {
            for r in redirs {
                sshd_check_here_doc(r, out);
            }
        }
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

// ---------------------------------------------------------------------------
// SC2097 / SC2098 — checkPrefixAssignmentReference
// ---------------------------------------------------------------------------

fn check_prefix_assignment_reference(params: &Parameters, t: &Token, out: &mut Out) {
    if let InnerToken::T_DollarBraced { op, .. } = &*t.inner {
        let name = cfg::get_braced_reference(&astlib::oversimplify_concat(op));
        let path = get_path(params, t);
        let id_path: Vec<Id> = path.iter().map(|x| x.id()).collect();
        // check: walk path until a T_SimpleCommand with vars and non-empty words.
        for node in &path {
            if let InnerToken::T_SimpleCommand { assignments, words } = &*node.inner {
                if !words.is_empty() {
                    for v in assignments {
                        par_check_var(v, &name, &id_path, t.id(), out);
                    }
                    break;
                }
            }
        }
    }
}

fn par_check_var(v: &Token, name: &str, id_path: &[Id], expansion_id: Id, out: &mut Out) {
    if let InnerToken::T_Assignment { var, indices, .. } = &*v.inner {
        if indices.is_empty() && var == name && !id_path.contains(&v.id()) {
            warn(
                out,
                v.id(),
                2097,
                "This assignment is only seen by the forked process.",
            );
            warn(
                out,
                expansion_id,
                2098,
                "This expansion will not see the mentioned assignment.",
            );
        }
    }
}

// ---------------------------------------------------------------------------
// SC2247 — checkDollarQuoteParen
// ---------------------------------------------------------------------------

fn check_dollar_quote_paren(params: &Parameters, t: &Token, out: &mut Out) {
    if let InnerToken::T_DollarDoubleQuoted(list) = &*t.inner {
        if let Some(first) = list.first() {
            if let InnerToken::T_Literal(s) = &*first.inner {
                if let Some(c) = s.chars().next() {
                    if c == '(' || c == '{' {
                        let fix = fix_with(vec![replace_start(params, t.id(), 2, "\"$")]);
                        warn_with_fix(
                            out,
                            t.id(),
                            2247,
                            "Flip leading $ and \" if this should be a quoted substitution.",
                            fix,
                        );
                    }
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// SC2256 — checkTranslatedStringVariable (uses variable_flow)
// ---------------------------------------------------------------------------

fn check_translated_string_variable(params: &Parameters, t: &Token, out: &mut Out) {
    if let InnerToken::T_DollarDoubleQuoted(list) = &*t.inner {
        if list.len() == 1 {
            if let InnerToken::T_Literal(s) = &*list[0].inner {
                if s.chars().all(cfg::is_variable_char)
                    && translated_assignments(params).contains(s)
                {
                    let fix = fix_with(vec![replace_start(params, t.id(), 2, "\"$")]);
                    warn_with_fix(
                        out,
                        t.id(),
                        2256,
                        "This translated string is the name of a variable. Flip leading $ and \" if this should be a quoted substitution.",
                        fix,
                    );
                }
            }
        }
    }
}

fn translated_assignments(params: &Parameters) -> std::collections::HashSet<String> {
    let mut set = std::collections::HashSet::new();
    for sd in &params.variable_flow {
        if let StackData::Assignment(_, _, name, _) = sd {
            if cfg::is_variable_name(name) {
                set.insert(name.clone());
            }
        }
    }
    set
}

// ---------------------------------------------------------------------------
// SC2188 / SC2189 — checkRedirectedNowhere
// ---------------------------------------------------------------------------

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

fn check_redirected_nowhere(params: &Parameters, token: &Token, out: &mut Out) {
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

// ---------------------------------------------------------------------------
// SC2210 — checkRedirectionToNumber
// ---------------------------------------------------------------------------

fn check_redirection_to_number(_params: &Parameters, t: &Token, out: &mut Out) {
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

// ---------------------------------------------------------------------------
// SC2238 — checkRedirectionToCommand
// ---------------------------------------------------------------------------

fn check_redirection_to_command(_params: &Parameters, t: &Token, out: &mut Out) {
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

// ---------------------------------------------------------------------------
// SC2216 / SC2217 / SC2259 / SC2260 / SC2261 — checkPipeToNowhere
// ---------------------------------------------------------------------------

// Variant names mirror the Haskell constructors StdoutPipe / StdoutStderrPipe / NoPipe.
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

/// Full checkPipeToNowhere (with warnAboutDupes / SC2261) — used by prop tests.
fn check_pipe_to_nowhere(params: &Parameters, t: &Token, out: &mut Out) {
    ptn_impl(params, t, true, out);
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

// ---------------------------------------------------------------------------
// SC2327 / SC2328 — checkExpansionWithRedirection
// ---------------------------------------------------------------------------

fn check_expansion_with_redirection(params: &Parameters, t: &Token, out: &mut Out) {
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
                    let suggest = astlib::get_literal_string(file).as_deref() != Some("/dev/null");
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

// ---------------------------------------------------------------------------
// SC2190 / SC2191 / SC2192 — checkArrayAssignmentIndices
// ---------------------------------------------------------------------------

fn caai_get_associative_arrays(root: &Token) -> std::collections::HashSet<String> {
    let mut out = std::collections::HashSet::new();
    root.visit_preorder(&mut |t| {
        if let InnerToken::T_SimpleCommand { words, .. } = &*t.inner {
            if words.is_empty() {
                return;
            }
            let name = get_command_name(t);
            if !matches!(
                name.as_deref(),
                Some("declare") | Some("local") | Some("typeset")
            ) {
                return;
            }
            let args = &words[1..];
            let mut has_a = false;
            for a in args {
                if let Some(s) = astlib::get_literal_string(a) {
                    if s.starts_with("--") {
                    } else if let Some(chars) = s.strip_prefix('-') {
                        if chars.contains('A') {
                            has_a = true;
                        }
                    }
                }
            }
            if !has_a {
                return;
            }
            for a in args {
                let lit = astlib::get_literal_string(a);
                if let Some(ref s) = lit {
                    if s.starts_with('-') {
                        continue;
                    }
                }
                // nameAssignments: name before '=' if present.
                if let Some(s) = &lit {
                    let name: String = s.chars().take_while(|&c| c != '=').collect();
                    out.insert(name);
                } else if let InnerToken::T_Assignment { var, .. } = &*a.inner {
                    out.insert(var.clone());
                }
            }
        }
    });
    out
}

fn check_array_assignment_indices(params: &Parameters, root: &Token, out: &mut Out) {
    let assocs = caai_get_associative_arrays(root);
    root.visit_preorder(&mut |t| {
        if let InnerToken::T_Assignment {
            var,
            indices,
            value,
            ..
        } = &*t.inner
        {
            if indices.is_empty() {
                if let InnerToken::T_Array(list) = &*value.inner {
                    let is_assoc = assocs.contains(var);
                    for el in list {
                        caai_check_element(params, is_assoc, el, out);
                    }
                }
            }
        }
    });
}

fn caai_empty_value_id(value: &Token) -> Option<Id> {
    match &*value.inner {
        InnerToken::T_Literal(s) if s.is_empty() => Some(value.id()),
        InnerToken::T_NormalWord(parts) if parts.len() == 1 => match &*parts[0].inner {
            InnerToken::T_Literal(s) if s.is_empty() => Some(parts[0].id()),
            _ => None,
        },
        _ => None,
    }
}

fn caai_check_element(params: &Parameters, is_associative: bool, t: &Token, out: &mut Out) {
    match &*t.inner {
        InnerToken::T_IndexedElement { value, .. } => {
            // Haskell matches `T_IndexedElement _ _ (T_Literal id "")`; this parser
            // wraps an empty element value in a single-literal T_NormalWord.
            if let Some(lit_id) = caai_empty_value_id(value) {
                warn(
                    out,
                    lit_id,
                    2192,
                    "This array element has no value. Remove spaces after = or use \"\" for empty string.",
                );
            }
        }
        InnerToken::T_NormalWord(parts) => {
            // literalEquals: parts that are `<digits>=...`.
            let mut literal_equals: Vec<(Id, Fix)> = Vec::new();
            for p in parts {
                if let InnerToken::T_Literal(str) = &*p.inner {
                    let before: String = str.chars().take_while(|&c| c != '=').collect();
                    let has_eq = before.len() < str.len();
                    if before.chars().all(|c| c.is_ascii_digit()) && has_eq {
                        literal_equals.push((p.id(), surround_with(params, p.id(), "\"")));
                    }
                }
            }
            if literal_equals.is_empty() && is_associative {
                warn(
                    out,
                    t.id(),
                    2190,
                    "Elements in associative arrays need index, e.g. array=( [index]=value ) .",
                );
            } else {
                for (id, fix) in literal_equals {
                    warn_with_fix(
                        out,
                        id,
                        2191,
                        "The = here is literal. To assign by index, use ( [index]=value ) with no spaces. To keep as literal, quote it.",
                        fix,
                    );
                }
            }
        }
        _ => {}
    }
}

// ---------------------------------------------------------------------------
// SC2295 — checkUnquotedParameterExpansionPattern
// ---------------------------------------------------------------------------

fn check_unquoted_parameter_expansion_pattern(params: &Parameters, x: &Token, out: &mut Out) {
    if let InnerToken::T_DollarBraced { braced: true, op } = &*x.inner
        && let InnerToken::T_NormalWord(word_parts) = &*op.inner
    {
        // T_NormalWord _ (T_Literal _ s : rest@(_:_))
        if word_parts.len() >= 2 && matches!(&*word_parts[0].inner, InnerToken::T_Literal(_)) {
            let modifier = cfg::get_braced_modifier(&astlib::oversimplify_concat(op));
            if modifier.starts_with('%') || modifier.starts_with('#') {
                for r in &word_parts[1..] {
                    upep_check(params, r, out);
                }
            }
        }
    }
}

fn upep_check(params: &Parameters, t: &Token, out: &mut Out) {
    if matches!(
        &*t.inner,
        InnerToken::T_DollarBraced { .. }
            | InnerToken::T_DollarExpansion(_)
            | InnerToken::T_Backticked(_)
    ) {
        let fix = surround_with(params, t.id(), "\"");
        info_with_fix(
            out,
            t.id(),
            2295,
            "Expansions inside ${..} need to be quoted separately, otherwise they match as patterns.",
            fix,
        );
    }
}

// ---------------------------------------------------------------------------
// SC2302 / SC2303 — checkArrayValueUsedAsIndex (uses variable_flow)
// ---------------------------------------------------------------------------

fn avi_get_array_name(t: &Token) -> Option<String> {
    let parts = word_parts(t);
    if parts.len() == 1 {
        if let InnerToken::T_DollarBraced { op, .. } = &*parts[0].inner {
            let str = astlib::oversimplify_concat(op);
            if cfg::get_braced_modifier(&str) == "[@]" && !str.starts_with('!') {
                return Some(cfg::get_braced_reference(&str));
            }
        }
    }
    None
}

/// Returns (arrayRef token, arrayName).
fn avi_get_array_if_used_as_index<'a>(
    params: &'a Parameters,
    name: &str,
    t: &'a Token,
) -> Option<(Token, String)> {
    match &*t.inner {
        InnerToken::T_DollarBraced { op, .. } => {
            let reference = cfg::get_braced_reference(&astlib::oversimplify_concat(op));
            if reference != name {
                return None;
            }
            // parent must be T_NormalWord
            let parent_word = params.parent(t)?;
            if !matches!(&*parent_word.inner, InnerToken::T_NormalWord(_)) {
                return None;
            }
            // grandparent must be T_DollarBraced whose op word-parts are [Literal, index, Literal, ..]
            let grandparent = params.parent(parent_word)?;
            let parent_list = match &*grandparent.inner {
                InnerToken::T_DollarBraced { op, .. } => op,
                _ => return None,
            };
            let gp_parts = word_parts(parent_list);
            if gp_parts.len() < 3 {
                return None;
            }
            if !matches!(&*gp_parts[0].inner, InnerToken::T_Literal(_)) {
                return None;
            }
            let index = gp_parts[1];
            if !matches!(&*gp_parts[2].inner, InnerToken::T_Literal(_)) {
                return None;
            }
            let str = astlib::oversimplify_concat(parent_word);
            let modifier = cfg::get_braced_modifier(&str);
            if index.id() != t.id() {
                return None;
            }
            if !modifier.starts_with("[${VAR}]") {
                return None;
            }
            Some((t.clone(), cfg::get_braced_reference(&str)))
        }
        InnerToken::T_NormalWord(_) => {
            let parent = params.parent(t)?;
            let parent_list = match &*parent.inner {
                InnerToken::T_DollarBraced { op, .. } => op,
                _ => return None,
            };
            let str = astlib::oversimplify_concat(t);
            let modifier = cfg::get_braced_modifier(&str);
            let _ = parent_list;
            if !modifier.starts_with(&format!("[{}]", name)) {
                return None;
            }
            let pstr = astlib::oversimplify_concat(match &*parent.inner {
                InnerToken::T_DollarBraced { op, .. } => op,
                _ => return None,
            });
            Some((parent.clone(), cfg::get_braced_reference(&pstr)))
        }
        InnerToken::TA_Variable {
            name: reference,
            indices,
        } if indices.is_empty() => {
            if reference != name {
                return None;
            }
            // parent TA_Sequence [element] where element == t
            let seq = params.parent(t)?;
            let seq_elems = match &*seq.inner {
                InnerToken::TA_Sequence(l) if l.len() == 1 => l,
                _ => return None,
            };
            if seq_elems[0].id() != t.id() {
                return None;
            }
            // parent TA_Variable arrayName [element] where element == seq
            let arr = params.parent(seq)?;
            match &*arr.inner {
                InnerToken::TA_Variable {
                    name: array_name,
                    indices,
                } if indices.len() == 1 => {
                    if indices[0].id() != seq.id() {
                        return None;
                    }
                    Some((arr.clone(), array_name.clone()))
                }
                _ => None,
            }
        }
        _ => None,
    }
}

fn check_array_value_used_as_index(params: &Parameters, _root: &Token, out: &mut Out) {
    // State: name -> (loop token, Vec<(loopWord, arrayName)>).
    let mut var_map: HashMap<String, (Token, Vec<(Token, String)>)> = HashMap::new();
    for sd in &params.variable_flow {
        match sd {
            StackData::Assignment(base, _token, name, dt) => {
                let is_for_from = matches!(&*base.inner, InnerToken::T_ForIn { .. })
                    && matches!(dt, DataType::DataString(DataSource::SourceFrom(_)));
                if is_for_from {
                    if let DataType::DataString(DataSource::SourceFrom(words)) = dt {
                        let arrays: Vec<(Token, String)> = words
                            .iter()
                            .filter_map(|x| avi_get_array_name(x).map(|n| (x.clone(), n)))
                            .collect();
                        var_map.insert(name.clone(), (base.clone(), arrays));
                    }
                } else {
                    var_map.remove(name);
                }
            }
            StackData::Reference(_base, token, name) => {
                if let Some((loop_tok, arrays)) = var_map.get(name) {
                    if let Some((array_ref, array_name)) =
                        avi_get_array_if_used_as_index(params, name, token)
                    {
                        if let Some((loop_word, _)) = arrays.iter().find(|(_, n)| *n == array_name)
                        {
                            let loop_id = loop_tok.id();
                            let in_loop = get_path(params, token).iter().any(|x| x.id() == loop_id);
                            if in_loop {
                                warn(
                                    out,
                                    loop_word.id(),
                                    2302,
                                    "This loops over values. To loop over keys, use \"${!array[@]}\".",
                                );
                                warn(
                                    out,
                                    array_ref.id(),
                                    2303,
                                    &format!(
                                        "{} is an array value, not a key. Use directly or loop over keys instead.",
                                        name
                                    ),
                                );
                            }
                        }
                    }
                }
            }
            _ => {}
        }
    }
}

#[cfg(test)]
#[allow(non_snake_case)]
mod tests {
    use super::*;
    use crate::analyzer_lib::make_parameters;

    use crate::parser::parse_script;

    fn params_for(script: &str) -> Parameters {
        let p = parse_script("test", script);
        let root = p.root.expect("parse produced no root");
        make_parameters(root, p.positions, None, None)
    }
    fn node_emits(f: fn(&Parameters, &Token, &mut Out), s: &str) -> bool {
        let params = params_for(s);
        let mut out = Out::new();
        params.root.visit_preorder(&mut |t| f(&params, t, &mut out));
        !out.is_empty()
    }
    fn tree_emits(f: fn(&Parameters, &Token, &mut Out), s: &str) -> bool {
        let params = params_for(s);
        let mut out = Out::new();
        f(&params, &params.root, &mut out);
        !out.is_empty()
    }

    // ---- SC2082/2296/2297/2298/2299/2300/2301 checkBadParameterSubstitution ----
    #[test]
    fn prop_checkBadParameterSubstitution1() {
        assert!(node_emits(check_bad_parameter_substitution, "${foo$n}"));
    }
    #[test]
    fn prop_checkBadParameterSubstitution2() {
        assert!(!node_emits(
            check_bad_parameter_substitution,
            "${foo//$n/lol}"
        ));
    }
    #[test]
    fn prop_checkBadParameterSubstitution3() {
        assert!(node_emits(check_bad_parameter_substitution, "${$#}"));
    }
    #[test]
    fn prop_checkBadParameterSubstitution4() {
        assert!(node_emits(
            check_bad_parameter_substitution,
            "${var${n}_$((i%2))}"
        ));
    }
    #[test]
    fn prop_checkBadParameterSubstitution5() {
        assert!(!node_emits(check_bad_parameter_substitution, "${bar}"));
    }
    #[test]
    fn prop_checkBadParameterSubstitution6() {
        assert!(node_emits(check_bad_parameter_substitution, "${\"bar\"}"));
    }
    #[test]
    fn prop_checkBadParameterSubstitution7() {
        assert!(node_emits(check_bad_parameter_substitution, "${{var}"));
    }
    #[test]
    fn prop_checkBadParameterSubstitution8() {
        assert!(node_emits(check_bad_parameter_substitution, "${$(x)//x/y}"));
    }
    #[test]
    fn prop_checkBadParameterSubstitution9() {
        assert!(!node_emits(
            check_bad_parameter_substitution,
            "$# ${#} $! ${!} ${!#} ${#!}"
        ));
    }
    #[test]
    fn prop_checkBadParameterSubstitution10() {
        assert!(node_emits(check_bad_parameter_substitution, "${'foo'}"));
    }
    #[test]
    fn prop_checkBadParameterSubstitution11() {
        assert!(node_emits(
            check_bad_parameter_substitution,
            "${${x%.*}##*/}"
        ));
    }

    // ---- SC2088 checkTildeInQuotes ----
    #[test]
    fn prop_checkTildeInQuotes1() {
        assert!(node_emits(check_tilde_in_quotes, "var=\"~/out.txt\""));
    }
    #[test]
    fn prop_checkTildeInQuotes2() {
        assert!(node_emits(check_tilde_in_quotes, "foo > '~/dir'"));
    }
    #[test]
    fn prop_checkTildeInQuotes4() {
        assert!(!node_emits(check_tilde_in_quotes, "~/file"));
    }
    #[test]
    fn prop_checkTildeInQuotes5() {
        assert!(!node_emits(check_tilde_in_quotes, "echo '/~foo/cow'"));
    }
    #[test]
    fn prop_checkTildeInQuotes6() {
        assert!(!node_emits(check_tilde_in_quotes, "awk '$0 ~ /foo/'"));
    }

    // ---- SC2026/2027/2140 checkInexplicablyUnquoted ----
    #[test]
    fn prop_checkInexplicablyUnquoted1() {
        assert!(node_emits(
            check_inexplicably_unquoted,
            "echo 'var='value';'"
        ));
    }
    #[test]
    fn prop_checkInexplicablyUnquoted2() {
        assert!(!node_emits(check_inexplicably_unquoted, "'foo'*"));
    }
    #[test]
    fn prop_checkInexplicablyUnquoted3() {
        assert!(!node_emits(
            check_inexplicably_unquoted,
            "wget --user-agent='something'"
        ));
    }
    #[test]
    fn prop_checkInexplicablyUnquoted4() {
        assert!(node_emits(
            check_inexplicably_unquoted,
            "echo \"VALUES (\"id\")\""
        ));
    }
    #[test]
    fn prop_checkInexplicablyUnquoted5() {
        assert!(!node_emits(
            check_inexplicably_unquoted,
            "\"$dir\"/\"$file\""
        ));
    }
    #[test]
    fn prop_checkInexplicablyUnquoted6() {
        assert!(!node_emits(
            check_inexplicably_unquoted,
            "\"$dir\"some_stuff\"$file\""
        ));
    }
    #[test]
    fn prop_checkInexplicablyUnquoted7() {
        assert!(!node_emits(
            check_inexplicably_unquoted,
            "${dir/\"foo\"/\"bar\"}"
        ));
    }
    #[test]
    fn prop_checkInexplicablyUnquoted8() {
        assert!(!node_emits(
            check_inexplicably_unquoted,
            "  'foo'\\\n  'bar'"
        ));
    }
    #[test]
    fn prop_checkInexplicablyUnquoted9() {
        assert!(!node_emits(
            check_inexplicably_unquoted,
            "[[ $x =~ \"foo\"(\"bar\"|\"baz\") ]]"
        ));
    }
    #[test]
    fn prop_checkInexplicablyUnquoted10() {
        assert!(!node_emits(
            check_inexplicably_unquoted,
            "cmd ${x+--name=\"$x\" --output=\"$x.out\"}"
        ));
    }
    #[test]
    fn prop_checkInexplicablyUnquoted11() {
        assert!(!node_emits(
            check_inexplicably_unquoted,
            "echo \"foo\"/\"bar\""
        ));
    }
    #[test]
    fn prop_checkInexplicablyUnquoted12() {
        assert!(!node_emits(
            check_inexplicably_unquoted,
            "declare \"foo\"=\"bar\""
        ));
    }

    // ---- SC2083 checkLonelyDotDash ----
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
    fn prop_checkSpuriousExpansion1() {
        assert!(node_emits(
            check_spurious_expansion,
            "if $(true); then true; fi"
        ));
    }
    #[test]
    fn prop_checkSpuriousExpansion3() {
        assert!(!node_emits(
            check_spurious_expansion,
            "$(cmd) --flag1 --flag2"
        ));
    }
    #[test]
    fn prop_checkSpuriousExpansion4() {
        assert!(node_emits(check_spurious_expansion, "$((i++))"));
    }

    // ---- SC2007 checkDollarBrackets ----
    #[test]
    fn prop_checkDollarBrackets1() {
        assert!(node_emits(check_dollar_brackets, "echo $[1+2]"));
    }
    #[test]
    fn prop_checkDollarBrackets2() {
        assert!(!node_emits(check_dollar_brackets, "echo $((1+2))"));
    }

    // ---- SC2087 checkSshHereDoc ----
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
    fn prop_checkPrefixAssign1() {
        assert!(node_emits(
            check_prefix_assignment_reference,
            "var=foo echo $var"
        ));
    }
    #[test]
    fn prop_checkPrefixAssign2() {
        assert!(!node_emits(
            check_prefix_assignment_reference,
            "var=$(echo $var) cmd"
        ));
    }

    // ---- SC2247 checkDollarQuoteParen ----
    #[test]
    fn prop_checkDollarQuoteParen1() {
        assert!(node_emits(check_dollar_quote_paren, "$\"(foo)\""));
    }
    #[test]
    fn prop_checkDollarQuoteParen2() {
        assert!(node_emits(check_dollar_quote_paren, "$\"{foo}\""));
    }
    #[test]
    fn prop_checkDollarQuoteParen3() {
        assert!(!node_emits(check_dollar_quote_paren, "\"$(foo)\""));
    }
    #[test]
    fn prop_checkDollarQuoteParen4() {
        assert!(!node_emits(check_dollar_quote_paren, "$\"..\""));
    }

    // ---- SC2256 checkTranslatedStringVariable ----
    #[test]
    fn prop_checkTranslatedStringVariable1() {
        assert!(node_emits(
            check_translated_string_variable,
            "foo_bar2=val; $\"foo_bar2\""
        ));
    }
    #[test]
    fn prop_checkTranslatedStringVariable2() {
        assert!(!node_emits(
            check_translated_string_variable,
            "$\"foo_bar2\""
        ));
    }
    #[test]
    fn prop_checkTranslatedStringVariable3() {
        assert!(!node_emits(check_translated_string_variable, "$\"..\""));
    }
    #[test]
    fn prop_checkTranslatedStringVariable4() {
        assert!(!node_emits(
            check_translated_string_variable,
            "var=val; $\"$var\""
        ));
    }
    #[test]
    fn prop_checkTranslatedStringVariable5() {
        assert!(!node_emits(
            check_translated_string_variable,
            "foo=var; bar=val2; $\"foo bar\""
        ));
    }

    // ---- SC2188/2189 checkRedirectedNowhere ----
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
    fn prop_checkArrayAssignmentIndices1() {
        assert!(tree_emits(
            check_array_assignment_indices,
            "declare -A foo; foo=(bar)"
        ));
    }
    #[test]
    fn prop_checkArrayAssignmentIndices2() {
        assert!(!tree_emits(
            check_array_assignment_indices,
            "declare -a foo; foo=(bar)"
        ));
    }
    #[test]
    fn prop_checkArrayAssignmentIndices3() {
        assert!(!tree_emits(
            check_array_assignment_indices,
            "declare -A foo; foo=([i]=bar)"
        ));
    }
    #[test]
    fn prop_checkArrayAssignmentIndices4() {
        assert!(tree_emits(
            check_array_assignment_indices,
            "typeset -A foo; foo+=(bar)"
        ));
    }
    #[test]
    fn prop_checkArrayAssignmentIndices5() {
        assert!(tree_emits(
            check_array_assignment_indices,
            "arr=( [foo]= bar )"
        ));
    }
    #[test]
    fn prop_checkArrayAssignmentIndices6() {
        assert!(tree_emits(
            check_array_assignment_indices,
            "arr=( [foo] = bar )"
        ));
    }
    #[test]
    fn prop_checkArrayAssignmentIndices7() {
        assert!(!tree_emits(
            check_array_assignment_indices,
            "arr=( var=value )"
        ));
    }
    #[test]
    fn prop_checkArrayAssignmentIndices8() {
        assert!(!tree_emits(
            check_array_assignment_indices,
            "arr=( [foo]=bar )"
        ));
    }
    #[test]
    fn prop_checkArrayAssignmentIndices9() {
        assert!(!tree_emits(
            check_array_assignment_indices,
            "arr=( [foo]=\"\" )"
        ));
    }
    #[test]
    fn prop_checkArrayAssignmentIndices10() {
        assert!(tree_emits(
            check_array_assignment_indices,
            "declare -A arr; arr=( var=value )"
        ));
    }
    #[test]
    fn prop_checkArrayAssignmentIndices11() {
        assert!(tree_emits(
            check_array_assignment_indices,
            "arr=( 1=value )"
        ));
    }
    #[test]
    fn prop_checkArrayAssignmentIndices12() {
        assert!(tree_emits(
            check_array_assignment_indices,
            "arr=( $a=value )"
        ));
    }
    #[test]
    fn prop_checkArrayAssignmentIndices13() {
        assert!(tree_emits(
            check_array_assignment_indices,
            "arr=( $((1+1))=value )"
        ));
    }

    // ---- SC2295 checkUnquotedParameterExpansionPattern ----
    #[test]
    fn prop_checkUnquotedParameterExpansionPattern1() {
        assert!(node_emits(
            check_unquoted_parameter_expansion_pattern,
            "echo \"${var#$x}\""
        ));
    }
    #[test]
    fn prop_checkUnquotedParameterExpansionPattern2() {
        assert!(node_emits(
            check_unquoted_parameter_expansion_pattern,
            "echo \"${var%%$(x)}\""
        ));
    }
    #[test]
    fn prop_checkUnquotedParameterExpansionPattern3() {
        assert!(!node_emits(
            check_unquoted_parameter_expansion_pattern,
            "echo \"${var[#$x]}\""
        ));
    }
    #[test]
    fn prop_checkUnquotedParameterExpansionPattern4() {
        assert!(!node_emits(
            check_unquoted_parameter_expansion_pattern,
            "echo \"${var%\"$x\"}\""
        ));
    }

    // ---- SC2302/2303 checkArrayValueUsedAsIndex ----
    #[test]
    fn prop_checkArrayValueUsedAsIndex1() {
        assert!(tree_emits(
            check_array_value_used_as_index,
            "for i in ${arr[@]}; do echo ${arr[i]}; done"
        ));
    }
    #[test]
    fn prop_checkArrayValueUsedAsIndex2() {
        assert!(tree_emits(
            check_array_value_used_as_index,
            "for i in ${arr[@]}; do echo ${arr[$i]}; done"
        ));
    }
    #[test]
    fn prop_checkArrayValueUsedAsIndex3() {
        assert!(tree_emits(
            check_array_value_used_as_index,
            "for i in ${arr[@]}; do echo $((arr[i])); done"
        ));
    }
    #[test]
    fn prop_checkArrayValueUsedAsIndex4() {
        assert!(tree_emits(
            check_array_value_used_as_index,
            "for i in ${arr1[@]} ${arr2[@]}; do echo ${arr1[$i]}; done"
        ));
    }
    #[test]
    fn prop_checkArrayValueUsedAsIndex5() {
        assert!(tree_emits(
            check_array_value_used_as_index,
            "for i in ${arr1[@]} ${arr2[@]}; do echo ${arr2[$i]}; done"
        ));
    }
    #[test]
    fn prop_checkArrayValueUsedAsIndex7() {
        assert!(!tree_emits(
            check_array_value_used_as_index,
            "for i in ${arr[@]}; do echo ${arr[K]}; done"
        ));
    }
    #[test]
    fn prop_checkArrayValueUsedAsIndex8() {
        assert!(!tree_emits(
            check_array_value_used_as_index,
            "for i in ${arr[@]}; do i=42; echo ${arr[i]}; done"
        ));
    }
    #[test]
    fn prop_checkArrayValueUsedAsIndex9() {
        assert!(!tree_emits(
            check_array_value_used_as_index,
            "for i in ${arr[@]}; do echo ${arr2[i]}; done"
        ));
    }
}
