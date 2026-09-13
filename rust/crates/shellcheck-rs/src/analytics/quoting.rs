//! Quoting and word-splitting checks from `ShellCheck.Analytics`.
use super::common::*;
use crate::analyzer_lib::assignment_is_quoting;
use crate::analyzer_lib::get_closest_command;
use crate::analyzer_lib::get_command_basename;
use crate::analyzer_lib::get_command_name;
use crate::analyzer_lib::is_array_expansion;
use crate::analyzer_lib::is_quote_free;
use crate::analyzer_lib::is_quote_free_element;
use crate::analyzer_lib::simple_command_words;
use crate::analyzer_lib::*;
use crate::ast::*;
use crate::ast_lib;
use crate::ast_lib::get_word_parts;
use crate::ast_lib::oversimplify;
use crate::ast_lib::will_split;
use crate::cfg;
use crate::cfg::get_braced_modifier;
use crate::cfg::is_variable_char;
use crate::cfg::will_become_multiple_args;
use crate::cfg::will_concat_in_assignment;
use crate::data::VARIABLES_WITHOUT_SPACES;
use crate::interface::Shell;
use std::collections::HashMap;

pub(super) fn check_quotes_in_literals(params: &Parameters, _root: &Token, out: &mut Out) {
    let suggestion = if supports_arrays(params.shell) {
        "Use an array."
    } else {
        "Rewrite using set/\"$@\" or functions."
    };
    let mut quote_map: HashMap<String, Id> = HashMap::new();

    for sd in &params.variable_flow {
        match sd {
            // writeF _ _ name (DataString (SourceFrom values))
            StackData::Assignment(
                _base,
                _place,
                name,
                DataType::DataString(DataSource::SourceFrom(values)),
            ) => {
                let quoted = values.iter().find_map(|v| for_token(&quote_map, v));
                match quoted {
                    Some(x) => {
                        quote_map.insert(name.clone(), x);
                    }
                    None => {
                        quote_map.remove(name);
                    }
                }
            }
            // writeF _ _ _ _ = return []  (no state change)
            StackData::Assignment(..) => {}
            // readF _ expr name
            StackData::Reference(_base, expr, name) => {
                if let Some(&j) = quote_map.get(name) {
                    if !is_param_to(params, "eval", expr)
                        && !is_quote_free(params, expr)
                        && !squashes_quotes(expr)
                    {
                        warn(
                            out,
                            j,
                            2089,
                            &format!(
                                "Quotes/backslashes will be treated literally. {}",
                                suggestion
                            ),
                        );
                        warn(
                            out,
                            expr.id(),
                            2090,
                            "Quotes/backslashes in this variable will not be respected.",
                        );
                    }
                }
            }
            _ => {}
        }
    }
}

pub(super) fn check_dollar_star(params: &Parameters, t: &Token, out: &mut Out) {
    if let InnerToken::T_NormalWord(parts) = &*t.inner {
        if parts.len() != 1 {
            return;
        }
        if let InnerToken::T_DollarBraced { op, .. } = &*parts[0].inner {
            if is_strictly_quote_free(params, t) {
                return;
            }
            let id = parts[0].id();
            let s = oversimplify(op).concat();
            if s.starts_with('*') {
                warn(
                    out,
                    id,
                    2048,
                    "Use \"$@\" (with quotes) to prevent whitespace problems.",
                );
            }
            let head = s.chars().next().unwrap_or('!');
            if get_braced_modifier(&s).starts_with("[*]") && is_variable_char(head) {
                warn(
                    out,
                    id,
                    2048,
                    "Use \"${array[@]}\" (with quotes) to prevent whitespace problems.",
                );
            }
        }
    }
}

pub(super) fn check_unquoted_dollar_at(params: &Parameters, t: &Token, out: &mut Out) {
    if let InnerToken::T_NormalWord(parts) = &*t.inner {
        if is_strictly_quote_free(params, t) {
            return;
        }
        if let Some(x) = parts.iter().find(|p| is_array_expansion(p)) {
            if !is_quoted_alternative_reference(x) {
                err(
                    out,
                    x.id(),
                    2068,
                    "Double quote array expansions to avoid re-splitting elements.",
                );
            }
        }
    }
}

pub(super) fn check_unquoted_n(_params: &Parameters, t: &Token, out: &mut Out) {
    if let InnerToken::TC_Unary { typ, op, token } = &*t.inner {
        if *typ == ConditionType::SingleBracket
            && op == "-n"
            && will_split(token)
            && !get_word_parts(token).iter().any(|p| is_array_expansion(p))
        {
            err(
                out,
                token.id(),
                2070,
                "-n doesn't work with unquoted arguments. Quote or use [[ ]].",
            );
        }
    }
}

/// `checkBackticks` (SC2006): legacy backticks -> `$(...)`, with a fix.
pub(super) fn check_backticks(params: &Parameters, t: &Token, out: &mut Out) {
    if let InnerToken::T_Backticked(list) = &*t.inner {
        if !list.is_empty() {
            let fix = fix_with(vec![
                replace_start(params, t.id(), 1, "$("),
                replace_end(params, t.id(), 1, ")"),
            ]);
            style_with_fix(
                out,
                t.id(),
                2006,
                "Use $(...) notation instead of legacy backticks `...`.",
                fix,
            );
        }
    }
}

/// The full checkInexplicablyUnquoted (emits 2026, 2027, 2140).
pub(super) fn check_inexplicably_unquoted(params: &Parameters, t: &Token, out: &mut Out) {
    if let InnerToken::T_NormalWord(tokens) = &*t.inner {
        for start in 0..tokens.len() {
            iu_check(params, &tokens[start..], out);
        }
    }
}

pub(super) fn check_tilde_in_quotes(_params: &Parameters, t: &Token, out: &mut Out) {
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

pub(super) fn check_spurious_expansion(_params: &Parameters, t: &Token, out: &mut Out) {
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

pub(super) fn check_unquoted_expansions(p: &Parameters, t: &Token, out: &mut Out) {
    use InnerToken::*;
    let contents: &[Token] = match &*t.inner {
        T_DollarExpansion(c) => c,
        T_Backticked(c) => c,
        T_DollarBraceCommandExpansion { list, .. } => list,
        _ => return,
    };
    if contents.is_empty() {
        return;
    }
    if should_be_split(t) || is_quote_free(p, t) || used_as_command_name(p, t) {
        return;
    }
    warn(out, t.id(), 2046, "Quote this to prevent word splitting.");
}

pub(super) fn check_single_quoted_variables(params: &Parameters, t: &Token, out: &mut Out) {
    let s = match &*t.inner {
        InnerToken::T_SingleQuoted(s) => s,
        _ => return,
    };
    if !matches_expansion_re(s) {
        return;
    }

    let closest = get_closest_command(params, t);

    let command_name: String = closest
        .and_then(|cmd| get_command_basename(cmd).map(|name| (cmd, name)))
        .map(|(cmd, name)| {
            if name == "find" {
                get_find_command(cmd)
            } else if name == "git" {
                get_git_command(cmd)
            } else if name == "mumps" {
                get_mumps_command(cmd)
            } else {
                name
            }
        })
        .unwrap_or_default();

    let show = |out: &mut Out| {
        info(
            out,
            t.id(),
            2016,
            "Expressions don't expand in single quotes, use double quotes for that.",
        );
    };

    if command_name == "sed" {
        if !matches_sed_contra(s) {
            show(out);
        }
        return;
    }

    // isProbablyOk
    let ok_assignment = {
        // any isOkAssignment (NE.take 3 $ getPath parents t)
        let mut ok = false;
        let mut cur = Some(t);
        for _ in 0..3 {
            match cur {
                Some(node) => {
                    match &*node.inner {
                        InnerToken::T_Assignment { var, .. }
                            if SC2016_COMMONLY_QUOTED.contains(&var.as_str()) =>
                        {
                            ok = true;
                            break;
                        }
                        InnerToken::TC_Unary { op, .. } if op == "-v" => {
                            ok = true;
                            break;
                        }
                        _ => {}
                    }
                    cur = params.parent(node);
                }
                None => break,
            }
        }
        ok
    };

    let is_probably_ok = ok_assignment
        || SC2016_OK_COMMANDS.contains(&command_name.as_str())
        || command_name.ends_with("awk")
        || command_name.starts_with("perl");

    if !is_probably_ok {
        show(out);
    }
}

pub(super) fn check_array_as_string(_params: &Parameters, t: &Token, out: &mut Out) {
    if let InnerToken::T_Assignment { value, .. } = &*t.inner {
        if will_concat_in_assignment(value) {
            warn(
                out,
                value.id(),
                2124,
                "Assigning an array to a string! Assign as array, or use * instead of @ to concatenate.",
            );
        } else if will_become_multiple_args(value) {
            warn(
                out,
                value.id(),
                2125,
                "Brace expansions and globs are literal in assignments. Quote it or use an array.",
            );
        }
    }
}

pub(super) fn check_concatenated_dollar_at(params: &Parameters, word: &Token, out: &mut Out) {
    if !matches!(&*word.inner, InnerToken::T_NormalWord(_)) {
        return;
    }
    let mut parts: Vec<&Token> = Vec::new();
    parts.extend(get_word_parts(word));
    // Guard: not quote-free AND more than one part.
    if is_quote_free(params, word) || parts.len() <= 1 {
        return;
    }
    if let Some(array) = parts.iter().find(|p| is_array_expansion(p)) {
        err(
            out,
            array.id(),
            2145,
            "Argument mixes string and array. Use * or separate argument.",
        );
    }
}

pub(super) fn check_tilde_in_path(_params: &Parameters, t: &Token, out: &mut Out) {
    let InnerToken::T_SimpleCommand { assignments, .. } = &*t.inner else {
        return;
    };
    for var in assignments {
        let InnerToken::T_Assignment {
            mode,
            var: name,
            indices,
            value,
        } = &*var.inner
        else {
            continue;
        };
        if *mode != AssignmentMode::Assign || name != "PATH" || !indices.is_empty() {
            continue;
        }
        let InnerToken::T_NormalWord(parts) = &*value.inner else {
            continue;
        };
        let is_quoted = |x: &Token| {
            matches!(
                &*x.inner,
                InnerToken::T_DoubleQuoted(_) | InnerToken::T_SingleQuoted(_)
            )
        };
        let has_tilde = |x: &Token| ast_lib::only_literal_string(x).contains('~');
        if parts.iter().any(|x| is_quoted(x) && has_tilde(x)) {
            warn(
                out,
                var.id(),
                2147,
                "Literal tilde in PATH works poorly across programs.",
            );
        }
    }
}

pub(super) fn check_splitting_in_arrays(params: &Parameters, t: &Token, out: &mut Out) {
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

pub(super) fn check_dollar_quote_paren(params: &Parameters, t: &Token, out: &mut Out) {
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

pub(super) fn check_translated_string_variable(params: &Parameters, t: &Token, out: &mut Out) {
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

pub(super) fn check_unquoted_parameter_expansion_pattern(
    params: &Parameters,
    x: &Token,
    out: &mut Out,
) {
    if let InnerToken::T_DollarBraced { braced: true, op } = &*x.inner
        && let InnerToken::T_NormalWord(word_parts) = &*op.inner
    {
        // T_NormalWord _ (T_Literal _ s : rest@(_:_))
        if word_parts.len() >= 2 && matches!(&*word_parts[0].inner, InnerToken::T_Literal(_)) {
            let modifier = cfg::get_braced_modifier(&ast_lib::oversimplify_concat(op));
            if modifier.starts_with('%') || modifier.starts_with('#') {
                for r in &word_parts[1..] {
                    upep_check(params, r, out);
                }
            }
        }
    }
}

/// `isQuotedAlternativeReference`: matches the regex `(^|\])​:?\+` on the modifier.
fn is_quoted_alternative_reference(t: &Token) -> bool {
    match &*t.inner {
        InnerToken::T_DollarBraced { op, .. } => {
            let modifier = get_braced_modifier(&oversimplify(op).concat());
            matches_alternative_regex(&modifier)
        }
        _ => false,
    }
}

/// Search for `(^|\])​:?\+`: at start or after a `]`, an optional `:` then `+`.
fn matches_alternative_regex(m: &str) -> bool {
    // `^:?\+`
    if m.starts_with('+') || m.starts_with(":+") {
        return true;
    }
    // `\]:?\+`
    let bytes = m.as_bytes();
    for i in 0..bytes.len() {
        if bytes[i] == b']' {
            let mut j = i + 1;
            if j < bytes.len() && bytes[j] == b':' {
                j += 1;
            }
            if j < bytes.len() && bytes[j] == b'+' {
                return true;
            }
        }
    }
    false
}

/// `isQuoteFreeContext` with `strict = True` (so for/select contexts are NOT
/// treated as quoting).
fn is_quote_free_context_strict(params: &Parameters, t: &Token) -> Option<bool> {
    use ConditionType::DoubleBracket;
    match &*t.inner {
        InnerToken::TC_Nullary {
            typ: DoubleBracket, ..
        } => Some(true),
        InnerToken::TC_Unary {
            typ: DoubleBracket, ..
        } => Some(true),
        InnerToken::TC_Binary {
            typ: DoubleBracket, ..
        } => Some(true),
        InnerToken::TA_Sequence(_) => Some(true),
        InnerToken::T_Arithmetic(_) => Some(true),
        InnerToken::T_Assignment { .. } => Some(assignment_is_quoting(params, t)),
        InnerToken::T_Redirecting { .. } => Some(false),
        InnerToken::T_DoubleQuoted(_) => Some(true),
        InnerToken::T_DollarDoubleQuoted(_) => Some(true),
        InnerToken::T_CaseExpression { .. } => Some(true),
        InnerToken::T_HereDoc { .. } => Some(true),
        InnerToken::T_DollarBraced { .. } => Some(true),
        // strict = True.
        InnerToken::T_ForIn { .. } => Some(false),
        InnerToken::T_SelectIn { .. } => Some(false),
        _ => None,
    }
}

fn is_strictly_quote_free(params: &Parameters, t: &Token) -> bool {
    if is_quote_free_element(params, t) {
        return true;
    }
    // msum over the ancestors (NE.tail of getPath): first `Just` wins.
    let mut cur = t;
    while let Some(p) = params.parent(cur) {
        if let Some(v) = is_quote_free_context_strict(params, p) {
            return v;
        }
        cur = p;
    }
    false
}

/// `re = \$[{(0-9a-zA-Z_]|`[^`]+``
fn matches_expansion_re(s: &str) -> bool {
    let bytes = s.as_bytes();
    for i in 0..bytes.len() {
        if bytes[i] == b'$' {
            if let Some(&c) = bytes.get(i + 1) {
                let ch = c as char;
                if ch == '{' || ch == '(' || ch.is_ascii_alphanumeric() || ch == '_' {
                    return true;
                }
            }
        }
        if bytes[i] == b'`' {
            // `[^`]+`
            let mut j = i + 1;
            let mut count = 0;
            while j < bytes.len() && bytes[j] != b'`' {
                j += 1;
                count += 1;
            }
            if count > 0 && j < bytes.len() && bytes[j] == b'`' {
                return true;
            }
        }
    }
    false
}

/// `sedContra = \$[{dpsaic]($|[^a-zA-Z])`
fn matches_sed_contra(s: &str) -> bool {
    let bytes = s.as_bytes();
    for i in 0..bytes.len() {
        if bytes[i] == b'$' {
            if let Some(&c) = bytes.get(i + 1) {
                if matches!(c, b'{' | b'd' | b'p' | b's' | b'a' | b'i' | b'c') {
                    match bytes.get(i + 2) {
                        None => return true,
                        Some(&after) => {
                            if !(after as char).is_ascii_alphabetic() {
                                return true;
                            }
                        }
                    }
                }
            }
        }
    }
    false
}

fn get_find_command(cmd: &Token) -> String {
    let words = match simple_command_words(cmd) {
        Some(w) => w,
        None => return "find".to_string(),
    };
    let lits: Vec<Option<String>> = words.iter().map(ast_lib::get_literal_string).collect();
    let exec_flags = ["-exec", "-execdir", "-ok", "-okdir"];
    // dropWhile (not in exec_flags)
    let start = lits.iter().position(|x| {
        x.as_deref()
            .map(|s| exec_flags.contains(&s))
            .unwrap_or(false)
    });
    match start {
        Some(idx) => {
            // cmd is at idx+1 (flag:cmd:rest)
            match lits.get(idx + 1) {
                Some(Some(c)) => c.clone(),
                _ => "find".to_string(),
            }
        }
        None => "find".to_string(),
    }
}

fn get_git_command(cmd: &Token) -> String {
    if let Some(words) = simple_command_words(cmd) {
        let lits: Vec<Option<String>> = words.iter().map(ast_lib::get_literal_string).collect();
        if lits.first().and_then(|x| x.as_deref()) == Some("git")
            && lits.get(1).and_then(|x| x.as_deref()) == Some("filter-branch")
        {
            return "git filter-branch".to_string();
        }
    }
    "git".to_string()
}

fn get_mumps_command(cmd: &Token) -> String {
    if let Some(words) = simple_command_words(cmd) {
        let lits: Vec<Option<String>> = words.iter().map(ast_lib::get_literal_string).collect();
        if lits.first().and_then(|x| x.as_deref()) == Some("mumps")
            && lits.get(1).and_then(|x| x.as_deref()) == Some("-run")
        {
            match lits.get(2).and_then(|x| x.as_deref()) {
                Some("%XCMD") => return "mumps -run %XCMD".to_string(),
                Some("LOOP%XCMD") => return "mumps -run LOOP%XCMD".to_string(),
                _ => {}
            }
        }
    }
    "mumps".to_string()
}

const SC2016_OK_COMMANDS: &[&str] = &[
    "trap",
    "sh",
    "bash",
    "ksh",
    "zsh",
    "ssh",
    "eval",
    "xprop",
    "alias",
    "sudo",
    "doas",
    "run0",
    "docker",
    "podman",
    "oc",
    "dpkg-query",
    "jq",
    "rename",
    "rg",
    "unset",
    "git filter-branch",
    "mumps -run %XCMD",
    "mumps -run LOOP%XCMD",
];

const SC2016_COMMONLY_QUOTED: &[&str] = &["PS1", "PS2", "PS3", "PS4", "PROMPT_COMMAND"];

/// `getCommandNameFromExpansion`: if a substitution is a single command, its name.
fn get_command_name_from_expansion(t: &Token) -> Option<String> {
    use InnerToken::*;
    let list: &[Token] = match &*t.inner {
        T_DollarExpansion(l) if l.len() == 1 => l,
        T_Backticked(l) if l.len() == 1 => l,
        T_DollarBraceCommandExpansion { list, .. } if list.len() == 1 => list,
        _ => return None,
    };
    match &*list[0].inner {
        T_Pipeline { commands, .. } if commands.len() == 1 => get_command_name(&commands[0]),
        _ => None,
    }
}

/// `usedAsCommandName`: is the token the first word of a T_SimpleCommand?
fn used_as_command_name(p: &Parameters, token: &Token) -> bool {
    use InnerToken::*;
    let mut current_id = token.id();
    let mut node = p.parent(token);
    while let Some(t) = node {
        match &*t.inner {
            T_NormalWord(list) if list.len() == 1 && list[0].id() == current_id => {
                current_id = t.id();
                node = p.parent(t);
            }
            T_DoubleQuoted(list) if list.len() == 1 && list[0].id() == current_id => {
                current_id = t.id();
                node = p.parent(t);
            }
            T_SimpleCommand { words, .. } if !words.is_empty() => {
                return words[0].id() == current_id
                    || get_command_token_or_this(t).id() == current_id;
            }
            _ => return false,
        }
    }
    false
}

fn should_be_split(t: &Token) -> bool {
    matches!(
        get_command_name_from_expansion(t).as_deref(),
        Some("seq") | Some("pgrep")
    )
}

/// `supportsArrays`.
fn supports_arrays(shell: Shell) -> bool {
    matches!(shell, Shell::Bash | Shell::Ksh)
}

/// `containsQuotes s`: regex `"|([/= ]|^)'|'( |$)|\\ `.
fn contains_quotes(s: &str) -> bool {
    let b: Vec<char> = s.chars().collect();
    if b.contains(&'"') {
        return true;
    }
    for (i, &c) in b.iter().enumerate() {
        if c == '\'' {
            let prev_ok = i == 0 || matches!(b[i - 1], '/' | '=' | ' ');
            let next_ok = i + 1 == b.len() || b[i + 1] == ' ';
            if prev_ok || next_ok {
                return true;
            }
        }
        if c == '\\' && i + 1 < b.len() && b[i + 1] == ' ' {
            return true;
        }
    }
    false
}

/// `forToken quoteMap t`.
fn for_token(map: &HashMap<String, Id>, t: &Token) -> Option<Id> {
    match &*t.inner {
        // skip getBracedReference here to avoid false positives on PE
        InnerToken::T_DollarBraced { op, .. } => map.get(&oversimplify(op).concat()).copied(),
        InnerToken::T_DoubleQuoted(tokens) | InnerToken::T_NormalWord(tokens) => {
            tokens.iter().find_map(|x| for_token(map, x))
        }
        _ => {
            if contains_quotes(&oversimplify(t).concat()) {
                Some(t.id())
            } else {
                None
            }
        }
    }
}

/// `squashesQuotes t`: a `${#...}` length reference.
fn squashes_quotes(t: &Token) -> bool {
    if let InnerToken::T_DollarBraced { op, .. } = &*t.inner {
        oversimplify(op).concat().starts_with('#')
    } else {
        false
    }
}

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
                crate::cfg::get_braced_reference(&crate::ast_lib::oversimplify(op).concat());
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

fn tiq_verify(id: Id, str: &str, out: &mut Out) {
    if str.starts_with("~/") {
        warn(out, id, 2088, "Tilde does not expand in quotes. Use $HOME.");
    }
}

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

/// `unbracedVariables`: the names that never need braces -- the special
/// variables, and the single-digit positionals.
fn is_unbraced_variable(name: &str) -> bool {
    crate::data::SPECIAL_VARIABLES_WITHOUT_SPACES.contains(&name)
        || name == "@"
        || name == "*"
        || (name.len() == 1 && name.chars().all(|c| c.is_ascii_digit()))
}

/// `checkVariableBraces` (optional: `require-variable-braces`).
pub(super) fn check_variable_braces(params: &Parameters, t: &Token, out: &mut Out) {
    let InnerToken::T_DollarBraced { braced: false, op } = &*t.inner else {
        return;
    };
    let name = crate::cfg::get_braced_reference(&crate::ast_lib::oversimplify(op).concat());
    if is_unbraced_variable(&name) || super::flow::quotes_may_conflict_with_sc2281(params, t) {
        return;
    }
    let fix = fix_with(vec![
        replace_start(params, t.id(), 1, "${"),
        replace_end(params, t.id(), 0, "}"),
    ]);
    style_with_fix(
        out,
        t.id(),
        2250,
        "Prefer putting braces around variable references even when not strictly required.",
        fix,
    );
}

#[cfg(test)]
#[allow(non_snake_case)]
mod tests {
    use super::*;
    use crate::test_support::*;

    #[test]
    fn prop_CheckVariableBraces1_5() {
        assert!(emits(check_variable_braces, "a='123'; echo $a"));
        for s in [
            "a='123'; echo ${a}",
            "#shellcheck disable=SC2016\necho '$a'",
            "echo $* $1",
            "$foo=42",
        ] {
            assert!(!emits(check_variable_braces, s), "{s}");
        }
    }

    #[test]
    fn prop_checkQuotesInLiterals1() {
        assert!(tree_emits(
            check_quotes_in_literals,
            "param='--foo=\"bar\"'; app $param"
        ));
    }

    #[test]
    fn prop_checkQuotesInLiterals1a() {
        assert!(tree_emits(
            check_quotes_in_literals,
            "param=\"--foo='lolbar'\"; app $param"
        ));
    }

    #[test]
    fn prop_checkQuotesInLiterals2() {
        assert!(!tree_emits(
            check_quotes_in_literals,
            "param='--foo=\"bar\"'; app \"$param\""
        ));
    }

    #[test]
    fn prop_checkQuotesInLiterals3() {
        assert!(!tree_emits(
            check_quotes_in_literals,
            "param=('--foo='); app \"${param[@]}\""
        ));
    }

    #[test]
    fn prop_checkQuotesInLiterals4() {
        assert!(!tree_emits(
            check_quotes_in_literals,
            "param=\"don't bother with this one\"; app $param"
        ));
    }

    #[test]
    fn prop_checkQuotesInLiterals5() {
        assert!(!tree_emits(
            check_quotes_in_literals,
            "param=\"--foo='lolbar'\"; eval app $param"
        ));
    }

    #[test]
    fn prop_checkQuotesInLiterals6() {
        assert!(tree_emits(
            check_quotes_in_literals,
            "param='my\\ file'; cmd=\"rm $param\"; $cmd"
        ));
    }

    #[test]
    fn prop_checkQuotesInLiterals6a() {
        assert!(!tree_emits(
            check_quotes_in_literals,
            "param='my\\ file'; cmd=\"rm ${#param}\"; $cmd"
        ));
    }

    #[test]
    fn prop_checkQuotesInLiterals7() {
        assert!(tree_emits(
            check_quotes_in_literals,
            "param='my\\ file'; rm $param"
        ));
    }

    #[test]
    fn prop_checkQuotesInLiterals8() {
        assert!(tree_emits(
            check_quotes_in_literals,
            "param=\"/foo/'bar baz'/etc\"; rm $param"
        ));
    }

    #[test]
    fn prop_checkQuotesInLiterals9() {
        assert!(!tree_emits(
            check_quotes_in_literals,
            "param=\"/foo/'bar baz'/etc\"; rm ${#param}"
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
    fn prop_checkTildeInPath1() {
        assert!(emits(check_tilde_in_path, "PATH=\"$PATH:~/bin\""));
    }

    #[test]
    fn prop_checkTildeInPath2() {
        assert!(emits(check_tilde_in_path, "PATH='~foo/bin'"));
    }

    #[test]
    fn prop_checkTildeInPath3() {
        assert!(!emits(check_tilde_in_path, "PATH=~/bin"));
    }

    // ---- checkUnsupported ----

    #[test]
    fn prop_checkUnquotedN() {
        assert!(produces(
            check_unquoted_n,
            "if [ -n $foo ]; then echo cow; fi"
        ));
    }

    #[test]
    fn prop_checkUnquotedN2() {
        assert!(produces(check_unquoted_n, "[ -n $cow ]"));
    }

    #[test]
    fn prop_checkUnquotedN3() {
        assert!(!produces(check_unquoted_n, "[[ -n $foo ]] && echo cow"));
    }

    #[test]
    fn prop_checkUnquotedN4() {
        assert!(produces(check_unquoted_n, "[ -n $cow -o -t 1 ]"));
    }

    #[test]
    fn prop_checkUnquotedN5() {
        assert!(!produces(check_unquoted_n, "[ -n \"$@\" ]"));
    }

    // checkSourceArgs (SC2240)
}
