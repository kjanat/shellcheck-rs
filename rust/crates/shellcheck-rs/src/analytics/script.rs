//! Script-structure checks (shebang, functions, aliases, reachability) from `ShellCheck.Analytics`.
use super::common::*;
use crate::analyzer_lib::is_array_expansion;
use crate::analyzer_lib::is_sourced;
use crate::analyzer_lib::is_unqualified_command;
use crate::analyzer_lib::*;
use crate::ast::*;
use crate::astlib;
use crate::astlib::basename;
use crate::astlib::e4m;
use crate::astlib::get_command_sequences;
use crate::astlib::get_literal_string_def;
use crate::astlib::get_word_parts;
use crate::astlib::is_command_substitution;
use crate::astlib::oversimplify;
use crate::cfg::get_braced_modifier;
use crate::cfg::get_unquoted_literal;
use crate::cfg::is_variable_name;
use crate::interface::Shell;
use std::collections::BTreeMap;
use std::collections::HashMap;

pub(super) fn check_shebang_parameters(_params: &Parameters, t: &Token, out: &mut Out) {
    match &*t.inner {
        InnerToken::T_Annotation { token, .. } => check_shebang_parameters(_params, token, out),
        InnerToken::T_Script { shebang, .. } => {
            if let InnerToken::T_Literal(sb) = &*shebang.inner {
                use std::sync::OnceLock;
                static RE: OnceLock<regex::Regex> = OnceLock::new();
                let re = RE.get_or_init(|| regex::Regex::new(r"env +(-S|--split-string)").unwrap());
                let is_multi_word = sb.split_whitespace().count() > 2 && !re.is_match(sb);
                if is_multi_word {
                    err(
                        out,
                        shebang.id(),
                        2096,
                        "On most OS, shebangs can only specify a single parameter.",
                    );
                }
            }
        }
        _ => {}
    }
}

pub(super) fn check_functions_used_externally(params: &Parameters, root: &Token, out: &mut Out) {
    let functions_aliases = functions_and_aliases(root);

    let pattern_context = |id: Id| -> String {
        match params.token_positions.get(&id) {
            Some((start, _)) => format!(" on line {}.", start.line),
            None => ".".to_string(),
        }
    };

    root.visit_preorder(&mut |t| {
        let argv = match &*t.inner {
            InnerToken::T_SimpleCommand { words, .. } => words,
            _ => return,
        };
        let name_str = match get_command_name(t) {
            Some(s) => s,
            None => return,
        };
        let cmd_token = get_command_token_or_this(t);
        let name = basename(&name_str);
        let args = skip_over(cmd_token, argv);
        let arg_strings: Vec<(String, Token)> =
            args.iter().map(|x| (astlib::only_literal_string(x), x.clone())).collect();
        let candidates = get_potential_commands(&name, &arg_strings);
        let cmd_id = cmd_token.id();
        for (_, arg) in candidates {
            if let Some(literal_arg) = get_unquoted_literal(arg) {
                if let Some(&definition_id) = functions_aliases.get(&literal_arg) {
                    warn(
                        out,
                        arg.id(),
                        2033,
                        "Shell functions can't be passed to external commands. Use separate script or sh -c.",
                    );
                    info(
                        out,
                        definition_id,
                        2032,
                        &format!("This function can't be invoked via {}{}", name, pattern_context(cmd_id)),
                    );
                }
            }
        }
    });
}

pub(super) fn check_unpassed_in_functions(params: &Parameters, root: &Token, out: &mut Out) {
    // functionMap: name -> function token, for functions that reference a
    // positional parameter directly and never assign one.
    let mut function_map: HashMap<String, Token> = HashMap::new();
    root.visit_preorder(&mut |t| {
        if let InnerToken::T_Function { name, body, .. } = &*t.inner {
            let flow = get_variable_flow(
                &params.parent_map,
                &params.id_map,
                params.has_lastpipe,
                body,
            );
            let references_positional = flow.iter().any(|sd| match sd {
                StackData::Reference(_, tok, str) => {
                    is_positional(str)
                        && is_direct_child_of(params, tok, t)
                        && !has_default_value(tok)
                }
                _ => false,
            });
            let assigns_positional = flow.iter().any(|sd| match sd {
                StackData::Assignment(_, _, str, _) => is_positional(str),
                _ => false,
            });
            if references_positional && !assigns_positional {
                // Map.fromList keeps the last entry for a key in preorder.
                function_map.insert(name.clone(), t.clone());
            }
        }
    });

    // referenceList: (name, argumentless, callsite) for every call of a
    // tracked function.
    let mut reference_list: Vec<(String, bool, Token)> = Vec::new();
    root.visit_preorder(&mut |t| {
        if let InnerToken::T_SimpleCommand { words, .. } = &*t.inner {
            if let Some((cmd, args)) = words.split_first() {
                if let Some(str) = astlib::get_literal_string(cmd) {
                    if function_map.contains_key(&str) {
                        reference_list.push((str, args.is_empty(), t.clone()));
                    }
                }
            }
        }
    });

    // Group by name (order within/among groups is irrelevant: output is sorted).
    let mut groups: HashMap<String, Vec<(String, bool, Token)>> = HashMap::new();
    for entry in reference_list {
        groups.entry(entry.0.clone()).or_default().push(entry);
    }

    for (name, group) in &groups {
        let all_argumentless = group.iter().all(|(_, b, _)| *b);
        if !all_argumentless {
            continue;
        }
        let func = &function_map[name];
        let ignoring = should_ignore_code(params, 2120, func);
        if ignoring {
            continue;
        }
        for (_, _, thing) in group {
            info(
                out,
                thing.id(),
                2119,
                &format!(
                    "Use {} \"$@\" if function's $1 should mean script's $1.",
                    e4m(name)
                ),
            );
        }
        warn(
            out,
            func.id(),
            2120,
            &format!("{} references arguments, but none are ever passed.", name),
        );
    }
}

/// `checkShebang` (SC2148 / SC2239 / SC2246 / SC2187).
pub(super) fn check_shebang(params: &Parameters, t: &Token, out: &mut Out) {
    // Unwrap the T_Annotation root; skip entirely if a ShellOverride is present.
    let script = match &*t.inner {
        InnerToken::T_Annotation { annotations, token } => {
            if annotations
                .iter()
                .any(|a| matches!(a, Annotation::ShellOverride(_)))
            {
                return;
            }
            token
        }
        _ => t,
    };
    if let InnerToken::T_Script { shebang, .. } = &*script.inner {
        if let InnerToken::T_Literal(sb) = &*shebang.inner {
            let id = shebang.id();
            if !params.shell_type_specified {
                if sb.is_empty() {
                    err(
                        out,
                        id,
                        2148,
                        "Tips depend on target shell and yours is unknown. Add a shebang or a 'shell' directive.",
                    );
                }
                if astlib::executable_from_shebang(sb) == "ash" {
                    warn(
                        out,
                        id,
                        2187,
                        "Ash scripts will be checked as Dash. Add '# shellcheck shell=dash' to silence.",
                    );
                }
            }
            if !sb.is_empty() {
                if !sb.starts_with('/') {
                    err(
                        out,
                        id,
                        2239,
                        "Ensure the shebang uses an absolute path to the interpreter.",
                    );
                }
                if let Some(first) = sb.split_whitespace().next() {
                    if first.ends_with('/') {
                        err(
                            out,
                            id,
                            2246,
                            "This shebang specifies a directory. Ensure the interpreter is a file.",
                        );
                    }
                }
            }
        }
    }
}

pub(super) fn check_use_before_definition(params: &Parameters, root: &Token, out: &mut Out) {
    let cfga = match params.cfg_analysis.as_ref() {
        Some(c) => c,
        None => return,
    };

    // funcs: name -> [definition ids]
    let mut funcs: BTreeMap<String, Vec<Id>> = BTreeMap::new();
    root.visit_preorder(&mut |t| {
        if let InnerToken::T_Function { name, .. } = &*t.inner {
            funcs.entry(name.clone()).or_default().push(t.id());
        }
    });

    // Green cut: no functions -> nothing to do.
    if funcs.is_empty() {
        return;
    }

    root.visit_preorder(&mut |t| {
        if let InnerToken::T_SimpleCommand { words, .. } = &*t.inner {
            if let Some(cmd) = words.first() {
                let id = t.id();
                (|| {
                    let name = crate::astlib::get_literal_string(cmd)?;
                    let invocations = funcs.get(&name)?;
                    // Is the function definitely being defined later?
                    if !invocations.iter().any(|&c| cfga.does_post_dominate(c, id)) {
                        return None;
                    }
                    // Was one already defined, so it's actually a re-definition?
                    if invocations.iter().any(|&c| cfga.does_post_dominate(id, c)) {
                        return None;
                    }
                    err(
                        out,
                        id,
                        2218,
                        "This function is only defined later. Move the definition up.",
                    );
                    Some(())
                })();
            }
        }
    });
}

pub(super) fn check_alias_used_in_same_parsing_unit(
    params: &Parameters,
    root: &Token,
    out: &mut Out,
) {
    let commands: Vec<&Token> = get_command_sequences(root)
        .into_iter()
        .flat_map(|s| s.iter())
        .collect();

    let line_span = |id: Id| -> Option<(i64, i64)> {
        let (start, end) = params.token_positions.get(&id)?;
        Some((start.line, end.line))
    };
    let follows_on_line = |a: &Token, b: &Token| -> bool {
        (|| {
            let (_, end) = line_span(a.id())?;
            let (start, _) = line_span(b.id())?;
            Some(end == start)
        })()
        .unwrap_or(false)
    };

    let units = group_by_link(follows_on_line, &commands);

    for unit in units {
        // doAnalysis findCommands over each token in the unit, sharing state.
        let mut aliases: HashMap<String, Token> = HashMap::new();
        for tok in unit {
            find_alias_commands(params, tok, &mut aliases, out);
        }
    }
}

pub(super) fn check_function_declarations(params: &Parameters, t: &Token, out: &mut Out) {
    let InnerToken::T_Function {
        keyword, parens, ..
    } = &*t.inner
    else {
        return;
    };
    let has_keyword = *keyword;
    let has_parens = *parens;
    let id = t.id();
    match params.shell {
        Shell::Bash => {}
        Shell::Ksh => {
            if has_keyword && has_parens {
                err(
                    out,
                    id,
                    2111,
                    "ksh does not allow 'function' keyword and '()' at the same time.",
                );
            }
        }
        Shell::Dash | Shell::BusyboxSh | Shell::Sh => {
            if has_keyword && has_parens {
                warn(
                    out,
                    id,
                    2112,
                    "'function' keyword is non-standard. Delete it.",
                );
            }
            if has_keyword && !has_parens {
                warn(
                    out,
                    id,
                    2113,
                    "'function' keyword is non-standard. Use 'foo()' instead of 'function foo'.",
                );
            }
        }
    }
}

pub(super) fn check_blatant_recursion(params: &Parameters, t: &Token, out: &mut Out) {
    let InnerToken::T_Function { name, body, .. } = &*t.inner else {
        return;
    };
    let seqs = get_command_sequences(body);
    let first_seq = match seqs.as_slice() {
        [seq] => *seq,
        _ => return,
    };
    let Some(first) = first_seq.first() else {
        return;
    };
    recursion_check_list(params, name, first, out);
}

pub(super) fn check_command_is_unreachable(params: &Parameters, t: &Token, out: &mut Out) {
    match &*t.inner {
        InnerToken::T_Pipeline { .. } => {
            (|| {
                let cfga = params.cfg_analysis.as_ref()?;
                let state = cfga.get_incoming_state(t.id())?;
                if state.state_is_reachable() {
                    return None;
                }
                if is_sourced(params, t) {
                    return None;
                }
                let path = get_path(params, t);
                if path
                    .iter()
                    .skip(1)
                    .any(|a| is_unreachable(params, a) || is_unreachable_function(params, a))
                {
                    return None;
                }
                info(
                    out,
                    t.id(),
                    2317,
                    "Command appears to be unreachable. Check usage (or ignore if invoked indirectly).",
                );
                Some(())
            })();
        }
        InnerToken::T_Function { .. } => {
            let path = get_path(params, t);
            if is_unreachable_function(params, t)
                && !path
                    .iter()
                    .skip(1)
                    .any(|a| is_unreachable_function(params, a))
                && !is_sourced(params, t)
            {
                info(
                    out,
                    t.id(),
                    2329,
                    "This function is never invoked. Check usage (or ignored if invoked indirectly).",
                );
            }
        }
        _ => {}
    }
}

pub(super) fn check_overwritten_exit_code(params: &Parameters, t: &Token, out: &mut Out) {
    if let InnerToken::T_DollarBraced { op, .. } = &*t.inner {
        if crate::astlib::get_literal_string(op).as_deref() == Some("?") {
            overwritten_check(params, t, out);
        }
    }
}

pub(super) fn check_source_not_followed(params: &Parameters, t: &Token, out: &mut Out) {
    let words = match &*t.inner {
        InnerToken::T_SimpleCommand { words, .. } if !words.is_empty() => words,
        _ => return,
    };
    let cmd = &words[0];
    if !is_source_command_word(cmd) {
        return;
    }
    let args = &words[1..];
    let file = get_source_file(args);

    // literalFile: override `mplus` literal `mplus` stripDynamicPrefix, then
    // reject a literal `~/` prefix.
    let literal_file = get_source_override(params, t)
        .or_else(|| file.and_then(astlib::get_literal_string))
        .or_else(|| file.and_then(strip_dynamic_prefix))
        .filter(|name| !name.starts_with("~/"));

    // fileId = fromMaybe (getId cmd) (getId <$> file)
    let file_id = file.map_or_else(|| cmd.id(), |f| f.id());

    match literal_file {
        None => warn(
            out,
            file_id,
            1090,
            "ShellCheck can't follow non-constant source. Use a directive to specify location.",
        ),
        Some(filename) => {
            // /dev/null is always readable as "" and yields no note.
            if filename == "/dev/null" {
                return;
            }
            info(
                out,
                file_id,
                1091,
                &format!(
                    "Not following: {filename} was not specified as input (see shellcheck -x)."
                ),
            );
        }
    }
}

/// `functions t` + `aliases t`, unioned left-biased (functions win).
fn functions_and_aliases(root: &Token) -> HashMap<String, Id> {
    // functions: Map.fromList over the preorder list; last-in-list wins, i.e.
    // the FIRST function encountered in preorder is retained (the list is built
    // by prepending). We reproduce "first encountered wins".
    let mut functions: HashMap<String, Id> = HashMap::new();
    let mut aliases: HashMap<String, Id> = HashMap::new();
    root.visit_preorder(&mut |t| match &*t.inner {
        InnerToken::T_Function { name, .. } => {
            functions.entry(name.clone()).or_insert_with(|| t.id());
        }
        InnerToken::T_SimpleCommand { words, .. }
            if !words.is_empty() && is_unqualified_command(t, "alias") =>
        {
            for arg in &words[1..] {
                let string = astlib::only_literal_string(arg);
                if string.contains('=') {
                    let key: String = string.chars().take_while(|c| *c != '=').collect();
                    aliases.entry(key).or_insert_with(|| arg.id());
                }
            }
        }
        _ => {}
    });
    // Map.union functions aliases  (left-biased: functions override aliases)
    let mut combined = aliases;
    for (k, v) in functions {
        combined.insert(k, v);
    }
    combined
}

/// `skipOver t list` = drop everything up to and including the token `t`.
fn skip_over(tok: &Token, list: &[Token]) -> Vec<Token> {
    match list.iter().position(|c| c.id() == tok.id()) {
        Some(i) => list[i + 1..].to_vec(),
        None => Vec::new(),
    }
}

/// `getPotentialCommands name argAndString`.
fn get_potential_commands<'a>(
    name: &str,
    arg_and_string: &'a [(String, Token)],
) -> Vec<&'a (String, Token)> {
    let is_flag = |x: &(String, Token)| x.0.starts_with('-');
    let drop_flags = |list: &'a [(String, Token)]| -> &'a [(String, Token)] {
        let i = list.iter().take_while(|x| is_flag(x)).count();
        &list[i..]
    };
    let first_non_flag =
        || -> Vec<&'a (String, Token)> { drop_flags(arg_and_string).iter().take(1).collect() };
    match name {
        "chroot" | "screen" | "sudo" | "doas" | "run0" | "xargs" | "tmux" => first_non_flag(),
        "timeout" | "ssh" => drop_flags(arg_and_string).iter().skip(1).take(1).collect(),
        "find" => {
            const FIND_EXEC_FLAGS: &[&str] = &["-exec", "-execdir", "-ok", "-okdir"];
            let i = arg_and_string
                .iter()
                .take_while(|x| !FIND_EXEC_FLAGS.contains(&x.0.as_str()))
                .count();
            arg_and_string[i..].iter().skip(1).take(1).collect()
        }
        _ => Vec::new(),
    }
}

/// `isPositional str`.
fn is_positional(s: &str) -> bool {
    s == "*"
        || s == "@"
        || s == "#"
        || (!s.is_empty() && s != "0" && s.chars().all(|c| c.is_ascii_digit()))
}

/// `isDefaultValueModifier str`.
fn is_default_value_modifier(s: &str) -> bool {
    const HANDLES_DEFAULT: &str = "-+?";
    let chars: Vec<char> = s.chars().collect();
    match chars.as_slice() {
        [':', c, ..] => HANDLES_DEFAULT.contains(*c),
        [c, ..] => HANDLES_DEFAULT.contains(*c),
        _ => false,
    }
}

/// `hasDefaultValue t` — such as `${1-x}` or `${1:-x}`.
fn has_default_value(t: &Token) -> bool {
    if let InnerToken::T_DollarBraced { braced: true, op } = &*t.inner {
        let str = oversimplify(op).concat();
        is_default_value_modifier(&get_braced_modifier(&str))
    } else {
        false
    }
}

/// `isDirectChildOf child parent`: the nearest enclosing function or script of
/// `child` is `parent`.
fn is_direct_child_of(params: &Parameters, child: &Token, parent: &Token) -> bool {
    get_path(params, child)
        .iter()
        .find(|x| {
            matches!(
                &*x.inner,
                InnerToken::T_Function { .. } | InnerToken::T_Script { .. }
            )
        })
        .map(|f| f.id() == parent.id())
        .unwrap_or(false)
}

/// `groupByLink`: group consecutive elements where each adjacent pair links.
fn group_by_link<'a, F: Fn(&Token, &Token) -> bool>(
    f: F,
    list: &[&'a Token],
) -> Vec<Vec<&'a Token>> {
    let mut out: Vec<Vec<&'a Token>> = vec![];
    let mut current: Vec<&'a Token> = vec![];
    for &item in list {
        if let Some(&prev) = current.last() {
            if f(prev, item) {
                current.push(item);
            } else {
                out.push(std::mem::take(&mut current));
                current.push(item);
            }
        } else {
            current.push(item);
        }
    }
    if !current.is_empty() {
        out.push(current);
    }
    out
}

fn find_alias_commands(
    params: &Parameters,
    t: &Token,
    aliases: &mut HashMap<String, Token>,
    out: &mut Out,
) {
    // preorder: run on t, then recurse into children.
    process_alias_node(params, t, aliases, out);
    for c in t.children() {
        find_alias_commands(params, c, aliases, out);
    }
}

fn process_alias_node(
    params: &Parameters,
    t: &Token,
    aliases: &mut HashMap<String, Token>,
    out: &mut Out,
) {
    let InnerToken::T_SimpleCommand { words, .. } = &*t.inner else {
        return;
    };
    let Some((cmd, args)) = words.split_first() else {
        return;
    };
    match get_unquoted_literal(cmd).as_deref() {
        Some("alias") => {
            for arg in args {
                add_alias(arg, aliases);
            }
        }
        Some(name) if !name.contains('/') => {
            if let Some(alias) = aliases.get(name) {
                if !(is_sourced(params, t) || should_ignore_code(params, 2262, alias)) {
                    warn(
                        out,
                        alias.id(),
                        2262,
                        "This alias can't be defined and used in the same parsing unit. Use a function instead.",
                    );
                    info(
                        out,
                        t.id(),
                        2263,
                        "Since they're in the same parsing unit, this command will not refer to the previously mentioned alias.",
                    );
                }
            }
        }
        _ => {}
    }
}

fn add_alias(arg: &Token, aliases: &mut HashMap<String, Token>) {
    let full = get_literal_string_def("-", arg);
    let (name, value) = match full.find('=') {
        Some(i) => (&full[..i], &full[i..]),
        None => (full.as_str(), ""),
    };
    if is_variable_name(name) && !value.is_empty() {
        // insertWith (\new old -> old): keep the first inserted.
        aliases
            .entry(name.to_string())
            .or_insert_with(|| arg.clone());
    }
}

/// `getCommandNameAndToken True` (direct): the first word literal.
fn direct_command_name_and_token(cmd: &Token) -> (Option<String>, &Token) {
    if let Some(c) = get_command_local(cmd) {
        if let InnerToken::T_SimpleCommand { words, .. } = &*c.inner {
            if let Some(w) = words.first() {
                if let Some(s) = astlib::get_literal_string(w) {
                    return (Some(s), w);
                }
            }
        }
    }
    (None, cmd)
}

fn recursion_check_list(params: &Parameters, name: &str, t: &Token, out: &mut Out) {
    match &*t.inner {
        InnerToken::T_Backgrounded(inner) => recursion_check_list(params, name, inner, out),
        InnerToken::T_AndIf { lhs, .. } => recursion_check_list(params, name, lhs, out),
        InnerToken::T_OrIf { lhs, .. } => recursion_check_list(params, name, lhs, out),
        InnerToken::T_Pipeline { commands, .. } => {
            for cmd in commands {
                recursion_check_command(params, name, cmd, out);
            }
        }
        _ => {}
    }
}

fn recursion_check_command(params: &Parameters, name: &str, cmd: &Token, out: &mut Out) {
    let (invoked, tok) = direct_command_name_and_token(cmd);
    if let Some(invoked) = invoked {
        if name == invoked {
            err_with_fix(
                out,
                tok.id(),
                2264,
                "This function unconditionally re-invokes itself. Missing 'command'?",
                fix_with(vec![replace_start(params, tok.id(), 0, "command ")]),
            );
        }
    }
}

fn is_unreachable(params: &Parameters, t: &Token) -> bool {
    (|| {
        let cfga = params.cfg_analysis.as_ref()?;
        let state = cfga.get_incoming_state(t.id())?;
        Some(!state.state_is_reachable())
    })()
    .unwrap_or(false)
}

fn is_unreachable_function(params: &Parameters, f: &Token) -> bool {
    if let InnerToken::T_Function { body, .. } = &*f.inner {
        is_unreachable(params, body)
    } else {
        false
    }
}

fn overwritten_check(params: &Parameters, t: &Token, out: &mut Out) {
    let id = t.id();
    (|| {
        let cfga = params.cfg_analysis.as_ref()?;
        let state = cfga.get_incoming_state(id)?;
        let exit_code_ids = state.exit_codes().clone();
        if exit_code_ids.is_empty() {
            return None;
        }
        // traverse (Map.lookup) — all must be present.
        let mut exit_code_tokens: Vec<Token> = Vec::new();
        for k in exit_code_ids.iter() {
            let tok = params.id_map.get(k)?;
            exit_code_tokens.push(tok.clone());
        }

        if exit_code_tokens.iter().all(is_condition)
            && !used_unconditionally(params, t, &exit_code_ids)
        {
            warn(
                out,
                id,
                2319,
                "This $? refers to a condition, not a command. Assign to a variable to avoid it being overwritten.",
            );
        }
        if exit_code_tokens.iter().all(is_printing) {
            warn(
                out,
                id,
                2320,
                "This $? refers to echo/printf, not a previous command. Assign to variable to avoid it being overwritten.",
            );
        }
        Some(())
    })();
}

fn is_condition(t: &Token) -> bool {
    match &*t.inner {
        InnerToken::T_Condition { .. } => true,
        InnerToken::T_SimpleCommand { .. } => get_command_name(t).as_deref() == Some("test"),
        _ => false,
    }
}

fn used_unconditionally(
    params: &Parameters,
    t: &Token,
    test_ids: &std::collections::BTreeSet<Id>,
) -> bool {
    let cfga = match params.cfg_analysis.as_ref() {
        Some(c) => c,
        None => return false,
    };
    test_ids.iter().all(|&c| cfga.does_post_dominate(t.id(), c))
}

fn is_printing(t: &Token) -> bool {
    matches!(
        get_command_basename(t).as_deref(),
        Some("echo") | Some("printf")
    )
}

/// `isCommand ["source", "."] cmd`: the command word is a single `T_Literal`
/// equal to `source` or `.`. (`builtin`/slash forms are deliberately excluded,
/// matching the parser — unlike SC2240's dispatch.)
fn is_source_command_word(cmd: &Token) -> bool {
    if let InnerToken::T_NormalWord(parts) = &*cmd.inner {
        if let [only] = &parts[..] {
            if let InnerToken::T_Literal(s) = &*only.inner {
                return s == "source" || s == ".";
            }
        }
    }
    false
}

/// `getFile args'`: the token naming the sourced file, honouring `--` and `-p`.
fn get_source_file(args: &[Token]) -> Option<&Token> {
    let (first, rest) = args.split_first()?;
    match astlib::get_literal_string(first).as_deref() {
        Some("--") => rest.first(),
        Some("-p") => rest.get(1),
        _ => Some(first),
    }
}

/// `isStringExpansion`.
fn is_string_expansion(t: &Token) -> bool {
    use InnerToken::*;
    is_command_substitution(t)
        || match &*t.inner {
            T_DollarArithmetic(_) => true,
            T_DollarBraced { .. } => !is_array_expansion(t),
            _ => false,
        }
}

/// `stripDynamicPrefix`: for `$foo/bar` (a single leading string expansion
/// followed by a literal `/...`), yield `"." ++ "/bar"`.
fn strip_dynamic_prefix(word: &Token) -> Option<String> {
    let parts = get_word_parts(word);
    let (first, rest) = parts.split_first()?;
    if !is_string_expansion(first) {
        return None;
    }
    let rest_word = Token::new(
        Id(0),
        InnerToken::T_NormalWord(rest.iter().map(|t| (*t).clone()).collect()),
    );
    let str = astlib::get_literal_string(&rest_word)?;
    if !str.starts_with('/') {
        return None;
    }
    Some(format!(".{str}"))
}

/// `getSourceOverride`: the innermost in-scope `# shellcheck source=...`
/// directive (stopping at a source frame, mirroring `takeWhile isSameFile`).
fn get_source_override(params: &Parameters, t: &Token) -> Option<String> {
    for a in crate::analyzer_lib::get_path(params, t) {
        match &*a.inner {
            InnerToken::T_SourceCommand { .. } => return None,
            InnerToken::T_Annotation { annotations, .. } => {
                for ann in annotations {
                    if let Annotation::SourceOverride(s) = ann {
                        return Some(s.clone());
                    }
                }
            }
            _ => {}
        }
    }
    None
}

#[cfg(test)]
#[allow(non_snake_case)]
mod tests {
    use super::*;
    use crate::test_support::*;

    #[test]
    fn prop_checkFunctionsUsedExternally1() {
        assert!(tree_emits(
            check_functions_used_externally,
            "foo() { :; }; sudo foo"
        ));
    }

    #[test]
    fn prop_checkFunctionsUsedExternally2() {
        assert!(tree_emits(
            check_functions_used_externally,
            "alias f='a'; xargs -0 f"
        ));
    }

    #[test]
    fn prop_checkFunctionsUsedExternally2b() {
        assert!(!tree_emits(
            check_functions_used_externally,
            "alias f='a'; find . -type f"
        ));
    }

    #[test]
    fn prop_checkFunctionsUsedExternally2c() {
        assert!(tree_emits(
            check_functions_used_externally,
            "alias f='a'; find . -type f -exec f {} +"
        ));
    }

    #[test]
    fn prop_checkFunctionsUsedExternally3() {
        assert!(!tree_emits(
            check_functions_used_externally,
            "f() { :; }; echo f"
        ));
    }

    #[test]
    fn prop_checkFunctionsUsedExternally4() {
        assert!(!tree_emits(
            check_functions_used_externally,
            "foo() { :; }; run0 \"foo\""
        ));
    }

    #[test]
    fn prop_checkFunctionsUsedExternally5() {
        assert!(tree_emits(
            check_functions_used_externally,
            "foo() { :; }; ssh host foo"
        ));
    }

    #[test]
    fn prop_checkFunctionsUsedExternally6() {
        assert!(!tree_emits(
            check_functions_used_externally,
            "foo() { :; }; ssh host echo foo"
        ));
    }

    #[test]
    fn prop_checkFunctionsUsedExternally7() {
        assert!(!tree_emits(
            check_functions_used_externally,
            "install() { :; }; sudo apt-get install foo"
        ));
    }

    #[test]
    fn prop_checkFunctionsUsedExternally8() {
        assert!(tree_emits(
            check_functions_used_externally,
            "foo() { :; }; command sudo foo"
        ));
    }

    #[test]
    fn prop_checkFunctionsUsedExternally9() {
        assert!(tree_emits(
            check_functions_used_externally,
            "foo() { :; }; exec -c doas foo"
        ));
    }

    #[test]
    fn prop_checkFunctionsUsedExternally10() {
        assert!(tree_emits(
            check_functions_used_externally,
            "foo() { :; }; timeout -p 10 foo"
        ));
    }

    // SC2119 / SC2120 — checkUnpassedInFunctions

    #[test]
    fn prop_checkUnpassedInFunctions1() {
        assert!(tree_emits(
            check_unpassed_in_functions,
            "foo() { echo $1; }; foo"
        ));
    }

    #[test]
    fn prop_checkUnpassedInFunctions2() {
        assert!(!tree_emits(
            check_unpassed_in_functions,
            "foo() { echo $1; };"
        ));
    }

    #[test]
    fn prop_checkUnpassedInFunctions3() {
        assert!(!tree_emits(
            check_unpassed_in_functions,
            "foo() { echo $lol; }; foo"
        ));
    }

    #[test]
    fn prop_checkUnpassedInFunctions4() {
        assert!(!tree_emits(
            check_unpassed_in_functions,
            "foo() { echo $0; }; foo"
        ));
    }

    #[test]
    fn prop_checkUnpassedInFunctions5() {
        assert!(!tree_emits(
            check_unpassed_in_functions,
            "foo() { echo $1; }; foo 'lol'; foo"
        ));
    }

    #[test]
    fn prop_checkUnpassedInFunctions6() {
        assert!(!tree_emits(
            check_unpassed_in_functions,
            "foo() { set -- *; echo $1; }; foo"
        ));
    }

    #[test]
    fn prop_checkUnpassedInFunctions7() {
        assert!(tree_emits(
            check_unpassed_in_functions,
            "foo() { echo $1; }; foo; foo;"
        ));
    }

    #[test]
    fn prop_checkUnpassedInFunctions8() {
        assert!(!tree_emits(
            check_unpassed_in_functions,
            "foo() { echo $((1)); }; foo;"
        ));
    }

    #[test]
    fn prop_checkUnpassedInFunctions9() {
        assert!(!tree_emits(
            check_unpassed_in_functions,
            "foo() { echo $(($b)); }; foo;"
        ));
    }

    #[test]
    fn prop_checkUnpassedInFunctions10() {
        assert!(!tree_emits(
            check_unpassed_in_functions,
            "foo() { echo $!; }; foo;"
        ));
    }

    #[test]
    fn prop_checkUnpassedInFunctions11() {
        assert!(!tree_emits(
            check_unpassed_in_functions,
            "foo() { bar() { echo $1; }; bar baz; }; foo;"
        ));
    }

    #[test]
    fn prop_checkUnpassedInFunctions12() {
        assert!(!tree_emits(
            check_unpassed_in_functions,
            "foo() { echo ${!var*}; }; foo;"
        ));
    }

    #[test]
    fn prop_checkUnpassedInFunctions13() {
        assert!(!tree_emits(
            check_unpassed_in_functions,
            "# shellcheck disable=SC2120\nfoo() { echo $1; }\nfoo\n"
        ));
    }

    #[test]
    fn prop_checkUnpassedInFunctions14() {
        assert!(tree_emits(
            check_unpassed_in_functions,
            "foo() { echo $#; }; foo"
        ));
    }

    #[test]
    fn prop_checkUnpassedInFunctions15() {
        assert!(!tree_emits(
            check_unpassed_in_functions,
            "foo() { echo ${1-x}; }; foo"
        ));
    }

    #[test]
    fn prop_checkUnpassedInFunctions16() {
        assert!(!tree_emits(
            check_unpassed_in_functions,
            "foo() { echo ${1:-x}; }; foo"
        ));
    }

    #[test]
    fn prop_checkUnpassedInFunctions17() {
        assert!(!tree_emits(
            check_unpassed_in_functions,
            "foo() { mycommand ${1+--verbose}; }; foo"
        ));
    }

    #[test]
    fn prop_checkUnpassedInFunctions18() {
        assert!(!tree_emits(
            check_unpassed_in_functions,
            "foo() { if mycheck; then foo ${1?Missing}; fi; }; foo"
        ));
    }

    // SC2089 / SC2090 — checkQuotesInLiterals

    #[test]
    fn prop_checkShebangParameters1() {
        assert!(tree_emits(
            check_shebang_parameters,
            "#!/usr/bin/env bash -x\necho cow"
        ));
    }

    #[test]
    fn prop_checkShebangParameters2() {
        assert!(!tree_emits(check_shebang_parameters, "#! /bin/sh  -l "));
    }

    #[test]
    fn prop_checkShebangParameters3() {
        assert!(!tree_emits(
            check_shebang_parameters,
            "#!/usr/bin/env -S bash -x\necho cow"
        ));
    }

    #[test]
    fn prop_checkShebangParameters4() {
        assert!(!tree_emits(
            check_shebang_parameters,
            "#!/usr/bin/env --split-string bash -x\necho cow"
        ));
    }

    // ---- checkForInQuoted ----

    #[test]
    fn prop_checkFunctionDeclarations1() {
        assert!(emits(
            check_function_declarations,
            "#!/bin/ksh\nfunction foo() { command foo --lol \"$@\"; }"
        ));
    }

    #[test]
    fn prop_checkFunctionDeclarations2() {
        assert!(emits(
            check_function_declarations,
            "#!/bin/dash\nfunction foo { lol; }"
        ));
    }

    #[test]
    fn prop_checkFunctionDeclarations3() {
        assert!(!emits(check_function_declarations, "foo() { echo bar; }"));
    }

    // ---- checkStderrPipe ----

    #[test]
    fn prop_checkAliasUsedInSameParsingUnit1() {
        assert!(tree_emits(
            check_alias_used_in_same_parsing_unit,
            "alias x=y; x"
        ));
    }

    #[test]
    fn prop_checkAliasUsedInSameParsingUnit2() {
        assert!(!tree_emits(
            check_alias_used_in_same_parsing_unit,
            "alias x=y\nx"
        ));
    }

    #[test]
    fn prop_checkAliasUsedInSameParsingUnit3() {
        assert!(tree_emits(
            check_alias_used_in_same_parsing_unit,
            "{ alias x=y\nx\n}"
        ));
    }

    #[test]
    fn prop_checkAliasUsedInSameParsingUnit4() {
        assert!(!tree_emits(
            check_alias_used_in_same_parsing_unit,
            "alias x=y; 'x';"
        ));
    }

    #[test]
    fn prop_checkAliasUsedInSameParsingUnit5() {
        assert!(!tree_emits(
            check_alias_used_in_same_parsing_unit,
            ":\n{\n#shellcheck disable=SC2262\nalias x=y\nx\n}"
        ));
    }

    #[test]
    fn prop_checkAliasUsedInSameParsingUnit6() {
        assert!(!tree_emits(
            check_alias_used_in_same_parsing_unit,
            ":\n{\n#shellcheck disable=SC2262\nalias x=y\nalias x=z\nx\n}"
        ));
    }

    // ---- checkBlatantRecursion ----

    #[test]
    fn prop_checkBlatantRecursion1() {
        assert!(emits(check_blatant_recursion, ":(){ :|:& };:"));
    }

    #[test]
    fn prop_checkBlatantRecursion2() {
        assert!(emits(check_blatant_recursion, "f() { f; }"));
    }

    #[test]
    fn prop_checkBlatantRecursion3() {
        assert!(!emits(check_blatant_recursion, "f() { command f; }"));
    }

    #[test]
    fn prop_checkBlatantRecursion4() {
        assert!(emits(
            check_blatant_recursion,
            "cd() { cd \"$lol/$1\" || exit; }"
        ));
    }

    #[test]
    fn prop_checkBlatantRecursion5() {
        assert!(!emits(
            check_blatant_recursion,
            "cd() { [ -z \"$1\" ] || cd \"$1\"; }"
        ));
    }

    #[test]
    fn prop_checkBlatantRecursion6() {
        assert!(!emits(
            check_blatant_recursion,
            "cd() { something; cd $1; }"
        ));
    }

    #[test]
    fn prop_checkBlatantRecursion7() {
        assert!(!emits(check_blatant_recursion, "cd() { builtin cd $1; }"));
    }

    // ---- checkAssignToSelf ----

    #[test]
    fn prop_checkUseBeforeDefinition1() {
        assert!(tree_emits(check_use_before_definition, "f; f() { true; }"));
    }

    #[test]
    fn prop_checkUseBeforeDefinition2() {
        assert!(!(tree_emits(check_use_before_definition, "f() { true; }; f")));
    }

    #[test]
    fn prop_checkUseBeforeDefinition3() {
        assert!(
            !(tree_emits(
                check_use_before_definition,
                "if ! mycmd --version; then mycmd() { true; }; fi"
            ))
        );
    }

    #[test]
    fn prop_checkUseBeforeDefinition4() {
        assert!(!(tree_emits(check_use_before_definition, "mycmd || mycmd() { f; }")));
    }

    #[test]
    fn prop_checkUseBeforeDefinition5() {
        assert!(tree_emits(
            check_use_before_definition,
            "false || mycmd; mycmd() { f; }"
        ));
    }

    #[test]
    fn prop_checkUseBeforeDefinition6() {
        assert!(
            !(tree_emits(
                check_use_before_definition,
                "f() { one; }; f; f() { two; }; f"
            ))
        );
    }

    // --- SC2317/2329 checkCommandIsUnreachable ---

    #[test]
    fn prop_checkCommandIsUnreachable1() {
        assert!(node_emits(
            check_command_is_unreachable,
            "foo; bar; exit; baz"
        ));
    }

    #[test]
    fn prop_checkCommandIsUnreachable2() {
        assert!(node_emits(
            check_command_is_unreachable,
            "die() { exit; }; foo; bar; die; baz"
        ));
    }

    #[test]
    fn prop_checkCommandIsUnreachable3() {
        assert!(!(node_emits(check_command_is_unreachable, "foo; bar || exit; baz")));
    }

    #[test]
    fn prop_checkCommandIsUnreachable4() {
        assert!(
            !(node_emits(
                check_command_is_unreachable,
                "f() { foo; };    # Maybe sourced"
            ))
        );
    }

    #[test]
    fn prop_checkCommandIsUnreachable5() {
        assert!(node_emits(
            check_command_is_unreachable,
            "f() { foo; }; exit  # Not sourced"
        ));
    }

    // --- SC2319/2320 checkOverwrittenExitCode ---

    #[test]
    fn prop_checkOverwrittenExitCode1() {
        assert!(node_emits(
            check_overwritten_exit_code,
            "x; [ $? -eq 1 ] || [ $? -eq 2 ]"
        ));
    }

    #[test]
    fn prop_checkOverwrittenExitCode2() {
        assert!(!(node_emits(check_overwritten_exit_code, "x; [ $? -eq 1 ]")));
    }

    #[test]
    fn prop_checkOverwrittenExitCode3() {
        assert!(node_emits(
            check_overwritten_exit_code,
            "x; echo \"Exit is $?\"; [ $? -eq 0 ]"
        ));
    }

    #[test]
    fn prop_checkOverwrittenExitCode4() {
        assert!(
            !(node_emits(
                check_overwritten_exit_code,
                "x; [ $? -eq 0 ] && echo Success"
            ))
        );
    }

    #[test]
    fn prop_checkOverwrittenExitCode5() {
        assert!(node_emits(
            check_overwritten_exit_code,
            "x; if [ $? -eq 0 ]; then var=$?; fi"
        ));
    }

    #[test]
    fn prop_checkOverwrittenExitCode6() {
        assert!(node_emits(
            check_overwritten_exit_code,
            "x; [ $? -gt 0 ] && fail=$?"
        ));
    }

    #[test]
    fn prop_checkOverwrittenExitCode7() {
        assert!(!(node_emits(check_overwritten_exit_code, "[ 1 -eq 2 ]; status=$?")));
    }

    #[test]
    fn prop_checkOverwrittenExitCode8() {
        assert!(!(node_emits(check_overwritten_exit_code, "[ 1 -eq 2 ]; exit $?")));
    }

    // --- SC2324 checkPlusEqualsNumber ---

    fn only_code(f: fn(&Parameters, &Token, &mut Out), s: &str) -> Vec<i32> {
        let params = params_for(s);
        let mut out = Out::new();
        params.root.visit_preorder(&mut |t| f(&params, t, &mut out));
        out.iter().map(|c| c.comment.code as i32).collect()
    }

    fn only_msg(f: fn(&Parameters, &Token, &mut Out), s: &str) -> Vec<String> {
        let params = params_for(s);
        let mut out = Out::new();
        params.root.visit_preorder(&mut |t| f(&params, t, &mut out));
        out.iter().map(|c| c.comment.message.clone()).collect()
    }

    #[test]
    fn prop_source_dot_not_followed() {
        // prop_checkCommandWithTrailingSymbol7 corpus input.
        assert_eq!(only_code(check_source_not_followed, ". foo.sh"), vec![1091]);
        assert_eq!(
            only_msg(check_source_not_followed, ". foo.sh"),
            vec!["Not following: foo.sh was not specified as input (see shellcheck -x)."]
        );
    }

    #[test]
    fn prop_source_keyword_not_followed() {
        // prop_checkBashisms5 corpus input.
        assert_eq!(
            only_code(check_source_not_followed, "source file"),
            vec![1091]
        );
        assert_eq!(
            only_msg(check_source_not_followed, "source file"),
            vec!["Not following: file was not specified as input (see shellcheck -x)."]
        );
    }

    #[test]
    fn prop_source_args_still_not_followed() {
        // prop_checkSourceArgs1/3 corpus inputs: file arg is followed by more args.
        assert_eq!(
            only_msg(check_source_not_followed, "#!/bin/sh\n. script arg"),
            vec!["Not following: script was not specified as input (see shellcheck -x)."]
        );
    }

    #[test]
    fn prop_devnull_is_not_flagged() {
        // prop_canParseDevNull / prop_checkBashisms110: /dev/null yields no note.
        assert!(only_code(check_source_not_followed, "source /dev/null").is_empty());
        assert!(only_code(check_source_not_followed, ". /dev/null").is_empty());
    }

    #[test]
    fn prop_cant_source_dynamic() {
        // prop_cantSourceDynamic: a non-constant target is SC1090, not SC1091.
        assert_eq!(only_code(check_source_not_followed, ". \"$1\""), vec![1090]);
    }

    #[test]
    fn prop_cant_source_tilde() {
        // prop_cantSourceDynamic2: literal `~/` is treated as non-constant.
        assert_eq!(
            only_code(check_source_not_followed, "source ~/foo"),
            vec![1090]
        );
    }

    #[test]
    fn prop_source_override_directive_is_followed_constant() {
        // A `source=` directive supplies a constant target -> SC1091, not SC1090.
        assert_eq!(
            only_msg(
                check_source_not_followed,
                "# shellcheck source=lib\n. \"$1\""
            ),
            vec!["Not following: lib was not specified as input (see shellcheck -x)."]
        );
    }

    #[test]
    fn prop_not_a_source_command() {
        // A plain command is untouched; `builtin source` is not the parser form.
        assert!(only_code(check_source_not_followed, "echo foo").is_empty());
        assert!(only_code(check_source_not_followed, "builtin source lib").is_empty());
    }
}
