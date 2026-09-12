//! Variable and array checks from `ShellCheck.Analytics`.
use super::common::*;
use crate::analyzer_lib::is_true_assignment_source;
use crate::analyzer_lib::*;
use crate::ast::*;
use crate::astlib;
use crate::astlib::is_command_substitution;
use crate::astlib::is_literal;
use crate::astlib::oversimplify;
use crate::cfg;
use crate::cfg::get_word_parts;
use crate::interface::Fix;
use crate::interface::Shell;
use std::collections::HashMap;
use std::collections::HashSet;
use std::sync::OnceLock;

pub(super) fn check_subshell_assignment(params: &Parameters, _root: &Token, out: &mut Out) {
    // findSubshelled flow [("oops",[])] Map.empty
    let mut scopes: Vec<(String, Vec<(Token, String)>)> = vec![("oops".to_string(), Vec::new())];
    let mut dead: HashMap<String, VarState> = HashMap::new();

    for sd in &params.variable_flow {
        match sd {
            StackData::Assignment(_base, place, name, dt) => {
                if is_true_assignment_source(dt) {
                    if let Some(top) = scopes.last_mut() {
                        top.1.push((place.clone(), name.clone()));
                    }
                    dead.insert(name.clone(), VarState::Alive);
                }
            }
            StackData::Reference(_base, read_token, name) => {
                if !subshell_should_ignore(name) {
                    if let Some(VarState::Dead(write_token, reason)) = dead.get(name).cloned() {
                        info(
                            out,
                            write_token.id(),
                            2030,
                            &format!(
                                "Modification of {} is local (to subshell caused by {}).",
                                name, reason
                            ),
                        );
                        info(
                            out,
                            read_token.id(),
                            2031,
                            &format!(
                                "{} was modified in a subshell. That change might be lost.",
                                name
                            ),
                        );
                    }
                }
            }
            StackData::StackScope(Scope::SubshellScope(reason)) => {
                scopes.push((reason.clone(), Vec::new()));
            }
            StackData::StackScope(Scope::NoneScope) => {}
            StackData::StackScopeEnd => {
                if let Some((reason, scope)) = scopes.pop() {
                    for (token, var) in scope {
                        dead.insert(var, VarState::Dead(token, reason.clone()));
                    }
                }
            }
        }
    }
}

pub(super) fn check_array_without_index(params: &Parameters, _root: &Token, out: &mut Out) {
    // doVariableFlowAnalysis readF writeF defaultSet (variableFlow params)
    let mut arrays: HashSet<String> = ARRAY_VARIABLES.iter().map(|s| s.to_string()).collect();

    for sd in &params.variable_flow {
        match sd {
            StackData::Reference(_base, place, _name) => {
                // readF _ (T_DollarBraced id _ token) _
                if let InnerToken::T_DollarBraced { op, .. } = &*place.inner {
                    if let Some(name) = astlib::get_literal_string(op) {
                        if arrays.contains(&name) {
                            warn(
                                out,
                                place.id(),
                                2128,
                                "Expanding an array without an index only gives the first element.",
                            );
                        }
                    }
                }
            }
            StackData::Assignment(_base, place, name, dt) => {
                match dt {
                    // writeF _ (T_Assignment id mode name [] _) _ (DataString _)
                    DataType::DataString(_)
                        if matches!(&*place.inner,
                            InnerToken::T_Assignment { indices, .. } if indices.is_empty()) =>
                    {
                        if arrays.contains(name) {
                            if let InnerToken::T_Assignment { mode, .. } = &*place.inner {
                                match mode {
                                    AssignmentMode::Assign => warn(
                                        out,
                                        place.id(),
                                        2178,
                                        "Variable was used as an array but is now assigned a string.",
                                    ),
                                    AssignmentMode::Append => warn(
                                        out,
                                        place.id(),
                                        2179,
                                        "Use array+=(\"item\") to append items to an array.",
                                    ),
                                }
                            }
                        }
                        // No state change.
                    }
                    // writeF _ t name (DataArray _)
                    DataType::DataArray(_) => {
                        arrays.insert(name.clone());
                    }
                    // writeF _ expr name _
                    _ => {
                        if is_indexed(place) {
                            arrays.insert(name.clone());
                        } else {
                            arrays.remove(name);
                        }
                    }
                }
            }
            _ => {}
        }
    }
}

pub(super) fn check_array_assignment_indices(params: &Parameters, root: &Token, out: &mut Out) {
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

pub(super) fn check_array_value_used_as_index(params: &Parameters, _root: &Token, out: &mut Out) {
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

pub(super) fn check_commarrays(_params: &Parameters, t: &Token, out: &mut Out) {
    if let InnerToken::T_Array(l) = &*t.inner {
        if l.iter().any(|e| commarray_literal(e).contains(',')) {
            warn(
                out,
                t.id(),
                2054,
                "Use spaces, not commas, to separate array elements.",
            );
        }
    }
}

pub(super) fn check_bad_parameter_substitution(_params: &Parameters, t: &Token, out: &mut Out) {
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

pub(super) fn check_dollar_brackets(_params: &Parameters, t: &Token, out: &mut Out) {
    if let InnerToken::T_DollarBracket(_) = &*t.inner {
        style(out, t.id(), 2007, "Use $((..)) instead of deprecated $[..]");
    }
}

pub(super) fn check_prefix_assignment_reference(params: &Parameters, t: &Token, out: &mut Out) {
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

pub(super) fn check_overriding_path(_params: &Parameters, t: &Token, out: &mut Out) {
    let InnerToken::T_SimpleCommand { assignments, words } = &*t.inner else {
        return;
    };
    if !words.is_empty() {
        return;
    }
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
        let string = oversimplify(value).concat();
        if ["/bin", "/sbin"].iter().any(|s| string.contains(s)) {
            continue;
        }
        let notify = |out: &mut Out| {
            warn(
                out,
                var.id(),
                2123,
                "PATH is the shell search path. Use another name.",
            );
        };
        if string.contains('/') && !string.contains(':') {
            notify(out);
        }
        if is_literal(value) && !string.contains(':') && !string.contains('/') {
            notify(out);
        }
    }
}

pub(super) fn check_suspicious_ifs(params: &Parameters, t: &Token, out: &mut Out) {
    let InnerToken::T_Assignment {
        var,
        indices,
        value,
        ..
    } = &*t.inner
    else {
        return;
    };
    if var != "IFS" || !indices.is_empty() {
        return;
    }
    let Some(v) = decoded_literal_string(value) else {
        return;
    };
    let has_dollar_single = params.shell == Shell::Bash || params.shell == Shell::Ksh;
    let n = if has_dollar_single {
        "$'\\n'"
    } else {
        "'<literal linefeed here>'"
    };
    let tab = if has_dollar_single {
        "$'\\t'"
    } else {
        "\"$(printf '\\t')\""
    };
    let suggest = |out: &mut Out, r: &str| {
        warn(
            out,
            value.id(),
            2141,
            &format!("This backslash is literal. Did you mean IFS={} ?", r),
        );
    };
    let suggest2 = |out: &mut Out, desc: &str| {
        warn(
            out,
            value.id(),
            2141,
            &format!(
                "This IFS value contains {}. For tabs/linefeeds/escapes, use $'..', literal, or printf.",
                desc
            ),
        );
    };
    match v.as_str() {
        "\\n" => suggest(out, n),
        "\\t" => suggest(out, tab),
        x if x.contains('\\') => suggest2(out, "a literal backslash"),
        x if x.contains('n') => suggest2(out, "the literal letter 'n'"),
        x if x.contains('t') => suggest2(out, "the literal letter 't'"),
        _ => {}
    }
}

pub(super) fn check_assign_to_self(_params: &Parameters, t: &Token, out: &mut Out) {
    let InnerToken::T_SimpleCommand { assignments, words } = &*t.inner else {
        return;
    };
    if !words.is_empty() {
        return;
    }
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
        if *mode != AssignmentMode::Assign || !indices.is_empty() {
            continue;
        }
        let parts = get_word_parts(value);
        if parts.len() == 1 {
            if let InnerToken::T_DollarBraced { op, .. } = &*parts[0].inner {
                if astlib::get_literal_string(op).as_deref() == Some(name.as_str()) {
                    info(
                        out,
                        var.id(),
                        2269,
                        "This variable is assigned to itself, so the assignment does nothing.",
                    );
                }
            }
        }
    }
}

pub(super) fn check_ps1_assignments(_params: &Parameters, t: &Token, out: &mut Out) {
    if let InnerToken::T_Assignment { var, value, .. } = &*t.inner {
        if var == "PS1" {
            let contents = oversimplify(value).concat();
            if contains_unescaped(&contents) {
                info(
                    out,
                    value.id(),
                    2025,
                    "Make sure all escape sequences are enclosed in \\[..\\] to prevent line wrapping issues",
                );
            }
        }
    }
}

fn enclosed_regex() -> &'static regex::Regex {
    static RE: OnceLock<regex::Regex> = OnceLock::new();
    RE.get_or_init(|| regex::Regex::new(r"\\\[.*\\\]").unwrap())
}

fn escape_regex() -> &'static regex::Regex {
    static RE: OnceLock<regex::Regex> = OnceLock::new();
    RE.get_or_init(|| regex::Regex::new(r"\\x1[Bb]|\\e|\x1b|\\033").unwrap())
}

fn contains_unescaped(s: &str) -> bool {
    let unenclosed = enclosed_regex().replace_all(s, "");
    escape_regex().is_match(&unenclosed)
}

fn subshell_should_ignore(name: &str) -> bool {
    matches!(name, "@" | "*" | "_" | "IFS")
}

/// `data VariableState = Dead Token String | Alive`.
#[derive(Clone)]
enum VarState {
    Alive,
    /// `Dead writeToken reason`
    Dead(Token, String),
}

const ARRAY_VARIABLES: &[&str] = &[
    "BASH_ALIASES",
    "BASH_ARGC",
    "BASH_ARGV",
    "BASH_CMDS",
    "BASH_LINENO",
    "BASH_REMATCH",
    "BASH_SOURCE",
    "BASH_VERSINFO",
    "COMP_WORDS",
    "COPROC",
    "DIRSTACK",
    "FUNCNAME",
    "GROUPS",
    "MAPFILE",
    "PIPESTATUS",
    "COMPREPLY",
];

/// `isIndexed (T_Assignment _ _ _ (_:_) _) = True`.
fn is_indexed(expr: &Token) -> bool {
    matches!(&*expr.inner, InnerToken::T_Assignment { indices, .. } if !indices.is_empty())
}

fn commarray_literal(t: &Token) -> String {
    use InnerToken::*;
    match &*t.inner {
        T_IndexedElement { value, .. } => commarray_literal(value),
        T_NormalWord(l) => l.iter().map(commarray_literal).collect(),
        T_Literal(s) => s.clone(),
        _ => String::new(),
    }
}

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

/// `decodeEscapes` for `$'..'` contents (ANSI-C), matching ASTLib.
fn decode_escapes(s: &str) -> String {
    let chars: Vec<char> = s.chars().collect();
    let mut out = String::new();
    let mut i = 0;
    while i < chars.len() {
        if chars[i] == '\\' && i + 1 < chars.len() {
            let c = chars[i + 1];
            match c {
                'a' => {
                    out.push('\u{07}');
                    i += 2;
                }
                'b' => {
                    out.push('\u{08}');
                    i += 2;
                }
                'e' | 'E' => {
                    out.push('\u{1B}');
                    i += 2;
                }
                'f' => {
                    out.push('\u{0C}');
                    i += 2;
                }
                'n' => {
                    out.push('\n');
                    i += 2;
                }
                'r' => {
                    out.push('\r');
                    i += 2;
                }
                't' => {
                    out.push('\t');
                    i += 2;
                }
                'v' => {
                    out.push('\u{0B}');
                    i += 2;
                }
                '\\' => {
                    out.push('\\');
                    i += 2;
                }
                '\'' => {
                    out.push('\'');
                    i += 2;
                }
                '"' => {
                    out.push('"');
                    i += 2;
                }
                '?' => {
                    out.push('?');
                    i += 2;
                }
                'x' => {
                    let hex: String = chars[i + 2..].iter().take(2).collect();
                    match u32::from_str_radix(&hex, 16) {
                        Ok(n) if !hex.is_empty() => {
                            if let Some(ch) = char::from_u32(n) {
                                out.push(ch);
                            }
                            i += 2 + hex.len();
                        }
                        _ => {
                            out.push('\\');
                            out.push('x');
                            i += 2;
                        }
                    }
                }
                'u' | 'U' => {
                    let width = if c == 'u' { 4 } else { 8 };
                    let hex: String = chars[i + 2..].iter().take(width).collect();
                    match u32::from_str_radix(&hex, 16) {
                        Ok(n) if !hex.is_empty() => {
                            if let Some(ch) = char::from_u32(n) {
                                out.push(ch);
                            }
                            i += 2 + hex.len();
                        }
                        _ => {
                            out.push('\\');
                            out.push('x');
                            i += 2;
                        }
                    }
                }
                _ => {
                    let oct: String = chars[i + 1..].iter().take(3).collect();
                    match u32::from_str_radix(&oct, 8) {
                        Ok(n) => {
                            if let Some(ch) = char::from_u32(n % 256) {
                                out.push(ch);
                            }
                            i += 1 + oct.len();
                        }
                        _ => {
                            out.push('\\');
                            out.push(c);
                            i += 2;
                        }
                    }
                }
            }
        } else {
            out.push(chars[i]);
            i += 1;
        }
    }
    out
}

/// `getLiteralString` mirroring ASTLib (decodes `$'..'`).
fn decoded_literal_string(t: &Token) -> Option<String> {
    use InnerToken::*;
    match &*t.inner {
        T_Literal(s) | T_SingleQuoted(s) | T_ParamSubSpecialChar(s) => Some(s.clone()),
        T_DollarSingleQuoted(s) => Some(decode_escapes(s)),
        T_DoubleQuoted(l) | T_DollarDoubleQuoted(l) | T_NormalWord(l) | TA_Expansion(l) => {
            let mut out = String::new();
            for p in l {
                out.push_str(&decoded_literal_string(p)?);
            }
            Some(out)
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
    fn prop_checkArrayWithoutIndex1() {
        assert!(tree_emits(
            check_array_without_index,
            "foo=(a b); echo $foo"
        ));
    }

    #[test]
    fn prop_checkArrayWithoutIndex2() {
        assert!(!tree_emits(
            check_array_without_index,
            "foo='bar baz'; foo=($foo); echo ${foo[0]}"
        ));
    }

    #[test]
    fn prop_checkArrayWithoutIndex3() {
        assert!(tree_emits(
            check_array_without_index,
            "coproc foo while true; do echo cow; done; echo $foo"
        ));
    }

    #[test]
    fn prop_checkArrayWithoutIndex4() {
        assert!(tree_emits(
            check_array_without_index,
            "coproc tail -f log; echo $COPROC"
        ));
    }

    #[test]
    fn prop_checkArrayWithoutIndex5() {
        assert!(tree_emits(check_array_without_index, "a[0]=foo; echo $a"));
    }

    #[test]
    fn prop_checkArrayWithoutIndex6() {
        assert!(tree_emits(check_array_without_index, "echo $PIPESTATUS"));
    }

    #[test]
    fn prop_checkArrayWithoutIndex7() {
        assert!(tree_emits(check_array_without_index, "a=(a b); a+=c"));
    }

    #[test]
    fn prop_checkArrayWithoutIndex8() {
        assert!(tree_emits(
            check_array_without_index,
            "declare -a foo; foo=bar;"
        ));
    }

    #[test]
    fn prop_checkArrayWithoutIndex9() {
        assert!(tree_emits(
            check_array_without_index,
            "read -r -a arr <<< 'foo bar'; echo \"$arr\""
        ));
    }

    #[test]
    fn prop_checkArrayWithoutIndex10() {
        assert!(tree_emits(
            check_array_without_index,
            "read -ra arr <<< 'foo bar'; echo \"$arr\""
        ));
    }

    #[test]
    fn prop_checkArrayWithoutIndex11() {
        assert!(!tree_emits(
            check_array_without_index,
            "read -rpfoobar r; r=42"
        ));
    }

    // SC2030 / SC2031 — subshellAssignmentCheck

    #[test]
    fn prop_subshellAssignmentCheck() {
        assert!(tree_emits(
            check_subshell_assignment,
            "cat foo | while read bar; do a=$bar; done; echo \"$a\""
        ));
    }

    #[test]
    fn prop_subshellAssignmentCheck2() {
        assert!(!tree_emits(
            check_subshell_assignment,
            "while read bar; do a=$bar; done < file; echo \"$a\""
        ));
    }

    #[test]
    fn prop_subshellAssignmentCheck3() {
        assert!(tree_emits(check_subshell_assignment, "( A=foo; ); rm $A"));
    }

    #[test]
    fn prop_subshellAssignmentCheck4() {
        assert!(!tree_emits(check_subshell_assignment, "( A=foo; rm $A; )"));
    }

    #[test]
    fn prop_subshellAssignmentCheck5() {
        assert!(tree_emits(
            check_subshell_assignment,
            "cat foo | while read cow; do true; done; echo $cow;"
        ));
    }

    #[test]
    fn prop_subshellAssignmentCheck6() {
        assert!(tree_emits(
            check_subshell_assignment,
            "( export lol=$(ls); ); echo $lol;"
        ));
    }

    #[test]
    fn prop_subshellAssignmentCheck6a() {
        assert!(tree_emits(
            check_subshell_assignment,
            "( typeset -a lol=a; ); echo $lol;"
        ));
    }

    #[test]
    fn prop_subshellAssignmentCheck7() {
        assert!(tree_emits(
            check_subshell_assignment,
            "cmd | while read foo; do (( n++ )); done; echo \"$n lines\""
        ));
    }

    #[test]
    fn prop_subshellAssignmentCheck8() {
        assert!(tree_emits(check_subshell_assignment, "n=3 & echo $((n++))"));
    }

    #[test]
    fn prop_subshellAssignmentCheck9() {
        assert!(tree_emits(check_subshell_assignment, "read n & n=foo$n"));
    }

    #[test]
    fn prop_subshellAssignmentCheck10() {
        assert!(tree_emits(
            check_subshell_assignment,
            "(( n <<= 3 )) & (( n |= 4 )) &"
        ));
    }

    #[test]
    fn prop_subshellAssignmentCheck11() {
        assert!(tree_emits(
            check_subshell_assignment,
            "cat /etc/passwd | while read line; do let n=n+1; done\necho $n"
        ));
    }

    #[test]
    fn prop_subshellAssignmentCheck12() {
        assert!(tree_emits(
            check_subshell_assignment,
            "cat /etc/passwd | while read line; do let ++n; done\necho $n"
        ));
    }

    #[test]
    fn prop_subshellAssignmentCheck13() {
        assert!(tree_emits(
            check_subshell_assignment,
            "#!/bin/bash\necho foo | read bar; echo $bar"
        ));
    }

    #[test]
    fn prop_subshellAssignmentCheck14() {
        assert!(!tree_emits(
            check_subshell_assignment,
            "#!/bin/ksh93\necho foo | read bar; echo $bar"
        ));
    }

    #[test]
    fn prop_subshellAssignmentCheck15() {
        assert!(!tree_emits(
            check_subshell_assignment,
            "#!/bin/ksh\ncat foo | while read bar; do a=$bar; done\necho \"$a\""
        ));
    }

    #[test]
    fn prop_subshellAssignmentCheck16() {
        assert!(!tree_emits(check_subshell_assignment, "(set -e); echo $@"));
    }

    #[test]
    fn prop_subshellAssignmentCheck17() {
        assert!(!tree_emits(
            check_subshell_assignment,
            "foo=${ { bar=$(baz); } 2>&1; }; echo $foo $bar"
        ));
    }

    #[test]
    fn prop_subshellAssignmentCheck18() {
        assert!(tree_emits(
            check_subshell_assignment,
            "( exec {n}>&2; ); echo $n"
        ));
    }

    #[test]
    fn prop_subshellAssignmentCheck19() {
        assert!(!tree_emits(
            check_subshell_assignment,
            "#!/bin/bash\nshopt -s lastpipe; echo a | read -r b; echo \"$b\""
        ));
    }

    #[test]
    fn prop_subshellAssignmentCheck20() {
        assert!(tree_emits(
            check_subshell_assignment,
            "@test 'foo' { a=1; }\n@test 'bar' { echo $a; }\n"
        ));
    }

    #[test]
    fn prop_subshellAssignmentCheck21() {
        assert!(!tree_emits(
            check_subshell_assignment,
            "test1() { echo foo | if [[ $var ]]; then echo $var; fi; }; test2() { echo $var; }"
        ));
    }

    #[test]
    fn prop_subshellAssignmentCheck22() {
        assert!(!tree_emits(
            check_subshell_assignment,
            "( [[ -n $foo || -z $bar ]] ); echo $foo $bar"
        ));
    }

    #[test]
    fn prop_subshellAssignmentCheck23() {
        assert!(!tree_emits(
            check_subshell_assignment,
            "( export foo ); echo $foo"
        ));
    }

    #[test]
    fn prop_subshellAssignmentCheck24() {
        assert!(!tree_emits(
            check_subshell_assignment,
            "( read -r a _ c <<< 'x y z'; ); echo $_"
        ));
    }

    #[test]
    fn prop_subshellAssignmentCheck25() {
        assert!(!tree_emits(
            check_subshell_assignment,
            "( _=discard; ); echo $_"
        ));
    }

    // SC2095 — checkWhileReadPitfalls

    #[test]
    fn prop_checkCommarrays1() {
        assert!(emits(check_commarrays, "a=(1, 2)"));
    }

    #[test]
    fn prop_checkCommarrays2() {
        assert!(emits(check_commarrays, "a+=(1,2,3)"));
    }

    #[test]
    fn prop_checkCommarrays3() {
        assert!(!emits(check_commarrays, "cow=(1 \"foo,bar\" 3)"));
    }

    #[test]
    fn prop_checkCommarrays4() {
        assert!(!emits(check_commarrays, "cow=('one,' 'two')"));
    }

    #[test]
    fn prop_checkCommarrays5() {
        assert!(emits(check_commarrays, "a=([a]=b, [c]=d)"));
    }

    #[test]
    fn prop_checkCommarrays6() {
        assert!(emits(check_commarrays, "a=([a]=b,[c]=d,[e]=f)"));
    }

    #[test]
    fn prop_checkCommarrays7() {
        assert!(emits(check_commarrays, "a=(1,2)"));
    }

    // SC2010 — ls | grep

    // SC2028 — checkUnusedEchoEscapes

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
    fn prop_checkDollarBrackets1() {
        assert!(node_emits(check_dollar_brackets, "echo $[1+2]"));
    }

    #[test]
    fn prop_checkDollarBrackets2() {
        assert!(!node_emits(check_dollar_brackets, "echo $((1+2))"));
    }

    // ---- SC2087 checkSshHereDoc ----

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

    #[test]
    fn prop_checkOverridingPath1() {
        assert!(emits(check_overriding_path, "PATH=\"$var/$foo\""));
    }

    #[test]
    fn prop_checkOverridingPath2() {
        assert!(emits(check_overriding_path, "PATH=\"mydir\""));
    }

    #[test]
    fn prop_checkOverridingPath3() {
        assert!(emits(check_overriding_path, "PATH=/cow/foo"));
    }

    #[test]
    fn prop_checkOverridingPath4() {
        assert!(!emits(check_overriding_path, "PATH=/cow/foo/bin"));
    }

    #[test]
    fn prop_checkOverridingPath5() {
        assert!(!emits(check_overriding_path, "PATH='/bin:/sbin'"));
    }

    #[test]
    fn prop_checkOverridingPath6() {
        assert!(!emits(check_overriding_path, "PATH=\"$var/$foo\" cmd"));
    }

    #[test]
    fn prop_checkOverridingPath7() {
        assert!(!emits(check_overriding_path, "PATH=$OLDPATH"));
    }

    #[test]
    fn prop_checkOverridingPath8() {
        assert!(!emits(check_overriding_path, "PATH=$PATH:/stuff"));
    }

    // ---- checkTildeInPath ----

    #[test]
    fn prop_checkSuspiciousIFS1() {
        assert!(emits(check_suspicious_ifs, "IFS=\"\\n\""));
    }

    #[test]
    fn prop_checkSuspiciousIFS2() {
        assert!(!emits(check_suspicious_ifs, "IFS=$'\\t'"));
    }

    #[test]
    fn prop_checkSuspiciousIFS3() {
        assert!(emits(check_suspicious_ifs, "IFS=' \\t\\n'"));
    }

    // ---- checkShouldUseGrepQ ----

    #[test]
    fn prop_checkAssignToSelf1() {
        assert!(emits(check_assign_to_self, "x=$x"));
    }

    #[test]
    fn prop_checkAssignToSelf2() {
        assert!(emits(check_assign_to_self, "x=${x}"));
    }

    #[test]
    fn prop_checkAssignToSelf3() {
        assert!(emits(check_assign_to_self, "x=\"$x\""));
    }

    #[test]
    fn prop_checkAssignToSelf4() {
        assert!(!emits(check_assign_to_self, "x=$x mycmd"));
    }

    // ---- checkCommandWithTrailingSymbol ----
}
