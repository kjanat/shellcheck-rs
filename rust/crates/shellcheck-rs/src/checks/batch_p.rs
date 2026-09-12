//! Ported check batch p. See rust/PORTING.md.
//!
//! Function / external-command and quote-in-literal checks ported from
//! `ShellCheck.Analytics` and `ShellCheck.Checks.Commands`:
//!   * SC2032 / SC2033 — `checkFunctionsUsedExternally`
//!     (a shell function/alias passed to an external command like sudo/xargs/find -exec).
//!   * SC2119 / SC2120 — `checkUnpassedInFunctions`
//!     (a function references `$1..`/`$@`/`$#` but is only ever called with no args).
//!   * SC2089 / SC2090 — `checkQuotesInLiterals`
//!     (quotes/backslashes in a variable's value are treated literally, not as syntax).
//!   * SC2229            — `checkReadExpansions` (the `dollarWarning` branch only):
//!     `read $var` does not read into `var`.
//!
//! The variable-flow checks lean on the linear `variableFlow`
//! (`params.variable_flow`) / `get_variable_flow`, which the Rust port produces
//! faithfully (see `analyzer_lib::get_variable_flow`).
use crate::analyzer_lib::is_unqualified_command;
use crate::analyzer_lib::*;
use crate::ast::*;
use crate::astlib;
use crate::astlib::basename;
use crate::astlib::e4m;
use crate::astlib::is_annotation_ignoring_code;
use crate::astlib::oversimplify;
use crate::cfg::get_braced_modifier;
use crate::cfg::get_unquoted_literal;
use crate::interface::Shell;
use std::collections::HashMap;

pub fn register(c: &mut Checker) {
    c.tree(check_functions_used_externally);
    c.tree(check_unpassed_in_functions);
    c.tree(check_quotes_in_literals);
}

// ---------------------------------------------------------------------------
// Shared local helpers (ported from ASTLib / AnalyzerLib; kept private so this
// module does not touch shared files that parallel agents also edit).
// ---------------------------------------------------------------------------

/// `supportsArrays`.
fn supports_arrays(shell: Shell) -> bool {
    matches!(shell, Shell::Bash | Shell::Ksh)
}

/// `shouldIgnoreCode params code t`.
fn should_ignore_code(params: &Parameters, code: i64, t: &Token) -> bool {
    get_path(params, t)
        .iter()
        .any(|p| is_annotation_ignoring_code(code, p))
}

// ===========================================================================
// SC2032 / SC2033 — checkFunctionsUsedExternally
// ===========================================================================

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

fn check_functions_used_externally(params: &Parameters, root: &Token, out: &mut Out) {
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

// ===========================================================================
// SC2119 / SC2120 — checkUnpassedInFunctions
// ===========================================================================

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

fn check_unpassed_in_functions(params: &Parameters, root: &Token, out: &mut Out) {
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

// ===========================================================================
// SC2089 / SC2090 — checkQuotesInLiterals
// ===========================================================================

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

fn check_quotes_in_literals(params: &Parameters, _root: &Token, out: &mut Out) {
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

// ===========================================================================
// Tests
// ===========================================================================

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
    fn tree_emits(f: fn(&Parameters, &Token, &mut Out), s: &str) -> bool {
        let params = params_for(s);
        let mut out = Out::new();
        f(&params, &params.root, &mut out);
        !out.is_empty()
    }
    // SC2032 / SC2033 — checkFunctionsUsedExternally
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
}
