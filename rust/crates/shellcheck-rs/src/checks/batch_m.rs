//! Ported check batch m. See rust/PORTING.md.
//!
//! Flow / subshell-scope based checks ported from `ShellCheck.Analytics`:
//!   * SC2030 / SC2031 — `subshellAssignmentCheck` / `findSubshelled`
//!     (variable modified/used across a subshell boundary).
//!   * SC2128 (+ SC2178 / SC2179) — `checkArrayWithoutIndex`
//!     (expanding an array without an index gives only the first element).
//!
//! Both lean on the linear `variableFlow` (`params.variable_flow`), which the
//! Rust port now produces faithfully (see `analyzer_lib::get_variable_flow`).
#![allow(unused_imports, unused_variables, dead_code)]
use crate::analyzer_lib::get_all_flags;
use crate::analyzer_lib::is_true_assignment_source;
use crate::analyzer_lib::*;
use crate::ast::*;
use crate::astlib;
use crate::astlib::oversimplify;
use crate::interface::{Fix, Shell};
use std::collections::{HashMap, HashSet};

pub fn register(c: &mut Checker) {
    c.tree(check_subshell_assignment);
    c.tree(check_array_without_index);
    // SC2095: enabled now that the T_WhileExpression/until span is fixed in the
    // parser (trailing spacing after `done` consumed, matching ShellCheck).
    c.node(check_while_read_pitfalls);
}

// ===========================================================================
// SC2030 / SC2031 — subshellAssignmentCheck / findSubshelled
// ===========================================================================

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

fn check_subshell_assignment(params: &Parameters, _root: &Token, out: &mut Out) {
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

// ===========================================================================
// SC2128 (+ SC2178 / SC2179) — checkArrayWithoutIndex
// ===========================================================================

// ShellCheck.Data.arrayVariables
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

fn check_array_without_index(params: &Parameters, _root: &Token, out: &mut Out) {
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

/// `isIndexed (T_Assignment _ _ _ (_:_) _) = True`.
fn is_indexed(expr: &Token) -> bool {
    matches!(&*expr.inner, InnerToken::T_Assignment { indices, .. } if !indices.is_empty())
}

// ===========================================================================
// SC2095 — checkWhileReadPitfalls
// ===========================================================================

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

fn check_while_read_pitfalls(params: &Parameters, t: &Token, out: &mut Out) {
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
                            for seq in get_command_sequences(&part) {
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
                    .filter_map(astlib::get_literal_string)
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
fn get_words(t: &Token) -> Vec<Token> {
    match &*t.inner {
        InnerToken::T_Assignment { value, .. } => crate::cfg::get_word_parts(value),
        _ => crate::cfg::get_word_parts(t),
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
    fn node_emits(f: fn(&Parameters, &Token, &mut Out), s: &str) -> bool {
        let params = params_for(s);
        let mut out = Out::new();
        params.root.visit_preorder(&mut |t| f(&params, t, &mut out));
        !out.is_empty()
    }

    // SC2128 — checkArrayWithoutIndex
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
}
