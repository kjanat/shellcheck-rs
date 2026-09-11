//! Dataflow checks ported from `ShellCheck.Analytics`:
//!   * SC2034 — `checkUnusedAssignments` (linear `variableFlow`, tree check).
//!   * SC2154 / SC2153 — `checkUnassignedReferences'` (linear `variableFlow`).
//!   * SC2086 / SC2223 — `checkSpacefulnessCfg'` (CFG data-flow, node check).
//!
//! SC2154/SC2034 use the linear `variableFlow`; SC2086 uses the CFG incoming
//! state. Faithful port; see the referenced Haskell for the exact semantics.
#![allow(clippy::collapsible_if)]

use crate::analyzer_lib::*;
use crate::ast::*;
use crate::cfg::{CFVariableProp, get_braced_modifier, get_braced_reference, is_variable_char};
use crate::cfg_analysis::SpaceStatus;
use crate::interface::Shell;
use std::collections::BTreeMap;

pub fn register(c: &mut Checker) {
    c.tree(check_unused_assignments);
    c.tree(check_unassigned_references);
    c.node(check_spacefulness_cfg);
}

// ShellCheck.Data.internalVariables
const INTERNAL_VARIABLES: &[&str] = &[
    "",
    "_",
    "rest",
    "REST",
    "CDPATH",
    "ENV",
    "FCEDIT",
    "HISTFILE",
    "HISTSIZE",
    "HOME",
    "IFS",
    "LANG",
    "LC_ALL",
    "LC_COLLATE",
    "LC_CTYPE",
    "LC_MESSAGES",
    "LC_MONETARY",
    "LC_NUMERIC",
    "LC_TIME",
    "MAIL",
    "MAILCHECK",
    "MAILPATH",
    "OLDPWD",
    "OPTARG",
    "OPTIND",
    "PATH",
    "PWD",
    "BASH",
    "BASHOPTS",
    "BASHPID",
    "BASH_ALIASES",
    "BASH_ARGC",
    "BASH_ARGV",
    "BASH_ARGV0",
    "BASH_CMDS",
    "BASH_COMMAND",
    "BASH_EXECUTION_STRING",
    "BASH_LINENO",
    "BASH_LOADABLES_PATH",
    "BASH_REMATCH",
    "BASH_SOURCE",
    "BASH_SUBSHELL",
    "BASH_VERSINFO",
    "BASH_VERSION",
    "COMP_CWORD",
    "COMP_KEY",
    "COMP_LINE",
    "COMP_POINT",
    "COMP_TYPE",
    "COMP_WORDBREAKS",
    "COMP_WORDS",
    "COPROC",
    "DIRSTACK",
    "EPOCHREALTIME",
    "EPOCHSECONDS",
    "EUID",
    "FUNCNAME",
    "GROUPS",
    "HISTCMD",
    "HOSTNAME",
    "HOSTTYPE",
    "MACHTYPE",
    "MAPFILE",
    "OSTYPE",
    "PIPESTATUS",
    "RANDOM",
    "READLINE_ARGUMENT",
    "READLINE_LINE",
    "READLINE_MARK",
    "READLINE_POINT",
    "REPLY",
    "SECONDS",
    "SHELLOPTS",
    "SHLVL",
    "SRANDOM",
    "UID",
    "BASH_COMPAT",
    "BASH_ENV",
    "BASH_XTRACEFD",
    "CHILD_MAX",
    "COLUMNS",
    "COMPREPLY",
    "EMACS",
    "EXECIGNORE",
    "FIGNORE",
    "FUNCNEST",
    "GLOBIGNORE",
    "HISTCONTROL",
    "HISTFILESIZE",
    "HISTIGNORE",
    "HISTTIMEFORMAT",
    "HOSTFILE",
    "IGNOREEOF",
    "INPUTRC",
    "INSIDE_EMACS",
    "LINES",
    "OPTERR",
    "POSIXLY_CORRECT",
    "PROMPT_COMMAND",
    "PROMPT_DIRTRIM",
    "PS0",
    "PS1",
    "PS2",
    "PS3",
    "PS4",
    "SHELL",
    "TIMEFORMAT",
    "TMOUT",
    "BASH_MONOSECONDS",
    "BASH_TRAPSIG",
    "GLOBSORT",
    "auto_resume",
    "histchars",
    "USER",
    "TZ",
    "TERM",
    "LOGNAME",
    "LD_LIBRARY_PATH",
    "LANGUAGE",
    "DISPLAY",
    "HOSTNAME",
    "KRB5CCNAME",
    "LINENO",
    "PPID",
    "TMPDIR",
    "XAUTHORITY",
    ".sh.version",
    "FLAGS_ARGC",
    "FLAGS_ARGV",
    "FLAGS_ERROR",
    "FLAGS_FALSE",
    "FLAGS_HELP",
    "FLAGS_PARENT",
    "FLAGS_RESERVED",
    "FLAGS_TRUE",
    "FLAGS_VERSION",
    "flags_error",
    "flags_return",
    "stderr",
    "stderr_lines",
];

// ShellCheck.Data.commonCommands
const COMMON_COMMANDS: &[&str] = &[
    "admin",
    "alias",
    "ar",
    "asa",
    "at",
    "awk",
    "basename",
    "batch",
    "bc",
    "bg",
    "break",
    "c99",
    "cal",
    "cat",
    "cd",
    "cflow",
    "chgrp",
    "chmod",
    "chown",
    "cksum",
    "cmp",
    "colon",
    "comm",
    "command",
    "compress",
    "continue",
    "cp",
    "crontab",
    "csplit",
    "ctags",
    "cut",
    "cxref",
    "date",
    "dd",
    "delta",
    "df",
    "diff",
    "dirname",
    "dot",
    "du",
    "echo",
    "ed",
    "env",
    "eval",
    "ex",
    "exec",
    "exit",
    "expand",
    "export",
    "expr",
    "fc",
    "fg",
    "file",
    "find",
    "fold",
    "fuser",
    "gencat",
    "get",
    "getconf",
    "getopts",
    "gettext",
    "grep",
    "hash",
    "head",
    "iconv",
    "ipcrm",
    "ipcs",
    "jobs",
    "join",
    "kill",
    "lex",
    "link",
    "ln",
    "locale",
    "localedef",
    "logger",
    "logname",
    "lp",
    "ls",
    "m4",
    "mailx",
    "make",
    "man",
    "mesg",
    "mkdir",
    "mkfifo",
    "more",
    "msgfmt",
    "mv",
    "newgrp",
    "ngettext",
    "nice",
    "nl",
    "nm",
    "nohup",
    "od",
    "paste",
    "patch",
    "pathchk",
    "pax",
    "pr",
    "printf",
    "prs",
    "ps",
    "pwd",
    "read",
    "readlink",
    "readonly",
    "realpath",
    "renice",
    "return",
    "rm",
    "rmdel",
    "rmdir",
    "sact",
    "sccs",
    "sed",
    "set",
    "sh",
    "shift",
    "sleep",
    "sort",
    "split",
    "strings",
    "strip",
    "stty",
    "tabs",
    "tail",
    "talk",
    "tee",
    "test",
    "time",
    "timeout",
    "times",
    "touch",
    "tput",
    "tr",
    "trap",
    "tsort",
    "tty",
    "type",
    "ulimit",
    "umask",
    "unalias",
    "uname",
    "uncompress",
    "unexpand",
    "unget",
    "uniq",
    "unlink",
    "unset",
    "uucp",
    "uudecode",
    "uuencode",
    "uustat",
    "uux",
    "val",
    "vi",
    "wait",
    "wc",
    "what",
    "who",
    "write",
    "xargs",
    "xgettext",
    "yacc",
    "zcat",
];

// ===========================================================================
// SC2034 — checkUnusedAssignments
// ===========================================================================

fn check_unused_assignments(params: &Parameters, _root: &Token, out: &mut Out) {
    let flow = &params.variable_flow;

    // references: stripSuffix of every Reference name, plus internalVariables.
    let mut references: std::collections::BTreeSet<String> = std::collections::BTreeSet::new();
    for sd in flow {
        if let StackData::Reference(_, _, name) = sd {
            references.insert(strip_suffix(name));
        }
    }
    for v in INTERNAL_VARIABLES {
        references.insert((*v).to_string());
    }
    // Variables embedded in unquoted globs (e.g. `foo[$key]`) are real
    // references that ShellCheck sees by parsing `$key`; this parser keeps the
    // glob as a flat string, so scan glob literals for `$var` names. SC2034
    // uses references as a set, so this only suppresses (never misplaces).
    params.root.visit_preorder(&mut |t| {
        if let InnerToken::T_Glob(s) = &*t.inner {
            for name in variables_in_glob(s) {
                references.insert(name);
            }
        }
    });

    // assignments: Map.fromList (last write per name), only real variable names.
    let mut assignments: BTreeMap<String, Token> = BTreeMap::new();
    for sd in flow {
        if let StackData::Assignment(_, token, name, _) = sd {
            if astlib_is_variable_name(name) {
                assignments.insert(name.clone(), token.clone());
            }
        }
    }

    // unused = assignments not in references (Map.assocs -> sorted by name).
    for (name, token) in assignments.iter() {
        if references.contains(name) {
            continue;
        }
        if name.starts_with('_') {
            continue;
        }
        warn(
            out,
            token.id(),
            2034,
            &format!(
                "{} appears unused. Verify use (or export if used externally).",
                name
            ),
        );
    }
}

fn strip_suffix(name: &str) -> String {
    name.chars().take_while(|c| is_variable_char(*c)).collect()
}

fn variables_in_glob(s: &str) -> Vec<String> {
    use std::sync::OnceLock;
    static RE: OnceLock<regex::Regex> = OnceLock::new();
    let re = RE.get_or_init(|| regex::Regex::new(r"\$\{?([A-Za-z_][A-Za-z0-9_]*)").unwrap());
    re.captures_iter(s)
        .filter_map(|c| c.get(1).map(|m| m.as_str().to_string()))
        .collect()
}

// ===========================================================================
// SC2154 / SC2153 — checkUnassignedReferences' (includeGlobals = False)
// ===========================================================================

fn check_unassigned_references(params: &Parameters, root: &Token, out: &mut Out) {
    check_unassigned_references_impl(params, root, out, false);
}

fn check_unassigned_references_impl(
    params: &Parameters,
    _root: &Token,
    out: &mut Out,
    include_globals: bool,
) {
    let flow = &params.variable_flow;

    // read map (first occurrence wins), write set.
    let mut read_map: BTreeMap<String, Token> = BTreeMap::new();
    let mut write_map: BTreeMap<String, ()> = BTreeMap::new();
    for sd in flow {
        match sd {
            StackData::Assignment(_, _, name, _) => {
                write_map.insert(name.clone(), ());
            }
            StackData::Reference(_, place, name) => {
                read_map
                    .entry(name.clone())
                    .or_insert_with(|| place.clone());
            }
            _ => {}
        }
    }

    let default_assigned: std::collections::BTreeSet<&str> = INTERNAL_VARIABLES
        .iter()
        .copied()
        .filter(|s| !s.is_empty())
        .collect();

    let written_vars: Vec<String> = write_map
        .keys()
        .filter(|k| astlib_is_variable_name(k))
        .cloned()
        .collect();

    // unassigned = readMap - writeMap - defaultAssigned, sorted by name.
    for (var, place) in read_map.iter() {
        if write_map.contains_key(var) || default_assigned.contains(var.as_str()) {
            continue;
        }
        if !astlib_is_variable_name(var) {
            continue;
        }
        if is_exception(params, var, place) || is_guarded(place) {
            continue;
        }
        if include_globals || is_local(var) {
            // SC2154
            let optional_tip = if COMMON_COMMANDS.contains(&var.as_str()) {
                format!(" (for output from commands, use \"$({} ...)\" )", var)
            } else {
                match get_best_match(var, &written_vars) {
                    Some(m) => format!(" (did you mean '{}'?)", m),
                    None => String::new(),
                }
            };
            warn(
                out,
                place.id(),
                2154,
                &format!("{} is referenced but not assigned{}.", var, optional_tip),
            );
        } else {
            // SC2153
            if let Some(m) = get_best_match(var, &written_vars) {
                info(
                    out,
                    place.id(),
                    2153,
                    &format!(
                        "Possible misspelling: {} may not be assigned. Did you mean {}?",
                        var, m
                    ),
                );
            }
        }
    }
}

fn is_local(var: &str) -> bool {
    var.chars().any(|c| c.is_lowercase())
}

fn match_score(var: &str, candidate: &str) -> usize {
    if var != candidate && var.to_lowercase() == candidate.to_lowercase() {
        1
    } else {
        dist(var, candidate)
    }
}

fn get_best_match(var: &str, written_vars: &[String]) -> Option<String> {
    // sortBy (comparing snd) is stable; keep first-min by original order.
    let mut best: Option<(&String, usize)> = None;
    for x in written_vars {
        let score = match_score(var, x);
        match &best {
            Some((_, bs)) if *bs <= score => {}
            _ => best = Some((x, score)),
        }
    }
    let (m, score) = best?;
    let l = m.chars().count();
    let good = (l > 3 && score <= 1) || (l > 7 && score <= 2);
    if good { Some(m.clone()) } else { None }
}

/// `isException var t`: any ancestor `${...}` uses `var` as an index or guards it.
fn is_exception(params: &Parameters, var: &str, t: &Token) -> bool {
    for anc in get_path(params, t) {
        if let InnerToken::T_DollarBraced { op, .. } = &*anc.inner {
            let str = concat_over(op);
            let reference = get_braced_reference(&str);
            let modifier = get_braced_modifier(&str);
            if reference != var || modifier.starts_with('+') || modifier.starts_with(":+") {
                return true;
            }
        }
    }
    false
}

/// `isGuarded (T_DollarBraced ...)`: `:?`/`:-` (with optional index) modifier.
fn is_guarded(t: &Token) -> bool {
    if let InnerToken::T_DollarBraced { op, .. } = &*t.inner {
        let name = concat_over(op);
        // dropWhile (`elem` "#!") then dropWhile isVariableChar
        let rest: String = name
            .chars()
            .skip_while(|c| *c == '#' || *c == '!')
            .collect();
        let rest: String = rest.chars().skip_while(|c| is_variable_char(*c)).collect();
        guard_regex_match(&rest)
    } else {
        false
    }
}

/// `^(\[.*\])?:?[-?]`.
fn guard_regex_match(s: &str) -> bool {
    let b: Vec<char> = s.chars().collect();
    let mut i = 0;
    // optional [ ... ]
    if i < b.len() && b[i] == '[' {
        // greedy up to last ']'
        if let Some(last) = b.iter().rposition(|c| *c == ']') {
            if last > i {
                i = last + 1;
            }
        }
    }
    if i < b.len() && b[i] == ':' {
        i += 1;
    }
    i < b.len() && (b[i] == '-' || b[i] == '?')
}

fn astlib_is_variable_name(s: &str) -> bool {
    crate::cfg::is_variable_name(s)
}

// ===========================================================================
// SC2086 / SC2223 — checkSpacefulnessCfg'
// ===========================================================================

fn check_spacefulness_cfg(params: &Parameters, token: &Token, out: &mut Out) {
    check_spacefulness_cfg_impl(true, params, token, out);
}

fn check_spacefulness_cfg_impl(
    dirty_pass: bool,
    params: &Parameters,
    token: &Token,
    out: &mut Out,
) {
    let (id, op) = match &*token.inner {
        InnerToken::T_DollarBraced { op, .. } => (token.id(), op),
        _ => return,
    };

    let braced_string = concat_over(op);
    let name = get_braced_reference(&braced_string);

    let needs_quoting = !is_array_expansion(token)
        && !is_counting_reference(token)
        && !is_quote_free(params, token)
        && !is_quoted_alternative_reference(token)
        && !used_as_command_name(params, token);

    if !needs_quoting {
        return;
    }

    let is_clean = compute_is_clean(params, id, &name);
    // dirtyPass == not isClean  (dirtyPass is always true here)
    if dirty_pass != !is_clean {
        return;
    }

    if SPECIAL_VARIABLES_WITHOUT_SPACES.contains(&name.as_str())
        || quotes_may_conflict_with_sc2281(params, token)
    {
        return;
    }

    if dirty_pass {
        if is_default_assignment(params, &braced_string, token) {
            info(
                out,
                token.id(),
                2223,
                "This default assignment may cause DoS due to globbing. Quote it.",
            );
        } else {
            let fix = add_double_quotes_around(params, token);
            info_with_fix(
                out,
                id,
                2086,
                "Double quote to prevent globbing and word splitting.",
                fix,
            );
        }
    } else {
        // Verbose pass (optional check `quote-safe-variables`): SC2248.
        let fix = add_double_quotes_around(params, token);
        style_with_fix(
            out,
            id,
            2248,
            "Prefer double quoting even when variables don't contain special characters.",
            fix,
        );
    }
}

fn compute_is_clean(params: &Parameters, id: Id, name: &str) -> bool {
    (|| {
        let cfga = params.cfg_analysis.as_ref()?;
        let state = cfga.get_incoming_state(id)?;
        let value = state.variables_in_scope.get(name)?;
        // isCleanState
        let all_integer = value
            .variable_properties
            .iter()
            .all(|s| s.contains(&CFVariableProp::CFVPInteger));
        let clean = value.variable_value.space_status == SpaceStatus::SpaceStatusClean;
        Some(all_integer || clean)
    })()
    .unwrap_or(false)
}

fn is_default_assignment(params: &Parameters, braced_string: &str, token: &Token) -> bool {
    let modifier = get_braced_modifier(braced_string);
    (modifier.starts_with('=') || modifier.starts_with(":=")) && is_param_to(params, ":", token)
}

fn add_double_quotes_around(params: &Parameters, token: &Token) -> crate::interface::Fix {
    fix_with(vec![
        replace_start(params, token.id(), 0, "\""),
        replace_end(params, token.id(), 0, "\""),
    ])
}

/// `quotesMayConflictWithSC2281`.
fn quotes_may_conflict_with_sc2281(params: &Parameters, t: &Token) -> bool {
    let path = get_path(params, t);
    if path.len() < 3 {
        return false;
    }
    // path[1] must be a T_NormalWord (me : T_Literal "=..." : _) with me == t.
    let normalword = &path[1];
    let (parts, parent_id) = match &*normalword.inner {
        InnerToken::T_NormalWord(parts) => (parts, normalword.id()),
        _ => return false,
    };
    if parts.len() < 2 {
        return false;
    }
    let me_ok = parts[0].id() == t.id();
    let lit_ok = matches!(&*parts[1].inner, InnerToken::T_Literal(s) if s.starts_with('='));
    if !(me_ok && lit_ok) {
        return false;
    }
    // path[2] is T_SimpleCommand whose first word == normalword.
    match &*path[2].inner {
        InnerToken::T_SimpleCommand { words, .. } => {
            words.first().map(|w| w.id()) == Some(parent_id)
        }
        _ => false,
    }
}

#[allow(dead_code)]
fn shell_is_sh(shell: Shell) -> bool {
    matches!(shell, Shell::Sh | Shell::Dash | Shell::BusyboxSh)
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
    fn unassigned_globals(p: &Parameters, root: &Token, out: &mut Out) {
        check_unassigned_references_impl(p, root, out, true);
    }
    fn spaceful_verbose(p: &Parameters, t: &Token, out: &mut Out) {
        check_spacefulness_cfg_impl(false, p, t, out);
    }

    #[test]
    fn prop_checkSpacefulnessCfg1() {
        assert_eq!(
            node_emits(check_spacefulness_cfg, "a='cow moo'; echo $a"),
            true
        );
    }
    #[test]
    fn prop_checkSpacefulnessCfg2() {
        assert_eq!(
            node_emits(check_spacefulness_cfg, "a='cow moo'; [[ $a ]]"),
            false
        );
    }
    #[test]
    fn prop_checkSpacefulnessCfg3() {
        assert_eq!(
            node_emits(check_spacefulness_cfg, "a='cow*.mp3'; echo \"$a\""),
            false
        );
    }
    #[test]
    fn prop_checkSpacefulnessCfg4() {
        assert_eq!(
            node_emits(check_spacefulness_cfg, "for f in *.mp3; do echo $f; done"),
            true
        );
    }
    #[test]
    fn prop_checkSpacefulnessCfg4a() {
        assert_eq!(
            node_emits(check_spacefulness_cfg, "foo=3; foo=$(echo $foo)"),
            false
        );
    }
    #[test]
    fn prop_checkSpacefulnessCfg5() {
        assert_eq!(
            node_emits(
                check_spacefulness_cfg,
                "a='*'; b=$a; c=lol${b//foo/bar}; echo $c"
            ),
            true
        );
    }
    #[test]
    fn prop_checkSpacefulnessCfg6() {
        assert_eq!(
            node_emits(check_spacefulness_cfg, "a=foo$(lol); echo $a"),
            true
        );
    }
    #[test]
    fn prop_checkSpacefulnessCfg7() {
        assert_eq!(
            node_emits(check_spacefulness_cfg, "a=foo\\ bar; rm $a"),
            true
        );
    }
    #[test]
    fn prop_checkSpacefulnessCfg8() {
        assert_eq!(
            node_emits(check_spacefulness_cfg, "a=foo\\ bar; a=foo; rm $a"),
            false
        );
    }
    #[test]
    fn prop_checkSpacefulnessCfg10() {
        assert_eq!(node_emits(check_spacefulness_cfg, "rm $1"), true);
    }
    #[test]
    fn prop_checkSpacefulnessCfg11() {
        assert_eq!(
            node_emits(check_spacefulness_cfg, "rm ${10//foo/bar}"),
            true
        );
    }
    #[test]
    fn prop_checkSpacefulnessCfg12() {
        assert_eq!(node_emits(check_spacefulness_cfg, "(( $1 + 3 ))"), false);
    }
    #[test]
    fn prop_checkSpacefulnessCfg13() {
        assert_eq!(
            node_emits(check_spacefulness_cfg, "if [[ $2 -gt 14 ]]; then true; fi"),
            false
        );
    }
    #[test]
    fn prop_checkSpacefulnessCfg14() {
        assert_eq!(node_emits(check_spacefulness_cfg, "foo=$3 env"), false);
    }
    #[test]
    fn prop_checkSpacefulnessCfg15() {
        assert_eq!(node_emits(check_spacefulness_cfg, "local foo=$1"), false);
    }
    #[test]
    fn prop_checkSpacefulnessCfg16() {
        assert_eq!(node_emits(check_spacefulness_cfg, "declare foo=$1"), false);
    }
    #[test]
    fn prop_checkSpacefulnessCfg17() {
        assert_eq!(node_emits(check_spacefulness_cfg, "echo foo=$1"), true);
    }
    #[test]
    fn prop_checkSpacefulnessCfg18() {
        assert_eq!(node_emits(check_spacefulness_cfg, "$1 --flags"), false);
    }
    #[test]
    fn prop_checkSpacefulnessCfg19() {
        assert_eq!(node_emits(check_spacefulness_cfg, "echo $PWD"), true);
    }
    #[test]
    fn prop_checkSpacefulnessCfg20() {
        assert_eq!(node_emits(check_spacefulness_cfg, "n+='foo bar'"), false);
    }
    #[test]
    fn prop_checkSpacefulnessCfg21() {
        assert_eq!(
            node_emits(check_spacefulness_cfg, "select foo in $bar; do true; done"),
            false
        );
    }
    #[test]
    fn prop_checkSpacefulnessCfg22() {
        assert_eq!(node_emits(check_spacefulness_cfg, "echo $\"$1\""), false);
    }
    #[test]
    fn prop_checkSpacefulnessCfg23() {
        assert_eq!(
            node_emits(check_spacefulness_cfg, "a=(1); echo ${a[@]}"),
            false
        );
    }
    #[test]
    fn prop_checkSpacefulnessCfg24() {
        assert_eq!(
            node_emits(check_spacefulness_cfg, "a='a    b'; cat <<< $a"),
            true
        );
    }
    #[test]
    fn prop_checkSpacefulnessCfg25() {
        assert_eq!(
            node_emits(check_spacefulness_cfg, "a='s/[0-9]//g'; sed $a"),
            true
        );
    }
    #[test]
    fn prop_checkSpacefulnessCfg26() {
        assert_eq!(
            node_emits(check_spacefulness_cfg, "a='foo bar'; echo {1,2,$a}"),
            true
        );
    }
    #[test]
    fn prop_checkSpacefulnessCfg27() {
        assert_eq!(
            node_emits(check_spacefulness_cfg, "echo ${a:+'foo'}"),
            false
        );
    }
    #[test]
    fn prop_checkSpacefulnessCfg28() {
        assert_eq!(
            node_emits(check_spacefulness_cfg, "exec {n}>&1; echo $n"),
            false
        );
    }
    #[test]
    fn prop_checkSpacefulnessCfg29() {
        assert_eq!(
            node_emits(check_spacefulness_cfg, "n=$(stuff); exec {n}>&-;"),
            false
        );
    }
    #[test]
    fn prop_checkSpacefulnessCfg30() {
        assert_eq!(
            node_emits(check_spacefulness_cfg, "file='foo bar'; echo foo > $file;"),
            true
        );
    }
    #[test]
    fn prop_checkSpacefulnessCfg31() {
        assert_eq!(
            node_emits(check_spacefulness_cfg, "echo \"`echo \\\"$1\\\"`\""),
            false
        );
    }
    #[test]
    fn prop_checkSpacefulnessCfg32() {
        assert_eq!(
            node_emits(check_spacefulness_cfg, "var=$1; [ -v var ]"),
            false
        );
    }
    #[test]
    fn prop_checkSpacefulnessCfg33() {
        assert_eq!(
            node_emits(check_spacefulness_cfg, "for file; do echo $file; done"),
            true
        );
    }
    #[test]
    fn prop_checkSpacefulnessCfg34() {
        assert_eq!(node_emits(check_spacefulness_cfg, "declare foo$n=$1"), true);
    }
    #[test]
    fn prop_checkSpacefulnessCfg35() {
        assert_eq!(
            node_emits(check_spacefulness_cfg, "echo ${1+\"$1\"}"),
            false
        );
    }
    #[test]
    fn prop_checkSpacefulnessCfg36() {
        assert_eq!(
            node_emits(check_spacefulness_cfg, "arg=$#; echo $arg"),
            false
        );
    }
    #[test]
    fn prop_checkSpacefulnessCfg37() {
        assert_eq!(
            node_emits(
                check_spacefulness_cfg,
                "@test 'status' {\n [ $status -eq 0 ]\n}"
            ),
            false
        );
    }
    #[test]
    fn prop_checkSpacefulnessCfg37v() {
        assert_eq!(
            node_emits(spaceful_verbose, "@test 'status' {\n [ $status -eq 0 ]\n}"),
            true
        );
    }
    #[test]
    fn prop_checkSpacefulnessCfg38() {
        assert_eq!(node_emits(check_spacefulness_cfg, "a=; echo $a"), true);
    }
    #[test]
    fn prop_checkSpacefulnessCfg39() {
        assert_eq!(
            node_emits(check_spacefulness_cfg, "a=''\"\"''; b=x$a; echo $b"),
            false
        );
    }
    #[test]
    fn prop_checkSpacefulnessCfg40() {
        assert_eq!(
            node_emits(check_spacefulness_cfg, "a=$((x+1)); echo $a"),
            false
        );
    }
    #[test]
    fn prop_checkSpacefulnessCfg41() {
        assert_eq!(node_emits(check_spacefulness_cfg, "exec $1 --flags"), false);
    }
    #[test]
    fn prop_checkSpacefulnessCfg42() {
        assert_eq!(node_emits(check_spacefulness_cfg, "run $1 --flags"), false);
    }
    #[test]
    fn prop_checkSpacefulnessCfg43() {
        assert_eq!(node_emits(check_spacefulness_cfg, "$foo=42"), false);
    }
    #[test]
    fn prop_checkSpacefulnessCfg44() {
        assert_eq!(
            node_emits(check_spacefulness_cfg, "#!/bin/sh\nexport var=$value"),
            true
        );
    }
    #[test]
    fn prop_checkSpacefulnessCfg45() {
        assert_eq!(
            node_emits(check_spacefulness_cfg, "wait -zzx -p foo; echo $foo"),
            false
        );
    }
    #[test]
    fn prop_checkSpacefulnessCfg46() {
        assert_eq!(
            node_emits(check_spacefulness_cfg, "x=0; (( x += 1 )); echo $x"),
            false
        );
    }
    #[test]
    fn prop_checkSpacefulnessCfg47() {
        assert_eq!(
            node_emits(check_spacefulness_cfg, "x=0; (( x-- )); echo $x"),
            false
        );
    }
    #[test]
    fn prop_checkSpacefulnessCfg48() {
        assert_eq!(
            node_emits(check_spacefulness_cfg, "x=0; (( ++x )); echo $x"),
            false
        );
    }
    #[test]
    fn prop_checkSpacefulnessCfg49() {
        assert_eq!(
            node_emits(check_spacefulness_cfg, "for i in 1 2 3; do echo $i; done"),
            false
        );
    }
    #[test]
    fn prop_checkSpacefulnessCfg50() {
        assert_eq!(
            node_emits(check_spacefulness_cfg, "for i in 1 2 *; do echo $i; done"),
            true
        );
    }
    #[test]
    fn prop_checkSpacefulnessCfg51() {
        assert_eq!(
            node_emits(check_spacefulness_cfg, "x='foo bar'; x && x=1; echo $x"),
            true
        );
    }
    #[test]
    fn prop_checkSpacefulnessCfg52() {
        assert_eq!(
            node_emits(
                check_spacefulness_cfg,
                "x=1; if f; then x='foo bar'; exit; fi; echo $x"
            ),
            false
        );
    }
    #[test]
    fn prop_checkSpacefulnessCfg53() {
        assert_eq!(
            node_emits(
                check_spacefulness_cfg,
                "s=1; f() { local s='a b'; }; f; echo $s"
            ),
            false
        );
    }
    #[test]
    fn prop_checkSpacefulnessCfg54() {
        assert_eq!(
            node_emits(check_spacefulness_cfg, "s='a b'; f() { s=1; }; f; echo $s"),
            false
        );
    }
    #[test]
    fn prop_checkSpacefulnessCfg55() {
        assert_eq!(
            node_emits(
                check_spacefulness_cfg,
                "s='a b'; x && f() { s=1; }; f; echo $s"
            ),
            true
        );
    }
    #[test]
    fn prop_checkSpacefulnessCfg56() {
        assert_eq!(
            node_emits(check_spacefulness_cfg, "s=1; cat <(s='a b'); echo $s"),
            false
        );
    }
    #[test]
    fn prop_checkSpacefulnessCfg57() {
        assert_eq!(
            node_emits(check_spacefulness_cfg, "declare -i s=0; s=$(f); echo $s"),
            false
        );
    }
    #[test]
    fn prop_checkSpacefulnessCfg58() {
        assert_eq!(
            node_emits(
                check_spacefulness_cfg,
                "f() { declare -i s; }; f; s=$(var); echo $s"
            ),
            true
        );
    }
    #[test]
    fn prop_checkSpacefulnessCfg59() {
        assert_eq!(
            node_emits(
                check_spacefulness_cfg,
                "f() { declare -gi s; }; f; s=$(var); echo $s"
            ),
            false
        );
    }
    #[test]
    fn prop_checkSpacefulnessCfg60() {
        assert_eq!(
            node_emits(
                check_spacefulness_cfg,
                "declare -i s; declare +i s; s=$(foo); echo $s"
            ),
            true
        );
    }
    #[test]
    fn prop_checkSpacefulnessCfg61() {
        assert_eq!(
            node_emits(check_spacefulness_cfg, "declare -x X; y=foo$X; echo $y;"),
            true
        );
    }
    #[test]
    fn prop_checkSpacefulnessCfg62() {
        assert_eq!(
            node_emits(
                check_spacefulness_cfg,
                "f() { declare -x X; y=foo$X; echo $y; }"
            ),
            false
        );
    }
    #[test]
    fn prop_checkSpacefulnessCfg63() {
        assert_eq!(
            node_emits(
                check_spacefulness_cfg,
                "f && declare -i s; s='x + y'; echo $s"
            ),
            true
        );
    }
    #[test]
    fn prop_checkSpacefulnessCfg64() {
        assert_eq!(
            node_emits(
                check_spacefulness_cfg,
                "declare -i s; s='x + y'; x=$s; echo $x"
            ),
            false
        );
    }
    #[test]
    fn prop_checkSpacefulnessCfg65() {
        assert_eq!(
            node_emits(check_spacefulness_cfg, "f() { s=$?; echo $s; }; f"),
            false
        );
    }
    #[test]
    fn prop_checkSpacefulnessCfg66() {
        assert_eq!(
            node_emits(check_spacefulness_cfg, "f() { s=$?; echo $s; }"),
            false
        );
    }
    #[test]
    fn prop_checkUnused0() {
        assert_eq!(
            tree_emits(check_unused_assignments, "var=foo; echo $var"),
            false
        );
    }
    #[test]
    fn prop_checkUnused1() {
        assert_eq!(
            tree_emits(check_unused_assignments, "var=foo; echo $bar"),
            true
        );
    }
    #[test]
    fn prop_checkUnused2() {
        assert_eq!(
            tree_emits(check_unused_assignments, "var=foo; export var;"),
            false
        );
    }
    #[test]
    fn prop_checkUnused3() {
        assert_eq!(
            tree_emits(check_unused_assignments, "for f in *; do echo '$f'; done"),
            true
        );
    }
    #[test]
    fn prop_checkUnused4() {
        assert_eq!(tree_emits(check_unused_assignments, "local i=0"), true);
    }
    #[test]
    fn prop_checkUnused5() {
        assert_eq!(
            tree_emits(check_unused_assignments, "read lol; echo $lol"),
            false
        );
    }
    #[test]
    fn prop_checkUnused6() {
        assert_eq!(
            tree_emits(check_unused_assignments, "var=4; (( var++ ))"),
            false
        );
    }
    #[test]
    fn prop_checkUnused7() {
        assert_eq!(
            tree_emits(check_unused_assignments, "var=2; $((var))"),
            false
        );
    }
    #[test]
    fn prop_checkUnused8() {
        assert_eq!(tree_emits(check_unused_assignments, "var=2; var=3;"), true);
    }
    #[test]
    fn prop_checkUnused9() {
        assert_eq!(tree_emits(check_unused_assignments, "read ''"), false);
    }
    #[test]
    fn prop_checkUnused10() {
        assert_eq!(
            tree_emits(check_unused_assignments, "read -p 'test: '"),
            false
        );
    }
    #[test]
    fn prop_checkUnused11() {
        assert_eq!(
            tree_emits(check_unused_assignments, "bar=5; export foo[$bar]=3"),
            false
        );
    }
    #[test]
    fn prop_checkUnused12() {
        assert_eq!(
            tree_emits(check_unused_assignments, "read foo; echo ${!foo}"),
            false
        );
    }
    #[test]
    fn prop_checkUnused13() {
        assert_eq!(
            tree_emits(check_unused_assignments, "x=(1); (( x[0] ))"),
            false
        );
    }
    #[test]
    fn prop_checkUnused14() {
        assert_eq!(
            tree_emits(check_unused_assignments, "x=(1); n=0; echo ${x[n]}"),
            false
        );
    }
    #[test]
    fn prop_checkUnused15() {
        assert_eq!(
            tree_emits(check_unused_assignments, "x=(1); n=0; (( x[n] ))"),
            false
        );
    }
    #[test]
    fn prop_checkUnused16() {
        assert_eq!(
            tree_emits(check_unused_assignments, "foo=5; declare -x foo"),
            false
        );
    }
    #[test]
    fn prop_checkUnused16b() {
        assert_eq!(
            tree_emits(
                check_unused_assignments,
                "f() { local -x foo; foo=42; bar; }; f"
            ),
            false
        );
    }
    #[test]
    fn prop_checkUnused17() {
        assert_eq!(
            tree_emits(
                check_unused_assignments,
                "read -i 'foo' -e -p 'Input: ' bar; $bar;"
            ),
            false
        );
    }
    #[test]
    fn prop_checkUnused18() {
        assert_eq!(
            tree_emits(
                check_unused_assignments,
                "a=1; arr=( [$a]=42 ); echo \"${arr[@]}\""
            ),
            false
        );
    }
    #[test]
    fn prop_checkUnused19() {
        assert_eq!(
            tree_emits(check_unused_assignments, "a=1; let b=a+1; echo $b"),
            false
        );
    }
    #[test]
    fn prop_checkUnused20() {
        assert_eq!(tree_emits(check_unused_assignments, "a=1; PS1='$a'"), false);
    }
    #[test]
    fn prop_checkUnused21() {
        assert_eq!(
            tree_emits(check_unused_assignments, "a=1; trap 'echo $a' INT"),
            false
        );
    }
    #[test]
    fn prop_checkUnused22() {
        assert_eq!(tree_emits(check_unused_assignments, "a=1; [ -v a ]"), false);
    }
    #[test]
    fn prop_checkUnused23() {
        assert_eq!(tree_emits(check_unused_assignments, "a=1; [ -R a ]"), false);
    }
    #[test]
    fn prop_checkUnused24() {
        assert_eq!(
            tree_emits(check_unused_assignments, "mapfile -C a b; echo ${b[@]}"),
            false
        );
    }
    #[test]
    fn prop_checkUnused25() {
        assert_eq!(
            tree_emits(check_unused_assignments, "readarray foo; echo ${foo[@]}"),
            false
        );
    }
    #[test]
    fn prop_checkUnused26() {
        assert_eq!(
            tree_emits(check_unused_assignments, "declare -F foo"),
            false
        );
    }
    #[test]
    fn prop_checkUnused27() {
        assert_eq!(
            tree_emits(check_unused_assignments, "var=3; [ var -eq 3 ]"),
            true
        );
    }
    #[test]
    fn prop_checkUnused28() {
        assert_eq!(
            tree_emits(check_unused_assignments, "var=3; [[ var -eq 3 ]]"),
            false
        );
    }
    #[test]
    fn prop_checkUnused29() {
        assert_eq!(
            tree_emits(check_unused_assignments, "var=(a b); declare -p var"),
            false
        );
    }
    #[test]
    fn prop_checkUnused30() {
        assert_eq!(tree_emits(check_unused_assignments, "let a=1"), true);
    }
    #[test]
    fn prop_checkUnused31() {
        assert_eq!(tree_emits(check_unused_assignments, "let 'a=1'"), true);
    }
    #[test]
    fn prop_checkUnused32() {
        assert_eq!(
            tree_emits(check_unused_assignments, "let a=b=c; echo $a"),
            true
        );
    }
    #[test]
    fn prop_checkUnused33() {
        assert_eq!(
            tree_emits(check_unused_assignments, "a=foo; [[ foo =~ ^{$a}$ ]]"),
            false
        );
    }
    #[test]
    fn prop_checkUnused34() {
        assert_eq!(
            tree_emits(check_unused_assignments, "foo=1; (( t = foo )); echo $t"),
            false
        );
    }
    #[test]
    fn prop_checkUnused35() {
        assert_eq!(
            tree_emits(check_unused_assignments, "a=foo; b=2; echo ${a:b}"),
            false
        );
    }
    #[test]
    fn prop_checkUnused36() {
        assert_eq!(
            tree_emits(check_unused_assignments, "if [[ -v foo ]]; then true; fi"),
            false
        );
    }
    #[test]
    fn prop_checkUnused37() {
        assert_eq!(
            tree_emits(check_unused_assignments, "fd=2; exec {fd}>&-"),
            false
        );
    }
    #[test]
    fn prop_checkUnused38() {
        assert_eq!(tree_emits(check_unused_assignments, "(( a=42 ))"), true);
    }
    #[test]
    fn prop_checkUnused39() {
        assert_eq!(
            tree_emits(check_unused_assignments, "declare -x -f foo"),
            false
        );
    }
    #[test]
    fn prop_checkUnused40() {
        assert_eq!(
            tree_emits(
                check_unused_assignments,
                "arr=(1 2); num=2; echo \"${arr[@]:num}\""
            ),
            false
        );
    }
    #[test]
    fn prop_checkUnused41() {
        assert_eq!(
            tree_emits(check_unused_assignments, "@test 'foo' {\ntrue\n}\n"),
            false
        );
    }
    #[test]
    fn prop_checkUnused42() {
        assert_eq!(
            tree_emits(
                check_unused_assignments,
                "DEFINE_string foo '' ''; echo \"${FLAGS_foo}\""
            ),
            false
        );
    }
    #[test]
    fn prop_checkUnused43() {
        assert_eq!(
            tree_emits(check_unused_assignments, "DEFINE_string foo '' ''"),
            true
        );
    }
    #[test]
    fn prop_checkUnused44() {
        assert_eq!(
            tree_emits(check_unused_assignments, "DEFINE_string \"foo$ibar\" x y"),
            false
        );
    }
    #[test]
    fn prop_checkUnused45() {
        assert_eq!(
            tree_emits(check_unused_assignments, "readonly foo=bar"),
            true
        );
    }
    #[test]
    fn prop_checkUnused46() {
        assert_eq!(
            tree_emits(check_unused_assignments, "readonly foo=(bar)"),
            true
        );
    }
    #[test]
    fn prop_checkUnused47() {
        assert_eq!(
            tree_emits(check_unused_assignments, "a=1; alias hello='echo $a'"),
            false
        );
    }
    #[test]
    fn prop_checkUnused48() {
        assert_eq!(tree_emits(check_unused_assignments, "_a=1"), false);
    }
    #[test]
    fn prop_checkUnused49() {
        assert_eq!(
            tree_emits(
                check_unused_assignments,
                "declare -A array; key=a; [[ -v array[$key] ]]"
            ),
            false
        );
    }
    #[test]
    fn prop_checkUnused50() {
        assert_eq!(
            tree_emits(
                check_unused_assignments,
                "foofunc() { :; }; typeset -fx foofunc"
            ),
            false
        );
    }
    #[test]
    fn prop_checkUnused51() {
        assert_eq!(
            tree_emits(check_unused_assignments, "x[y[z=1]]=1; echo ${x[@]}"),
            true
        );
    }
    #[test]
    fn prop_checkUnassignedReferences1() {
        assert_eq!(tree_emits(check_unassigned_references, "echo $foo"), true);
    }
    #[test]
    fn prop_checkUnassignedReferences2() {
        assert_eq!(
            tree_emits(check_unassigned_references, "foo=hello; echo $foo"),
            false
        );
    }
    #[test]
    fn prop_checkUnassignedReferences3() {
        assert_eq!(
            tree_emits(check_unassigned_references, "MY_VALUE=3; echo $MYVALUE"),
            true
        );
    }
    #[test]
    fn prop_checkUnassignedReferences4() {
        assert_eq!(
            tree_emits(check_unassigned_references, "RANDOM2=foo; echo $RANDOM"),
            false
        );
    }
    #[test]
    fn prop_checkUnassignedReferences5() {
        assert_eq!(
            tree_emits(
                check_unassigned_references,
                "declare -A foo=([bar]=baz); echo ${foo[bar]}"
            ),
            false
        );
    }
    #[test]
    fn prop_checkUnassignedReferences6() {
        assert_eq!(
            tree_emits(check_unassigned_references, "foo=..; echo ${foo-bar}"),
            false
        );
    }
    #[test]
    fn prop_checkUnassignedReferences7() {
        assert_eq!(
            tree_emits(check_unassigned_references, "getopts ':h' foo; echo $foo"),
            false
        );
    }
    #[test]
    fn prop_checkUnassignedReferences8() {
        assert_eq!(
            tree_emits(check_unassigned_references, "let 'foo = 1'; echo $foo"),
            false
        );
    }
    #[test]
    fn prop_checkUnassignedReferences9() {
        assert_eq!(
            tree_emits(check_unassigned_references, "echo ${foo-bar}"),
            false
        );
    }
    #[test]
    fn prop_checkUnassignedReferences10() {
        assert_eq!(
            tree_emits(check_unassigned_references, "echo ${foo:?}"),
            false
        );
    }
    #[test]
    fn prop_checkUnassignedReferences11() {
        assert_eq!(
            tree_emits(
                check_unassigned_references,
                "declare -A foo; echo \"${foo[@]}\""
            ),
            false
        );
    }
    #[test]
    fn prop_checkUnassignedReferences12() {
        assert_eq!(
            tree_emits(
                check_unassigned_references,
                "typeset -a foo; echo \"${foo[@]}\""
            ),
            false
        );
    }
    #[test]
    fn prop_checkUnassignedReferences13() {
        assert_eq!(
            tree_emits(check_unassigned_references, "f() { local foo; echo $foo; }"),
            false
        );
    }
    #[test]
    fn prop_checkUnassignedReferences14() {
        assert_eq!(
            tree_emits(check_unassigned_references, "foo=; echo $foo"),
            false
        );
    }
    #[test]
    fn prop_checkUnassignedReferences15() {
        assert_eq!(
            tree_emits(check_unassigned_references, "f() { true; }; export -f f"),
            false
        );
    }
    #[test]
    fn prop_checkUnassignedReferences16() {
        assert_eq!(
            tree_emits(
                check_unassigned_references,
                "declare -A foo=( [a b]=bar ); echo ${foo[a b]}"
            ),
            false
        );
    }
    #[test]
    fn prop_checkUnassignedReferences17() {
        assert_eq!(
            tree_emits(check_unassigned_references, "USERS=foo; echo $USER"),
            false
        );
    }
    #[test]
    fn prop_checkUnassignedReferences18() {
        assert_eq!(
            tree_emits(check_unassigned_references, "FOOBAR=42; export FOOBAR="),
            false
        );
    }
    #[test]
    fn prop_checkUnassignedReferences19() {
        assert_eq!(
            tree_emits(check_unassigned_references, "readonly foo=bar; echo $foo"),
            false
        );
    }
    #[test]
    fn prop_checkUnassignedReferences20() {
        assert_eq!(
            tree_emits(check_unassigned_references, "printf -v foo bar; echo $foo"),
            false
        );
    }
    #[test]
    fn prop_checkUnassignedReferences21() {
        assert_eq!(
            tree_emits(check_unassigned_references, "echo ${#foo}"),
            true
        );
    }
    #[test]
    fn prop_checkUnassignedReferences22() {
        assert_eq!(
            tree_emits(check_unassigned_references, "echo ${!os*}"),
            false
        );
    }
    #[test]
    fn prop_checkUnassignedReferences23() {
        assert_eq!(
            tree_emits(check_unassigned_references, "declare -a foo; foo[bar]=42;"),
            true
        );
    }
    #[test]
    fn prop_checkUnassignedReferences24() {
        assert_eq!(
            tree_emits(check_unassigned_references, "declare -A foo; foo[bar]=42;"),
            false
        );
    }
    #[test]
    fn prop_checkUnassignedReferences25() {
        assert_eq!(
            tree_emits(
                check_unassigned_references,
                "declare -A foo=(); foo[bar]=42;"
            ),
            false
        );
    }
    #[test]
    fn prop_checkUnassignedReferences26() {
        assert_eq!(
            tree_emits(
                check_unassigned_references,
                "a::b() { foo; }; readonly -f a::b"
            ),
            false
        );
    }
    #[test]
    fn prop_checkUnassignedReferences27() {
        assert_eq!(
            tree_emits(check_unassigned_references, ": ${foo:=bar}"),
            false
        );
    }
    #[test]
    fn prop_checkUnassignedReferences28() {
        assert_eq!(
            tree_emits(
                check_unassigned_references,
                "#!/bin/ksh\necho \"${.sh.version}\"\n"
            ),
            false
        );
    }
    #[test]
    fn prop_checkUnassignedReferences29() {
        assert_eq!(
            tree_emits(
                check_unassigned_references,
                "if [[ -v foo ]]; then echo $foo; fi"
            ),
            false
        );
    }
    #[test]
    fn prop_checkUnassignedReferences30() {
        assert_eq!(
            tree_emits(
                check_unassigned_references,
                "if [[ -v foo[3] ]]; then echo ${foo[3]}; fi"
            ),
            false
        );
    }
    #[test]
    fn prop_checkUnassignedReferences31() {
        assert_eq!(
            tree_emits(
                check_unassigned_references,
                "X=1; if [[ -v foo[$X+42] ]]; then echo ${foo[$X+42]}; fi"
            ),
            false
        );
    }
    #[test]
    fn prop_checkUnassignedReferences32() {
        assert_eq!(
            tree_emits(
                check_unassigned_references,
                "if [[ -v \"foo[1]\" ]]; then echo ${foo[@]}; fi"
            ),
            false
        );
    }
    #[test]
    fn prop_checkUnassignedReferences33() {
        assert_eq!(
            tree_emits(
                check_unassigned_references,
                "f() { local -A foo; echo \"${foo[@]}\"; }"
            ),
            false
        );
    }
    #[test]
    fn prop_checkUnassignedReferences34() {
        assert_eq!(
            tree_emits(
                check_unassigned_references,
                "declare -A foo; (( foo[bar] ))"
            ),
            false
        );
    }
    #[test]
    fn prop_checkUnassignedReferences35() {
        assert_eq!(
            tree_emits(check_unassigned_references, "echo ${arr[foo-bar]:?fail}"),
            false
        );
    }
    #[test]
    fn prop_checkUnassignedReferences36() {
        assert_eq!(
            tree_emits(
                check_unassigned_references,
                "read -a foo -r <<<\"foo bar\"; echo \"$foo\""
            ),
            false
        );
    }
    #[test]
    fn prop_checkUnassignedReferences37() {
        assert_eq!(
            tree_emits(
                check_unassigned_references,
                "var=howdy; printf -v 'array[0]' %s \"$var\"; printf %s \"${array[0]}\";"
            ),
            false
        );
    }
    #[test]
    fn prop_checkUnassignedReferences38() {
        assert_eq!(tree_emits(unassigned_globals, "echo $VAR"), true);
    }
    #[test]
    fn prop_checkUnassignedReferences39() {
        assert_eq!(
            tree_emits(
                check_unassigned_references,
                "builtin export var=4; echo $var"
            ),
            false
        );
    }
    #[test]
    fn prop_checkUnassignedReferences40() {
        assert_eq!(
            tree_emits(check_unassigned_references, ": ${foo=bar}"),
            false
        );
    }
    #[test]
    fn prop_checkUnassignedReferences41() {
        assert_eq!(
            tree_emits(
                check_unassigned_references,
                "mapfile -t files 123; echo \"${files[@]}\""
            ),
            false
        );
    }
    #[test]
    fn prop_checkUnassignedReferences42() {
        assert_eq!(
            tree_emits(
                check_unassigned_references,
                "mapfile files -t; echo \"${files[@]}\""
            ),
            false
        );
    }
    #[test]
    fn prop_checkUnassignedReferences43() {
        assert_eq!(
            tree_emits(
                check_unassigned_references,
                "mapfile --future files; echo \"${files[@]}\""
            ),
            false
        );
    }
    #[test]
    fn prop_checkUnassignedReferences_minusNPlain() {
        assert_eq!(
            tree_emits(
                check_unassigned_references,
                "if [ -n \"$x\" ]; then echo $x; fi"
            ),
            false
        );
    }
    #[test]
    fn prop_checkUnassignedReferences_minusZPlain() {
        assert_eq!(
            tree_emits(
                check_unassigned_references,
                "if [ -z \"$x\" ]; then echo \"\"; fi"
            ),
            false
        );
    }
    #[test]
    fn prop_checkUnassignedReferences_minusNBraced() {
        assert_eq!(
            tree_emits(
                check_unassigned_references,
                "if [ -n \"${x}\" ]; then echo $x; fi"
            ),
            false
        );
    }
    #[test]
    fn prop_checkUnassignedReferences_minusZBraced() {
        assert_eq!(
            tree_emits(
                check_unassigned_references,
                "if [ -z \"${x}\" ]; then echo \"\"; fi"
            ),
            false
        );
    }
    #[test]
    fn prop_checkUnassignedReferences_minusNDefault() {
        assert_eq!(
            tree_emits(
                check_unassigned_references,
                "if [ -n \"${x:-}\" ]; then echo $x; fi"
            ),
            false
        );
    }
    #[test]
    fn prop_checkUnassignedReferences_minusZDefault() {
        assert_eq!(
            tree_emits(
                check_unassigned_references,
                "if [ -z \"${x:-}\" ]; then echo \"\"; fi"
            ),
            false
        );
    }
    #[test]
    fn prop_checkUnassignedReferences50() {
        assert_eq!(
            tree_emits(check_unassigned_references, "echo ${foo:+bar}"),
            false
        );
    }
    #[test]
    fn prop_checkUnassignedReferences51() {
        assert_eq!(
            tree_emits(check_unassigned_references, "echo ${foo:+$foo}"),
            false
        );
    }
    #[test]
    fn prop_checkUnassignedReferences52() {
        assert_eq!(
            tree_emits(check_unassigned_references, "wait -p pid; echo $pid"),
            false
        );
    }
    #[test]
    fn prop_checkUnassignedReferences53() {
        assert_eq!(tree_emits(check_unassigned_references, "x=($foo)"), true);
    }
}
