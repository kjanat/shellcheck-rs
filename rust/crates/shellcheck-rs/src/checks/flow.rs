//! Dataflow checks ported from `ShellCheck.Analytics`:
//!   * SC2034 — `checkUnusedAssignments` (linear `variableFlow`, tree check).
//!   * SC2154 / SC2153 — `checkUnassignedReferences'` (linear `variableFlow`).
//!   * SC2086 / SC2223 — `checkSpacefulnessCfg'` (CFG data-flow, node check).
//!
//! SC2154/SC2034 use the linear `variableFlow`; SC2086 uses the CFG incoming
//! state. Faithful port; see the referenced Haskell for the exact semantics.

use crate::analyzer_lib::*;
use crate::ast::*;
use crate::astlib::oversimplify_concat;
use crate::cfg::{CFVariableProp, get_braced_modifier, get_braced_reference, is_variable_char};
use crate::cfg_analysis::SpaceStatus;
use crate::data::{COMMON_COMMANDS, INTERNAL_VARIABLES, SPECIAL_VARIABLES_WITHOUT_SPACES};
use std::collections::BTreeMap;

pub fn register(c: &mut Checker) {
    c.tree(check_unused_assignments);
    c.tree(check_unassigned_references);
    c.node(check_spacefulness_cfg);
}

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
            let str = oversimplify_concat(op);
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
        let name = oversimplify_concat(op);
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

    let braced_string = oversimplify_concat(op);
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
        assert!(node_emits(check_spacefulness_cfg, "a='cow moo'; echo $a"));
    }
    #[test]
    fn prop_checkSpacefulnessCfg2() {
        assert!(!(node_emits(check_spacefulness_cfg, "a='cow moo'; [[ $a ]]")));
    }
    #[test]
    fn prop_checkSpacefulnessCfg3() {
        assert!(!(node_emits(check_spacefulness_cfg, "a='cow*.mp3'; echo \"$a\"")));
    }
    #[test]
    fn prop_checkSpacefulnessCfg4() {
        assert!(node_emits(
            check_spacefulness_cfg,
            "for f in *.mp3; do echo $f; done"
        ));
    }
    #[test]
    fn prop_checkSpacefulnessCfg4a() {
        assert!(!(node_emits(check_spacefulness_cfg, "foo=3; foo=$(echo $foo)")));
    }
    #[test]
    fn prop_checkSpacefulnessCfg5() {
        assert!(node_emits(
            check_spacefulness_cfg,
            "a='*'; b=$a; c=lol${b//foo/bar}; echo $c"
        ));
    }
    #[test]
    fn prop_checkSpacefulnessCfg6() {
        assert!(node_emits(check_spacefulness_cfg, "a=foo$(lol); echo $a"));
    }
    #[test]
    fn prop_checkSpacefulnessCfg7() {
        assert!(node_emits(check_spacefulness_cfg, "a=foo\\ bar; rm $a"));
    }
    #[test]
    fn prop_checkSpacefulnessCfg8() {
        assert!(!(node_emits(check_spacefulness_cfg, "a=foo\\ bar; a=foo; rm $a")));
    }
    #[test]
    fn prop_checkSpacefulnessCfg10() {
        assert!(node_emits(check_spacefulness_cfg, "rm $1"));
    }
    #[test]
    fn prop_checkSpacefulnessCfg11() {
        assert!(node_emits(check_spacefulness_cfg, "rm ${10//foo/bar}"));
    }
    #[test]
    fn prop_checkSpacefulnessCfg12() {
        assert!(!(node_emits(check_spacefulness_cfg, "(( $1 + 3 ))")));
    }
    #[test]
    fn prop_checkSpacefulnessCfg13() {
        assert!(!(node_emits(check_spacefulness_cfg, "if [[ $2 -gt 14 ]]; then true; fi")));
    }
    #[test]
    fn prop_checkSpacefulnessCfg14() {
        assert!(!(node_emits(check_spacefulness_cfg, "foo=$3 env")));
    }
    #[test]
    fn prop_checkSpacefulnessCfg15() {
        assert!(!(node_emits(check_spacefulness_cfg, "local foo=$1")));
    }
    #[test]
    fn prop_checkSpacefulnessCfg16() {
        assert!(!(node_emits(check_spacefulness_cfg, "declare foo=$1")));
    }
    #[test]
    fn prop_checkSpacefulnessCfg17() {
        assert!(node_emits(check_spacefulness_cfg, "echo foo=$1"));
    }
    #[test]
    fn prop_checkSpacefulnessCfg18() {
        assert!(!(node_emits(check_spacefulness_cfg, "$1 --flags")));
    }
    #[test]
    fn prop_checkSpacefulnessCfg19() {
        assert!(node_emits(check_spacefulness_cfg, "echo $PWD"));
    }
    #[test]
    fn prop_checkSpacefulnessCfg20() {
        assert!(!(node_emits(check_spacefulness_cfg, "n+='foo bar'")));
    }
    #[test]
    fn prop_checkSpacefulnessCfg21() {
        assert!(!(node_emits(check_spacefulness_cfg, "select foo in $bar; do true; done")));
    }
    #[test]
    fn prop_checkSpacefulnessCfg22() {
        assert!(!(node_emits(check_spacefulness_cfg, "echo $\"$1\"")));
    }
    #[test]
    fn prop_checkSpacefulnessCfg23() {
        assert!(!(node_emits(check_spacefulness_cfg, "a=(1); echo ${a[@]}")));
    }
    #[test]
    fn prop_checkSpacefulnessCfg24() {
        assert!(node_emits(check_spacefulness_cfg, "a='a    b'; cat <<< $a"));
    }
    #[test]
    fn prop_checkSpacefulnessCfg25() {
        assert!(node_emits(check_spacefulness_cfg, "a='s/[0-9]//g'; sed $a"));
    }
    #[test]
    fn prop_checkSpacefulnessCfg26() {
        assert!(node_emits(
            check_spacefulness_cfg,
            "a='foo bar'; echo {1,2,$a}"
        ));
    }
    #[test]
    fn prop_checkSpacefulnessCfg27() {
        assert!(!(node_emits(check_spacefulness_cfg, "echo ${a:+'foo'}")));
    }
    #[test]
    fn prop_checkSpacefulnessCfg28() {
        assert!(!(node_emits(check_spacefulness_cfg, "exec {n}>&1; echo $n")));
    }
    #[test]
    fn prop_checkSpacefulnessCfg29() {
        assert!(!(node_emits(check_spacefulness_cfg, "n=$(stuff); exec {n}>&-;")));
    }
    #[test]
    fn prop_checkSpacefulnessCfg30() {
        assert!(node_emits(
            check_spacefulness_cfg,
            "file='foo bar'; echo foo > $file;"
        ));
    }
    #[test]
    fn prop_checkSpacefulnessCfg31() {
        assert!(!(node_emits(check_spacefulness_cfg, "echo \"`echo \\\"$1\\\"`\"")));
    }
    #[test]
    fn prop_checkSpacefulnessCfg32() {
        assert!(!(node_emits(check_spacefulness_cfg, "var=$1; [ -v var ]")));
    }
    #[test]
    fn prop_checkSpacefulnessCfg33() {
        assert!(node_emits(
            check_spacefulness_cfg,
            "for file; do echo $file; done"
        ));
    }
    #[test]
    fn prop_checkSpacefulnessCfg34() {
        assert!(node_emits(check_spacefulness_cfg, "declare foo$n=$1"));
    }
    #[test]
    fn prop_checkSpacefulnessCfg35() {
        assert!(!(node_emits(check_spacefulness_cfg, "echo ${1+\"$1\"}")));
    }
    #[test]
    fn prop_checkSpacefulnessCfg36() {
        assert!(!(node_emits(check_spacefulness_cfg, "arg=$#; echo $arg")));
    }
    #[test]
    fn prop_checkSpacefulnessCfg37() {
        assert!(
            !(node_emits(
                check_spacefulness_cfg,
                "@test 'status' {\n [ $status -eq 0 ]\n}"
            ))
        );
    }
    #[test]
    fn prop_checkSpacefulnessCfg37v() {
        assert!(node_emits(
            spaceful_verbose,
            "@test 'status' {\n [ $status -eq 0 ]\n}"
        ));
    }
    #[test]
    fn prop_checkSpacefulnessCfg38() {
        assert!(node_emits(check_spacefulness_cfg, "a=; echo $a"));
    }
    #[test]
    fn prop_checkSpacefulnessCfg39() {
        assert!(!(node_emits(check_spacefulness_cfg, "a=''\"\"''; b=x$a; echo $b")));
    }
    #[test]
    fn prop_checkSpacefulnessCfg40() {
        assert!(!(node_emits(check_spacefulness_cfg, "a=$((x+1)); echo $a")));
    }
    #[test]
    fn prop_checkSpacefulnessCfg41() {
        assert!(!(node_emits(check_spacefulness_cfg, "exec $1 --flags")));
    }
    #[test]
    fn prop_checkSpacefulnessCfg42() {
        assert!(!(node_emits(check_spacefulness_cfg, "run $1 --flags")));
    }
    #[test]
    fn prop_checkSpacefulnessCfg43() {
        assert!(!(node_emits(check_spacefulness_cfg, "$foo=42")));
    }
    #[test]
    fn prop_checkSpacefulnessCfg44() {
        assert!(node_emits(
            check_spacefulness_cfg,
            "#!/bin/sh\nexport var=$value"
        ));
    }
    #[test]
    fn prop_checkSpacefulnessCfg45() {
        assert!(!(node_emits(check_spacefulness_cfg, "wait -zzx -p foo; echo $foo")));
    }
    #[test]
    fn prop_checkSpacefulnessCfg46() {
        assert!(!(node_emits(check_spacefulness_cfg, "x=0; (( x += 1 )); echo $x")));
    }
    #[test]
    fn prop_checkSpacefulnessCfg47() {
        assert!(!(node_emits(check_spacefulness_cfg, "x=0; (( x-- )); echo $x")));
    }
    #[test]
    fn prop_checkSpacefulnessCfg48() {
        assert!(!(node_emits(check_spacefulness_cfg, "x=0; (( ++x )); echo $x")));
    }
    #[test]
    fn prop_checkSpacefulnessCfg49() {
        assert!(!(node_emits(check_spacefulness_cfg, "for i in 1 2 3; do echo $i; done")));
    }
    #[test]
    fn prop_checkSpacefulnessCfg50() {
        assert!(node_emits(
            check_spacefulness_cfg,
            "for i in 1 2 *; do echo $i; done"
        ));
    }
    #[test]
    fn prop_checkSpacefulnessCfg51() {
        assert!(node_emits(
            check_spacefulness_cfg,
            "x='foo bar'; x && x=1; echo $x"
        ));
    }
    #[test]
    fn prop_checkSpacefulnessCfg52() {
        assert!(
            !(node_emits(
                check_spacefulness_cfg,
                "x=1; if f; then x='foo bar'; exit; fi; echo $x"
            ))
        );
    }
    #[test]
    fn prop_checkSpacefulnessCfg53() {
        assert!(
            !(node_emits(
                check_spacefulness_cfg,
                "s=1; f() { local s='a b'; }; f; echo $s"
            ))
        );
    }
    #[test]
    fn prop_checkSpacefulnessCfg54() {
        assert!(!(node_emits(check_spacefulness_cfg, "s='a b'; f() { s=1; }; f; echo $s")));
    }
    #[test]
    fn prop_checkSpacefulnessCfg55() {
        assert!(node_emits(
            check_spacefulness_cfg,
            "s='a b'; x && f() { s=1; }; f; echo $s"
        ));
    }
    #[test]
    fn prop_checkSpacefulnessCfg56() {
        assert!(!(node_emits(check_spacefulness_cfg, "s=1; cat <(s='a b'); echo $s")));
    }
    #[test]
    fn prop_checkSpacefulnessCfg57() {
        assert!(!(node_emits(check_spacefulness_cfg, "declare -i s=0; s=$(f); echo $s")));
    }
    #[test]
    fn prop_checkSpacefulnessCfg58() {
        assert!(node_emits(
            check_spacefulness_cfg,
            "f() { declare -i s; }; f; s=$(var); echo $s"
        ));
    }
    #[test]
    fn prop_checkSpacefulnessCfg59() {
        assert!(
            !(node_emits(
                check_spacefulness_cfg,
                "f() { declare -gi s; }; f; s=$(var); echo $s"
            ))
        );
    }
    #[test]
    fn prop_checkSpacefulnessCfg60() {
        assert!(node_emits(
            check_spacefulness_cfg,
            "declare -i s; declare +i s; s=$(foo); echo $s"
        ));
    }
    #[test]
    fn prop_checkSpacefulnessCfg61() {
        assert!(node_emits(
            check_spacefulness_cfg,
            "declare -x X; y=foo$X; echo $y;"
        ));
    }
    #[test]
    fn prop_checkSpacefulnessCfg62() {
        assert!(
            !(node_emits(
                check_spacefulness_cfg,
                "f() { declare -x X; y=foo$X; echo $y; }"
            ))
        );
    }
    #[test]
    fn prop_checkSpacefulnessCfg63() {
        assert!(node_emits(
            check_spacefulness_cfg,
            "f && declare -i s; s='x + y'; echo $s"
        ));
    }
    #[test]
    fn prop_checkSpacefulnessCfg64() {
        assert!(
            !(node_emits(
                check_spacefulness_cfg,
                "declare -i s; s='x + y'; x=$s; echo $x"
            ))
        );
    }
    #[test]
    fn prop_checkSpacefulnessCfg65() {
        assert!(!(node_emits(check_spacefulness_cfg, "f() { s=$?; echo $s; }; f")));
    }
    #[test]
    fn prop_checkSpacefulnessCfg66() {
        assert!(!(node_emits(check_spacefulness_cfg, "f() { s=$?; echo $s; }")));
    }
    #[test]
    fn prop_checkUnused0() {
        assert!(!(tree_emits(check_unused_assignments, "var=foo; echo $var")));
    }
    #[test]
    fn prop_checkUnused1() {
        assert!(tree_emits(check_unused_assignments, "var=foo; echo $bar"));
    }
    #[test]
    fn prop_checkUnused2() {
        assert!(!(tree_emits(check_unused_assignments, "var=foo; export var;")));
    }
    #[test]
    fn prop_checkUnused3() {
        assert!(tree_emits(
            check_unused_assignments,
            "for f in *; do echo '$f'; done"
        ));
    }
    #[test]
    fn prop_checkUnused4() {
        assert!(tree_emits(check_unused_assignments, "local i=0"));
    }
    #[test]
    fn prop_checkUnused5() {
        assert!(!(tree_emits(check_unused_assignments, "read lol; echo $lol")));
    }
    #[test]
    fn prop_checkUnused6() {
        assert!(!(tree_emits(check_unused_assignments, "var=4; (( var++ ))")));
    }
    #[test]
    fn prop_checkUnused7() {
        assert!(!(tree_emits(check_unused_assignments, "var=2; $((var))")));
    }
    #[test]
    fn prop_checkUnused8() {
        assert!(tree_emits(check_unused_assignments, "var=2; var=3;"));
    }
    #[test]
    fn prop_checkUnused9() {
        assert!(!(tree_emits(check_unused_assignments, "read ''")));
    }
    #[test]
    fn prop_checkUnused10() {
        assert!(!(tree_emits(check_unused_assignments, "read -p 'test: '")));
    }
    #[test]
    fn prop_checkUnused11() {
        assert!(!(tree_emits(check_unused_assignments, "bar=5; export foo[$bar]=3")));
    }
    #[test]
    fn prop_checkUnused12() {
        assert!(!(tree_emits(check_unused_assignments, "read foo; echo ${!foo}")));
    }
    #[test]
    fn prop_checkUnused13() {
        assert!(!(tree_emits(check_unused_assignments, "x=(1); (( x[0] ))")));
    }
    #[test]
    fn prop_checkUnused14() {
        assert!(!(tree_emits(check_unused_assignments, "x=(1); n=0; echo ${x[n]}")));
    }
    #[test]
    fn prop_checkUnused15() {
        assert!(!(tree_emits(check_unused_assignments, "x=(1); n=0; (( x[n] ))")));
    }
    #[test]
    fn prop_checkUnused16() {
        assert!(!(tree_emits(check_unused_assignments, "foo=5; declare -x foo")));
    }
    #[test]
    fn prop_checkUnused16b() {
        assert!(
            !(tree_emits(
                check_unused_assignments,
                "f() { local -x foo; foo=42; bar; }; f"
            ))
        );
    }
    #[test]
    fn prop_checkUnused17() {
        assert!(
            !(tree_emits(
                check_unused_assignments,
                "read -i 'foo' -e -p 'Input: ' bar; $bar;"
            ))
        );
    }
    #[test]
    fn prop_checkUnused18() {
        assert!(
            !(tree_emits(
                check_unused_assignments,
                "a=1; arr=( [$a]=42 ); echo \"${arr[@]}\""
            ))
        );
    }
    #[test]
    fn prop_checkUnused19() {
        assert!(!(tree_emits(check_unused_assignments, "a=1; let b=a+1; echo $b")));
    }
    #[test]
    fn prop_checkUnused20() {
        assert!(!(tree_emits(check_unused_assignments, "a=1; PS1='$a'")));
    }
    #[test]
    fn prop_checkUnused21() {
        assert!(!(tree_emits(check_unused_assignments, "a=1; trap 'echo $a' INT")));
    }
    #[test]
    fn prop_checkUnused22() {
        assert!(!(tree_emits(check_unused_assignments, "a=1; [ -v a ]")));
    }
    #[test]
    fn prop_checkUnused23() {
        assert!(!(tree_emits(check_unused_assignments, "a=1; [ -R a ]")));
    }
    #[test]
    fn prop_checkUnused24() {
        assert!(!(tree_emits(check_unused_assignments, "mapfile -C a b; echo ${b[@]}")));
    }
    #[test]
    fn prop_checkUnused25() {
        assert!(!(tree_emits(check_unused_assignments, "readarray foo; echo ${foo[@]}")));
    }
    #[test]
    fn prop_checkUnused26() {
        assert!(!(tree_emits(check_unused_assignments, "declare -F foo")));
    }
    #[test]
    fn prop_checkUnused27() {
        assert!(tree_emits(check_unused_assignments, "var=3; [ var -eq 3 ]"));
    }
    #[test]
    fn prop_checkUnused28() {
        assert!(!(tree_emits(check_unused_assignments, "var=3; [[ var -eq 3 ]]")));
    }
    #[test]
    fn prop_checkUnused29() {
        assert!(!(tree_emits(check_unused_assignments, "var=(a b); declare -p var")));
    }
    #[test]
    fn prop_checkUnused30() {
        assert!(tree_emits(check_unused_assignments, "let a=1"));
    }
    #[test]
    fn prop_checkUnused31() {
        assert!(tree_emits(check_unused_assignments, "let 'a=1'"));
    }
    #[test]
    fn prop_checkUnused32() {
        assert!(tree_emits(check_unused_assignments, "let a=b=c; echo $a"));
    }
    #[test]
    fn prop_checkUnused33() {
        assert!(!(tree_emits(check_unused_assignments, "a=foo; [[ foo =~ ^{$a}$ ]]")));
    }
    #[test]
    fn prop_checkUnused34() {
        assert!(!(tree_emits(check_unused_assignments, "foo=1; (( t = foo )); echo $t")));
    }
    #[test]
    fn prop_checkUnused35() {
        assert!(!(tree_emits(check_unused_assignments, "a=foo; b=2; echo ${a:b}")));
    }
    #[test]
    fn prop_checkUnused36() {
        assert!(!(tree_emits(check_unused_assignments, "if [[ -v foo ]]; then true; fi")));
    }
    #[test]
    fn prop_checkUnused37() {
        assert!(!(tree_emits(check_unused_assignments, "fd=2; exec {fd}>&-")));
    }
    #[test]
    fn prop_checkUnused38() {
        assert!(tree_emits(check_unused_assignments, "(( a=42 ))"));
    }
    #[test]
    fn prop_checkUnused39() {
        assert!(!(tree_emits(check_unused_assignments, "declare -x -f foo")));
    }
    #[test]
    fn prop_checkUnused40() {
        assert!(
            !(tree_emits(
                check_unused_assignments,
                "arr=(1 2); num=2; echo \"${arr[@]:num}\""
            ))
        );
    }
    #[test]
    fn prop_checkUnused41() {
        assert!(!(tree_emits(check_unused_assignments, "@test 'foo' {\ntrue\n}\n")));
    }
    #[test]
    fn prop_checkUnused42() {
        assert!(
            !(tree_emits(
                check_unused_assignments,
                "DEFINE_string foo '' ''; echo \"${FLAGS_foo}\""
            ))
        );
    }
    #[test]
    fn prop_checkUnused43() {
        assert!(tree_emits(
            check_unused_assignments,
            "DEFINE_string foo '' ''"
        ));
    }
    #[test]
    fn prop_checkUnused44() {
        assert!(!(tree_emits(check_unused_assignments, "DEFINE_string \"foo$ibar\" x y")));
    }
    #[test]
    fn prop_checkUnused45() {
        assert!(tree_emits(check_unused_assignments, "readonly foo=bar"));
    }
    #[test]
    fn prop_checkUnused46() {
        assert!(tree_emits(check_unused_assignments, "readonly foo=(bar)"));
    }
    #[test]
    fn prop_checkUnused47() {
        assert!(!(tree_emits(check_unused_assignments, "a=1; alias hello='echo $a'")));
    }
    #[test]
    fn prop_checkUnused48() {
        assert!(!(tree_emits(check_unused_assignments, "_a=1")));
    }
    #[test]
    fn prop_checkUnused49() {
        assert!(
            !(tree_emits(
                check_unused_assignments,
                "declare -A array; key=a; [[ -v array[$key] ]]"
            ))
        );
    }
    #[test]
    fn prop_checkUnused50() {
        assert!(
            !(tree_emits(
                check_unused_assignments,
                "foofunc() { :; }; typeset -fx foofunc"
            ))
        );
    }
    #[test]
    fn prop_checkUnused51() {
        assert!(tree_emits(
            check_unused_assignments,
            "x[y[z=1]]=1; echo ${x[@]}"
        ));
    }
    #[test]
    fn prop_checkUnassignedReferences1() {
        assert!(tree_emits(check_unassigned_references, "echo $foo"));
    }
    #[test]
    fn prop_checkUnassignedReferences2() {
        assert!(!(tree_emits(check_unassigned_references, "foo=hello; echo $foo")));
    }
    #[test]
    fn prop_checkUnassignedReferences3() {
        assert!(tree_emits(
            check_unassigned_references,
            "MY_VALUE=3; echo $MYVALUE"
        ));
    }
    #[test]
    fn prop_checkUnassignedReferences4() {
        assert!(!(tree_emits(check_unassigned_references, "RANDOM2=foo; echo $RANDOM")));
    }
    #[test]
    fn prop_checkUnassignedReferences5() {
        assert!(
            !(tree_emits(
                check_unassigned_references,
                "declare -A foo=([bar]=baz); echo ${foo[bar]}"
            ))
        );
    }
    #[test]
    fn prop_checkUnassignedReferences6() {
        assert!(!(tree_emits(check_unassigned_references, "foo=..; echo ${foo-bar}")));
    }
    #[test]
    fn prop_checkUnassignedReferences7() {
        assert!(!(tree_emits(check_unassigned_references, "getopts ':h' foo; echo $foo")));
    }
    #[test]
    fn prop_checkUnassignedReferences8() {
        assert!(!(tree_emits(check_unassigned_references, "let 'foo = 1'; echo $foo")));
    }
    #[test]
    fn prop_checkUnassignedReferences9() {
        assert!(!(tree_emits(check_unassigned_references, "echo ${foo-bar}")));
    }
    #[test]
    fn prop_checkUnassignedReferences10() {
        assert!(!(tree_emits(check_unassigned_references, "echo ${foo:?}")));
    }
    #[test]
    fn prop_checkUnassignedReferences11() {
        assert!(
            !(tree_emits(
                check_unassigned_references,
                "declare -A foo; echo \"${foo[@]}\""
            ))
        );
    }
    #[test]
    fn prop_checkUnassignedReferences12() {
        assert!(
            !(tree_emits(
                check_unassigned_references,
                "typeset -a foo; echo \"${foo[@]}\""
            ))
        );
    }
    #[test]
    fn prop_checkUnassignedReferences13() {
        assert!(!(tree_emits(check_unassigned_references, "f() { local foo; echo $foo; }")));
    }
    #[test]
    fn prop_checkUnassignedReferences14() {
        assert!(!(tree_emits(check_unassigned_references, "foo=; echo $foo")));
    }
    #[test]
    fn prop_checkUnassignedReferences15() {
        assert!(!(tree_emits(check_unassigned_references, "f() { true; }; export -f f")));
    }
    #[test]
    fn prop_checkUnassignedReferences16() {
        assert!(
            !(tree_emits(
                check_unassigned_references,
                "declare -A foo=( [a b]=bar ); echo ${foo[a b]}"
            ))
        );
    }
    #[test]
    fn prop_checkUnassignedReferences17() {
        assert!(!(tree_emits(check_unassigned_references, "USERS=foo; echo $USER")));
    }
    #[test]
    fn prop_checkUnassignedReferences18() {
        assert!(!(tree_emits(check_unassigned_references, "FOOBAR=42; export FOOBAR=")));
    }
    #[test]
    fn prop_checkUnassignedReferences19() {
        assert!(!(tree_emits(check_unassigned_references, "readonly foo=bar; echo $foo")));
    }
    #[test]
    fn prop_checkUnassignedReferences20() {
        assert!(!(tree_emits(check_unassigned_references, "printf -v foo bar; echo $foo")));
    }
    #[test]
    fn prop_checkUnassignedReferences21() {
        assert!(tree_emits(check_unassigned_references, "echo ${#foo}"));
    }
    #[test]
    fn prop_checkUnassignedReferences22() {
        assert!(!(tree_emits(check_unassigned_references, "echo ${!os*}")));
    }
    #[test]
    fn prop_checkUnassignedReferences23() {
        assert!(tree_emits(
            check_unassigned_references,
            "declare -a foo; foo[bar]=42;"
        ));
    }
    #[test]
    fn prop_checkUnassignedReferences24() {
        assert!(!(tree_emits(check_unassigned_references, "declare -A foo; foo[bar]=42;")));
    }
    #[test]
    fn prop_checkUnassignedReferences25() {
        assert!(
            !(tree_emits(
                check_unassigned_references,
                "declare -A foo=(); foo[bar]=42;"
            ))
        );
    }
    #[test]
    fn prop_checkUnassignedReferences26() {
        assert!(
            !(tree_emits(
                check_unassigned_references,
                "a::b() { foo; }; readonly -f a::b"
            ))
        );
    }
    #[test]
    fn prop_checkUnassignedReferences27() {
        assert!(!(tree_emits(check_unassigned_references, ": ${foo:=bar}")));
    }
    #[test]
    fn prop_checkUnassignedReferences28() {
        assert!(
            !(tree_emits(
                check_unassigned_references,
                "#!/bin/ksh\necho \"${.sh.version}\"\n"
            ))
        );
    }
    #[test]
    fn prop_checkUnassignedReferences29() {
        assert!(
            !(tree_emits(
                check_unassigned_references,
                "if [[ -v foo ]]; then echo $foo; fi"
            ))
        );
    }
    #[test]
    fn prop_checkUnassignedReferences30() {
        assert!(
            !(tree_emits(
                check_unassigned_references,
                "if [[ -v foo[3] ]]; then echo ${foo[3]}; fi"
            ))
        );
    }
    #[test]
    fn prop_checkUnassignedReferences31() {
        assert!(
            !(tree_emits(
                check_unassigned_references,
                "X=1; if [[ -v foo[$X+42] ]]; then echo ${foo[$X+42]}; fi"
            ))
        );
    }
    #[test]
    fn prop_checkUnassignedReferences32() {
        assert!(
            !(tree_emits(
                check_unassigned_references,
                "if [[ -v \"foo[1]\" ]]; then echo ${foo[@]}; fi"
            ))
        );
    }
    #[test]
    fn prop_checkUnassignedReferences33() {
        assert!(
            !(tree_emits(
                check_unassigned_references,
                "f() { local -A foo; echo \"${foo[@]}\"; }"
            ))
        );
    }
    #[test]
    fn prop_checkUnassignedReferences34() {
        assert!(
            !(tree_emits(
                check_unassigned_references,
                "declare -A foo; (( foo[bar] ))"
            ))
        );
    }
    #[test]
    fn prop_checkUnassignedReferences35() {
        assert!(!(tree_emits(check_unassigned_references, "echo ${arr[foo-bar]:?fail}")));
    }
    #[test]
    fn prop_checkUnassignedReferences36() {
        assert!(
            !(tree_emits(
                check_unassigned_references,
                "read -a foo -r <<<\"foo bar\"; echo \"$foo\""
            ))
        );
    }
    #[test]
    fn prop_checkUnassignedReferences37() {
        assert!(
            !(tree_emits(
                check_unassigned_references,
                "var=howdy; printf -v 'array[0]' %s \"$var\"; printf %s \"${array[0]}\";"
            ))
        );
    }
    #[test]
    fn prop_checkUnassignedReferences38() {
        assert!(tree_emits(unassigned_globals, "echo $VAR"));
    }
    #[test]
    fn prop_checkUnassignedReferences39() {
        assert!(
            !(tree_emits(
                check_unassigned_references,
                "builtin export var=4; echo $var"
            ))
        );
    }
    #[test]
    fn prop_checkUnassignedReferences40() {
        assert!(!(tree_emits(check_unassigned_references, ": ${foo=bar}")));
    }
    #[test]
    fn prop_checkUnassignedReferences41() {
        assert!(
            !(tree_emits(
                check_unassigned_references,
                "mapfile -t files 123; echo \"${files[@]}\""
            ))
        );
    }
    #[test]
    fn prop_checkUnassignedReferences42() {
        assert!(
            !(tree_emits(
                check_unassigned_references,
                "mapfile files -t; echo \"${files[@]}\""
            ))
        );
    }
    #[test]
    fn prop_checkUnassignedReferences43() {
        assert!(
            !(tree_emits(
                check_unassigned_references,
                "mapfile --future files; echo \"${files[@]}\""
            ))
        );
    }
    #[test]
    fn prop_checkUnassignedReferences_minusNPlain() {
        assert!(
            !(tree_emits(
                check_unassigned_references,
                "if [ -n \"$x\" ]; then echo $x; fi"
            ))
        );
    }
    #[test]
    fn prop_checkUnassignedReferences_minusZPlain() {
        assert!(
            !(tree_emits(
                check_unassigned_references,
                "if [ -z \"$x\" ]; then echo \"\"; fi"
            ))
        );
    }
    #[test]
    fn prop_checkUnassignedReferences_minusNBraced() {
        assert!(
            !(tree_emits(
                check_unassigned_references,
                "if [ -n \"${x}\" ]; then echo $x; fi"
            ))
        );
    }
    #[test]
    fn prop_checkUnassignedReferences_minusZBraced() {
        assert!(
            !(tree_emits(
                check_unassigned_references,
                "if [ -z \"${x}\" ]; then echo \"\"; fi"
            ))
        );
    }
    #[test]
    fn prop_checkUnassignedReferences_minusNDefault() {
        assert!(
            !(tree_emits(
                check_unassigned_references,
                "if [ -n \"${x:-}\" ]; then echo $x; fi"
            ))
        );
    }
    #[test]
    fn prop_checkUnassignedReferences_minusZDefault() {
        assert!(
            !(tree_emits(
                check_unassigned_references,
                "if [ -z \"${x:-}\" ]; then echo \"\"; fi"
            ))
        );
    }
    #[test]
    fn prop_checkUnassignedReferences50() {
        assert!(!(tree_emits(check_unassigned_references, "echo ${foo:+bar}")));
    }
    #[test]
    fn prop_checkUnassignedReferences51() {
        assert!(!(tree_emits(check_unassigned_references, "echo ${foo:+$foo}")));
    }
    #[test]
    fn prop_checkUnassignedReferences52() {
        assert!(!(tree_emits(check_unassigned_references, "wait -p pid; echo $pid")));
    }
    #[test]
    fn prop_checkUnassignedReferences53() {
        assert!(tree_emits(check_unassigned_references, "x=($foo)"));
    }
}
