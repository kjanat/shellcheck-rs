//! Port of `ShellCheck.AnalyzerLib`: the check-authoring API and shared context.
//!
//! Haskell models a check as `Parameters -> Token -> Writer [TokenComment] ()`
//! and combines them monoidally into a `Checker { perScript, perToken }`.
//! Here a [`Checker`] holds vectors of tree-checks (run once on the root) and
//! node-checks (run on every node pre-order); each is a boxed closure that
//! pushes diagnostics into an output vector.

use crate::ast::*;
use crate::astlib;
use crate::interface::{Code, Comment, Fix, PositionMap, Severity, Shell, TokenComment};
use std::collections::BTreeMap;

/// Precomputed analysis context (`ShellCheck.AnalyzerLib.Parameters`).
///
/// Grown as checks require more fields. The linear `variableFlow` and CFG are
/// added when their dependent checks are ported.
pub struct Parameters {
    pub shell: Shell,
    pub shell_type_specified: bool,
    pub root: Token,
    pub token_positions: PositionMap,
    /// Id -> parent Id.
    pub parent_map: BTreeMap<Id, Id>,
    /// Id -> a clone of that token (for parent/ancestor inspection).
    pub id_map: BTreeMap<Id, Token>,
    pub has_set_e: bool,
    pub has_pipefail: bool,
    pub has_lastpipe: bool,
}

impl Parameters {
    pub fn parent(&self, t: &Token) -> Option<&Token> {
        let pid = self.parent_map.get(&t.id())?;
        self.id_map.get(pid)
    }
}

/// A check pushes `TokenComment`s into this sink via the emit helpers.
pub type Out = Vec<TokenComment>;

pub fn make_comment(severity: Severity, id: Id, code: Code, note: &str) -> TokenComment {
    TokenComment {
        id,
        comment: Comment { severity, code, message: note.to_string() },
        fix: None,
    }
}

pub fn make_comment_with_fix(severity: Severity, id: Id, code: Code, note: &str, fix: Fix) -> TokenComment {
    TokenComment {
        id,
        comment: Comment { severity, code, message: note.to_string() },
        fix: Some(fix),
    }
}

pub fn err(out: &mut Out, id: Id, code: Code, note: &str) {
    out.push(make_comment(Severity::ErrorC, id, code, note));
}
pub fn warn(out: &mut Out, id: Id, code: Code, note: &str) {
    out.push(make_comment(Severity::WarningC, id, code, note));
}
pub fn info(out: &mut Out, id: Id, code: Code, note: &str) {
    out.push(make_comment(Severity::InfoC, id, code, note));
}
pub fn style(out: &mut Out, id: Id, code: Code, note: &str) {
    out.push(make_comment(Severity::StyleC, id, code, note));
}
pub fn err_with_fix(out: &mut Out, id: Id, code: Code, note: &str, fix: Fix) {
    out.push(make_comment_with_fix(Severity::ErrorC, id, code, note, fix));
}
pub fn warn_with_fix(out: &mut Out, id: Id, code: Code, note: &str, fix: Fix) {
    out.push(make_comment_with_fix(Severity::WarningC, id, code, note, fix));
}
pub fn info_with_fix(out: &mut Out, id: Id, code: Code, note: &str, fix: Fix) {
    out.push(make_comment_with_fix(Severity::InfoC, id, code, note, fix));
}
pub fn style_with_fix(out: &mut Out, id: Id, code: Code, note: &str, fix: Fix) {
    out.push(make_comment_with_fix(Severity::StyleC, id, code, note, fix));
}

// ---- fix construction (from ShellCheck.Analytics) --------------------------

use crate::interface::{InsertionPoint, Position, Replacement};

/// Precedence = length of the parent path (getPath) from the token to the root,
/// counting the token itself. Higher precedence is applied first.
fn fix_depth(params: &Parameters, id: Id) -> i32 {
    let mut depth = 1;
    let mut cur = id;
    while let Some(&p) = params.parent_map.get(&cur) {
        depth += 1;
        cur = p;
    }
    depth
}

/// `replaceStart id params n r`: replace `n` columns at the token's start.
pub fn replace_start(params: &Parameters, id: Id, n: i64, r: &str) -> Replacement {
    let (start, _) = params.token_positions.get(&id).cloned().unwrap_or_default();
    let new_end = Position { column: start.column + n, ..start.clone() };
    Replacement {
        start,
        end: new_end,
        string: r.to_string(),
        precedence: fix_depth(params, id),
        insertion_point: InsertionPoint::InsertAfter,
    }
}

/// `replaceEnd id params n r`: replace `n` columns at the token's end.
pub fn replace_end(params: &Parameters, id: Id, n: i64, r: &str) -> Replacement {
    let (_, end) = params.token_positions.get(&id).cloned().unwrap_or_default();
    let new_start = Position { column: end.column - n, ..end.clone() };
    Replacement {
        start: new_start,
        end,
        string: r.to_string(),
        precedence: fix_depth(params, id),
        insertion_point: InsertionPoint::InsertBefore,
    }
}

/// `replaceToken id params r`: replace the whole token span.
pub fn replace_token(params: &Parameters, id: Id, r: &str) -> Replacement {
    let (start, end) = params.token_positions.get(&id).cloned().unwrap_or_default();
    Replacement {
        start,
        end,
        string: r.to_string(),
        precedence: fix_depth(params, id),
        insertion_point: InsertionPoint::InsertBefore,
    }
}

pub fn fix_with(replacements: Vec<Replacement>) -> Fix {
    Fix { replacements }
}

/// `ShellCheck.AnalyzerLib.Checker` — a set of tree- and node-level checks.
#[derive(Default)]
pub struct Checker {
    pub tree_checks: Vec<Box<dyn Fn(&Parameters, &Token, &mut Out)>>,
    pub node_checks: Vec<Box<dyn Fn(&Parameters, &Token, &mut Out)>>,
}

impl Checker {
    pub fn new() -> Checker {
        Checker::default()
    }

    pub fn tree<F: Fn(&Parameters, &Token, &mut Out) + 'static>(&mut self, f: F) {
        self.tree_checks.push(Box::new(f));
    }

    pub fn node<F: Fn(&Parameters, &Token, &mut Out) + 'static>(&mut self, f: F) {
        self.node_checks.push(Box::new(f));
    }

    pub fn merge(&mut self, mut other: Checker) {
        self.tree_checks.append(&mut other.tree_checks);
        self.node_checks.append(&mut other.node_checks);
    }
}

/// `runChecker`: run tree checks on the root, then node checks on every node.
pub fn run_checker(params: &Parameters, checker: &Checker) -> Out {
    let mut out = Out::new();
    for c in &checker.tree_checks {
        c(params, &params.root, &mut out);
    }
    if !checker.node_checks.is_empty() {
        params.root.visit_preorder(&mut |t| {
            for c in &checker.node_checks {
                c(params, t, &mut out);
            }
        });
    }
    out
}

// ---- context construction --------------------------------------------------

/// `determineShell`: derive the shell from the shebang / shell override, else
/// the fallback, else Bash.
pub fn determine_shell(fallback: Option<Shell>, root: &Token) -> Shell {
    let candidate = get_candidate(root);
    astlib::shell_for_executable(&candidate)
        .or(fallback)
        .unwrap_or(Shell::Bash)
}

fn get_candidate(t: &Token) -> String {
    match &*t.inner {
        InnerToken::T_Script { shebang, .. } => from_shebang(shebang),
        InnerToken::T_Annotation { annotations, token } => {
            for a in annotations {
                if let Annotation::ShellOverride(s) = a {
                    return s.clone();
                }
            }
            get_candidate(token)
        }
        _ => String::new(),
    }
}

fn from_shebang(shebang: &Token) -> String {
    if let InnerToken::T_Literal(s) = &*shebang.inner {
        astlib::executable_from_shebang(s)
    } else {
        String::new()
    }
}

/// Build Id -> parent-Id and Id -> token maps.
pub fn build_maps(root: &Token) -> (BTreeMap<Id, Id>, BTreeMap<Id, Token>) {
    let mut parent = BTreeMap::new();
    let mut id_map = BTreeMap::new();
    fn go(t: &Token, parent: &mut BTreeMap<Id, Id>, id_map: &mut BTreeMap<Id, Token>) {
        id_map.insert(t.id(), t.clone());
        for c in t.children() {
            parent.insert(c.id(), t.id());
            go(c, parent, id_map);
        }
    }
    go(root, &mut parent, &mut id_map);
    (parent, id_map)
}

/// Whether the script sets a given `set -o` / `shopt -s` option anywhere.
/// Simplified scan over simple commands.
pub fn is_option_set(opt: &str, root: &Token) -> bool {
    let mut found = false;
    root.visit_preorder(&mut |t| {
        if let InnerToken::T_SimpleCommand { words, .. } = &*t.inner {
            let lits: Vec<String> = words.iter().filter_map(astlib::get_literal_string).collect();
            if let Some(first) = lits.first() {
                if first == "shopt" && lits.iter().any(|w| w == opt) {
                    found = true;
                }
                if first == "set" && lits.iter().any(|w| w == opt || w == "-o") {
                    // `set -o opt`
                    if lits.iter().any(|w| w == opt) {
                        found = true;
                    }
                }
            }
        }
    });
    found
}

/// `containsSetE` (approximate): script has `set -e` / `set -o errexit`.
pub fn contains_set_e(root: &Token) -> bool {
    let mut found = false;
    root.visit_preorder(&mut |t| {
        if let InnerToken::T_SimpleCommand { words, .. } = &*t.inner {
            let lits: Vec<String> = words.iter().filter_map(astlib::get_literal_string).collect();
            if lits.first().map(|s| s == "set").unwrap_or(false) {
                if lits.iter().any(|w| w.starts_with("-e") || w == "errexit" || w == "-o") {
                    if lits.iter().any(|w| w.contains('e') && w.starts_with('-')) || lits.iter().any(|w| w == "errexit") {
                        found = true;
                    }
                }
            }
        }
    });
    found
}

/// Build the full `Parameters` for a parsed script.
pub fn make_parameters(
    root: Token,
    token_positions: PositionMap,
    shell_override: Option<Shell>,
    fallback_shell: Option<Shell>,
) -> Parameters {
    let shell = shell_override.unwrap_or_else(|| determine_shell(fallback_shell, &root));
    let shell_type_specified = shell_override.is_some() || fallback_shell.is_some();
    let (parent_map, id_map) = build_maps(&root);
    let has_set_e = contains_set_e(&root);
    let has_pipefail = is_option_set("pipefail", &root);
    let has_lastpipe = match shell {
        Shell::Bash => is_option_set("lastpipe", &root),
        Shell::Ksh => true,
        _ => false,
    };
    Parameters {
        shell,
        shell_type_specified,
        root,
        token_positions,
        parent_map,
        id_map,
        has_set_e,
        has_pipefail,
        has_lastpipe,
    }
}

