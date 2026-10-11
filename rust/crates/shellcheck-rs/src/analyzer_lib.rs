//! Port of `ShellCheck.AnalyzerLib`: the check-authoring API and shared context.
//!
//! Haskell models a check as `Parameters -> Token -> Writer [TokenComment] ()`
//! and combines them monoidally into a `Checker { perScript, perToken }`.
//! Here a [`Checker`] holds vectors of tree-checks (run once on the root) and
//! node-checks (run on every node pre-order); each is a boxed closure that
//! pushes diagnostics into an output vector.

use crate::ast::{Annotation, AssignmentMode, ConditionType, Id, InnerToken, Token};
use crate::ast_lib;
use crate::ast_lib::is_annotation_ignoring_code;
use crate::ast_lib::{get_literal_string_def, oversimplify_concat};
use crate::cfg::{CFGParameters, InternalError};
use crate::cfg_analysis::{self, CFGAnalysis};
use crate::idhash::IdMap;
use crate::interface::{Code, Comment, Fix, PositionMap, Severity, Shell, TokenComment};
use crate::regex_lib::mk_regex;

/// Precomputed analysis context (`ShellCheck.AnalyzerLib.Parameters`).
///
/// Grown as checks require more fields. The linear `variableFlow` and CFG are
/// added when their dependent checks are ported.
pub struct Parameters {
    /// `shellType`: the shell type, such as Bash or Ksh.
    pub shell: Shell,
    /// `shellTypeSpecified`: true if the shell type was forced via flags.
    pub shell_type_specified: bool,
    /// `rootNode`: the root node of the AST.
    pub root: Token,
    /// `tokenPositions`: map from token id to start and end position.
    pub token_positions: PositionMap,
    /// Id -> parent Id. Iteration order is unspecified.
    pub parent_map: IdMap<Id, Id>,
    /// Id -> a clone of that token (for parent/ancestor inspection).
    /// Iteration order is unspecified; diagnostic ordering must not use it.
    pub id_map: IdMap<Id, Token>,
    /// `hasSetE`, `hasPipefail`, `hasLastpipe`, `hasInheritErrexit`, `hasNoglob` and `hasExecfail`,
    /// read through the methods of the same names.
    pub options: ShellOptions,
    /// A linear (bad) analysis of data flow (`ShellCheck.AnalyzerLib.variableFlow`).
    pub variable_flow: Vec<StackData>,
    /// Result of the Control Flow Graph data-flow analysis, when extended
    /// analysis is enabled (`ShellCheck.AnalyzerLib.cfgAnalysis`).
    pub cfg_analysis: Option<CFGAnalysis>,
    /// The internal error that stopped the dataflow analysis, which then
    /// runs as if extended analysis were off.
    pub dataflow_error: Option<InternalError>,
}

impl Parameters {
    /// `hasSetE`: whether this script has `set -e` anywhere.
    #[must_use]
    pub const fn has_set_e(&self) -> bool {
        self.options.has(ShellOption::SetE)
    }

    /// `hasPipefail`: whether this script has `set -o pipefail` anywhere.
    #[must_use]
    pub const fn has_pipefail(&self) -> bool {
        self.options.has(ShellOption::Pipefail)
    }

    /// `hasLastpipe`: whether this script has the `lastpipe` option set or default.
    #[must_use]
    pub const fn has_lastpipe(&self) -> bool {
        self.options.has(ShellOption::Lastpipe)
    }

    /// `hasInheritErrexit`: whether a command substitution inherits `set -e`.
    /// Bash only when `shopt -s inherit_errexit`; always for the POSIX shells;
    /// never for ksh.
    #[must_use]
    pub const fn has_inherit_errexit(&self) -> bool {
        self.options.has(ShellOption::InheritErrexit)
    }

    /// `hasNoglob`: whether this script has `set -f` or `set -o noglob` anywhere.
    #[must_use]
    pub const fn has_noglob(&self) -> bool {
        self.options.has(ShellOption::Noglob)
    }

    /// `hasExecfail`: `shopt -s execfail`, and bash only.
    #[must_use]
    pub const fn has_execfail(&self) -> bool {
        self.options.has(ShellOption::Execfail)
    }
}

/// A shell option that `Parameters` records for the whole script.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ShellOption {
    /// `set -e`.
    SetE,
    /// `set -o pipefail`.
    Pipefail,
    /// `shopt -s lastpipe`, or ksh.
    Lastpipe,
    /// `shopt -s inherit_errexit`, or a POSIX shell.
    InheritErrexit,
    /// `set -f` or `set -o noglob`.
    Noglob,
    /// `shopt -s execfail` in bash.
    Execfail,
}

/// The set of `ShellOption`s that hold for a script.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct ShellOptions(u8);

impl ShellOptions {
    const fn bit(option: ShellOption) -> u8 {
        1 << option as u8
    }

    /// Whether `option` holds.
    #[must_use]
    pub const fn has(self, option: ShellOption) -> bool {
        self.0 & Self::bit(option) != 0
    }

    /// This set, with `option` added when `on` holds.
    #[must_use]
    pub const fn with(self, option: ShellOption, on: bool) -> Self {
        if on {
            Self(self.0 | Self::bit(option))
        } else {
            self
        }
    }
}

// ---------------------------------------------------------------------------
// Linear variable-flow model (`ShellCheck.AnalyzerLib`)
// ---------------------------------------------------------------------------

/// `data Scope = SubshellScope String | NoneScope`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Scope {
    /// `SubshellScope`: a subshell, named by what created it.
    SubshellScope(String),
    /// `NoneScope`.
    NoneScope,
}

/// `data DataType = DataString DataSource | DataArray DataSource`.
#[derive(Debug, Clone)]
pub enum DataType {
    /// `DataString`.
    DataString(DataSource),
    /// `DataArray`.
    DataArray(DataSource),
}

/// `data DataSource = ...`.
#[derive(Debug, Clone)]
pub enum DataSource {
    /// `SourceFrom`: the value comes from these tokens.
    SourceFrom(Vec<Token>),
    /// `SourceExternal`.
    SourceExternal,
    /// `SourceDeclaration`.
    SourceDeclaration,
    /// `SourceInteger`.
    SourceInteger,
    /// `SourceChecked`.
    SourceChecked,
}

/// `data StackData` — one event of the linear flow.
#[derive(Debug, Clone)]
pub enum StackData {
    /// `StackScope`: a scope opens.
    StackScope(Scope),
    /// `StackScopeEnd`: the innermost scope closes.
    StackScopeEnd,
    /// (base expression, specific position, var name, assigned values)
    Assignment(Token, Token, String, DataType),
    /// (base expression, specific position, var name)
    Reference(Token, Token, String),
}

impl Parameters {
    /// The parent of `t` in `parentMap`.
    #[must_use]
    pub fn parent(&self, t: &Token) -> Option<&Token> {
        let pid = self.parent_map.get(&t.id())?;
        self.id_map.get(pid)
    }
}

/// A check pushes `TokenComment`s into this sink via the emit helpers.
pub type Out = Vec<TokenComment>;

/// `makeComment`.
#[must_use]
pub fn make_comment(severity: Severity, id: Id, code: Code, note: &str) -> TokenComment {
    TokenComment {
        id,
        comment: Comment {
            severity,
            code,
            message: note.to_string(),
        },
        fix: None,
    }
}

/// `makeCommentWithFix`.
#[must_use]
pub fn make_comment_with_fix(
    severity: Severity,
    id: Id,
    code: Code,
    note: &str,
    fix: Fix,
) -> TokenComment {
    TokenComment {
        id,
        comment: Comment {
            severity,
            code,
            message: note.to_string(),
        },
        // "If fix is empty, pretend it wasn't there" -- a check that decides it
        // cannot suggest a rewrite passes `fixWith []`, and that must read as no
        // fix at all, not as a fix with nothing in it.
        fix: if fix.replacements.is_empty() {
            None
        } else {
            Some(fix)
        },
    }
}

/// `err`: emit a `ErrorC` comment.
pub fn err(out: &mut Out, id: Id, code: Code, note: &str) {
    out.push(make_comment(Severity::ErrorC, id, code, note));
}
/// `warn`: emit a `WarningC` comment.
pub fn warn(out: &mut Out, id: Id, code: Code, note: &str) {
    out.push(make_comment(Severity::WarningC, id, code, note));
}
/// `info`: emit a `InfoC` comment.
pub fn info(out: &mut Out, id: Id, code: Code, note: &str) {
    out.push(make_comment(Severity::InfoC, id, code, note));
}
/// `style`: emit a `StyleC` comment.
pub fn style(out: &mut Out, id: Id, code: Code, note: &str) {
    out.push(make_comment(Severity::StyleC, id, code, note));
}
/// `errWithFix`: emit a `ErrorC` comment with a fix.
pub fn err_with_fix(out: &mut Out, id: Id, code: Code, note: &str, fix: Fix) {
    out.push(make_comment_with_fix(Severity::ErrorC, id, code, note, fix));
}
/// `warnWithFix`: emit a `WarningC` comment with a fix.
pub fn warn_with_fix(out: &mut Out, id: Id, code: Code, note: &str, fix: Fix) {
    out.push(make_comment_with_fix(
        Severity::WarningC,
        id,
        code,
        note,
        fix,
    ));
}
/// `infoWithFix`: emit a `InfoC` comment with a fix.
pub fn info_with_fix(out: &mut Out, id: Id, code: Code, note: &str, fix: Fix) {
    out.push(make_comment_with_fix(Severity::InfoC, id, code, note, fix));
}
/// `styleWithFix`: emit a `StyleC` comment with a fix.
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
#[must_use]
pub fn replace_start(params: &Parameters, id: Id, n: i64, r: &str) -> Replacement {
    let (start, _) = params.token_positions.get(&id).cloned().unwrap_or_default();
    let new_end = Position {
        column: start.column + n,
        ..start.clone()
    };
    Replacement {
        start,
        end: new_end,
        string: r.to_string(),
        precedence: fix_depth(params, id),
        insertion_point: InsertionPoint::InsertAfter,
    }
}

/// `replaceEnd id params n r`: replace `n` columns at the token's end.
#[must_use]
pub fn replace_end(params: &Parameters, id: Id, n: i64, r: &str) -> Replacement {
    let (_, end) = params.token_positions.get(&id).cloned().unwrap_or_default();
    let new_start = Position {
        column: end.column - n,
        ..end.clone()
    };
    Replacement {
        start: new_start,
        end,
        string: r.to_string(),
        precedence: fix_depth(params, id),
        insertion_point: InsertionPoint::InsertBefore,
    }
}

/// `replaceToken id params r`: replace the whole token span.
#[must_use]
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

/// `fixWith`.
#[must_use]
pub const fn fix_with(replacements: Vec<Replacement>) -> Fix {
    Fix { replacements }
}

/// A single tree- or node-level check: `Parameters -> Token -> Writer [TokenComment] ()`.
///
/// A check over one token: Haskell's `Parameters -> Token -> Writer [TokenComment] ()`.
/// Plain functions and closures implement it directly; `CommandCheck` and
/// `ForShell` implement it with their dispatch in front.
pub trait Check {
    /// Whether this check applies to a node kind. This must depend only on
    /// the enum variant, never its fields: dispatch caches it by discriminant.
    fn accepts_kind(&self, _kind: &InnerToken) -> bool {
        true
    }

    /// Run the check on `t`, pushing its comments into `out`.
    fn run(&self, params: &Parameters, t: &Token, out: &mut Out);
}

impl<F: Fn(&Parameters, &Token, &mut Out)> Check for F {
    fn run(&self, params: &Parameters, t: &Token, out: &mut Out) {
        self(params, t, out);
    }
}

struct KindCheck<C> {
    accepts: fn(&InnerToken) -> bool,
    check: C,
}

impl<C: Check> Check for KindCheck<C> {
    fn accepts_kind(&self, kind: &InnerToken) -> bool {
        (self.accepts)(kind)
    }

    fn run(&self, params: &Parameters, t: &Token, out: &mut Out) {
        self.check.run(params, t, out);
    }
}

/// A boxed [`Check`].
pub type CheckFn = Box<dyn Check>;

/// `ShellCheck.AnalyzerLib.Checker` — a set of tree- and node-level checks.
#[derive(Default)]
pub struct Checker {
    /// `perScript`: checks run once on the root.
    pub tree_checks: Vec<CheckFn>,
    /// `perToken`: checks run on every node.
    pub node_checks: Vec<CheckFn>,
}

impl Checker {
    /// `mempty`.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Add a tree check.
    pub fn tree<C: Check + 'static>(&mut self, c: C) {
        self.tree_checks.push(Box::new(c));
    }

    /// Add a node check.
    pub fn node<C: Check + 'static>(&mut self, c: C) {
        self.node_checks.push(Box::new(c));
    }

    /// Add a check restricted to enum variants. `accepts` must ignore fields.
    pub fn node_for<C: Check + 'static>(&mut self, accepts: fn(&InnerToken) -> bool, check: C) {
        self.node(KindCheck { accepts, check });
    }

    /// `<>`: append the checks of `other`.
    pub fn merge(&mut self, mut other: Self) {
        self.tree_checks.append(&mut other.tree_checks);
        self.node_checks.append(&mut other.node_checks);
    }
}

/// `runChecker`: run tree checks on the root, then node checks on every node.
#[must_use]
pub fn run_checker(params: &Parameters, checker: &Checker) -> Out {
    let mut out = Out::new();
    for c in &checker.tree_checks {
        c.run(params, &params.root, &mut out);
    }
    if !checker.node_checks.is_empty() {
        let mut dispatch = crate::idhash::IdMap::default();
        params.root.visit_preorder(&mut |t| {
            let checks = dispatch
                .entry(std::mem::discriminant(&*t.inner))
                .or_insert_with(|| {
                    checker
                        .node_checks
                        .iter()
                        .filter(|c| c.accepts_kind(&t.inner))
                        .collect::<Vec<_>>()
                });
            for c in checks {
                c.run(params, t, &mut out);
            }
        });
    }
    out
}

// ---- context construction --------------------------------------------------

/// `determineShell`: derive the shell from the shebang / shell override, else
/// the fallback, else Bash.
#[must_use]
pub fn determine_shell(fallback: Option<Shell>, root: &Token) -> Shell {
    let candidate = get_candidate(root);
    crate::data::shell_for_executable(&candidate)
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
        ast_lib::executable_from_shebang(s)
    } else {
        String::new()
    }
}

/// Build Id -> parent-Id and Id -> token maps.
#[must_use]
pub fn build_maps(root: &Token) -> (IdMap<Id, Id>, IdMap<Id, Token>) {
    fn go(t: &Token, parent: &mut IdMap<Id, Id>, id_map: &mut IdMap<Id, Token>) {
        id_map.insert(t.id(), t.clone());
        t.inner.for_each_child(|c| {
            parent.insert(c.id(), t.id());
            go(c, parent, id_map);
        });
    }
    let mut parent = IdMap::default();
    let mut id_map = IdMap::default();
    go(root, &mut parent, &mut id_map);
    (parent, id_map)
}

/// `isOptionSet opt`: does the script mention `shopt -s opt` or `set -o opt`
/// anywhere? Mirrors `containsShopt opt || containsSetOption opt`:
///
/// - `containsShopt`: a `shopt` command with `opt` among its arguments.
/// - `containsSetOption`: a `set` command with `opt` among its arguments, or
///   with an `o` flag before `--` at all. That last clause is the oracle's
///   behaviour (any `set -o ...` satisfies it for every `opt`), reproduced
///   deliberately rather than "corrected".
#[must_use]
pub fn is_option_set(opt: &str, root: &Token) -> bool {
    let mut found = false;
    root.visit_preorder(&mut |t| {
        if found {
            return;
        }
        if let InnerToken::T_SimpleCommand { .. } = &*t.inner {
            let name = get_command_name(t);
            let has_opt = || ast_lib::oversimplify(t).iter().any(|w| w == opt);
            found = match name.as_deref() {
                Some("shopt") => has_opt(),
                Some("set") => has_opt() || get_all_flags(t).iter().any(|(_, f)| f == "o"),
                _ => false,
            };
        }
    });
    found
}

/// `containsNoglob`: does the script disable globbing anywhere?
///
/// Same shape as `contains_set_e` with `noglob` / flag `f`: a `set` command whose arguments
/// contain `noglob` (with or without `-o`) or carry `f` in a flag group before
/// `--`, or a shebang such as `#!/bin/sh -f` (Haskell's `[[:space:]]-[^-]*f`).
pub fn contains_noglob(root: &Token) -> bool {
    use std::sync::OnceLock;
    static SHEBANG_RE: OnceLock<regex::Regex> = OnceLock::new();
    let shebang_re = SHEBANG_RE.get_or_init(|| mk_regex(r"[[:space:]]-[^-]*f"));
    let mut found = false;
    root.visit_preorder(&mut |t| {
        if found {
            return;
        }
        found = match &*t.inner {
            InnerToken::T_Script { shebang, .. } => match &*shebang.inner {
                InnerToken::T_Literal(s) => shebang_re.is_match(s),
                _ => false,
            },
            InnerToken::T_SimpleCommand { .. } => {
                get_command_name(t).as_deref() == Some("set")
                    && (ast_lib::oversimplify(t).iter().any(|w| w == "noglob")
                        || get_all_flags(t).iter().any(|(_, f)| f == "f"))
            }
            _ => false,
        };
    });
    found
}

/// `getFlagsUntil stopCondition`: turn a simple command's arguments into
/// `(token, flag)` pairs the way `ASTLib` does — `-avz` yields `a`, `v`, `z`;
/// `--bar=baz` yields `bar`; a non-flag argument yields `""`. From the first
/// argument satisfying `stop` onward, everything (that argument included) is
/// a non-flag, so for `get_all_flags` nothing at or after `--` is a flag.
/// Argument text comes from `oversimplify`, as in Haskell.
pub(crate) fn get_flags_until<'a>(
    stop: &dyn Fn(&str) -> bool,
    t: &'a Token,
) -> Vec<(&'a Token, String)> {
    get_flags_until_args(stop, arguments(t))
}

/// The body of `getFlagsUntil` over an already-extracted argument list, for
/// checks that (like `checkCommand`'s `builtin x ..` rewrite) operate on a
/// word slice rather than the `T_SimpleCommand` token.
pub(crate) fn get_flags_until_args<'a>(
    stop: &dyn Fn(&str) -> bool,
    args: &'a [Token],
) -> Vec<(&'a Token, String)> {
    let texts: Vec<(&Token, String)> = args
        .iter()
        .map(|x| (x, ast_lib::oversimplify(x).concat()))
        .collect();
    let split = texts
        .iter()
        .position(|(_, s)| stop(s))
        .unwrap_or(texts.len());
    let mut out = Vec::new();
    for (x, s) in &texts[..split] {
        if let Some(arg) = s.strip_prefix("--") {
            out.push((*x, arg.split('=').next().unwrap_or("").to_string()));
        } else if let Some(group) = s.strip_prefix('-') {
            for c in group.chars() {
                out.push((*x, c.to_string()));
            }
        } else {
            out.push((*x, String::new()));
        }
    }
    for (x, _) in &texts[split..] {
        out.push((*x, String::new()));
    }
    out
}

/// `getAllFlags`: all flags in the GNU way, up until `--`.
pub(crate) fn get_all_flags(t: &Token) -> Vec<(&Token, String)> {
    get_flags_until(&|s| s == "--", t)
}

/// `containsSetE`: does the script enable errexit anywhere?
///
/// True for a `set` command whose arguments contain `errexit` or carry the short flag `e` in
/// any flag group before `--` (`set -e`, `set -ue`, `set -xe`, `set -o
/// errexit`, but not `set -- -e`), or for a shebang such as `#!/bin/sh -e`
/// (Haskell's `[[:space:]]-[^-]*e`).
pub fn contains_set_e(root: &Token) -> bool {
    use std::sync::OnceLock;
    static SHEBANG_RE: OnceLock<regex::Regex> = OnceLock::new();
    let shebang_re = SHEBANG_RE.get_or_init(|| mk_regex(r"[[:space:]]-[^-]*e"));
    let mut found = false;
    root.visit_preorder(&mut |t| {
        if found {
            return;
        }
        found = match &*t.inner {
            InnerToken::T_Script { shebang, .. } => match &*shebang.inner {
                InnerToken::T_Literal(s) => shebang_re.is_match(s),
                _ => false,
            },
            InnerToken::T_SimpleCommand { .. } => {
                get_command_name(t).as_deref() == Some("set")
                    && (ast_lib::oversimplify(t).iter().any(|w| w == "errexit")
                        || get_all_flags(t).iter().any(|(_, f)| f == "e"))
            }
            _ => false,
        };
    });
    found
}

/// Build the full `Parameters` for a parsed script.
#[must_use]
pub fn make_parameters(
    root: Token,
    token_positions: PositionMap,
    shell_override: Option<Shell>,
    fallback_shell: Option<Shell>,
) -> Parameters {
    make_parameters_ext(root, token_positions, shell_override, fallback_shell, None)
}

/// Like [`make_parameters`] but with an explicit extended-analysis override from
/// the `CheckSpec` (`--extended-analysis` / rc `extended-analysis=`).
///
/// The override takes precedence over any inline directive, matching the Haskell
/// `AnalyzerLib`: `fromMaybe True $ msum [asExtendedAnalysis spec, directive]`.
#[must_use]
pub fn make_parameters_ext(
    root: Token,
    token_positions: PositionMap,
    shell_override: Option<Shell>,
    fallback_shell: Option<Shell>,
    extended_analysis_override: Option<bool>,
) -> Parameters {
    let shell = shell_override.unwrap_or_else(|| determine_shell(fallback_shell, &root));
    let shell_type_specified = shell_override.is_some() || fallback_shell.is_some();
    let (parent_map, id_map) = build_maps(&root);
    let has_set_e = contains_set_e(&root);
    let has_noglob = contains_noglob(&root);
    let has_pipefail = is_option_set("pipefail", &root);
    let has_inherit_errexit = match shell {
        Shell::Bash => is_option_set("inherit_errexit", &root),
        Shell::Dash | Shell::BusyboxSh | Shell::Sh => true,
        Shell::Ksh => false,
    };
    let has_lastpipe = match shell {
        Shell::Bash => is_option_set("lastpipe", &root),
        Shell::Ksh => true,
        _ => false,
    };
    // `hasExecfail`, computed here once as upstream does. `checkSpuriousExec`
    // consults it on every node, and `isOptionSet` walks the whole tree.
    let has_execfail = match shell {
        Shell::Bash => is_option_set("execfail", &root),
        _ => false,
    };

    // Linear variable-flow analysis (does not depend on itself or the CFG).
    let variable_flow = get_variable_flow(&parent_map, &id_map, has_lastpipe, &root);

    // Control Flow Graph data-flow analysis, gated on extended analysis. The
    // spec override (CLI/rc) wins over a `# shellcheck extended-analysis=...`
    // directive, which wins over the default True (Haskell `msum`).
    let extended_analysis = extended_analysis_override
        .or_else(|| get_extended_analysis_directive(&root))
        .unwrap_or(true);
    let (cfg_analysis, dataflow_error) = if extended_analysis {
        let cf_params = CFGParameters {
            cf_lastpipe: has_lastpipe,
            cf_pipefail: has_pipefail,
        };
        match analyze_control_flow(cf_params, &root) {
            Ok(analysis) => (Some(analysis), None),
            Err(e) => (None, Some(e)),
        }
    } else {
        (None, None)
    };

    Parameters {
        shell,
        shell_type_specified,
        root,
        token_positions,
        parent_map,
        id_map,
        options: ShellOptions::default()
            .with(ShellOption::SetE, has_set_e)
            .with(ShellOption::Pipefail, has_pipefail)
            .with(ShellOption::Lastpipe, has_lastpipe)
            .with(ShellOption::InheritErrexit, has_inherit_errexit)
            .with(ShellOption::Noglob, has_noglob)
            .with(ShellOption::Execfail, has_execfail),
        variable_flow,
        cfg_analysis,
        dataflow_error,
    }
}

/// `getEnableDirectives`: the `enable=` names on the file-wide annotation, which
/// turn optional checks on exactly as `--enable` does.
///
/// Only the root is
/// consulted, as upstream does -- an `enable=` deeper in the file does nothing.
#[must_use]
pub fn get_enable_directives(root: &Token) -> Vec<String> {
    match &*root.inner {
        InnerToken::T_Annotation { annotations, .. } => annotations
            .iter()
            .filter_map(|a| match a {
                Annotation::EnableComment(s) => Some(s.clone()),
                _ => None,
            })
            .collect(),
        _ => Vec::new(),
    }
}

#[cfg(test)]
thread_local! {
    pub(crate) static INJECTED_DATAFLOW_ERROR: std::cell::Cell<Option<InternalError>> =
        const { std::cell::Cell::new(None) };
}

fn analyze_control_flow(params: CFGParameters, root: &Token) -> Result<CFGAnalysis, InternalError> {
    #[cfg(test)]
    if let Some(error) = INJECTED_DATAFLOW_ERROR.with(std::cell::Cell::take) {
        return Err(error);
    }
    cfg_analysis::analyze_control_flow(&params, root)
}

/// `getExtendedAnalysisDirective`: the first `extended-analysis=` annotation, if any.
fn get_extended_analysis_directive(root: &Token) -> Option<bool> {
    if let InnerToken::T_Annotation { annotations, .. } = &*root.inner {
        annotations.iter().find_map(|a| match a {
            Annotation::ExtendedAnalysis(b) => Some(*b),
            _ => None,
        })
    } else {
        None
    }
}

// ===========================================================================
// Shared AST helpers for the dataflow checks (SC2154/SC2034/SC2086)
// Ported from ShellCheck.ASTLib / ShellCheck.AnalyzerLib / ShellCheck.Data.
// ===========================================================================

use crate::cfg::{
    get_braced_modifier, get_braced_reference, get_bsd_opts as cfg_get_bsd_opts,
    get_generic_opts as cfg_get_generic_opts, get_gnu_opts as cfg_get_gnu_opts,
    get_index_references, get_offset_references, is_variable_char, is_variable_name,
};

/// `getPrintfFormats` from `ShellCheck.Checks.Commands`: the format string's
/// conversions as a string of type characters, `*` for each argument-consuming
/// width/precision — e.g. `"Hello %s"` -> `"s"`, `"%(%s)T %0*d\n"` -> `"T*d"`.
pub(crate) fn get_printf_formats(s: &str) -> String {
    let cs: Vec<char> = s.chars().collect();
    get_formats(&cs)
}

fn get_formats(cs: &[char]) -> String {
    if cs.is_empty() {
        return String::new();
    }
    if cs[0] == '%' {
        if cs.get(1) == Some(&'%') {
            return get_formats(&cs[2..]);
        }
        if cs.get(1) == Some(&'(') {
            let rest = &cs[2..];
            if let Some(pos) = rest.iter().position(|&c| c == ')')
                && pos + 1 < rest.len()
            {
                let c = rest[pos + 1];
                let trailing = &rest[pos + 2..];
                let mut out = String::new();
                out.push(c);
                out.push_str(&get_formats(trailing));
                return out;
            }
            return String::new();
        }
        return regex_based_get_formats(&cs[1..]);
    }
    get_formats(&cs[1..])
}

fn regex_based_get_formats(rest: &[char]) -> String {
    let (mut out, remaining) = match match_format_re(rest) {
        Some((width_star, prec_star, typ, remaining)) => {
            let mut out = String::new();
            if width_star {
                out.push('*');
            }
            if prec_star {
                out.push('*');
            }
            out.push(typ);
            (out, remaining)
        }
        None => (rest.iter().take(1).collect::<String>(), rest),
    };
    out.push_str(&get_formats(remaining));
    out
}

const PRINTF_TYPE_CHARS: &str = "diouxXfFeEgGaAcsbqQSC";

/// Manual match of
/// `^#?-?\+? ?0?(\*|\d*)\.?(\d*|\*)(hh|h|l|ll|q|L|j|z|Z|t)?([diouxXfFeEgGaAcsbqQSC])((\n|.)*)`
/// Returns (`width_is_star`, `precision_is_star`, `type_char`, `remaining_after_type`).
fn match_format_re(rest: &[char]) -> Option<(bool, bool, char, &[char])> {
    let mut i = 0usize;
    // flags: #? -? +? space? 0?  (each optional, fixed order)
    if rest.get(i) == Some(&'#') {
        i += 1;
    }
    if rest.get(i) == Some(&'-') {
        i += 1;
    }
    if rest.get(i) == Some(&'+') {
        i += 1;
    }
    if rest.get(i) == Some(&' ') {
        i += 1;
    }
    if rest.get(i) == Some(&'0') {
        i += 1;
    }
    // width: (\*|\d*)
    let width_star;
    if rest.get(i) == Some(&'*') {
        width_star = true;
        i += 1;
    } else {
        width_star = false;
        while rest.get(i).is_some_and(char::is_ascii_digit) {
            i += 1;
        }
    }
    // \.?
    if rest.get(i) == Some(&'.') {
        i += 1;
    }
    // precision: (\d*|\*) — '*' only via backtracking; equivalently, '*' here is star.
    let prec_star;
    if rest.get(i) == Some(&'*') {
        prec_star = true;
        i += 1;
    } else {
        prec_star = false;
        while rest.get(i).is_some_and(char::is_ascii_digit) {
            i += 1;
        }
    }
    // length modifier (hh|h|l|ll|q|L|j|z|Z|t)? — greedy, but only if a type char
    // then follows (regex backtracking). Alternation preference order preserved.
    let type_at = |j: usize| -> Option<char> {
        rest.get(j)
            .copied()
            .filter(|c| PRINTF_TYPE_CHARS.contains(*c))
    };
    let mods = ["hh", "h", "l", "ll", "q", "L", "j", "z", "Z", "t"];
    let mut chosen_len = 0usize;
    for m in mods {
        let mc: Vec<char> = m.chars().collect();
        if i + mc.len() <= rest.len()
            && rest[i..i + mc.len()] == mc[..]
            && type_at(i + mc.len()).is_some()
        {
            chosen_len = mc.len();
            break;
        }
    }
    let type_pos = i + chosen_len;
    let typ = type_at(type_pos)?;
    Some((width_star, prec_star, typ, &rest[type_pos + 1..]))
}

/// `getWordParts`.
pub(crate) fn word_parts(t: &Token) -> Vec<&Token> {
    ast_lib::get_word_parts(t)
}

/// The token and its ancestors, stopping without allocating when a caller
/// finds the enclosing construct it needs.
pub(crate) fn path_iter<'a>(
    params: &'a Parameters,
    t: &'a Token,
) -> impl Iterator<Item = &'a Token> {
    std::iter::successors(Some(t), |node| params.parent(node))
}

/// `getPath tree t`: the token and its ancestors up to the root (owned clones).
pub(crate) fn get_path(params: &Parameters, t: &Token) -> Vec<Token> {
    path_iter(params, t).cloned().collect()
}

// ---- command-name resolution ----------------------------------------------

fn is_flag_word(t: &Token) -> bool {
    word_parts(t)
        .first()
        .is_some_and(|p| matches!(&*p.inner, InnerToken::T_Literal(s) if s.starts_with('-')))
}

/// `getCommand`.
pub(crate) fn get_command(t: &Token) -> Option<&Token> {
    match &*t.inner {
        InnerToken::T_Redirecting { cmd, .. } => get_command(cmd),
        InnerToken::T_SimpleCommand { words, .. } if !words.is_empty() => Some(t),
        InnerToken::T_Annotation { token, .. } => get_command(token),
        _ => None,
    }
}

pub(crate) fn get_effective_command_token<'a>(s: &str, args: &'a [Token]) -> Option<&'a Token> {
    let first_arg = || -> Option<&'a Token> {
        let arg = args.first()?;
        if is_flag_word(arg) { None } else { Some(arg) }
    };
    match s {
        "busybox" | "builtin" | "command" | "run" => first_arg(),
        "exec" => {
            let opts = cfg_get_bsd_opts("cla:", args)?;
            let (_, (t, _)) = opts.into_iter().find(|(name, _)| name.is_empty())?;
            // find the token in args by identity
            args.iter().find(|x| x.id() == t.id())
        }
        _ => None,
    }
}

pub(crate) fn get_command_name_and_token(direct: bool, t: &Token) -> (Option<String>, &Token) {
    if let Some(cmd) = get_command(t)
        && let InnerToken::T_SimpleCommand { words, .. } = &*cmd.inner
        && let Some((w, rest)) = words.split_first()
        && let Some(s) = ast_lib::get_literal_string(w)
    {
        if !direct && let Some(actual) = get_effective_command_token(&s, rest) {
            return (ast_lib::get_literal_string(actual), actual);
        }
        return (Some(s), w);
    }
    (None, t)
}

/// `getCommandName`.
pub(crate) fn get_command_name(t: &Token) -> Option<String> {
    get_command_name_and_token(false, t).0
}

/// `getCommandTokenOrThis`.
pub(crate) fn get_command_token_or_this(t: &Token) -> &Token {
    get_command_name_and_token(false, t).1
}

/// `getCommandBasename`.
pub(crate) fn get_command_basename(t: &Token) -> Option<String> {
    get_command_name(t).map(|s| s.rsplit('/').next().unwrap_or(&s).to_string())
}

/// `isCommandMatch`.
fn is_command_match(t: &Token, matcher: impl Fn(&str) -> bool) -> bool {
    get_command_name(t).is_some_and(|s| matcher(&s))
}

/// `isCommand token str` (also matches `/usr/bin/str`).
pub(crate) fn is_command(t: &Token, str: &str) -> bool {
    is_command_match(t, |cmd| cmd == str || cmd.ends_with(&format!("/{str}")))
}

/// `getAllFlags` restricted to the flag strings (`map snd $ getAllFlags`).
fn command_flag_strings(words: &[Token]) -> Vec<String> {
    get_all_flags_words(words)
        .into_iter()
        .map(|(_, s)| s)
        .collect()
}

/// `getFlagsUntil (== "--")` over an already-extracted words list (words[0] is cmd).
fn get_all_flags_words(words: &[Token]) -> Vec<(Token, String)> {
    let args: &[Token] = if words.is_empty() { &[] } else { &words[1..] };
    let mut broken = false;
    let mut flag_args: Vec<(Token, String)> = vec![];
    let mut rest: Vec<Token> = vec![];
    for x in args {
        let txt = oversimplify_concat(x);
        if !broken && txt == "--" {
            broken = true;
        }
        if broken {
            rest.push(x.clone());
        } else {
            flag_args.push((x.clone(), txt));
        }
    }
    let mut out: Vec<(Token, String)> = vec![];
    for (x, txt) in flag_args {
        if let Some(arg) = txt.strip_prefix("--") {
            out.push((x, arg.split('=').next().unwrap_or("").to_string()));
        } else if let Some(a) = txt.strip_prefix('-') {
            for v in a.chars() {
                out.push((x.clone(), v.to_string()));
            }
        } else {
            out.push((x, String::new()));
        }
    }
    for x in rest {
        out.push((x, String::new()));
    }
    out
}

// ---- predicates for SC2086 -------------------------------------------------

/// `isArrayExpansion`.
pub(crate) fn is_array_expansion(t: &Token) -> bool {
    match &*t.inner {
        InnerToken::T_DollarBraced { op, .. } => {
            let s = oversimplify_concat(op);
            s.starts_with('@') || (!s.starts_with('#') && s.contains("[@]"))
        }
        _ => false,
    }
}

/// `isCountingReference` — `${#var}`.
pub(crate) fn is_counting_reference(t: &Token) -> bool {
    match &*t.inner {
        InnerToken::T_DollarBraced { op, .. } => oversimplify_concat(op).starts_with('#'),
        _ => false,
    }
}

/// `isQuotedAlternativeReference` — `${x:+..}` / `${x[i]:+..}`.
pub(crate) fn is_quoted_alternative_reference(t: &Token) -> bool {
    match &*t.inner {
        InnerToken::T_DollarBraced { op, .. } => {
            let m = get_braced_modifier(&oversimplify_concat(op));
            // (^|\]):?\+
            if m.starts_with('+') || m.starts_with(":+") {
                return true;
            }
            let b: Vec<char> = m.chars().collect();
            for i in 0..b.len() {
                if b[i] == ']' {
                    let mut j = i + 1;
                    if j < b.len() && b[j] == ':' {
                        j += 1;
                    }
                    if j < b.len() && b[j] == '+' {
                        return true;
                    }
                }
            }
            false
        }
        _ => false,
    }
}

/// `usedAsCommandName`.
pub(crate) fn used_as_command_name(params: &Parameters, token: &Token) -> bool {
    use InnerToken::{T_DoubleQuoted, T_NormalWord, T_SimpleCommand};
    let mut current_id = token.id();
    let mut node = params.parent(token);
    while let Some(t) = node {
        match &*t.inner {
            T_NormalWord(list) if list.len() == 1 && list[0].id() == current_id => {
                current_id = t.id();
                node = params.parent(t);
            }
            T_DoubleQuoted(list) if list.len() == 1 && list[0].id() == current_id => {
                current_id = t.id();
                node = params.parent(t);
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

/// `isParamTo tree cmd t`.
pub(crate) fn is_param_to(params: &Parameters, cmd: &str, t: &Token) -> bool {
    let mut cur = t;
    loop {
        let Some(parent) = params.parent(cur) else {
            return false;
        };
        match &*parent.inner {
            InnerToken::T_SingleQuoted(_)
            | InnerToken::T_DoubleQuoted(_)
            | InnerToken::T_NormalWord(_) => {
                cur = parent;
            }
            InnerToken::T_SimpleCommand { .. } | InnerToken::T_Redirecting { .. } => {
                return is_command(parent, cmd);
            }
            _ => return false,
        }
    }
}

// ---- isQuoteFree (parent-context walk, non-strict) -------------------------

pub(crate) fn is_quote_free(params: &Parameters, t: &Token) -> bool {
    if is_quote_free_element(params, t) {
        return true;
    }
    let mut node = params.parent(t);
    while let Some(a) = node {
        if let Some(b) = is_quote_free_context(params, a) {
            return b;
        }
        node = params.parent(a);
    }
    false
}

pub(crate) fn is_quote_free_element(params: &Parameters, t: &Token) -> bool {
    match &*t.inner {
        InnerToken::T_Assignment { .. } => assignment_is_quoting(params, t),
        InnerToken::T_FdRedirect { .. } => true,
        _ => false,
    }
}

pub(crate) fn is_quote_free_context(params: &Parameters, t: &Token) -> Option<bool> {
    use InnerToken::{
        T_Arithmetic, T_Assignment, T_CaseExpression, T_DollarArithmetic, T_DollarBraced,
        T_DollarDoubleQuoted, T_DoubleQuoted, T_ForIn, T_HereDoc, T_Redirecting, T_SelectIn,
        TA_Sequence, TC_Binary, TC_Nullary, TC_Unary,
    };
    match &*t.inner {
        TC_Nullary {
            typ: ConditionType::DoubleBracket,
            ..
        }
        | TC_Unary {
            typ: ConditionType::DoubleBracket,
            ..
        }
        | TC_Binary {
            typ: ConditionType::DoubleBracket,
            ..
        }
        | TA_Sequence(_)
        | T_Arithmetic(_)
        | T_DollarArithmetic(_)
        | T_DoubleQuoted(_)
        | T_DollarDoubleQuoted(_)
        | T_CaseExpression { .. }
        | T_HereDoc { .. }
        | T_DollarBraced { .. }
        | T_ForIn { .. }
        | T_SelectIn { .. } => Some(true),
        T_Assignment { .. } => Some(assignment_is_quoting(params, t)),
        T_Redirecting { .. } => Some(false),
        _ => None,
    }
}

pub(crate) fn assignment_is_quoting(params: &Parameters, assign: &Token) -> bool {
    if params.shell != Shell::Sh {
        return true;
    }
    !is_assignment_param_to_command(params, assign)
}

pub(crate) fn is_assignment_param_to_command(params: &Parameters, assign: &Token) -> bool {
    if let Some(parent) = params.parent(assign)
        && let InnerToken::T_SimpleCommand { words, .. } = &*parent.inner
        && !words.is_empty()
    {
        return words[1..].iter().any(|w| w.id() == assign.id());
    }
    false
}

// ---- Levenshtein distance (`dist`) -----------------------------------------

pub(crate) fn dist(a: &str, b: &str) -> usize {
    let a: Vec<char> = a.chars().collect();
    let b: Vec<char> = b.chars().collect();
    let n = a.len();
    let m = b.len();
    if n == 0 {
        return m;
    }
    if m == 0 {
        return n;
    }
    let mut prev: Vec<usize> = (0..=m).collect();
    let mut cur = vec![0usize; m + 1];
    for i in 1..=n {
        cur[0] = i;
        for j in 1..=m {
            let cost = usize::from(a[i - 1] != b[j - 1]);
            cur[j] = (prev[j] + 1).min(cur[j - 1] + 1).min(prev[j - 1] + cost);
        }
        std::mem::swap(&mut prev, &mut cur);
    }
    prev[m]
}

// ---- getVariablesFromLiteral(Token) ----------------------------------------

fn get_variables_from_literal(s: &str) -> Vec<String> {
    use std::sync::OnceLock;
    static RE: OnceLock<regex::Regex> = OnceLock::new();
    let re = RE.get_or_init(|| mk_regex(r"\$\{?([A-Za-z0-9_]+)"));
    re.captures_iter(s)
        .filter_map(|c| c.get(1).map(|m| m.as_str().to_string()))
        .collect()
}

fn get_variables_from_literal_token(t: &Token) -> Vec<String> {
    get_variables_from_literal(&get_literal_string_def(" ", t))
}

// ---- special variable data (ShellCheck.Data) -------------------------------

// ===========================================================================
// getVariableFlow (`ShellCheck.AnalyzerLib.getVariableFlow`)
// ===========================================================================

struct FlowCtx<'a> {
    parent_map: &'a IdMap<Id, Id>,
    id_map: &'a IdMap<Id, Token>,
    // The only shell-dependent decision in this flow (whether the last pipeline
    // element runs in a subshell) is captured by `has_lastpipe`, computed
    // upstream exactly as Haskell's `hasLastpipe`; `shellType` itself is not used
    // by getVariableFlow (see AnalyzerLib.hs `leadType`/`causesSubshell`).
    has_lastpipe: bool,
}

impl FlowCtx<'_> {
    fn parent(&self, t: &Token) -> Option<&Token> {
        let pid = self.parent_map.get(&t.id())?;
        self.id_map.get(pid)
    }
}

#[derive(Clone)]
enum DefCtor {
    Str,
    Arr,
}

const fn apply_def(d: &DefCtor, src: DataSource) -> DataType {
    match d {
        DefCtor::Str => DataType::DataString(src),
        DefCtor::Arr => DataType::DataArray(src),
    }
}

/// `dataTypeFrom defaultType v`.
fn data_type_from(def: &DefCtor, value: &Token) -> DataType {
    let ctor = if matches!(&*value.inner, InnerToken::T_Array(_)) {
        DefCtor::Arr
    } else {
        def.clone()
    };
    apply_def(&ctor, DataSource::SourceFrom(vec![value.clone()]))
}

pub(crate) fn get_variable_flow(
    parent_map: &IdMap<Id, Id>,
    id_map: &IdMap<Id, Token>,
    has_lastpipe: bool,
    root: &Token,
) -> Vec<StackData> {
    let ctx = FlowCtx {
        parent_map,
        id_map,
        has_lastpipe,
    };
    let mut out = Vec::new();
    stack_analysis(&ctx, root, &mut out);
    out
}

fn assign_first(t: &Token) -> bool {
    matches!(
        &*t.inner,
        InnerToken::T_ForIn { .. } | InnerToken::T_SelectIn { .. } | InnerToken::T_BatsTest { .. }
    )
}

fn stack_analysis(ctx: &FlowCtx, t: &Token, out: &mut Vec<StackData>) {
    // startScope
    let scope = lead_type(ctx, t);
    let has_scope = !matches!(scope, Scope::NoneScope);
    if has_scope {
        out.push(StackData::StackScope(scope));
    }
    let af = assign_first(t);
    if af {
        push_modified(t, out);
    }
    // recurse (doStackAnalysis)
    t.inner.for_each_child(|c| stack_analysis(ctx, c, out));
    // endScope
    for (b, tok, name) in get_referenced_variables(ctx, t) {
        out.push(StackData::Reference(b, tok, name));
    }
    if !af {
        push_modified(t, out);
    }
    if has_scope {
        out.push(StackData::StackScopeEnd);
    }
}

fn push_modified(t: &Token, out: &mut Vec<StackData>) {
    for (b, tok, name, dt) in get_modified_variables(t) {
        out.push(StackData::Assignment(b, tok, name, dt));
    }
}

fn lead_type(ctx: &FlowCtx, t: &Token) -> Scope {
    use InnerToken::{
        T_Backgrounded, T_Backticked, T_BatsTest, T_CoProcBody, T_DollarExpansion, T_Redirecting,
        T_Subshell,
    };
    let s = |x: &str| Scope::SubshellScope(x.to_string());
    match &*t.inner {
        T_DollarExpansion(_) => s("$(..) expansion"),
        T_Backticked(_) => s("`..` expansion"),
        T_Backgrounded(_) => s("backgrounding &"),
        T_Subshell(_) => s("(..) group"),
        T_BatsTest { .. } => s("@bats test"),
        T_CoProcBody(_) => s("coproc"),
        T_Redirecting { .. } => {
            if causes_subshell(ctx, t) == Some(true) {
                s("pipeline")
            } else {
                Scope::NoneScope
            }
        }
        _ => Scope::NoneScope,
    }
}

fn causes_subshell(ctx: &FlowCtx, t: &Token) -> Option<bool> {
    let parent = ctx.parent(t)?;
    let InnerToken::T_Pipeline { commands: list, .. } = &*parent.inner else {
        return None;
    };
    Some(if list.len() >= 2 {
        !ctx.has_lastpipe || list.last().map(super::ast::Token::id) != Some(t.id())
    } else {
        false
    })
}

// ---- getModifiedVariables --------------------------------------------------

fn is_closing_file_op(op: &Token) -> bool {
    match &*op.inner {
        InnerToken::T_IoDuplicate { op: inner, num } if num == "-" => {
            matches!(
                &*inner.inner,
                InnerToken::T_GREATAND | InnerToken::T_LESSAND
            )
        }
        _ => false,
    }
}

/// `getVariableForTestDashV`.
fn get_variable_for_test_dash_v(t: &Token) -> Option<String> {
    let full = ast_lib::get_literal_string_ext(t, &|inner| match inner {
        InnerToken::T_Glob(s) => Some(s.clone()),
        _ => Some("\0".to_string()),
    })?;
    let str: String = full.chars().take_while(|c| *c != '[').collect();
    if is_variable_name(&str) {
        Some(str)
    } else {
        None
    }
}

fn mark_as_checked(place: &Token, token: &Token) -> Vec<(Token, Token, String, DataType)> {
    let mut out = Vec::new();
    for part in word_parts(token) {
        if let InnerToken::T_DollarBraced { op, .. } = &*part.inner {
            let str = get_braced_reference(&oversimplify_concat(op));
            if is_variable_name(&str) {
                out.push((
                    place.clone(),
                    part.clone(),
                    str,
                    DataType::DataString(DataSource::SourceChecked),
                ));
            }
        }
    }
    out
}

fn get_modified_variables(t: &Token) -> Vec<(Token, Token, String, DataType)> {
    use DataSource::{SourceChecked, SourceExternal, SourceFrom, SourceInteger};
    use DataType::{DataArray, DataString};
    use InnerToken::{
        T_Assignment, T_BatsTest, T_CoProc, T_DollarBraced, T_FdRedirect, T_ForIn, T_SelectIn,
        T_SimpleCommand, TA_Assignment, TA_Unary, TC_Nullary, TC_Unary,
    };
    let own = |name: String, dt: DataType| (t.clone(), t.clone(), name, dt);
    match &*t.inner {
        T_SimpleCommand { assignments, words } if words.is_empty() => assignments
            .iter()
            .filter_map(|x| match &*x.inner {
                T_Assignment { var, value, .. } => Some((
                    x.clone(),
                    x.clone(),
                    var.clone(),
                    data_type_from(&DefCtor::Str, value),
                )),
                _ => None,
            })
            .collect(),
        T_SimpleCommand { words, .. } => get_modified_variable_command(t, words),

        TA_Unary { .. } | TA_Assignment { .. } => get_modified_arithmetic_variable(t),

        T_BatsTest { .. } => vec![
            own("lines".into(), DataArray(SourceExternal)),
            own("status".into(), DataString(SourceInteger)),
            own("output".into(), DataString(SourceExternal)),
            own("stderr".into(), DataString(SourceExternal)),
            own("stderr_lines".into(), DataArray(SourceExternal)),
        ],

        TC_Unary { op, token, .. } if op == "-v" => get_variable_for_test_dash_v(token)
            .map(|str| (t.clone(), token.clone(), str, DataString(SourceChecked)))
            .into_iter()
            .collect(),
        TC_Unary { op, token, .. } if op == "-n" || op == "-z" => mark_as_checked(t, token),
        TC_Nullary { token, .. } => mark_as_checked(t, token),

        T_DollarBraced { op, .. } => {
            let string = oversimplify_concat(op);
            let modifier = get_braced_modifier(&string);
            if modifier.starts_with('=') || modifier.starts_with(":=") {
                vec![own(
                    get_braced_reference(&string),
                    DataString(SourceFrom(vec![op.clone()])),
                )]
            } else {
                vec![]
            }
        }

        T_FdRedirect { fd, target } if fd.starts_with('{') => {
            if is_closing_file_op(target) {
                vec![]
            } else {
                let var: String = fd[1..].chars().take_while(|c| *c != '}').collect();
                vec![own(var, DataString(SourceInteger))]
            }
        }

        T_CoProc { name: None, .. } => vec![own("COPROC".into(), DataArray(SourceInteger))],
        T_CoProc {
            name: Some(token), ..
        } => ast_lib::get_literal_string(token)
            .map(|name| own(name, DataArray(SourceInteger)))
            .into_iter()
            .collect(),

        T_ForIn { var, items, .. } if items.is_empty() => {
            vec![own(var.clone(), DataString(SourceExternal))]
        }
        T_ForIn { var, items, .. } | T_SelectIn { var, items, .. } => {
            vec![own(var.clone(), DataString(SourceFrom(items.clone())))]
        }
        _ => vec![],
    }
}

/// The `TA_Unary` and `TA_Assignment` cases of `getModifiedVariables`.
fn get_modified_arithmetic_variable(t: &Token) -> Vec<(Token, Token, String, DataType)> {
    use InnerToken::{TA_Assignment, TA_Unary, TA_Variable};
    match &*t.inner {
        TA_Unary { op, operand } if op.contains("++") || op.contains("--") => {
            match &*operand.inner {
                TA_Variable { name, .. } => vec![(
                    t.clone(),
                    operand.clone(),
                    name.clone(),
                    DataType::DataString(DataSource::SourceInteger),
                )],
                _ => vec![],
            }
        }
        TA_Assignment { op, lhs, rhs: _ } => {
            const OPS: &[&str] = &[
                "=", "*=", "/=", "%=", "+=", "-=", "<<=", ">>=", "&=", "^=", "|=",
            ];
            if OPS.contains(&op.as_str())
                && let TA_Variable { name, .. } = &*lhs.inner
            {
                return vec![(
                    t.clone(),
                    t.clone(),
                    name.clone(),
                    DataType::DataString(DataSource::SourceInteger),
                )];
            }
            vec![]
        }
        _ => vec![],
    }
}

/// `getModifierParam def t`.
fn get_modifier_param(
    def: &DefCtor,
    base: &Token,
    t: &Token,
) -> Vec<(Token, Token, String, DataType)> {
    match &*t.inner {
        InnerToken::T_Assignment { var, value, .. } => {
            vec![(
                base.clone(),
                t.clone(),
                var.clone(),
                data_type_from(def, value),
            )]
        }
        InnerToken::T_NormalWord(_) => {
            // `getModifierParam def t@T_NormalWord{}`: the *whole* literal has
            // to be a variable name. `declare foo=bar` is a T_Assignment by the
            // time it gets here, and a word that merely looks like one
            // (`declare a\=b`, `declare 'f=1'`) declares nothing.
            match ast_lib::get_literal_string(t) {
                Some(name) if is_variable_name(&name) => vec![(
                    base.clone(),
                    t.clone(),
                    name,
                    apply_def(def, DataSource::SourceDeclaration),
                )],
                _ => vec![],
            }
        }
        _ => vec![],
    }
}

fn get_modifier_param_string(base: &Token, t: &Token) -> Vec<(Token, Token, String, DataType)> {
    get_modifier_param(&DefCtor::Str, base, t)
}

/// `getLiteralOfDataType`.
fn get_literal_of_data_type(
    base: &Token,
    t: &Token,
    d: DataType,
) -> Option<(Token, Token, String, DataType)> {
    let s = ast_lib::get_literal_string(t)?;
    if s.starts_with('-') {
        return None;
    }
    Some((base.clone(), t.clone(), s, d))
}

fn get_literal_c(base: &Token, t: &Token) -> Option<(Token, Token, String, DataType)> {
    get_literal_of_data_type(base, t, DataType::DataString(DataSource::SourceExternal))
}
fn get_literal_array_c(base: &Token, t: &Token) -> Option<(Token, Token, String, DataType)> {
    get_literal_of_data_type(base, t, DataType::DataArray(DataSource::SourceExternal))
}

fn let_param_to_literal(base: &Token, token: &Token) -> Vec<(Token, Token, String, DataType)> {
    let s = oversimplify_concat(token);
    let after_sign: String = s.chars().skip_while(|c| *c == '+' || *c == '-').collect();
    let var: String = after_sign
        .chars()
        .take_while(|c| is_variable_char(*c))
        .collect();
    if var.is_empty() {
        vec![]
    } else {
        vec![(
            base.clone(),
            token.clone(),
            var,
            DataType::DataString(DataSource::SourceFrom(vec![token.clone()])),
        )]
    }
}

fn get_set_params(tokens: &[Token]) -> Option<Vec<Token>> {
    if tokens.len() >= 2 && ast_lib::get_literal_string(&tokens[0]).as_deref() == Some("-o") {
        return get_set_params(&tokens[2..]);
    }
    let first = tokens.first()?;
    let rest = &tokens[1..];
    match ast_lib::get_literal_string(first) {
        Some(s) if s == "--" => Some(rest.to_vec()),
        Some(s) if s.starts_with('-') => get_set_params(rest),
        _ => {
            let mut out = vec![first.clone()];
            out.extend(get_set_params(rest).unwrap_or_default());
            Some(out)
        }
    }
}

fn get_flag_assigned_variable(
    base: &Token,
    flag_name: &str,
    source: DataSource,
    maybe_flags: Option<Vec<(String, (Token, Token))>>,
) -> Option<(Token, Token, String, DataType)> {
    let flags = maybe_flags?;
    let (_, (_flag, value)) = flags.iter().find(|(f, _)| f == flag_name)?;
    let variable_name = ast_lib::get_literal_string_ext(value, &|_| Some("!".to_string()))?;
    let base_name: String = variable_name.chars().take_while(|c| *c != '[').collect();
    let has_index = base_name.chars().count() != variable_name.chars().count();
    let dt = if has_index {
        DataType::DataArray(source)
    } else {
        DataType::DataString(source)
    };
    Some((base.clone(), value.clone(), base_name, dt))
}

fn get_mapfile_array(base: &Token, rest: &[Token]) -> Option<(Token, Token, String, DataType)> {
    let parse_args = || -> Option<(Token, Token, String, DataType)> {
        let args = cfg_get_gnu_opts("d:n:O:s:u:C:c:t", rest)?;
        let non_opts: Vec<&(String, (Token, Token))> =
            args.iter().filter(|(f, _)| f.is_empty()).collect();
        match non_opts.first() {
            None => Some((
                base.clone(),
                base.clone(),
                "MAPFILE".into(),
                DataType::DataArray(DataSource::SourceExternal),
            )),
            Some((_, (_, y))) => {
                let name = ast_lib::get_literal_string(y)?;
                if !is_variable_name(&name) {
                    return None;
                }
                Some((
                    base.clone(),
                    y.clone(),
                    name,
                    DataType::DataArray(DataSource::SourceExternal),
                ))
            }
        }
    };
    let fallback = || -> Option<(Token, Token, String, DataType)> {
        for tok in rest.iter().rev() {
            if let Some(name) = ast_lib::get_literal_string(tok)
                && is_variable_name(&name)
            {
                return Some((
                    base.clone(),
                    tok.clone(),
                    name,
                    DataType::DataArray(DataSource::SourceExternal),
                ));
            }
        }
        None
    };
    parse_args().or_else(fallback)
}

fn get_flag_variable(base: &Token, rest: &[Token]) -> Option<(Token, Token, String, DataType)> {
    if rest.len() >= 2 {
        let name = ast_lib::get_literal_string(&rest[0])?;
        Some((
            base.clone(),
            rest[0].clone(),
            format!("FLAGS_{name}"),
            DataType::DataString(DataSource::SourceExternal),
        ))
    } else {
        None
    }
}

/// The `x` of `T_NormalWord _ (T_Literal _ x:_)`: a word's leading literal.
fn leading_literal(word: &Token) -> Option<&str> {
    let InnerToken::T_NormalWord(parts) = &*word.inner else {
        return None;
    };
    match &*parts.first()?.inner {
        InnerToken::T_Literal(s) => Some(s),
        _ => None,
    }
}

/// `getPrintfVariable`.
fn get_printf_variable(base: &Token, rest: &[Token]) -> Option<(Token, Token, String, DataType)> {
    get_flag_assigned_variable(
        base,
        "v",
        DataSource::SourceFrom(rest.to_vec()),
        cfg_get_bsd_opts("v:", rest),
    )
}

/// `getWaitVariable`.
fn get_wait_variable(base: &Token, rest: &[Token]) -> Option<(Token, Token, String, DataType)> {
    get_flag_assigned_variable(
        base,
        "p",
        DataSource::SourceInteger,
        Some(cfg_get_generic_opts(rest)),
    )
}

/// `forDeclare`, with its `declaredVars`.
fn for_declare(
    base: &Token,
    rest: &[Token],
    has: &dyn Fn(&str) -> bool,
) -> Vec<(Token, Token, String, DataType)> {
    if has("F") || has("f") || has("p") {
        return vec![];
    }
    let def = if has("a") || has("A") {
        DefCtor::Arr
    } else {
        DefCtor::Str
    };
    rest.iter()
        .flat_map(|t| get_modifier_param(&def, base, t))
        .collect()
}

/// The `"read"` case of `getModifiedVariableCommand`.
fn get_read_variables(base: &Token, rest: &[Token]) -> Vec<(Token, Token, String, DataType)> {
    let fallback = || -> Vec<(Token, Token, String, DataType)> {
        let mut v = Vec::new();
        for tok in rest.iter().rev() {
            match get_literal_c(base, tok) {
                Some(a) => v.push(a),
                None => break,
            }
        }
        v
    };
    let Some(parsed) = cfg_get_gnu_opts("sreu:n:N:i:p:a:t:", rest) else {
        return fallback();
    };
    match parsed.iter().find(|(f, _)| f == "a") {
        // Haskell: `Just (_, var) -> (:[]) <$> getLiteralArray var`
        // inside `fromMaybe fallback $ do ...`. When getLiteralArray
        // is Nothing (non-literal, or `-`-prefixed such as the
        // bundled `-ar` in `read -ar foo`), the whole `do` is Nothing
        // and control falls back to the trailing-literal run.
        Some((_, (_, var))) => get_literal_array_c(base, var).map_or_else(fallback, |a| vec![a]),
        None => parsed
            .iter()
            .filter(|(f, _)| f.is_empty())
            .filter_map(|(_, (_, v))| get_literal_c(base, v))
            .collect(),
    }
}

/// `getModifiedVariableCommand` — `base` is the `T_SimpleCommand`, `words[0]` its name.
fn get_modified_variable_command(
    base: &Token,
    words: &[Token],
) -> Vec<(Token, Token, String, DataType)> {
    // first word's leading literal is the command name x
    let Some(x) = words.first().and_then(leading_literal) else {
        return vec![];
    };
    let rest = &words[1..];
    let flags = command_flag_strings(words);
    let has = |f: &str| flags.iter().any(|s| s == f);

    let result: Vec<(Token, Token, String, DataType)> = match x {
        "builtin" => return get_modified_variable_command(base, rest),
        "read" => get_read_variables(base, rest),
        "getopts" => {
            if rest.len() >= 2 {
                get_literal_c(base, &rest[1]).into_iter().collect()
            } else {
                vec![]
            }
        }
        "let" => rest
            .iter()
            .flat_map(|t| let_param_to_literal(base, t))
            .collect(),
        "export" => {
            if has("f") {
                vec![]
            } else {
                rest.iter()
                    .flat_map(|t| get_modifier_param_string(base, t))
                    .collect()
            }
        }
        "declare" | "typeset" => for_declare(base, rest, &has),
        "local" => rest
            .iter()
            .flat_map(|t| get_modifier_param_string(base, t))
            .collect(),
        "readonly" => {
            if has("f") || has("p") {
                vec![]
            } else {
                rest.iter()
                    .flat_map(|t| get_modifier_param_string(base, t))
                    .collect()
            }
        }
        "set" => get_set_params(rest)
            .map(|params| {
                (
                    base.clone(),
                    base.clone(),
                    "@".into(),
                    DataType::DataString(DataSource::SourceFrom(params)),
                )
            })
            .into_iter()
            .collect(),
        "printf" => get_printf_variable(base, rest).into_iter().collect(),
        "wait" => get_wait_variable(base, rest).into_iter().collect(),
        "mapfile" | "readarray" => get_mapfile_array(base, rest).into_iter().collect(),
        "DEFINE_boolean" | "DEFINE_float" | "DEFINE_integer" | "DEFINE_string" => {
            get_flag_variable(base, rest).into_iter().collect()
        }
        _ => vec![],
    };
    result
        .into_iter()
        .filter(|(_, _, s, _)| !s.starts_with('-'))
        .collect()
}

// ---- getReferencedVariables ------------------------------------------------

fn is_dereferencing_binary_op(op: &str) -> bool {
    matches!(op, "-eq" | "-ne" | "-lt" | "-le" | "-gt" | "-ge")
}

fn is_arithmetic_assignment(ctx: &FlowCtx, t: &Token) -> bool {
    ctx.parent(t).is_some_and(|p| match &*p.inner {
        InnerToken::TA_Assignment { op, lhs, .. } if op == "=" => lhs == t,
        _ => false,
    })
}

fn get_if_reference(context: &Token, token: &Token) -> Vec<(Token, Token, String)> {
    get_variable_for_test_dash_v(token)
        .map(|str| (context.clone(), token.clone(), get_braced_reference(&str)))
        .into_iter()
        .collect()
}

fn special_references(name: &str, base: &Token, word: &Token) -> Vec<(Token, Token, String)> {
    const PROMPTS: &[&str] = &["PS1", "PS2", "PS3", "PS4", "PROMPT_COMMAND"];
    if PROMPTS.contains(&name) {
        get_variables_from_literal_token(word)
            .into_iter()
            .map(|x| (base.clone(), base.clone(), x))
            .collect()
    } else {
        vec![]
    }
}

fn get_referenced_variables(ctx: &FlowCtx, t: &Token) -> Vec<(Token, Token, String)> {
    use InnerToken::{
        T_Assignment, T_BatsTest, T_DollarBraced, T_FdRedirect, TA_Variable, TC_Binary, TC_Unary,
    };
    match &*t.inner {
        T_DollarBraced { op, .. } => {
            let str = oversimplify_concat(op);
            let mut out = vec![(t.clone(), t.clone(), get_braced_reference(&str))];
            let l = op.clone();
            let mut idx = get_index_references(&str);
            idx.extend(get_offset_references(&get_braced_modifier(&str)));
            for x in idx {
                out.push((l.clone(), l.clone(), x));
            }
            out
        }
        TA_Variable { name, .. } => {
            if is_arithmetic_assignment(ctx, t) {
                vec![]
            } else {
                vec![(t.clone(), t.clone(), name.clone())]
            }
        }
        T_Assignment {
            mode, var, value, ..
        } => {
            let mut out = Vec::new();
            if *mode == AssignmentMode::Append {
                out.push((t.clone(), t.clone(), var.clone()));
            }
            out.extend(special_references(var, t, value));
            out
        }
        TC_Unary { op, token, .. } if op == "-v" || op == "-R" => get_if_reference(t, token),
        TC_Binary {
            typ: ConditionType::DoubleBracket,
            op,
            lhs,
            rhs,
        } => {
            if is_dereferencing_binary_op(op) {
                let mut out = get_if_reference(t, lhs);
                out.extend(get_if_reference(t, rhs));
                out
            } else {
                vec![]
            }
        }
        T_BatsTest { .. } => vec![
            (t.clone(), t.clone(), "lines".into()),
            (t.clone(), t.clone(), "status".into()),
            (t.clone(), t.clone(), "output".into()),
        ],
        T_FdRedirect { fd, target } if fd.starts_with('{') => {
            if is_closing_file_op(target) {
                let var: String = fd[1..].chars().take_while(|c| *c != '}').collect();
                vec![(t.clone(), t.clone(), var)]
            } else {
                vec![]
            }
        }
        _ => get_referenced_variable_command(t),
    }
}

fn get_reference(t: &Token) -> Vec<(Token, Token, String)> {
    match &*t.inner {
        InnerToken::T_Assignment { var, .. } => vec![(t.clone(), t.clone(), var.clone())],
        InnerToken::T_NormalWord(parts) => {
            // `T_NormalWord [T_Literal name]` where not "-"-prefixed.
            if parts.len() == 1
                && let InnerToken::T_Literal(name) = &*parts[0].inner
                && !name.starts_with('-')
            {
                return vec![(t.clone(), t.clone(), name.clone())];
            }
            vec![]
        }
        _ => vec![],
    }
}

/// `getReferencedVariableCommand`.
fn get_referenced_variable_command(base: &Token) -> Vec<(Token, Token, String)> {
    let words = match &*base.inner {
        InnerToken::T_SimpleCommand { words, .. } if !words.is_empty() => words,
        _ => return vec![],
    };
    let Some(x) = words.first().and_then(leading_literal) else {
        return vec![];
    };
    let rest = &words[1..];
    let flags = command_flag_strings(words);
    let has = |f: &str| flags.iter().any(|s| s == f);

    match x {
        "declare" | "typeset" => {
            if (has("x") || has("p")) && !(has("f") || has("F")) {
                rest.iter().flat_map(get_reference).collect()
            } else {
                vec![]
            }
        }
        "export" => {
            if has("f") {
                vec![]
            } else {
                rest.iter().flat_map(get_reference).collect()
            }
        }
        "local" => {
            if has("x") {
                rest.iter().flat_map(get_reference).collect()
            } else {
                vec![]
            }
        }
        "trap" => rest.first().map_or_else(Vec::new, |head| {
            get_variables_from_literal_token(head)
                .into_iter()
                .map(|v| (base.clone(), head.clone(), v))
                .collect()
        }),
        "alias" => rest
            .iter()
            .flat_map(|token| {
                get_variables_from_literal_token(token)
                    .into_iter()
                    .map(move |name| (base.clone(), token.clone(), name))
            })
            .collect(),
        _ => vec![],
    }
}

// ---- helpers consolidated from the check batches (ports of AnalyzerLib) ----

/// The words after the command name of a `T_SimpleCommand`.
pub(crate) fn arguments(t: &Token) -> &[Token] {
    match &*t.inner {
        InnerToken::T_SimpleCommand { words, .. } if !words.is_empty() => &words[1..],
        _ => &[],
    }
}

/// `getClosestCommand`: nearest enclosing `T_Redirecting` on the path, stopping
/// at the enclosing `T_Script`.
pub(crate) fn get_closest_command<'a>(params: &'a Parameters, t: &'a Token) -> Option<&'a Token> {
    // `findFirst findCommand $ getPath tree t`, walking the path by reference.
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

/// `isTrueAssignmentSource` from `ShellCheck.AnalyzerLib`.
pub(crate) const fn is_true_assignment_source(dt: &DataType) -> bool {
    !matches!(
        dt,
        DataType::DataString(DataSource::SourceChecked | DataSource::SourceDeclaration)
            | DataType::DataArray(DataSource::SourceChecked | DataSource::SourceDeclaration)
    )
}

/// `isUnqualifiedCommand token str` — exact command-name match.
pub(crate) fn is_unqualified_command(t: &Token, str: &str) -> bool {
    get_command_name(t).as_deref() == Some(str)
}

pub(crate) fn head_id(t: &Token) -> Id {
    match &*t.inner {
        InnerToken::T_NormalWord(list) if !list.is_empty() => list[0].id(),
        _ => t.id(),
    }
}

/// `isConfusedGlobRegex`.
pub(crate) fn is_confused_glob_regex(s: &str) -> bool {
    let chars: Vec<char> = s.chars().collect();
    if chars.first() == Some(&'*') {
        return true;
    }
    if chars.len() == 2 && chars[1] == '*' && chars[0] != '\\' && chars[0] != '.' {
        return true;
    }
    false
}

pub(crate) fn is_sourced(params: &Parameters, t: &Token) -> bool {
    path_iter(params, t).any(|p| matches!(&*p.inner, InnerToken::T_SourceCommand { .. }))
}

/// Condition-children of a parent node, per `isCondition`'s `getConditionChildren`.
pub(crate) fn condition_children(t: &Token) -> Vec<&Token> {
    match &*t.inner {
        InnerToken::T_AndIf { lhs, .. } | InnerToken::T_OrIf { lhs, .. } => vec![lhs],
        InnerToken::T_IfExpression { clauses, .. } => {
            // concatMap (take 1 . reverse . fst) conditions
            clauses.iter().filter_map(|(cond, _)| cond.last()).collect()
        }
        InnerToken::T_WhileExpression { condition, .. }
        | InnerToken::T_UntilExpression { condition, .. } => condition.last().into_iter().collect(),
        _ => vec![],
    }
}

/// `isCondition (getPath ..)`: walking from `t` up to the root, is each node a
/// condition-child of its parent (or is any node a bats test)?
pub(crate) fn in_condition(params: &Parameters, t: &Token) -> bool {
    let mut child = t;
    loop {
        // `go _ _ T_BatsTest{} = True`: any node examined that is a bats test.
        if matches!(&*child.inner, InnerToken::T_BatsTest { .. }) {
            return true;
        }
        let Some(parent) = params.parent(child) else {
            return false;
        };
        if condition_children(parent)
            .iter()
            .any(|c| c.id() == child.id())
        {
            return true;
        }
        child = parent;
    }
}

/// `isTestCommand`.
pub(crate) fn is_test_command(t: &Token) -> bool {
    use InnerToken::{T_Annotation, T_Condition, T_Pipeline, T_Redirecting, T_SimpleCommand};
    match &*t.inner {
        T_Condition { .. } => true,
        T_SimpleCommand { .. } => is_command(t, "test"),
        T_Redirecting { cmd, .. } => is_test_command(cmd),
        T_Annotation { token, .. } => is_test_command(token),
        T_Pipeline { commands, .. } if commands.len() == 1 => is_test_command(&commands[0]),
        _ => false,
    }
}

/// Is the immediate parent of `t` a `T_Function`?
pub(crate) fn is_function_body(params: &Parameters, t: &Token) -> bool {
    matches!(
        params.parent(t).map(|p| &*p.inner),
        Some(InnerToken::T_Function { .. })
    )
}

/// `getLeadingFlags`: flags in the BSD way, up until the first non-flag argument or `--`.
pub(crate) fn get_leading_flags(t: &Token) -> Vec<(&Token, String)> {
    get_flags_until(&|x| x == "--" || !x.starts_with('-'), t)
}

/// checkGrepRe's `f`: walk args to find the regex argument.
pub(crate) fn find_grep_regex(args: &[Token]) -> Option<&Token> {
    let mut rest = args;
    loop {
        let (x, tail) = rest.split_first()?;
        let s = ast_lib::get_literal_string_def("_", x);
        if s == "--" || s == "-e" || s == "--regex" {
            return tail.first(); // Regex is *after* this
        }
        // skippable: not "--regex=" prefix and starts with "-"
        if !s.starts_with("--regex=") && s.starts_with('-') {
            rest = tail; // Regex is elsewhere
        } else {
            return Some(x); // Regex is this
        }
    }
}

pub(crate) fn simple_command_words(t: &Token) -> Option<&Vec<Token>> {
    let cmd = get_command(t)?;
    if let InnerToken::T_SimpleCommand { words, .. } = &*cmd.inner {
        Some(words)
    } else {
        None
    }
}

#[cfg(test)]
mod set_option_tests {
    //! Unit tests for `contains_set_e` / `contains_noglob` / `is_option_set`,
    //! mirroring the semantics of AnalyzerLib.hs `containsSetE`,
    //! `containsNoglob` and `isOptionSet` (flag groups via `getAllFlags`, the
    //! `--` stop, the bare-word forms, and the shebang regexes).
    use super::*;

    fn root(script: &str) -> Token {
        crate::parser::parse_script("test", script)
            .root
            .expect("test script parses")
    }

    #[test]
    fn set_e_flag_forms() {
        for s in [
            "set -e",
            "set -ue",
            "set -xe",
            "set -eu",
            "set -o errexit",
            "set errexit",
        ] {
            assert!(contains_set_e(&root(s)), "{s}");
        }
    }

    #[test]
    fn set_e_shebang() {
        assert!(contains_set_e(&root("#!/bin/bash -e\ntrue")));
        assert!(contains_set_e(&root("#!/bin/bash -xe\ntrue")));
        assert!(!contains_set_e(&root("#!/bin/bash --posix\ntrue")));
        assert!(!contains_set_e(&root("#!/usr/bin/env bash\ntrue")));
    }

    #[test]
    fn set_e_negatives() {
        for s in [
            "true",
            "set -u",
            "set -- -e",
            "set --errexit",
            "echo set -e",
            "shopt -s errexit",
        ] {
            assert!(!contains_set_e(&root(s)), "{s}");
        }
    }

    #[test]
    fn noglob_forms() {
        for s in [
            "set -f",
            "set -xf",
            "set -o noglob",
            "set noglob",
            "#!/bin/sh -f\ntrue",
        ] {
            assert!(contains_noglob(&root(s)), "{s}");
        }
        for s in ["true", "set -- -f", "set -e", "echo set -f"] {
            assert!(!contains_noglob(&root(s)), "{s}");
        }
    }

    #[test]
    fn option_set_shopt_and_set_o() {
        assert!(is_option_set("lastpipe", &root("shopt -s lastpipe")));
        assert!(is_option_set("lastpipe", &root("shopt -- -s lastpipe")));
        assert!(is_option_set("pipefail", &root("set -o pipefail")));
        assert!(is_option_set("pipefail", &root("set -- -o pipefail")));
        assert!(is_option_set("pipefail", &root("shopt -s pipefail")));
        assert!(!is_option_set("pipefail", &root("true")));
        assert!(!is_option_set("lastpipe", &root("set -e")));
        assert!(!is_option_set("pipefail", &root("echo set -o pipefail")));
    }

    #[test]
    fn option_set_mirrors_oracle_dash_o_quirk() {
        // Haskell's containsSetOption is satisfied by any `set -o ...` for
        // every opt (`"o" elem map snd (getAllFlags t)`); mirrored on purpose.
        assert!(is_option_set("pipefail", &root("set -o vi")));
        assert!(!is_option_set("pipefail", &root("set -- -o vi")));
    }

    /// `hasExecfail` is a `Parameters` field upstream, computed once from the
    /// root — bash only. `checkSpuriousExec` reads it on every node, so it
    /// must not be recomputed per node.
    #[test]
    fn has_execfail_is_precomputed_and_bash_only() {
        let params = |script: &str| {
            let r = root(script);
            make_parameters(r, PositionMap::new(), None, None)
        };
        assert!(params("#!/bin/bash\nshopt -s execfail; exec foo; bar").has_execfail());
        assert!(!params("#!/bin/bash\nexec foo; bar").has_execfail());
        assert!(!params("#!/bin/dash\nshopt -s execfail; exec foo; bar").has_execfail());
        // And the value the check reads is the field, not a fresh tree walk.
        let p = params("#!/bin/bash\nshopt -s execfail; exec foo; bar");
        assert_eq!(p.has_execfail(), is_option_set("execfail", &p.root));
    }
}

#[cfg(test)]
#[allow(non_snake_case)]
mod printf_format_tests {
    use super::get_printf_formats;

    #[test]
    fn prop_checkGetPrintfFormats1() {
        assert_eq!(get_printf_formats("%s"), "s");
    }
    #[test]
    fn prop_checkGetPrintfFormats2() {
        assert_eq!(get_printf_formats("%0*s"), "*s");
    }
    #[test]
    fn prop_checkGetPrintfFormats3() {
        assert_eq!(get_printf_formats("%(%s)T"), "T");
    }
    #[test]
    fn prop_checkGetPrintfFormats4() {
        assert_eq!(get_printf_formats("%d%%%(%s)T"), "dT");
    }
    #[test]
    fn prop_checkGetPrintfFormats5() {
        assert_eq!(
            get_printf_formats("%bPassed: %d, %bFailed: %d%b, Skipped: %d, %bErrored: %d%b\\n"),
            "bdbdbdbdb"
        );
    }
    #[test]
    fn prop_checkGetPrintfFormats6() {
        assert_eq!(get_printf_formats("%s%s"), "ss");
    }
    #[test]
    fn prop_checkGetPrintfFormats7() {
        assert_eq!(get_printf_formats("%s\n%s"), "ss");
    }
    #[test]
    fn prop_checkGetPrintfFormats8() {
        assert_eq!(get_printf_formats("%ld"), "d");
    }
    #[test]
    fn prop_checkGetPrintfFormats9() {
        assert_eq!(get_printf_formats("%lld"), "d");
    }
    #[test]
    fn prop_checkGetPrintfFormats10() {
        assert_eq!(get_printf_formats("%Q"), "Q");
    }
}

#[cfg(test)]
#[allow(non_snake_case)]
mod tests {
    use super::{determine_shell, get_variables_from_literal};
    use crate::interface::Shell;

    #[test]
    fn filtered_and_generic_checks_keep_order_after_merge() {
        use super::{Checker, Out, Parameters, info, run_checker};
        use crate::ast::{InnerToken, Token};
        let params = crate::test_support::params_for("echo first second\n");
        let check = |code| {
            move |_: &Parameters, t: &Token, out: &mut Out| {
                info(out, t.id(), code, "order marker");
            }
        };
        let literal = |kind: &InnerToken| matches!(kind, InnerToken::T_Literal(..));
        let mut checker = Checker::new();
        checker.tree(check(0));
        checker.node(check(1));
        checker.node_for(literal, check(2));
        let mut other = Checker::new();
        other.node(check(3));
        other.node_for(literal, check(4));
        checker.merge(other);

        let mut expected = vec![(params.root.id(), 0)];
        params.root.visit_preorder(&mut |t| {
            expected.push((t.id(), 1));
            if literal(&t.inner) {
                expected.push((t.id(), 2));
            }
            expected.push((t.id(), 3));
            if literal(&t.inner) {
                expected.push((t.id(), 4));
            }
        });
        let actual: Vec<_> = run_checker(&params, &checker)
            .into_iter()
            .map(|comment| (comment.id, comment.comment.code))
            .collect();
        assert_eq!(actual, expected);
    }

    fn determine_shell_test_with(fallback: Option<Shell>, script: &str) -> Shell {
        let root = crate::parser::parse_script("script", script)
            .root
            .expect("test script parses");
        determine_shell(fallback, &root)
    }

    fn determine_shell_test(script: &str) -> Shell {
        determine_shell_test_with(None, script)
    }

    #[test]
    fn prop_determineShell0() {
        assert_eq!(determine_shell_test("#!/bin/sh"), Shell::Sh);
    }

    #[test]
    fn prop_determineShell1() {
        assert_eq!(determine_shell_test("#!/usr/bin/env ksh"), Shell::Ksh);
    }

    #[test]
    fn prop_determineShell2() {
        assert_eq!(determine_shell_test(""), Shell::Bash);
    }

    #[test]
    fn prop_determineShell3() {
        assert_eq!(determine_shell_test("#!/bin/sh -e"), Shell::Sh);
    }

    #[test]
    fn prop_determineShell4() {
        assert_eq!(
            determine_shell_test("#!/bin/ksh\n#shellcheck shell=sh\nfoo"),
            Shell::Sh
        );
    }

    #[test]
    fn prop_determineShell5() {
        assert_eq!(determine_shell_test("#shellcheck shell=sh\nfoo"), Shell::Sh);
    }

    #[test]
    fn prop_determineShell6() {
        assert_eq!(determine_shell_test("#! /bin/sh"), Shell::Sh);
    }

    #[test]
    fn prop_determineShell7() {
        assert_eq!(determine_shell_test("#! /bin/ash"), Shell::Dash);
    }

    #[test]
    fn prop_determineShell8() {
        assert_eq!(
            determine_shell_test_with(Some(Shell::Ksh), "#!/bin/sh"),
            Shell::Sh
        );
    }

    #[test]
    fn prop_determineShell9() {
        assert_eq!(determine_shell_test("#!/bin/env -S dash -x"), Shell::Dash);
    }

    #[test]
    fn prop_determineShell10() {
        assert_eq!(
            determine_shell_test("#!/bin/env --split-string= dash -x"),
            Shell::Dash
        );
    }

    #[test]
    fn prop_determineShell11() {
        assert_eq!(determine_shell_test("#!/bin/busybox sh"), Shell::BusyboxSh);
    }

    #[test]
    fn prop_determineShell12() {
        assert_eq!(determine_shell_test("#!/bin/busybox ash"), Shell::BusyboxSh);
    }

    #[test]
    fn prop_getVariablesFromLiteral1() {
        assert_eq!(
            get_variables_from_literal("$foo${bar//a/b}$BAZ"),
            ["foo", "bar", "BAZ"]
        );
    }
}

/// `hasFloatingPoint` (Analytics): only ksh does floating point in arithmetic.
pub(crate) fn has_floating_point(params: &Parameters) -> bool {
    params.shell == Shell::Ksh
}

/// `shouldIgnoreCode`.
pub(crate) fn should_ignore_code(params: &Parameters, code: i64, t: &Token) -> bool {
    path_iter(params, t).any(|p| is_annotation_ignoring_code(code, p))
}

/// `hasFlag`.
pub(crate) fn has_flag(t: &Token, flag: &str) -> bool {
    get_all_flags(t).iter().any(|(_, f)| f == flag)
}

/// `tokenIsJustCommandOutput` (AnalyzerLib): a word that is entirely the output
/// of a single command substitution.
pub(crate) fn token_is_just_command_output(t: &Token) -> bool {
    // check: exactly one command, and it isn't only a redirection.
    fn check(cmds: &[Token]) -> bool {
        cmds.len() == 1 && !ast_lib::is_only_redirection(&cmds[0])
    }
    if let InnerToken::T_NormalWord(parts) = &*t.inner
        && parts.len() == 1
    {
        match &*parts[0].inner {
            InnerToken::T_DollarExpansion(cmds) | InnerToken::T_Backticked(cmds) => {
                return check(cmds);
            }
            InnerToken::T_DoubleQuoted(inner) if inner.len() == 1 => match &*inner[0].inner {
                InnerToken::T_DollarExpansion(cmds) | InnerToken::T_Backticked(cmds) => {
                    return check(cmds);
                }
                _ => {}
            },
            _ => {}
        }
    }
    false
}
