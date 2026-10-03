//! Port of `ShellCheck.Checks.Commands`: per-command checks, registered in the
//! order of the Haskell `commandChecks` list.
use std::collections::HashMap;

use crate::analyzer_lib::{Check, Checker, Out, Parameters};
use crate::ast::{InnerToken, Token};
use crate::ast_lib::{basename, get_literal_string, only_literal_string};
use crate::data::{DECLARING_COMMANDS, PRIVILEGE_ELEVATION_COMMANDS};

pub(crate) mod builtins;
pub(crate) mod common;
pub(crate) mod coreutils;
pub(crate) mod find;
pub(crate) mod sudo;

use CommandName::{Basename, Exactly};

/// `CommandName`: how a command check is keyed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum CommandName {
    Exactly(&'static str),
    Basename(&'static str),
}

/// The body of a command check: Haskell's `Token -> Analysis`, given the
/// effective command token.
type CommandBody = Box<dyn Fn(&Parameters, &Token, &mut Out)>;

/// `CommandCheck name f`: runs `f` on the effective command token whenever
/// `checkCommand` would dispatch a simple command to `name`.
pub(crate) struct CommandCheck {
    name: CommandName,
    f: CommandBody,
}

impl CommandCheck {
    pub(crate) fn new(
        name: CommandName,
        f: impl Fn(&Parameters, &Token, &mut Out) + 'static,
    ) -> CommandCheck {
        CommandCheck {
            name,
            f: Box::new(f),
        }
    }
}

impl Check for CommandCheck {
    fn run(&self, params: &Parameters, t: &Token, out: &mut Out) {
        let Some(route) = route(t) else { return };
        if self.name.matches(&route) {
            (self.f)(params, route.token(t), out);
        }
    }
}

impl CommandName {
    /// Whether a check keyed by `self` receives the command `route` describes.
    fn matches(self, route: &Route) -> bool {
        match self {
            Exactly(e) => route.exact && route.name == e,
            Basename(b) => route.base && route.name == b,
        }
    }
}

/// Where `checkCommand` sends a simple command: the one name it looks up and
/// which of the two key kinds (`Exactly`, `Basename`) it looks it up under.
struct Route {
    name: String,
    exact: bool,
    base: bool,
    /// For `builtin x ..`: the command with the `builtin` word dropped.
    rewritten: Option<Token>,
}

impl Route {
    /// The token the check bodies receive: `t`, or its `builtin`-less rewrite.
    fn token<'a>(&'a self, t: &'a Token) -> &'a Token {
        self.rewritten.as_ref().unwrap_or(t)
    }
}

/// `checkCommand`: the routing of the simple command `t`, if it has a literal
/// command name. A `/path/cmd` dispatches only to `Basename cmd`;
/// `builtin x ..` dispatches only to `Exactly x`, with the command rewritten to
/// drop the `builtin` word; any other literal name dispatches to both
/// `Exactly name` and `Basename name`.
fn route(t: &Token) -> Option<Route> {
    let InnerToken::T_SimpleCommand { assignments, words } = &*t.inner else {
        return None;
    };
    let literal = get_literal_string(words.first()?)?;
    if literal.contains('/') {
        return Some(Route {
            name: basename(&literal),
            exact: false,
            base: true,
            rewritten: None,
        });
    }
    if literal == "builtin" && words.len() >= 2 {
        return Some(Route {
            name: only_literal_string(&words[1]),
            exact: true,
            base: false,
            rewritten: Some(Token::new(
                t.id(),
                InnerToken::T_SimpleCommand {
                    assignments: assignments.clone(),
                    words: words[1..].to_vec(),
                },
            )),
        });
    }
    Some(Route {
        name: literal,
        exact: true,
        base: true,
        rewritten: None,
    })
}

/// `buildCommandMap` + `checkCommand`: every command check, in one node check
/// that looks the simple command up once instead of every check re-deriving
/// the command name for every node. A name maps to its checks in registration
/// order (the order the checks ran in when each was a node check of its own),
/// whether they are keyed `Exactly` or `Basename`.
#[derive(Default)]
pub(crate) struct CommandTable {
    by_name: HashMap<&'static str, Vec<CommandCheck>>,
}

impl CommandTable {
    pub(crate) fn add(&mut self, check: CommandCheck) {
        let (Exactly(n) | Basename(n)) = check.name;
        self.by_name.entry(n).or_default().push(check);
    }
}

impl Check for CommandTable {
    fn run(&self, params: &Parameters, t: &Token, out: &mut Out) {
        let Some(route) = route(t) else { return };
        let Some(checks) = self.by_name.get(route.name.as_str()) else {
            return;
        };
        let te = route.token(t);
        for c in checks {
            if c.name.matches(&route) {
                (c.f)(params, te, out);
            }
        }
    }
}

/// Every command check, in the order of the Haskell `commandChecks` list.
fn all_checks() -> Vec<CommandCheck> {
    let mut checks = vec![
        coreutils::check_tr(),
        find::check_find_name_glob(),
        coreutils::check_expr(),
        coreutils::check_grep_re(),
        builtins::check_trap_quotes(),
        builtins::check_return(),
        builtins::check_exit(),
        find::check_find_exec_with_single_argument(),
        coreutils::check_unused_echo_escapes(),
        find::check_injectable_find_sh(),
        find::check_find_action_precedence(),
        coreutils::check_mkdir_dash_pm(),
        builtins::check_nonportable_signals(),
        coreutils::check_interactive_su(),
        coreutils::check_ssh_command_string(),
        builtins::check_printf_var(),
        coreutils::check_uuoe_cmd(),
        builtins::check_set_assignment(),
        builtins::check_exported_expansions(),
        builtins::check_aliases_uses_args(),
        builtins::check_aliases_expand_early(),
        builtins::check_unset_globs(),
        find::check_find_without_path(),
        coreutils::check_time_parameters(),
        coreutils::check_timed_command(),
        builtins::check_local_scope(),
        coreutils::check_deprecated_tempfile(),
        coreutils::check_deprecated_egrep(),
        coreutils::check_deprecated_fgrep(),
        builtins::check_while_getopts_case(),
        coreutils::check_catastrophic_rm(),
        builtins::check_let_usage(),
        coreutils::check_mv_arguments(),
        coreutils::check_cp_arguments(),
        coreutils::check_ln_arguments(),
        find::check_find_redirections(),
        builtins::check_read_expansions(),
        builtins::check_source_args(),
        coreutils::check_chmod_dashr(),
        coreutils::check_xargs_dashi(),
        coreutils::check_unquoted_echo_spaces(),
        builtins::check_eval_array(),
        coreutils::check_grep_sends_pipefail(),
        coreutils::check_egrep_sends_pipefail(),
        coreutils::check_fgrep_sends_pipefail(),
    ];
    // ++ map checkArgComparison ("alias" : declaringCommands)
    for cmd in ["alias"]
        .into_iter()
        .chain(DECLARING_COMMANDS.iter().copied())
    {
        checks.push(builtins::check_arg_comparison(cmd));
    }
    // ++ map checkMaskedReturns declaringCommands
    for cmd in DECLARING_COMMANDS.iter().copied() {
        checks.push(builtins::check_masked_returns(cmd));
    }
    // ++ map checkMultipleDeclaring declaringCommands
    for cmd in DECLARING_COMMANDS.iter().copied() {
        checks.push(builtins::check_multiple_declaring(cmd));
    }
    // ++ map checkBackreferencingDeclaration declaringCommands
    for cmd in DECLARING_COMMANDS.iter().copied() {
        checks.push(builtins::check_backreferencing_declaration(cmd));
    }
    // ++ map checkSudoArgs privilegeElevationCommands
    for cmd in PRIVILEGE_ELEVATION_COMMANDS.iter().copied() {
        checks.push(sudo::check_sudo_args(cmd));
    }
    // ++ map checkSudoRedirect privilegeElevationCommands
    for cmd in PRIVILEGE_ELEVATION_COMMANDS.iter().copied() {
        checks.push(sudo::check_sudo_redirect(cmd));
    }
    checks
}

pub fn register(c: &mut Checker) {
    let mut table = CommandTable::default();
    for check in all_checks() {
        table.add(check);
    }
    c.node(table);
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::analyzer_lib::{Out, style};
    use crate::test_support::collect;

    /// One check per entry of `all_checks`, each a node check of its own and
    /// running its own `dispatch`: how the checks were registered before the
    /// table.
    struct Separately(Vec<CommandCheck>);

    impl Check for Separately {
        fn run(&self, params: &Parameters, t: &Token, out: &mut Out) {
            for c in &self.0 {
                c.run(params, t, out);
            }
        }
    }

    fn emitting(name: CommandName, code: i64) -> CommandCheck {
        CommandCheck::new(name, move |_, t, out| style(out, t.id(), code, "x"))
    }

    fn sequence(table: CommandTable, script: &str) -> Vec<i64> {
        collect(table, script)
            .iter()
            .map(|c| c.comment.code)
            .collect()
    }

    fn table(checks: Vec<CommandCheck>) -> CommandTable {
        let mut t = CommandTable::default();
        for c in checks {
            t.add(c);
        }
        t
    }

    #[test]
    fn checks_on_one_name_run_in_registration_order() {
        // `Exactly` and `Basename` on one name interleave as registered, and a
        // check on another name does not run.
        let checks = || {
            vec![
                emitting(Basename("foo"), 1),
                emitting(Exactly("bar"), 9),
                emitting(Exactly("foo"), 2),
                emitting(Basename("foo"), 3),
            ]
        };
        assert_eq!(sequence(table(checks()), "foo a"), [1, 2, 3]);
        assert_eq!(sequence(table(checks()), "/usr/bin/foo a"), [1, 3]);
        assert_eq!(sequence(table(checks()), "builtin foo a"), [2]);
        assert_eq!(sequence(table(checks()), "builtin /bin/foo a"), []);
        assert_eq!(sequence(table(checks()), "FOO=1 foo"), [1, 2, 3]);
        assert_eq!(sequence(table(checks()), "$foo a"), []);
        assert_eq!(sequence(table(checks()), "foobar"), []);
    }

    #[test]
    fn table_agrees_with_separate_checks() {
        let scripts = [
            "export a=$a b",
            "local x=1; declare y=$x z=$y",
            "builtin export a=$a b",
            "/bin/export a",
            "sudo -u root ls > f",
            "builtin sudo ls",
            "/usr/bin/sudo cmd >> f",
            "find . -name *.c -exec rm {} ;",
            "builtin return 5; return 1; exit 300",
            "tr a-z A-Z; /usr/bin/tr a-z A-Z; builtin tr a b",
            "echo $(tempfile) | egrep x; fgrep y",
            "let x=1; read $x; unset a*; trap 'a' SIG",
            "alias a=b; alias c='echo $1'; mv a; cp a; ln a",
            "builtin; builtin builtin trap 'x' INT; builtin $x return",
            "rm -rf /; chmod -R 777 /; xargs -i echo; time -p ls; ssh h 'x'",
        ];
        let mut emitted = 0;
        for s in scripts {
            let mut t = CommandTable::default();
            for c in all_checks() {
                t.add(c);
            }
            let a = collect(t, s);
            let b = collect(Separately(all_checks()), s);
            let key = |o: &Out| {
                o.iter()
                    .map(|c| (c.id, c.comment.code, c.comment.message.clone()))
                    .collect::<Vec<_>>()
            };
            assert_eq!(key(&a), key(&b), "{s}");
            emitted += a.len();
        }
        assert!(emitted > 10, "the scripts must exercise the checks");
    }
}
