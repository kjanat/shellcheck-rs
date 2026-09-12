//! Port of `ShellCheck.Checks.Commands`: per-command checks, registered in the
//! order of the Haskell `commandChecks` list.
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
        if let Some(te) = dispatch(t, self.name) {
            (self.f)(params, &te, out);
        }
    }
}

/// `checkCommand`: the token a check registered under `name` receives for the
/// simple command `t`, if any. A `/path/cmd` dispatches only to
/// `Basename cmd`; `builtin x ..` dispatches only to `Exactly x`, with the
/// command rewritten to drop the `builtin` word; any other literal name
/// dispatches to both `Exactly name` and `Basename name`.
fn dispatch(t: &Token, name: CommandName) -> Option<Token> {
    let InnerToken::T_SimpleCommand { assignments, words } = &*t.inner else {
        return None;
    };
    let literal = get_literal_string(words.first()?)?;
    if literal.contains('/') {
        return match name {
            Basename(b) if basename(&literal) == b => Some(t.clone()),
            _ => None,
        };
    }
    if literal == "builtin" && words.len() >= 2 {
        let selected = only_literal_string(&words[1]);
        return match name {
            Exactly(e) if selected == e => Some(Token::new(
                t.id(),
                InnerToken::T_SimpleCommand {
                    assignments: assignments.clone(),
                    words: words[1..].to_vec(),
                },
            )),
            _ => None,
        };
    }
    match name {
        Exactly(e) | Basename(e) if literal == e => Some(t.clone()),
        _ => None,
    }
}

pub fn register(c: &mut Checker) {
    c.node(coreutils::check_tr());
    c.node(find::check_find_name_glob());
    c.node(coreutils::check_expr());
    c.node(coreutils::check_grep_re());
    c.node(builtins::check_trap_quotes());
    c.node(builtins::check_return());
    c.node(builtins::check_exit());
    c.node(find::check_find_exec_with_single_argument());
    c.node(coreutils::check_unused_echo_escapes());
    c.node(find::check_injectable_find_sh());
    c.node(find::check_find_action_precedence());
    c.node(coreutils::check_mkdir_dash_pm());
    c.node(builtins::check_nonportable_signals());
    c.node(coreutils::check_interactive_su());
    c.node(coreutils::check_ssh_command_string());
    c.node(builtins::check_printf_var());
    c.node(coreutils::check_uuoe_cmd());
    c.node(builtins::check_set_assignment());
    c.node(builtins::check_exported_expansions());
    c.node(builtins::check_aliases_uses_args());
    c.node(builtins::check_aliases_expand_early());
    c.node(builtins::check_unset_globs());
    c.node(find::check_find_without_path());
    c.node(coreutils::check_time_parameters());
    c.node(coreutils::check_timed_command());
    c.node(builtins::check_local_scope());
    c.node(coreutils::check_deprecated_tempfile());
    c.node(coreutils::check_deprecated_egrep());
    c.node(coreutils::check_deprecated_fgrep());
    c.node(builtins::check_while_getopts_case());
    c.node(coreutils::check_catastrophic_rm());
    c.node(builtins::check_let_usage());
    c.node(coreutils::check_mv_arguments());
    c.node(coreutils::check_cp_arguments());
    c.node(coreutils::check_ln_arguments());
    c.node(find::check_find_redirections());
    c.node(builtins::check_read_expansions());
    c.node(builtins::check_source_args());
    c.node(coreutils::check_chmod_dashr());
    c.node(coreutils::check_xargs_dashi());
    c.node(coreutils::check_unquoted_echo_spaces());
    c.node(builtins::check_eval_array());
    // ++ map checkArgComparison ("alias" : declaringCommands)
    for cmd in ["alias"]
        .into_iter()
        .chain(DECLARING_COMMANDS.iter().copied())
    {
        c.node(builtins::check_arg_comparison(cmd));
    }
    // ++ map checkMaskedReturns declaringCommands
    for cmd in DECLARING_COMMANDS.iter().copied() {
        c.node(builtins::check_masked_returns(cmd));
    }
    // ++ map checkMultipleDeclaring declaringCommands
    for cmd in DECLARING_COMMANDS.iter().copied() {
        c.node(builtins::check_multiple_declaring(cmd));
    }
    // ++ map checkBackreferencingDeclaration declaringCommands
    for cmd in DECLARING_COMMANDS.iter().copied() {
        c.node(builtins::check_backreferencing_declaration(cmd));
    }
    // ++ map checkSudoArgs privilegeElevationCommands
    for cmd in PRIVILEGE_ELEVATION_COMMANDS.iter().copied() {
        c.node(sudo::check_sudo_args(cmd));
    }
    // ++ map checkSudoRedirect privilegeElevationCommands
    for cmd in PRIVILEGE_ELEVATION_COMMANDS.iter().copied() {
        c.node(sudo::check_sudo_redirect(cmd));
    }
}
