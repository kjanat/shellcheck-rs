//! Port of `ShellCheck.Checks.Commands`: per-command checks, registered in the
//! order of the Haskell `commandChecks` list.
use crate::analyzer_lib::Checker;

pub(crate) mod builtins;
pub(crate) mod common;
pub(crate) mod coreutils;
pub(crate) mod find;
pub(crate) mod sudo;

pub fn register(c: &mut Checker) {
    c.node(coreutils::check_tr);
    c.node(find::check_find_name_glob);
    c.node(coreutils::check_expr);
    c.node(coreutils::check_grep_re);
    c.node(builtins::check_trap_quotes);
    c.node(builtins::check_return);
    c.node(builtins::check_exit);
    c.node(find::check_find_exec_with_single_argument);
    c.node(coreutils::check_unused_echo_escapes);
    c.node(find::check_injectable_find_sh);
    c.node(find::check_find_action_precedence);
    c.node(coreutils::check_mkdir_dash_pm);
    c.node(builtins::check_nonportable_signals);
    c.node(coreutils::check_interactive_su);
    c.node(coreutils::check_ssh_command_string);
    c.node(builtins::check_printf_var);
    c.node(coreutils::check_uuoe_cmd);
    c.node(builtins::check_set_assignment);
    c.node(builtins::check_exported_expansions);
    c.node(builtins::check_aliases_uses_args);
    c.node(builtins::check_aliases_expand_early);
    c.node(builtins::check_unset_globs);
    c.node(find::check_find_without_path);
    c.node(coreutils::check_time_parameters);
    c.node(coreutils::check_timed_command);
    c.node(builtins::check_local_scope);
    c.node(coreutils::check_deprecated_tempfile);
    c.node(coreutils::check_deprecated_egrep);
    c.node(coreutils::check_deprecated_fgrep);
    c.node(builtins::check_while_getopts_case);
    c.node(coreutils::check_catastrophic_rm);
    c.node(builtins::check_let_usage);
    c.node(coreutils::check_mv_arguments);
    c.node(coreutils::check_cp_arguments);
    c.node(coreutils::check_ln_arguments);
    c.node(find::check_find_redirections);
    c.node(builtins::check_read_expansions);
    c.node(builtins::check_source_args);
    c.node(coreutils::check_chmod_dashr);
    c.node(coreutils::check_xargs_dashi);
    c.node(coreutils::check_unquoted_echo_spaces);
    c.node(builtins::check_eval_array);
    // ++ map checkArgComparison ("alias" : declaringCommands), etc.
    c.node(builtins::check_arg_comparison);
    c.node(builtins::check_masked_returns);
    c.node(builtins::check_multiple_declaring);
    c.node(builtins::check_backreferencing_declaration);
    c.node(sudo::check_sudo_args);
    c.node(sudo::check_sudo_redirect);
}
