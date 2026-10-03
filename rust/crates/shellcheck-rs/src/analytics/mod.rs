//! Port of `ShellCheck.Analytics`: the SC2xxx node and tree checks, split by
//! theme.
//!
//! `checker` registers them in the order of the Haskell `treeChecks` /
//! `nodeChecks` lists (a check missing from the port would show up here as a
//! `not ported` line, generated from those lists).
use crate::analyzer_lib::{Checker, Out, Parameters, run_checker};

pub(crate) mod arithmetic;
pub(crate) mod commands;
pub(crate) mod common;
pub(crate) mod conditions;
pub(crate) mod flow;
pub(crate) mod loops;
pub(crate) mod quoting;
pub(crate) mod redirections;
pub(crate) mod script;
pub(crate) mod variables;

/// A check function, as the `treeChecks` and `nodeChecks` lists hold them.
type CheckPtr = fn(&Parameters, &crate::ast::Token, &mut Out);

/// `treeChecks`, less `checkUncheckedCdPushdPopd`, which `checker` runs as a node check.
const TREE_CHECKS: &[CheckPtr] = &[
    variables::check_subshell_assignment,
    quoting::check_quotes_in_literals,
    script::check_shebang_parameters,
    script::check_functions_used_externally,
    flow::check_unused_assignments,
    script::check_unpassed_in_functions,
    variables::check_array_without_index,
    script::check_shebang,
    flow::check_unassigned_references,
    variables::check_array_assignment_indices,
    script::check_use_before_definition,
    script::check_alias_used_in_same_parsing_unit,
    variables::check_array_value_used_as_index,
];

/// `nodeChecks`.
const NODE_CHECKS: &[CheckPtr] = &[
    redirections::check_pipe_pitfalls,
    loops::check_for_in_quoted,
    loops::check_for_in_ls,
    conditions::check_shorthand_if,
    quoting::check_dollar_star,
    quoting::check_unquoted_dollar_at,
    redirections::check_stderr_redirect,
    quoting::check_unquoted_n,
    conditions::check_number_comparisons,
    conditions::check_single_bracket_operators,
    conditions::check_double_bracket_operators,
    conditions::check_literal_breaking_test,
    conditions::check_constant_nullary,
    arithmetic::check_div_before_mult,
    arithmetic::check_arithmetic_deref,
    arithmetic::check_arithmetic_bad_octal,
    conditions::check_comparison_against_glob,
    conditions::check_case_against_glob,
    variables::check_commarrays,
    conditions::check_or_neq,
    conditions::check_and_eq,
    redirections::check_echo_wc,
    conditions::check_constant_ifs,
    redirections::check_piped_assignment,
    commands::check_assign_ate_command,
    commands::check_uuoe_var,
    conditions::check_quoted_cond_regex,
    loops::check_for_in_cat,
    commands::check_find_exec,
    conditions::check_valid_cond_ops,
    conditions::check_globbed_regex,
    conditions::check_test_redirects,
    variables::check_bad_parameter_substitution,
    variables::check_ps1_assignments,
    quoting::check_backticks,
    quoting::check_inexplicably_unquoted,
    quoting::check_tilde_in_quotes,
    commands::check_lonely_dot_dash,
    commands::check_spurious_exec,
    quoting::check_spurious_expansion,
    variables::check_dollar_brackets,
    redirections::check_ssh_here_doc,
    commands::check_globs_as_options,
    loops::check_while_read_pitfalls,
    arithmetic::check_arithmetic_op_command,
    conditions::check_char_range_glob,
    quoting::check_unquoted_expansions,
    quoting::check_single_quoted_variables,
    redirections::check_redirect_to_same,
    variables::check_prefix_assignment_reference,
    loops::check_loop_keyword_scope,
    commands::check_cd_and_back,
    arithmetic::check_wrong_arithmetic_assignment,
    conditions::check_conditional_and_ors,
    script::check_function_declarations,
    redirections::check_stderr_pipe,
    variables::check_overriding_path,
    quoting::check_array_as_string,
    commands::check_unsupported,
    redirections::check_multiple_appends,
    variables::check_suspicious_ifs,
    redirections::check_should_use_grep_q,
    conditions::check_test_argument_splitting,
    quoting::check_concatenated_dollar_at,
    quoting::check_tilde_in_path,
    loops::check_read_without_r,
    commands::check_cp_legacy_r,
    loops::check_loop_variable_reassignment,
    conditions::check_trailing_bracket,
    conditions::check_return_against_zero,
    redirections::check_redirected_nowhere,
    conditions::check_unmatchable_cases,
    conditions::check_subshell_as_test,
    quoting::check_splitting_in_arrays,
    redirections::check_redirection_to_number,
    commands::check_glob_as_command,
    commands::check_flag_as_command,
    conditions::check_empty_condition,
    redirections::check_pipe_to_nowhere,
    loops::check_for_loop_glob_variables,
    conditions::check_subshelled_tests,
    redirections::check_redirection_to_command,
    quoting::check_dollar_quote_paren,
    conditions::check_useless_bang,
    quoting::check_translated_string_variable,
    arithmetic::check_modified_arithmetic_in_redirection,
    script::check_blatant_recursion,
    conditions::check_bad_test_and_or,
    variables::check_assign_to_self,
    commands::check_equals_in_command,
    conditions::check_second_arg_is_comparison,
    conditions::check_comparison_with_leading_x,
    commands::check_command_with_trailing_symbol,
    quoting::check_unquoted_parameter_expansion_pattern,
    commands::check_bats_test_does_not_use_negation,
    script::check_command_is_unreachable,
    flow::check_spacefulness_cfg,
    script::check_overwritten_exit_code,
    arithmetic::check_unnecessary_arithmetic_expansion_index,
    arithmetic::check_unnecessary_parens,
    arithmetic::check_plus_equals_number,
    redirections::check_expansion_with_redirection,
    conditions::check_unary_test_a,
];

/// Assemble the Analytics checks (and the command / dialect checkers) into one
/// `Checker`, mirroring `ShellCheck.Analyzer.analyzeScript`.
pub fn checker() -> Checker {
    let mut c = Checker::new();
    for &check in TREE_CHECKS {
        c.tree(check);
    }
    c.node(commands::check_unchecked_cd_pushd_popd);
    for &check in NODE_CHECKS {
        c.node(check);
    }
    crate::checks::register_all(&mut c);
    c
}

/// Run every check over a parsed script.
#[must_use]
pub fn analyze(params: &Parameters) -> Out {
    analyze_with(params, &[])
}

/// `optionalTreeChecks` + `optionalCommandChecks`: checks that run only when
/// named, by `--enable` or an `enable=` directive. The names are upstream's
/// `cdName`s, which `--list-optional` prints.
type Register = fn(&mut Checker);
const OPTIONAL_CHECKS: &[(&str, Register)] = &[
    ("quote-safe-variables", |c| {
        c.node(flow::check_verbose_spacefulness_cfg);
    }),
    ("avoid-nullary-conditions", |c| {
        c.node(conditions::check_nullary_expansion_test);
    }),
    ("avoid-negated-conditions", |c| {
        c.node(conditions::check_unnecessarily_inverted_test);
    }),
    ("add-default-case", |c| c.node(loops::check_default_case)),
    ("require-variable-braces", |c| {
        c.node(quoting::check_variable_braces);
    }),
    ("check-unassigned-uppercase", |c| {
        c.tree(flow::check_unassigned_references_uppercase);
    }),
    ("require-double-brackets", |c| {
        c.tree(conditions::check_require_double_bracket);
    }),
    ("require-double-equals", |c| {
        c.tree(conditions::check_require_double_equals);
    }),
    ("check-set-e-suppressed", |c| {
        c.tree(flow::check_set_e_suppressed);
    }),
    ("check-extra-masked-returns", |c| {
        c.tree(flow::check_extra_masked_returns);
    }),
    ("useless-use-of-cat", |c| c.node(redirections::check_uuoc)),
    ("deprecate-which", |c| {
        c.node(crate::checks::commands::coreutils::check_which());
    }),
];

/// Run every check, plus the optional ones named in `optional`.
///
/// `mkChecker`'s `optionals`: `"all"` turns on every one, and any other name is
/// looked up and silently dropped when unknown, as its `mapMaybe` does.
pub fn analyze_with(params: &Parameters, optional: &[String]) -> Out {
    let mut c = checker();
    let all = optional.iter().any(|n| n == "all");
    for (name, register) in OPTIONAL_CHECKS {
        if all || optional.iter().any(|n| n == name) {
            register(&mut c);
        }
    }
    run_checker(params, &c)
}
