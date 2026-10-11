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

/// Keep upstream check order while declaring the node kinds each check reads.
/// `_` retains generic dispatch for checks whose helpers accept several kinds.
macro_rules! node_checks {
    ($($check:path => $kind:pat),* $(,)?) => {
        fn register_node_checks(c: &mut Checker) {
            use crate::ast::InnerToken::*;
            $(c.node_for(|kind| matches!(kind, $kind), $check);)*
        }

        #[cfg(test)]
        const NODE_CHECKS: &[CheckPtr] = &[$($check),*];
    };
}

node_checks! {
    redirections::check_pipe_pitfalls => T_Pipeline { .. },
    loops::check_for_in_quoted => T_ForIn { .. },
    loops::check_for_in_ls => T_ForIn { .. },
    conditions::check_shorthand_if => T_OrIf { .. },
    quoting::check_dollar_star => T_NormalWord(..),
    quoting::check_unquoted_dollar_at => T_NormalWord(..),
    redirections::check_stderr_redirect => T_Redirecting { .. },
    quoting::check_unquoted_n => TC_Unary { .. },
    conditions::check_number_comparisons => TC_Binary { .. },
    conditions::check_single_bracket_operators => TC_Binary { .. },
    conditions::check_double_bracket_operators => TC_Binary { .. },
    conditions::check_literal_breaking_test => _,
    conditions::check_constant_nullary => TC_Nullary { .. },
    arithmetic::check_div_before_mult => TA_Binary { .. },
    arithmetic::check_arithmetic_deref => TA_Expansion(..),
    arithmetic::check_arithmetic_bad_octal => TA_Expansion(..),
    conditions::check_comparison_against_glob => TC_Binary { .. },
    conditions::check_case_against_glob => T_CaseExpression { .. },
    variables::check_commarrays => T_Array(..),
    conditions::check_or_neq => _,
    conditions::check_and_eq => _,
    redirections::check_echo_wc => T_Pipeline { .. },
    conditions::check_constant_ifs => TC_Binary { .. },
    redirections::check_piped_assignment => T_Pipeline { .. },
    commands::check_assign_ate_command => T_SimpleCommand { .. },
    commands::check_uuoe_var => T_Backticked(..) | T_DollarExpansion(..),
    conditions::check_quoted_cond_regex => TC_Binary { .. },
    loops::check_for_in_cat => T_ForIn { .. },
    commands::check_find_exec => _,
    conditions::check_valid_cond_ops => TC_Binary { .. } | TC_Unary { .. },
    conditions::check_globbed_regex => TC_Binary { .. },
    conditions::check_test_redirects => T_Redirecting { .. },
    variables::check_bad_parameter_substitution => T_DollarBraced { .. },
    variables::check_ps1_assignments => T_Assignment { .. },
    quoting::check_backticks => T_Backticked(..),
    quoting::check_inexplicably_unquoted => T_NormalWord(..),
    quoting::check_tilde_in_quotes => T_NormalWord(..),
    commands::check_lonely_dot_dash => T_Redirecting { .. },
    commands::check_spurious_exec => _,
    quoting::check_spurious_expansion => T_SimpleCommand { .. },
    variables::check_dollar_brackets => T_DollarBracket(..),
    redirections::check_ssh_here_doc => T_Redirecting { .. },
    commands::check_globs_as_options => T_SimpleCommand { .. },
    loops::check_while_read_pitfalls => T_WhileExpression { .. },
    arithmetic::check_arithmetic_op_command => T_SimpleCommand { .. },
    conditions::check_char_range_glob => T_Glob(..),
    quoting::check_unquoted_expansions => T_DollarExpansion(..) | T_Backticked(..) | T_DollarBraceCommandExpansion { .. },
    quoting::check_single_quoted_variables => T_SingleQuoted(..),
    redirections::check_redirect_to_same => T_Pipeline { .. },
    variables::check_prefix_assignment_reference => T_DollarBraced { .. },
    loops::check_loop_keyword_scope => _,
    commands::check_cd_and_back => _,
    arithmetic::check_wrong_arithmetic_assignment => T_SimpleCommand { .. },
    conditions::check_conditional_and_ors => TC_And { .. } | TC_Or { .. },
    script::check_function_declarations => T_Function { .. },
    redirections::check_stderr_pipe => T_Pipe(..),
    variables::check_overriding_path => T_SimpleCommand { .. },
    quoting::check_array_as_string => T_Assignment { .. },
    commands::check_unsupported => _,
    redirections::check_multiple_appends => _,
    variables::check_suspicious_ifs => T_Assignment { .. },
    redirections::check_should_use_grep_q => TC_Nullary { .. } | TC_Unary { .. },
    conditions::check_test_argument_splitting => _,
    quoting::check_concatenated_dollar_at => T_NormalWord(..),
    quoting::check_tilde_in_path => T_SimpleCommand { .. },
    loops::check_read_without_r => T_SimpleCommand { .. },
    commands::check_cp_legacy_r => T_SimpleCommand { .. },
    loops::check_loop_variable_reassignment => T_ForIn { .. } | T_ForArithmetic { .. },
    conditions::check_trailing_bracket => T_SimpleCommand { .. },
    conditions::check_return_against_zero => TC_Binary { .. } | TA_Binary { .. } | TA_Unary { .. } | TA_Sequence(..),
    redirections::check_redirected_nowhere => T_Pipeline { .. },
    conditions::check_unmatchable_cases => T_CaseExpression { .. },
    conditions::check_subshell_as_test => T_Subshell(..),
    quoting::check_splitting_in_arrays => T_Array(..),
    redirections::check_redirection_to_number => T_IoFile { .. },
    commands::check_glob_as_command => T_SimpleCommand { .. },
    commands::check_flag_as_command => T_SimpleCommand { .. },
    conditions::check_empty_condition => TC_Empty { .. },
    redirections::check_pipe_to_nowhere => _,
    loops::check_for_loop_glob_variables => T_ForIn { .. },
    conditions::check_subshelled_tests => T_Subshell(..),
    redirections::check_redirection_to_command => T_IoFile { .. },
    quoting::check_dollar_quote_paren => T_DollarDoubleQuoted(..),
    conditions::check_useless_bang => _,
    quoting::check_translated_string_variable => T_DollarDoubleQuoted(..),
    arithmetic::check_modified_arithmetic_in_redirection => T_Redirecting { .. },
    script::check_blatant_recursion => T_Function { .. },
    conditions::check_bad_test_and_or => T_Pipeline { .. } | T_Backgrounded(..),
    variables::check_assign_to_self => T_SimpleCommand { .. },
    commands::check_equals_in_command => T_SimpleCommand { .. },
    conditions::check_second_arg_is_comparison => T_SimpleCommand { .. },
    conditions::check_comparison_with_leading_x => TC_Binary { .. } | T_SimpleCommand { .. },
    commands::check_command_with_trailing_symbol => T_SimpleCommand { .. },
    quoting::check_unquoted_parameter_expansion_pattern => T_DollarBraced { .. },
    commands::check_bats_test_does_not_use_negation => T_BatsTest { .. },
    script::check_command_is_unreachable => _,
    flow::check_spacefulness_cfg => _,
    script::check_overwritten_exit_code => T_DollarBraced { .. },
    arithmetic::check_unnecessary_arithmetic_expansion_index => T_Assignment { .. },
    arithmetic::check_unnecessary_parens => _,
    arithmetic::check_plus_equals_number => T_Assignment { .. },
    redirections::check_expansion_with_redirection => T_DollarExpansion(..) | T_Backticked(..) | T_DollarBraceCommandExpansion { .. },
    conditions::check_unary_test_a => _,
}

/// Assemble the Analytics checks (and the command / dialect checkers) into one
/// `Checker`, mirroring `ShellCheck.Analyzer.analyzeScript`.
pub fn checker() -> Checker {
    let mut c = Checker::new();
    for &check in TREE_CHECKS {
        c.tree(check);
    }
    c.node(commands::check_unchecked_cd_pushd_popd);
    register_node_checks(&mut c);
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
#[cfg_attr(test, allow(clippy::missing_panics_doc))] // Test-only differential assertion.
pub fn analyze_with(params: &Parameters, optional: &[String]) -> Out {
    let mut c = checker();
    let all = optional.iter().any(|n| n == "all");
    for (name, register) in OPTIONAL_CHECKS {
        if all || optional.iter().any(|n| n == name) {
            register(&mut c);
        }
    }
    let result = run_checker(params, &c);
    #[cfg(test)]
    {
        // Compare with the original all-checks-on-all-nodes dispatcher for
        // every existing analytics test, including optional checks.
        let mut reference = Checker::new();
        for &check in TREE_CHECKS {
            reference.tree(check);
        }
        reference.node(commands::check_unchecked_cd_pushd_popd);
        for &check in NODE_CHECKS {
            reference.node(check);
        }
        crate::checks::register_all(&mut reference);
        for (name, register) in OPTIONAL_CHECKS {
            if all || optional.iter().any(|n| n == name) {
                register(&mut reference);
            }
        }
        assert_eq!(
            result,
            run_checker(params, &reference),
            "node-kind dispatch changed diagnostics"
        );
    }
    result
}
