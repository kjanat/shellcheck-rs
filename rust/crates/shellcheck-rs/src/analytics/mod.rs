//! Port of `ShellCheck.Analytics`: the SC2xxx node and tree checks, split by
//! theme. `checker` registers them in the order of the Haskell `treeChecks` /
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

/// Assemble the Analytics checks (and the command / dialect checkers) into one
/// `Checker`, mirroring `ShellCheck.Analyzer.analyzeScript`.
pub fn checker() -> Checker {
    let mut c = Checker::new();
    // treeChecks
    c.tree(variables::check_subshell_assignment);
    c.tree(quoting::check_quotes_in_literals);
    c.tree(script::check_shebang_parameters);
    c.tree(script::check_functions_used_externally);
    c.tree(flow::check_unused_assignments);
    c.tree(script::check_unpassed_in_functions);
    c.tree(variables::check_array_without_index);
    c.tree(script::check_shebang);
    c.tree(flow::check_unassigned_references);
    c.node(commands::check_unchecked_cd_pushd_popd);
    c.tree(variables::check_array_assignment_indices);
    c.tree(script::check_use_before_definition);
    c.tree(script::check_alias_used_in_same_parsing_unit);
    c.tree(variables::check_array_value_used_as_index);
    // nodeChecks
    c.node(redirections::check_pipe_pitfalls);
    c.node(loops::check_for_in_quoted);
    c.node(loops::check_for_in_ls);
    c.node(conditions::check_shorthand_if);
    c.node(quoting::check_dollar_star);
    c.node(quoting::check_unquoted_dollar_at);
    c.node(redirections::check_stderr_redirect);
    c.node(quoting::check_unquoted_n);
    c.node(conditions::check_number_comparisons);
    c.node(conditions::check_single_bracket_operators);
    c.node(conditions::check_double_bracket_operators);
    c.node(conditions::check_literal_breaking_test);
    c.node(conditions::check_constant_nullary);
    c.node(arithmetic::check_div_before_mult);
    c.node(arithmetic::check_arithmetic_deref);
    c.node(arithmetic::check_arithmetic_bad_octal);
    c.node(conditions::check_comparison_against_glob);
    c.node(conditions::check_case_against_glob);
    c.node(variables::check_commarrays);
    c.node(conditions::check_or_neq);
    c.node(conditions::check_and_eq);
    c.node(redirections::check_echo_wc);
    c.node(conditions::check_constant_ifs);
    c.node(redirections::check_piped_assignment);
    c.node(commands::check_assign_ate_command);
    c.node(commands::check_uuoe_var);
    c.node(conditions::check_quoted_cond_regex);
    c.node(loops::check_for_in_cat);
    c.node(commands::check_find_exec);
    c.node(conditions::check_valid_cond_ops);
    c.node(conditions::check_globbed_regex);
    c.node(conditions::check_test_redirects);
    c.node(variables::check_bad_parameter_substitution);
    c.node(variables::check_ps1_assignments);
    c.node(quoting::check_backticks);
    c.node(quoting::check_inexplicably_unquoted);
    c.node(quoting::check_tilde_in_quotes);
    c.node(commands::check_lonely_dot_dash);
    c.node(commands::check_spurious_exec);
    c.node(quoting::check_spurious_expansion);
    c.node(variables::check_dollar_brackets);
    c.node(redirections::check_ssh_here_doc);
    c.node(commands::check_globs_as_options);
    c.node(loops::check_while_read_pitfalls);
    c.node(arithmetic::check_arithmetic_op_command);
    c.node(conditions::check_char_range_glob);
    c.node(quoting::check_unquoted_expansions);
    c.node(quoting::check_single_quoted_variables);
    c.node(redirections::check_redirect_to_same);
    c.node(variables::check_prefix_assignment_reference);
    c.node(loops::check_loop_keyword_scope);
    c.node(commands::check_cd_and_back);
    c.node(arithmetic::check_wrong_arithmetic_assignment);
    c.node(conditions::check_conditional_and_ors);
    c.node(script::check_function_declarations);
    c.node(redirections::check_stderr_pipe);
    c.node(variables::check_overriding_path);
    c.node(quoting::check_array_as_string);
    c.node(commands::check_unsupported);
    c.node(redirections::check_multiple_appends);
    c.node(variables::check_suspicious_ifs);
    c.node(redirections::check_should_use_grep_q);
    c.node(conditions::check_test_argument_splitting);
    c.node(quoting::check_concatenated_dollar_at);
    c.node(quoting::check_tilde_in_path);
    c.node(loops::check_read_without_r);
    c.node(commands::check_cp_legacy_r);
    c.node(loops::check_loop_variable_reassignment);
    c.node(conditions::check_trailing_bracket);
    c.node(conditions::check_return_against_zero);
    c.node(redirections::check_redirected_nowhere);
    c.node(conditions::check_unmatchable_cases);
    c.node(conditions::check_subshell_as_test);
    c.node(quoting::check_splitting_in_arrays);
    c.node(redirections::check_redirection_to_number);
    c.node(commands::check_glob_as_command);
    c.node(commands::check_flag_as_command);
    c.node(conditions::check_empty_condition);
    c.node(redirections::check_pipe_to_nowhere);
    c.node(loops::check_for_loop_glob_variables);
    c.node(conditions::check_subshelled_tests);
    c.node(redirections::check_redirection_to_command);
    c.node(quoting::check_dollar_quote_paren);
    c.node(conditions::check_useless_bang);
    c.node(quoting::check_translated_string_variable);
    c.node(arithmetic::check_modified_arithmetic_in_redirection);
    c.node(script::check_blatant_recursion);
    c.node(conditions::check_bad_test_and_or);
    c.node(variables::check_assign_to_self);
    c.node(commands::check_equals_in_command);
    c.node(conditions::check_second_arg_is_comparison);
    c.node(conditions::check_comparison_with_leading_x);
    c.node(commands::check_command_with_trailing_symbol);
    c.node(quoting::check_unquoted_parameter_expansion_pattern);
    c.node(commands::check_bats_test_does_not_use_negation);
    c.node(script::check_command_is_unreachable);
    c.node(flow::check_spacefulness_cfg);
    c.node(script::check_overwritten_exit_code);
    c.node(arithmetic::check_unnecessary_arithmetic_expansion_index);
    c.node(arithmetic::check_unnecessary_parens);
    c.node(arithmetic::check_plus_equals_number);
    c.node(redirections::check_expansion_with_redirection);
    c.node(conditions::check_unary_test_a);
    // Not in Analytics.hs: SC1091 (source not followed) is a parser note in
    // Haskell, emitted while following `source`; it stays here until the
    // source resolver is ported.
    c.node(script::check_source_not_followed);
    crate::checks::register_all(&mut c);
    c
}

/// Run every check over a parsed script.
pub fn analyze(params: &Parameters) -> Out {
    analyze_with(params, &[])
}

/// `optionalTreeChecks` + `optionalCommandChecks`: checks that run only when
/// named, by `--enable` or an `enable=` directive. The names are upstream's
/// `cdName`s, which `--list-optional` prints.
type Register = fn(&mut Checker);
const OPTIONAL_CHECKS: &[(&str, Register)] = &[
    ("quote-safe-variables", |c| {
        c.node(flow::check_verbose_spacefulness_cfg)
    }),
    ("avoid-nullary-conditions", |c| {
        c.node(conditions::check_nullary_expansion_test)
    }),
    ("avoid-negated-conditions", |c| {
        c.node(conditions::check_unnecessarily_inverted_test)
    }),
    ("add-default-case", |c| c.node(loops::check_default_case)),
    ("require-variable-braces", |c| {
        c.node(quoting::check_variable_braces)
    }),
    ("check-unassigned-uppercase", |c| {
        c.tree(flow::check_unassigned_references_uppercase)
    }),
    ("require-double-brackets", |c| {
        c.tree(conditions::check_require_double_bracket)
    }),
    ("check-set-e-suppressed", |c| {
        c.tree(flow::check_set_e_suppressed)
    }),
    ("check-extra-masked-returns", |c| {
        c.tree(flow::check_extra_masked_returns)
    }),
    ("useless-use-of-cat", |c| c.node(redirections::check_uuoc)),
    ("deprecate-which", |c| {
        c.node(crate::checks::commands::coreutils::check_which())
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
