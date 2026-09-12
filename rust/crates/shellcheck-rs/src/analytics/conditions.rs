//! `[ ]` / `[[ ]]` / `case` condition checks from `ShellCheck.Analytics`.
use crate::analyzer_lib::get_closest_command;
use crate::analyzer_lib::get_command_basename;
use crate::analyzer_lib::get_command_name;
use crate::analyzer_lib::head_id;
use crate::analyzer_lib::in_condition;
use crate::analyzer_lib::is_command;
use crate::analyzer_lib::is_confused_glob_regex;
use crate::analyzer_lib::is_function_body;
use crate::analyzer_lib::is_test_command;
use crate::analyzer_lib::*;
use crate::ast::*;
use crate::ast_lib;
use crate::ast_lib::get_leading_unquoted_string;
use crate::ast_lib::get_literal_string;
use crate::ast_lib::get_literal_string_def;
use crate::ast_lib::get_word_parts;
use crate::ast_lib::is_assignment;
use crate::ast_lib::is_constant;
use crate::ast_lib::is_glob;
use crate::ast_lib::is_literal;
use crate::ast_lib::is_quoteable_expansion;
use crate::ast_lib::is_quotes;
use crate::ast_lib::oversimplify;
use crate::cfg::{get_braced_reference, is_variable_name};
use crate::cfg_analysis::NumericalStatus;
use crate::data::ARITHMETIC_BINARY_TEST_OPS;
use crate::interface::Replacement;
use crate::interface::Shell;

pub(super) fn check_shorthand_if(params: &Parameters, x: &Token, out: &mut Out) {
    // x@(T_OrIf _ (T_AndIf id _ b) (T_Pipeline _ _ t))
    let (or_lhs, or_rhs) = match &*x.inner {
        InnerToken::T_OrIf { lhs, rhs } => (lhs, rhs),
        _ => return,
    };
    let (and_id, b) = match &*or_lhs.inner {
        InnerToken::T_AndIf { rhs, .. } => (or_lhs.id(), rhs),
        _ => return,
    };
    let commands = match &*or_rhs.inner {
        InnerToken::T_Pipeline { commands, .. } => commands,
        _ => return,
    };

    // isOk [t] = isAssignment t || basename in [echo, exit, return, printf, true, :]
    let is_ok = if commands.len() == 1 {
        let cmd = &commands[0];
        is_assignment(cmd)
            || get_command_basename(cmd)
                .map(|name| {
                    matches!(
                        name.as_str(),
                        "echo" | "exit" | "return" | "printf" | "true" | ":"
                    )
                })
                .unwrap_or(false)
    } else {
        false
    };

    if !(is_ok || in_condition(params, x)) && !is_test_command(b) {
        info(
            out,
            and_id,
            2015,
            "Note that A && B || C is not if-then-else. C may run when A is true.",
        );
    }
}

pub(super) fn check_number_comparisons(params: &Parameters, t: &Token, out: &mut Out) {
    let InnerToken::TC_Binary { typ, op, lhs, rhs } = &*t.inner else {
        return;
    };
    let typ = *typ;
    let op = op.as_str();
    let id = t.id();
    let has_string_comparison = params.shell != Shell::Sh;

    if is_num(params, lhs) || is_num(params, rhs) {
        if is_lt_gt(op) {
            err(
                out,
                id,
                2071,
                &format!("{} is for string comparisons. Use {} instead.", op, eqv(op)),
            );
        }
        if is_le_ge(op) && has_string_comparison {
            err(
                out,
                id,
                2071,
                &format!("{} is not a valid operator. Use {} .", op, eqv(op)),
            );
        }
    } else {
        if is_le_ge(op) || is_lt_gt(op) {
            check_decimals(params, lhs, out);
            check_decimals(params, rhs, out);
        }

        if is_le_ge(op) && has_string_comparison {
            err(
                out,
                id,
                2122,
                &format!(
                    "{} is not a valid operator. Use '! a {}{} b' instead.",
                    op,
                    esc(typ),
                    invert_comparison(op)
                ),
            );
        }

        if typ == ConditionType::SingleBracket && (op == "<" || op == ">") {
            match params.shell {
                Shell::Sh => {} // Unsupported; caught by bashism checks.
                Shell::Dash | Shell::BusyboxSh => err(
                    out,
                    id,
                    2073,
                    &format!("Escape \\{} to prevent it redirecting.", op),
                ),
                _ => err(
                    out,
                    id,
                    2073,
                    &format!(
                        "Escape \\{} to prevent it redirecting (or switch to [[ .. ]]).",
                        op
                    ),
                ),
            }
        }
    }

    if ARITHMETIC_BINARY_TEST_OPS.contains(&op) {
        check_decimals(params, lhs, out);
        check_decimals(params, rhs, out);
        let assigned = assigned_variables(params);
        check_string(params, typ, op, lhs, &assigned, out);
        check_string(params, typ, op, rhs, &assigned, out);
    }
}

/// SC2074 — `checkSingleBracketOperators`.
pub(super) fn check_single_bracket_operators(params: &Parameters, t: &Token, out: &mut Out) {
    if let InnerToken::TC_Binary {
        typ: ConditionType::SingleBracket,
        op,
        ..
    } = &*t.inner
    {
        if op == "=~" && matches!(params.shell, Shell::Bash | Shell::Ksh) {
            err(
                out,
                t.id(),
                2074,
                "Can't use =~ in [ ]. Use [[..]] instead.",
            );
        }
    }
}

/// SC2075 — `checkDoubleBracketOperators`.
pub(super) fn check_double_bracket_operators(_params: &Parameters, t: &Token, out: &mut Out) {
    if let InnerToken::TC_Binary {
        typ: ConditionType::DoubleBracket,
        op,
        ..
    } = &*t.inner
    {
        if op == "\\<" || op == "\\>" {
            err(
                out,
                t.id(),
                2075,
                &format!("Escaping {} is required in [..], but invalid in [[..]]", op),
            );
        }
    }
}

/// SC2077 / SC2157 — `checkLiteralBreakingTest`.
pub(super) fn check_literal_breaking_test(_params: &Parameters, t: &Token, out: &mut Out) {
    let has_equals = |x: &Token| ast_lib::get_literal_string(x).is_some_and(|s| s.contains('='));
    let is_nonempty = |x: &Token| ast_lib::get_literal_string(x).is_some_and(|s| !s.is_empty());

    match &*t.inner {
        InnerToken::TC_Nullary { token: w, .. } => {
            if let InnerToken::T_NormalWord(l) = &*w.inner {
                // Constant nullaries are covered by SC2078.
                if is_constant(w) {
                    return;
                }
                // comparisonWarning `mplus` tautologyWarning: first that fires.
                if let Some(tok) = l.iter().find(|x| has_equals(x)) {
                    err(
                        out,
                        tok.id(),
                        2077,
                        "You need spaces around the comparison operator.",
                    );
                } else if let Some(tok) = get_word_parts(w).into_iter().find(|x| is_nonempty(x)) {
                    err(
                        out,
                        tok.id(),
                        2157,
                        "Argument to implicit -n is always true due to literal strings.",
                    );
                }
            }
        }
        InnerToken::TC_Unary { op, token: w, .. } => {
            if matches!(&*w.inner, InnerToken::T_NormalWord(_)) {
                let msg = match op.as_str() {
                    "-n" => Some("Argument to -n is always true due to literal strings."),
                    "-z" => Some("Argument to -z is always false due to literal strings."),
                    _ => None,
                };
                if let Some(msg) = msg {
                    if let Some(tok) = get_word_parts(w).into_iter().find(|x| is_nonempty(x)) {
                        err(out, tok.id(), 2157, msg);
                    }
                }
            }
        }
        _ => {}
    }
}

/// SC2158/2159/2160/2161/2078 — `checkConstantNullary`.
pub(super) fn check_constant_nullary(_params: &Parameters, t: &Token, out: &mut Out) {
    if let InnerToken::TC_Nullary { token, .. } = &*t.inner {
        if is_constant(token) {
            match ast_lib::only_literal_string(token).as_str() {
                "false" => err(
                    out,
                    token.id(),
                    2158,
                    "[ false ] is true. Remove the brackets.",
                ),
                "0" => err(out, token.id(), 2159, "[ 0 ] is true. Use 'false' instead."),
                "true" => style(
                    out,
                    token.id(),
                    2160,
                    "Instead of '[ true ]', just use 'true'.",
                ),
                "1" => style(out, token.id(), 2161, "Instead of '[ 1 ]', use 'true'."),
                _ => err(
                    out,
                    token.id(),
                    2078,
                    "This expression is constant. Did you forget a $ somewhere?",
                ),
            }
        }
    }
}

/// SC2053 / SC2081 / SC2330 — `checkComparisonAgainstGlob`.
pub(super) fn check_comparison_against_glob(params: &Parameters, t: &Token, out: &mut Out) {
    use ConditionType::*;
    use InnerToken::*;
    if let TC_Binary { typ, op, rhs, .. } = &*t.inner {
        let op_is_eq = matches!(op.as_str(), "=" | "==" | "!=");
        // Clause 1: [[ x == $unquoted ]] where rhs is a lone T_DollarBraced word.
        if *typ == DoubleBracket && op_is_eq {
            if let T_NormalWord(parts) = &*rhs.inner {
                if parts.len() == 1 && matches!(&*parts[0].inner, T_DollarBraced { .. }) {
                    warn(
                        out,
                        rhs.id(),
                        2053,
                        &format!(
                            "Quote the right-hand side of {} in [[ ]] to prevent glob matching.",
                            op
                        ),
                    );
                    return;
                }
            }
        }
        // Clause 2: [ x = glob ]
        if *typ == SingleBracket && op_is_eq && is_glob(rhs) {
            let msg = if matches!(params.shell, Shell::Bash | Shell::Ksh) {
                "[ .. ] can't match globs. Use [[ .. ]] or case statement."
            } else {
                "[ .. ] can't match globs. Use a case statement."
            };
            err(out, rhs.id(), 2081, msg);
            return;
        }
        // Clause 3: BusyBox [[ x == glob ]]
        if *typ == DoubleBracket && params.shell == Shell::BusyboxSh && op_is_eq && is_glob(rhs) {
            err(
                out,
                rhs.id(),
                2330,
                "BusyBox [[ .. ]] does not support glob matching. Use a case statement.",
            );
        }
    }
}

/// SC2254 — `checkCaseAgainstGlob`.
pub(super) fn check_case_against_glob(_params: &Parameters, t: &Token, out: &mut Out) {
    if let InnerToken::T_CaseExpression { cases, .. } = &*t.inner {
        for (_, patterns, _) in cases {
            for expr in patterns {
                if let InnerToken::T_NormalWord(list) = &*expr.inner {
                    if !is_glob(expr) && list.iter().any(is_quoteable_expansion) {
                        warn(
                            out,
                            expr.id(),
                            2254,
                            "Quote expansions in case patterns to match literally rather than as a glob.",
                        );
                    }
                }
            }
        }
    }
}

/// SC2055 / SC2056 / SC2252 — `checkOrNeq`.
pub(super) fn check_or_neq(_params: &Parameters, t: &Token, out: &mut Out) {
    use InnerToken::*;
    match &*t.inner {
        // Test-level "or": [ x != y -o x != z ]
        TC_Or { typ, lhs, rhs, .. } => {
            if let (
                TC_Binary {
                    op: op1,
                    lhs: lhs1,
                    rhs: rhs1,
                    ..
                },
                TC_Binary {
                    op: op2,
                    lhs: lhs2,
                    rhs: rhs2,
                    ..
                },
            ) = (&*lhs.inner, &*rhs.inner)
            {
                if op1 == op2
                    && (op1 == "-ne" || op1 == "!=")
                    && lhs1 == lhs2
                    && rhs1 != rhs2
                    && !is_glob(rhs1)
                    && !is_glob(rhs2)
                {
                    let conj = if *typ == ConditionType::SingleBracket {
                        "-a"
                    } else {
                        "&&"
                    };
                    warn(
                        out,
                        t.id(),
                        2055,
                        &format!(
                            "You probably wanted {} here, otherwise it's always true.",
                            conj
                        ),
                    );
                }
            }
        }
        // Arithmetic "or"
        TA_Binary { op, lhs, rhs } if op == "||" => {
            if let (
                TA_Binary {
                    op: o1, lhs: w1, ..
                },
                TA_Binary {
                    op: o2, lhs: w2, ..
                },
            ) = (&*lhs.inner, &*rhs.inner)
            {
                if o1 == "!=" && o2 == "!=" && w1 == w2 {
                    warn(
                        out,
                        t.id(),
                        2056,
                        "You probably wanted && here, otherwise it's always true.",
                    );
                }
            }
        }
        // Command-level "or": [ x != y ] || [ x != z ]
        T_OrIf { lhs, rhs } => {
            if let (Some((lhs1, op1, rhs1)), Some((lhs2, op2, rhs2))) =
                (or_get_expr(lhs), or_get_expr(rhs))
            {
                if op1 == op2
                    && (op1 == "-ne" || op1 == "!=")
                    && lhs1 == lhs2
                    && rhs1 != rhs2
                    && !is_glob(&rhs1)
                    && !is_glob(&rhs2)
                {
                    warn(
                        out,
                        t.id(),
                        2252,
                        "You probably wanted && here, otherwise it's always true.",
                    );
                }
            }
        }
        _ => {}
    }
}

/// SC2333 / SC2334 — `checkAndEq`.
pub(super) fn check_and_eq(_params: &Parameters, t: &Token, out: &mut Out) {
    use InnerToken::*;
    match &*t.inner {
        // Test-level "and": [ x = y -a x = z ]
        TC_And { typ, lhs, rhs, .. } => {
            if let (
                TC_Binary {
                    op: op1,
                    lhs: lhs1,
                    rhs: rhs1,
                    ..
                },
                TC_Binary {
                    op: op2,
                    lhs: lhs2,
                    rhs: rhs2,
                    ..
                },
            ) = (&*lhs.inner, &*rhs.inner)
            {
                if op1 == op2
                    && lhs1 == lhs2
                    && rhs1 != rhs2
                    && check_and_eq_operands(op1, rhs1, rhs2)
                {
                    let conj = if *typ == ConditionType::SingleBracket {
                        "-o"
                    } else {
                        "||"
                    };
                    warn(
                        out,
                        t.id(),
                        2333,
                        &format!(
                            "You probably wanted {} here, otherwise it's always false.",
                            conj
                        ),
                    );
                }
            }
        }
        // Arithmetic "and"
        TA_Binary { op, lhs, rhs } if op == "&&" => {
            if let (
                TA_Binary {
                    op: o1,
                    lhs: lhs1,
                    rhs: rhs1,
                },
                TA_Binary {
                    op: o2,
                    lhs: lhs2,
                    rhs: rhs2,
                },
            ) = (&*lhs.inner, &*rhs.inner)
            {
                if o1 == "=="
                    && o2 == "=="
                    && lhs1 == lhs2
                    && is_literal_number(rhs1)
                    && is_literal_number(rhs2)
                {
                    warn(
                        out,
                        t.id(),
                        2334,
                        "You probably wanted || here, otherwise it's always false.",
                    );
                }
            }
        }
        // Command-level "and": [ x = y ] && [ x = z ]
        T_AndIf { lhs, rhs } => {
            if let (Some((lhs1, op1, rhs1)), Some((lhs2, op2, rhs2))) =
                (cmd_level_get_expr(lhs), cmd_level_get_expr(rhs))
            {
                if op1 == op2
                    && lhs1 == lhs2
                    && rhs1 != rhs2
                    && check_and_eq_operands(&op1, &rhs1, &rhs2)
                {
                    warn(
                        out,
                        t.id(),
                        2333,
                        "You probably wanted || here, otherwise it's always false.",
                    );
                }
            }
        }
        _ => {}
    }
}

/// SC2050 / SC2193 — `checkConstantIfs`.
pub(super) fn check_constant_ifs(_params: &Parameters, t: &Token, out: &mut Out) {
    if let InnerToken::TC_Binary { typ, op, lhs, rhs } = &*t.inner {
        let is_dynamic = (ARITHMETIC_BINARY_TEST_OPS.contains(&op.as_str())
            && *typ == ConditionType::DoubleBracket)
            || matches!(op.as_str(), "-nt" | "-ot" | "-ef");
        if is_dynamic {
            return;
        }
        if is_constant(lhs) && is_constant(rhs) {
            warn(
                out,
                t.id(),
                2050,
                "This expression is constant. Did you forget the $ on a variable?",
            );
        } else if matches!(op.as_str(), "=" | "==" | "!=") && !words_can_be_equal(lhs, rhs) {
            warn(
                out,
                t.id(),
                2193,
                "The arguments to this comparison can never be equal. Make sure your syntax is correct.",
            );
        }
    }
}

pub(super) fn check_quoted_cond_regex(_params: &Parameters, t: &Token, out: &mut Out) {
    let rhs = match &*t.inner {
        InnerToken::TC_Binary { op, rhs, .. } if op == "=~" => rhs,
        _ => return,
    };
    let is_quoted = match &*rhs.inner {
        InnerToken::T_NormalWord(parts) if parts.len() == 1 => matches!(
            &*parts[0].inner,
            InnerToken::T_DoubleQuoted(_) | InnerToken::T_SingleQuoted(_)
        ),
        _ => false,
    };
    if is_quoted && !is_constant_non_re(rhs) {
        warn(
            out,
            rhs.id(),
            2076,
            "Remove quotes from right-hand side of =~ to match as a regex rather than literally.",
        );
    }
}

/// SC2057 / SC2058 — `checkValidCondOps`.
pub(super) fn check_valid_cond_ops(_params: &Parameters, t: &Token, out: &mut Out) {
    match &*t.inner {
        InnerToken::TC_Binary { op, .. } if !BINARY_TEST_OPS.contains(&op.as_str()) => {
            warn(out, t.id(), 2057, "Unknown binary operator.");
        }
        InnerToken::TC_Unary { op, .. } if !UNARY_TEST_OPS.contains(&op.as_str()) => {
            warn(out, t.id(), 2058, "Unknown unary operator.");
        }
        _ => {}
    }
}

/// SC2049 — `checkGlobbedRegex`.
pub(super) fn check_globbed_regex(_params: &Parameters, t: &Token, out: &mut Out) {
    if let InnerToken::TC_Binary {
        typ: ConditionType::DoubleBracket,
        op,
        rhs,
        ..
    } = &*t.inner
    {
        if op == "=~" {
            let s = oversimplify(rhs).concat();
            if is_confused_glob_regex(&s) {
                warn(
                    out,
                    rhs.id(),
                    2049,
                    "=~ is for regex, but this looks like a glob. Use = instead.",
                );
            }
        }
    }
}

pub(super) fn check_test_redirects(_params: &Parameters, t: &Token, out: &mut Out) {
    let (redirs, cmd) = match &*t.inner {
        InnerToken::T_Redirecting { redirs, cmd } => (redirs, cmd),
        _ => return,
    };
    if !crate::analyzer_lib::is_command(cmd, "test") {
        return;
    }
    for r in redirs {
        if redirect_is_suspicious(r) {
            warn(
                out,
                r.id(),
                2065,
                "This is interpreted as a shell file redirection, not a comparison.",
            );
        }
    }
}

/// SC2101 / SC2102 — `checkCharRangeGlob`.
pub(super) fn check_char_range_glob(params: &Parameters, t: &Token, out: &mut Out) {
    if let InnerToken::T_Glob(str) = &*t.inner {
        if !(str.starts_with('[') && str.ends_with(']')) {
            return;
        }
        // Parser-gap guard: the shared parser reads bracketed words containing
        // spaces (e.g. the argument `[ foo ]` in `run [ foo ]`) as a single
        // T_Glob "[ foo ]". The oracle's parser never produces a glob char-class
        // with an unquoted space there (it tokenizes `[`, `foo`, `]` as separate
        // words), so such a glob is a Rust-parser artifact. Skipping it matches
        // oracle behaviour on every input the oracle would turn into a glob and
        // avoids a spurious SC2102.
        if str.contains(' ') {
            return;
        }
        if is_ignored_command(params, t) || is_dereferenced(params, t) {
            return;
        }
        // contents = dropNegation . drop 1 . take (len-1)
        let chars: Vec<char> = str.chars().collect();
        let inner: String = chars[1..chars.len() - 1].iter().collect();
        let contents = drop_negation(&inner);

        if contents.starts_with(':') && contents.ends_with(':') && contents != ":" {
            warn(
                out,
                t.id(),
                2101,
                "Named class needs outer [], e.g. [[:digit:]].",
            );
        } else if !contents.contains('[') && has_dupes(&contents) {
            info(
                out,
                t.id(),
                2102,
                "Ranges can only match single chars (mentioned due to duplicates).",
            );
        }
    }
}

/// SC2107/2108/2109/2110/2166 — `checkConditionalAndOrs`.
pub(super) fn check_conditional_and_ors(_params: &Parameters, t: &Token, out: &mut Out) {
    use ConditionType::*;
    use InnerToken::*;
    match &*t.inner {
        TC_And {
            typ: SingleBracket,
            op,
            ..
        } if op == "&&" => {
            err(
                out,
                t.id(),
                2107,
                "Instead of [ a && b ], use [ a ] && [ b ].",
            );
        }
        TC_And {
            typ: DoubleBracket,
            op,
            ..
        } if op == "-a" => {
            err(out, t.id(), 2108, "In [[..]], use && instead of -a.");
        }
        TC_Or {
            typ: SingleBracket,
            op,
            ..
        } if op == "||" => {
            err(
                out,
                t.id(),
                2109,
                "Instead of [ a || b ], use [ a ] || [ b ].",
            );
        }
        TC_Or {
            typ: DoubleBracket,
            op,
            ..
        } if op == "-o" => {
            err(out, t.id(), 2110, "In [[..]], use || instead of -o.");
        }
        TC_And {
            typ: SingleBracket,
            op,
            ..
        } if op == "-a" => {
            warn(
                out,
                t.id(),
                2166,
                "Prefer [ p ] && [ q ] as [ p -a q ] is not well defined.",
            );
        }
        TC_Or {
            typ: SingleBracket,
            op,
            ..
        } if op == "-o" => {
            warn(
                out,
                t.id(),
                2166,
                "Prefer [ p ] || [ q ] as [ p -o q ] is not well defined.",
            );
        }
        _ => {}
    }
}

pub(super) fn check_test_argument_splitting(params: &Parameters, t: &Token, out: &mut Out) {
    match &*t.inner {
        InnerToken::TC_Unary { typ, op, token } if is_glob(token) => {
            if op == "-v" {
                if *typ == ConditionType::SingleBracket {
                    err(
                        out,
                        token.id(),
                        2208,
                        "Use [[ ]] or quote arguments to -v to avoid glob expansion.",
                    );
                }
            } else if *typ == ConditionType::SingleBracket && params.shell == Shell::Ksh {
                // Ksh appears to stop processing after unrecognized tokens.
                let ksh_ops: Vec<String> = "bcdfgkprsuwxLhNOGRS"
                    .chars()
                    .map(|c| format!("-{}", c))
                    .collect();
                if ksh_ops.iter().any(|o| o == op) {
                    warn(
                        out,
                        token.id(),
                        2245,
                        &format!(
                            "{} only applies to the first expansion of this glob. Use a loop to check any/all.",
                            op
                        ),
                    );
                }
            } else {
                err(
                    out,
                    token.id(),
                    2144,
                    &format!("{} doesn't work with globs. Use a for loop.", op),
                );
            }
        }
        InnerToken::TC_Nullary { typ, token } => {
            tas_check_braces(params, *typ, token, out);
            tas_check_globs(params, *typ, token, out);
            if *typ == ConditionType::DoubleBracket {
                tas_check_arrays(params, *typ, token, out);
            }
        }
        InnerToken::TC_Unary { typ, token, .. } => {
            tas_check_all(params, *typ, token, out);
        }
        InnerToken::TC_Binary { typ, op, lhs, rhs }
            if ARITHMETIC_BINARY_TEST_OPS.contains(&op.as_str()) =>
        {
            if *typ == ConditionType::DoubleBracket {
                for c in [lhs, rhs] {
                    tas_check_arrays(params, *typ, c, out);
                    tas_check_braces(params, *typ, c, out);
                }
            } else {
                for c in [lhs, rhs] {
                    tas_check_numerical_glob(params, c, out);
                    tas_check_arrays(params, *typ, c, out);
                    tas_check_braces(params, *typ, c, out);
                }
            }
        }
        InnerToken::TC_Binary { typ, op, lhs, rhs } => {
            if matches!(op.as_str(), "=" | "==" | "!=" | "=~") {
                tas_check_all(params, *typ, lhs, out);
                tas_check_arrays(params, *typ, rhs, out);
                tas_check_braces(params, *typ, rhs, out);
            } else {
                tas_check_all(params, *typ, lhs, out);
                tas_check_all(params, *typ, rhs, out);
            }
        }
        _ => {}
    }
}

/// SC2171 — `checkTrailingBracket`.
pub(super) fn check_trailing_bracket(_params: &Parameters, t: &Token, out: &mut Out) {
    if let InnerToken::T_SimpleCommand { words, .. } = &*t.inner {
        if let Some(last) = words.last() {
            trailing_check(last, t, out);
        }
    }
}

pub(super) fn check_return_against_zero(params: &Parameters, t: &Token, out: &mut Out) {
    use InnerToken::*;
    match &*t.inner {
        TC_Binary { op, lhs, rhs, .. } => rz_check(params, t, op, lhs, rhs, out),
        TA_Binary { op, lhs, rhs }
            if matches!(op.as_str(), ">" | "<" | ">=" | "<=" | "==" | "!=") =>
        {
            rz_check(params, t, op, lhs, rhs, out)
        }
        TA_Unary { op, operand } if op == "!" && is_exit_code(operand) => {
            rz_message(params, t, checks_success_lhs("!"), operand.id(), out)
        }
        TA_Sequence(v) if v.len() == 1 && is_exit_code(&v[0]) => {
            rz_message(params, t, false, v[0].id(), out)
        }
        _ => {}
    }
}

/// SC2194 / SC2195 / SC2221 / SC2222 — `checkUnmatchableCases`.
pub(super) fn check_unmatchable_cases(params: &Parameters, t: &Token, out: &mut Out) {
    if let InnerToken::T_CaseExpression { word, cases } = &*t.inner {
        // all patterns
        let all_patterns: Vec<&Token> = cases.iter().flat_map(|(_, ps, _)| ps.iter()).collect();
        // only CaseBreak branches for shadowing
        let break_patterns: Vec<&Token> = cases
            .iter()
            .filter(|(ct, _, _)| *ct == CaseType::CaseBreak)
            .flat_map(|(_, ps, _)| ps.iter())
            .collect();

        if is_constant(word) {
            warn(
                out,
                word.id(),
                2194,
                "This word is constant. Did you forget the $ on a variable?",
            );
        } else {
            let target = word_to_pseudo_glob(word);
            for candidate in &all_patterns {
                if !pseudo_globs_can_overlap(&target, &word_to_pseudo_glob(candidate)) {
                    warn(
                        out,
                        candidate.id(),
                        2195,
                        "This pattern will never match the case statement's word. Double check them.",
                    );
                }
            }
        }

        // dominators = zip exactGlobs (tails (drop 1 fuzzyGlobs))
        let exact_globs: Vec<(&Token, Option<Vec<PseudoGlob>>)> = break_patterns
            .iter()
            .map(|p| (*p, word_to_exact_pseudo_glob(p)))
            .collect();
        let fuzzy_globs: Vec<(&Token, Vec<PseudoGlob>)> = break_patterns
            .iter()
            .map(|p| (*p, word_to_pseudo_glob(p)))
            .collect();

        for (i, (glob_tok, exact)) in exact_globs.iter().enumerate() {
            if let Some(x) = exact {
                // rest = fuzzy_globs[i+1 ..]
                let rest = &fuzzy_globs[(i + 1).min(fuzzy_globs.len())..];
                if let Some((first_tok, _)) =
                    rest.iter().find(|(_, p)| pseudo_glob_is_superset_of(x, p))
                {
                    warn(
                        out,
                        glob_tok.id(),
                        2221,
                        &format!(
                            "This pattern always overrides a later one{}",
                            pattern_context(params, first_tok.id())
                        ),
                    );
                    warn(
                        out,
                        first_tok.id(),
                        2222,
                        &format!(
                            "This pattern never matches because of a previous pattern{}",
                            pattern_context(params, glob_tok.id())
                        ),
                    );
                }
            }
        }
    }
}

/// SC2204 / SC2205 — `checkSubshellAsTest`.
pub(super) fn check_subshell_as_test(_params: &Parameters, t: &Token, out: &mut Out) {
    if let InnerToken::T_Subshell(list) = &*t.inner {
        if list.len() == 1 {
            subshell_check(t.id(), &list[0], out);
        }
    }
}

/// SC2212 — `checkEmptyCondition`.
pub(super) fn check_empty_condition(_params: &Parameters, t: &Token, out: &mut Out) {
    if let InnerToken::TC_Empty { .. } = &*t.inner {
        style(
            out,
            t.id(),
            2212,
            "Use 'false' instead of empty [/[[ conditionals.",
        );
    }
}

pub(super) fn check_subshelled_tests(params: &Parameters, t: &Token, out: &mut Out) {
    if let InnerToken::T_Subshell(list) = &*t.inner {
        if list.iter().all(sst_is_test_structure) && !sst_has_assignment(t) {
            let path = get_path(params, t);
            if sst_is_compound_condition(&path) {
                style(
                    out,
                    t.id(),
                    2233,
                    "Remove superfluous (..) around condition to avoid subshell overhead.",
                );
            } else if sst_is_single_test(list) && !sst_is_function_body(&path) {
                style(
                    out,
                    t.id(),
                    2234,
                    "Remove superfluous (..) around test command to avoid subshell overhead.",
                );
            } else {
                style(
                    out,
                    t.id(),
                    2235,
                    "Use { ..; } instead of (..) to avoid subshell overhead.",
                );
            }
        }
    }
}

pub(super) fn check_useless_bang(params: &Parameters, t: &Token, out: &mut Out) {
    if !params.has_set_e {
        return;
    }
    for c in non_returning_commands(params, t) {
        check_bang(params, c, out);
    }
}

/// SC2265 / SC2266 — `checkBadTestAndOr`.
pub(super) fn check_bad_test_and_or(params: &Parameters, t: &Token, out: &mut Out) {
    use InnerToken::*;
    match &*t.inner {
        T_Pipeline {
            separators,
            commands,
        } if commands.len() >= 2 => {
            // zip3 (Nothing:seps) cmds (seps ++ [Nothing])
            let _n = commands.len();
            for (i, cmd) in commands.iter().enumerate() {
                if is_test_command(cmd) {
                    // before = seps[i-1] (i>0), after = seps[i] (i < seps.len())
                    if i > 0 {
                        if let Some(sep) = separators.get(i - 1) {
                            check_pipe(params, sep, out);
                        }
                    }
                    if let Some(sep) = separators.get(i) {
                        check_pipe(params, sep, out);
                    }
                }
            }
        }
        T_Backgrounded(cmd) => check_ands(params, t.id(), cmd, out),
        _ => {}
    }
}

/// SC2283 / SC2284 / SC2285 — `checkSecondArgIsComparison`.
pub(super) fn check_second_arg_is_comparison(_params: &Parameters, t: &Token, out: &mut Out) {
    if let InnerToken::T_SimpleCommand { words, .. } = &*t.inner {
        if words.len() >= 2 {
            let arg = &words[1];
            if let Some(arg_string) = get_leading_unquoted_string(arg) {
                let b: Vec<char> = arg_string.chars().collect();
                // '=' repeated 4+ -> ignore (echo ======)
                if b.len() >= 4 && b[0] == '=' && b[1] == '=' && b[2] == '=' && b[3] == '=' {
                    // Nothing
                } else if b.len() >= 2 && b[0] == '+' && b[1] == '=' {
                    err(
                        out,
                        head_id(t),
                        2285,
                        "Remove spaces around += to assign (or quote '+=' if literal).",
                    );
                } else if b.len() >= 2 && b[0] == '=' && b[1] == '=' {
                    err(
                        out,
                        t.id(),
                        2284,
                        "Use [ x = y ] to compare values (or quote '==' if literal).",
                    );
                } else if !b.is_empty() && b[0] == '=' {
                    err(
                        out,
                        head_id(arg),
                        2283,
                        "Remove spaces around = to assign (or use [ ] to compare, or quote '=' if literal).",
                    );
                }
            }
        }
    }
}

pub(super) fn check_comparison_with_leading_x(params: &Parameters, t: &Token, out: &mut Out) {
    match &*t.inner {
        InnerToken::TC_Binary { op, lhs, rhs, .. } if matches!(op.as_str(), "=" | "==" | "!=") => {
            leading_x_check(params, lhs, rhs, out);
        }
        InnerToken::T_SimpleCommand { words, .. } if words.len() == 4 => {
            let cmd = &words[0];
            let op = &words[2];
            if ast_lib::get_literal_string(cmd).as_deref() == Some("test")
                && matches!(
                    ast_lib::get_literal_string(op).as_deref(),
                    Some("=") | Some("==") | Some("!=")
                )
            {
                leading_x_check(params, &words[1], &words[3], out);
            }
        }
        _ => {}
    }
}

/// SC2331 — `checkUnaryTestA`.
pub(super) fn check_unary_test_a(params: &Parameters, t: &Token, out: &mut Out) {
    // See Haskell definition below (~5265).
    check_unary_test_a_impl(params, t, out);
}

fn concat_strings(v: Vec<String>) -> String {
    v.concat()
}

fn is_zero(t: &Token) -> bool {
    get_literal_string(t).as_deref() == Some("0")
}

fn is_exit_code(t: &Token) -> bool {
    let parts = get_word_parts(t);
    if parts.len() == 1 {
        if let InnerToken::T_DollarBraced { op, .. } = &*parts[0].inner {
            return concat_strings(oversimplify(op)) == "?";
        }
    }
    false
}

fn checks_success_lhs(op: &str) -> bool {
    !matches!(op, "-gt" | "-ne" | "!=" | "!")
}

fn checks_success_rhs(op: &str) -> bool {
    !matches!(op, "-ne" | "!=")
}

fn is_only_test_in_command(params: &Parameters, t: &Token) -> bool {
    let mut cur = t;
    loop {
        let p = match params.parent(cur) {
            Some(p) => p,
            None => return false,
        };
        match &*p.inner {
            InnerToken::T_Condition { .. } => return true,
            InnerToken::T_Arithmetic(_) => return true,
            InnerToken::TA_Sequence(v) if v.len() == 1 => {
                if let Some(gp) = params.parent(p) {
                    if matches!(&*gp.inner, InnerToken::T_Arithmetic(_)) {
                        return true;
                    }
                }
                cur = p;
            }
            InnerToken::TC_Unary { op, .. } if op == "!" => cur = p,
            InnerToken::TA_Unary { op, .. } if op == "!" => cur = p,
            InnerToken::TC_Group { .. } => cur = p,
            InnerToken::TA_Parenthesis(_) => cur = p,
            _ => return false,
        }
    }
}

fn get_first_command_in_function(t: &Token) -> &Token {
    use InnerToken::*;
    match &*t.inner {
        T_Function { body, .. } => get_first_command_in_function(body),
        T_BraceGroup(cmds) if !cmds.is_empty() => get_first_command_in_function(&cmds[0]),
        T_Subshell(cmds) if !cmds.is_empty() => get_first_command_in_function(&cmds[0]),
        T_Annotation { token, .. } => get_first_command_in_function(token),
        T_AndIf { lhs, .. } => get_first_command_in_function(lhs),
        T_OrIf { lhs, .. } => get_first_command_in_function(lhs),
        T_Pipeline { commands, .. } if !commands.is_empty() => {
            get_first_command_in_function(&commands[0])
        }
        T_Redirecting { cmd, .. } => {
            if let T_IfExpression { clauses, .. } = &*cmd.inner {
                if let Some((conds, _)) = clauses.first() {
                    if let Some(first) = conds.first() {
                        return get_first_command_in_function(first);
                    }
                }
            }
            t
        }
        _ => t,
    }
}

fn is_first_command_in_function(params: &Parameters, t: &Token) -> bool {
    // Find the innermost enclosing function in the path (token first).
    let mut func: Option<&Token> = None;
    let mut c = t;
    loop {
        if matches!(&*c.inner, InnerToken::T_Function { .. }) {
            func = Some(c);
            break;
        }
        match params.parent(c) {
            Some(p) => c = p,
            None => break,
        }
    }
    let func = match func {
        Some(f) => f,
        None => return false,
    };
    let cmd = match get_closest_command(params, t) {
        Some(c) => c,
        None => return false,
    };
    cmd.id() == get_first_command_in_function(func).id()
}

fn rz_check(params: &Parameters, t: &Token, op: &str, lhs: &Token, rhs: &Token, out: &mut Out) {
    if is_zero(rhs) && is_exit_code(lhs) {
        rz_message(params, t, checks_success_lhs(op), lhs.id(), out);
    } else if is_zero(lhs) && is_exit_code(rhs) {
        rz_message(params, t, checks_success_rhs(op), rhs.id(), out);
    }
}

fn rz_message(params: &Parameters, t: &Token, for_success: bool, id: Id, out: &mut Out) {
    if is_only_test_in_command(params, t) && !is_first_command_in_function(params, t) {
        let prefix = if for_success { "" } else { "! " };
        style(
            out,
            id,
            2181,
            &format!(
                "Check exit code directly with e.g. 'if {}mycmd;', not indirectly with $?.",
                prefix
            ),
        );
    }
}

fn has_metachars(s: &str) -> bool {
    s.chars()
        .any(|c| matches!(c, '[' | ']' | '*' | '.' | '+' | '(' | ')' | '|'))
}

/// `isConstantNonRe`: a literal with no regex metacharacters.
fn is_constant_non_re(t: &Token) -> bool {
    match get_literal_string(t) {
        Some(s) => !has_metachars(&s),
        None => false,
    }
}

fn drop_last<T>(v: &[T]) -> &[T] {
    if v.is_empty() { v } else { &v[..v.len() - 1] }
}

/// `getNonReturningCommands`.
fn non_returning_commands<'a>(params: &Parameters, t: &'a Token) -> Vec<&'a Token> {
    match &*t.inner {
        InnerToken::T_Script { commands, .. } => drop_last(commands).iter().collect(),
        InnerToken::T_BraceGroup(list) => {
            if is_function_body(params, t) {
                drop_last(list).iter().collect()
            } else {
                list.iter().collect()
            }
        }
        InnerToken::T_Subshell(list) => drop_last(list).iter().collect(),
        InnerToken::T_WhileExpression { condition, body } => {
            let mut v: Vec<&Token> = drop_last(condition).iter().collect();
            v.extend(body.iter());
            v
        }
        InnerToken::T_UntilExpression { condition, body } => {
            let mut v: Vec<&Token> = drop_last(condition).iter().collect();
            v.extend(body.iter());
            v
        }
        InnerToken::T_ForIn { body, .. } => body.iter().collect(),
        InnerToken::T_ForArithmetic { body, .. } => body.iter().collect(),
        InnerToken::T_Annotation { token, .. } => non_returning_commands(params, token),
        InnerToken::T_IfExpression { clauses, elses } => {
            let mut v: Vec<&Token> = Vec::new();
            for (cond, then) in clauses {
                v.extend(drop_last(cond).iter());
                v.extend(then.iter());
            }
            v.extend(elses.iter());
            v
        }
        _ => vec![],
    }
}

fn check_bang(params: &Parameters, t: &Token, out: &mut Out) {
    match &*t.inner {
        InnerToken::T_Banged(cmd) => {
            if !in_condition(params, t) {
                info_with_fix(
                    out,
                    t.id(),
                    2251,
                    "This ! is not on a condition and skips errexit. Use `&& exit 1` instead, or make sure $? is checked.",
                    fix_with(vec![
                        replace_start(params, t.id(), 1, ""),
                        replace_end(params, cmd.id(), 0, " && exit 1"),
                    ]),
                );
            }
        }
        InnerToken::T_Annotation { token, .. } => check_bang(params, token, out),
        _ => {}
    }
}

fn redirect_is_comparison(op: &Token) -> bool {
    matches!(&*op.inner, InnerToken::T_Greater | InnerToken::T_Less)
}

fn redirect_is_suspicious(t: &Token) -> bool {
    match &*t.inner {
        InnerToken::T_FdRedirect { fd, target } => match &*target.inner {
            InnerToken::T_IoFile { op, .. } => fd != "2" && redirect_is_comparison(op),
            _ => false,
        },
        _ => false,
    }
}

fn is_lt_gt(op: &str) -> bool {
    matches!(op, "<" | "\\<" | ">" | "\\>")
}

fn is_le_ge(op: &str) -> bool {
    matches!(op, "<=" | "\\<=" | ">=" | "\\>=")
}

/// `eqv`: numeric operator suggested for a stringy `<`/`>`.
fn eqv(op: &str) -> &'static str {
    let op = op.strip_prefix('\\').unwrap_or(op);
    match op {
        "<" => "-lt",
        ">" => "-gt",
        "<=" => "-le",
        ">=" => "-ge",
        _ => "the numerical equivalent",
    }
}

/// `esc = if typ == SingleBracket then "\\" else ""`.
fn esc(typ: ConditionType) -> &'static str {
    if typ == ConditionType::SingleBracket {
        "\\"
    } else {
        ""
    }
}

/// `seqv`: string operator suggested for a numeric operator.
fn seqv(op: &str, typ: ConditionType) -> String {
    let e = esc(typ);
    match op {
        "-ge" => format!("! a {}< b", e),
        "-gt" => format!("{}>", e),
        "-le" => format!("! a {}> b", e),
        "-lt" => format!("{}<", e),
        "-eq" => "=".to_string(),
        "-ne" => "!=".to_string(),
        _ => "the string equivalent".to_string(),
    }
}

/// `invert`: only defined for `<=`/`>=` (with optional leading backslash).
fn invert_comparison(op: &str) -> &'static str {
    let op = op.strip_prefix('\\').unwrap_or(op);
    match op {
        "<=" => ">",
        ">=" => "<",
        _ => "",
    }
}

fn is_fraction(t: &Token) -> bool {
    let o = oversimplify(t);
    if o.len() == 1 {
        matches_float(&o[0])
    } else {
        false
    }
}

/// `matchRegex "^[-+]?[0-9]+\.[0-9]+$"` — implemented directly to avoid a regex dep.
fn matches_float(s: &str) -> bool {
    let bytes = s.as_bytes();
    let mut i = 0usize;
    let n = bytes.len();
    if i < n && (bytes[i] == b'+' || bytes[i] == b'-') {
        i += 1;
    }
    let start_int = i;
    while i < n && bytes[i].is_ascii_digit() {
        i += 1;
    }
    if i == start_int {
        return false; // need at least one digit
    }
    if i >= n || bytes[i] != b'.' {
        return false;
    }
    i += 1;
    let start_frac = i;
    while i < n && bytes[i].is_ascii_digit() {
        i += 1;
    }
    if i == start_frac {
        return false; // need at least one digit after the dot
    }
    i == n
}

/// `isNum`: whether the operand is (or may be) a number.
fn is_num(params: &Parameters, t: &Token) -> bool {
    let parts = get_word_parts(t);
    if parts.len() == 1 {
        match &*parts[0].inner {
            InnerToken::T_DollarArithmetic(_) => return true,
            InnerToken::T_DollarBraced { op: content, .. } => {
                let id = parts[0].id();
                let str = oversimplify(content).concat();
                let var = get_braced_reference(&str);
                return (|| {
                    let cfga = params.cfg_analysis.as_ref()?;
                    let state = cfga.get_incoming_state(id)?;
                    let value = state.variables_in_scope.get(&var)?;
                    Some(
                        value.variable_value.numerical_status
                            >= NumericalStatus::NumericalStatusMaybe,
                    )
                })()
                .unwrap_or(false);
            }
            _ => {}
        }
    }
    let o = oversimplify(t);
    o.len() == 1 && o[0].chars().all(|c| c.is_ascii_digit())
}

/// `numChar x = isDigit x || x `elem` "+-. "`.
fn num_char(c: char) -> bool {
    c.is_ascii_digit() || matches!(c, '+' | '-' | '.' | ' ')
}

/// `isNonNum t = not . all numChar $ onlyLiteralString t`.
fn is_non_num(t: &Token) -> bool {
    !ast_lib::only_literal_string(t).chars().all(num_char)
}

/// The set of variable names assigned anywhere per the linear `variableFlow`.
fn assigned_variables(params: &Parameters) -> Vec<String> {
    params
        .variable_flow
        .iter()
        .filter_map(|sd| match sd {
            StackData::Assignment(_, _, name, _) => Some(name.clone()),
            _ => None,
        })
        .collect()
}

fn check_decimals(params: &Parameters, hs: &Token, out: &mut Out) {
    if is_fraction(hs) && !has_floating_point(params) {
        err(
            out,
            hs.id(),
            2072,
            "Decimals are not supported. Either use integers only, or use bc or awk to compare.",
        );
    }
}

fn check_string(
    _params: &Parameters,
    typ: ConditionType,
    op: &str,
    t: &Token,
    assigned: &[String],
    out: &mut Out,
) {
    let as_string = get_literal_string_def("\0", t);
    let is_var = is_variable_name(&as_string);
    let kind = if is_var {
        "a variable"
    } else {
        "an arithmetic expression"
    };
    let fix = if is_var { "$var" } else { "$((expr))" };

    if is_non_num(t) {
        if typ == ConditionType::SingleBracket {
            err(
                out,
                t.id(),
                2170,
                &format!(
                    "Invalid number for {}. Use {} to compare as string (or use {} to expand as {}).",
                    op,
                    seqv(op, typ),
                    fix,
                    kind
                ),
            );
        } else {
            // Warn if: not a variable name, OR any part is quoted, OR it is not
            // a recognized (assigned) variable name.
            let any_quotes = get_word_parts(t).iter().any(|p| is_quotes(p));
            if !is_var || any_quotes || !assigned.iter().any(|v| v == &as_string) {
                warn(
                    out,
                    t.id(),
                    2309,
                    &format!(
                        "{} treats this as {}. Use {} to compare as string (or expand explicitly with {}).",
                        op,
                        kind,
                        seqv(op, typ),
                        fix
                    ),
                );
            }
        }
    }
}

fn leading_x_check(params: &Parameters, lhs: &Token, rhs: &Token, out: &mut Out) {
    if let (Some(l), Some(r)) = (fix_leading_x(params, lhs), fix_leading_x(params, rhs)) {
        let fix = fix_with(vec![l, r]);
        style_with_fix(
            out,
            lhs.id(),
            2268,
            "Avoid x-prefix in comparisons as it no longer serves a purpose.",
            fix,
        );
    }
}

fn fix_leading_x(params: &Parameters, token: &Token) -> Option<Replacement> {
    let parts = word_parts(token);
    let first = parts.first()?;
    match &*first.inner {
        InnerToken::T_Literal(s) => {
            let c = s.chars().next()?;
            if !c.eq_ignore_ascii_case(&'x') {
                return None;
            }
            // The side is a single, unquoted x or X, so we have to quote.
            if let InnerToken::T_NormalWord(v) = &*token.inner {
                if v.len() == 1 {
                    if let InnerToken::T_Literal(single) = &*v[0].inner {
                        if single.chars().count() == 1 {
                            return Some(replace_start(params, v[0].id(), 1, "\"\""));
                        }
                    }
                }
            }
            // Otherwise we can just delete it.
            Some(replace_start(params, first.id(), 1, ""))
        }
        InnerToken::T_SingleQuoted(s) => {
            let c = s.chars().next()?;
            if !c.eq_ignore_ascii_case(&'x') {
                return None;
            }
            // Replace the single quote and the character x or X.
            Some(replace_start(params, first.id(), 2, "'"))
        }
        _ => None,
    }
}

fn is_brace_expansion(t: &Token) -> bool {
    matches!(&*t.inner, InnerToken::T_BraceExpansion(_))
}

fn tas_check_arrays(_params: &Parameters, typ: ConditionType, token: &Token, out: &mut Out) {
    if word_parts(token).iter().any(|p| is_array_expansion(p)) {
        if typ == ConditionType::SingleBracket {
            warn(
                out,
                token.id(),
                2198,
                "Arrays don't work as operands in [ ]. Use a loop (or concatenate with * instead of @).",
            );
        } else {
            err(
                out,
                token.id(),
                2199,
                "Arrays implicitly concatenate in [[ ]]. Use a loop (or explicit * instead of @).",
            );
        }
    }
}

fn tas_check_braces(_params: &Parameters, typ: ConditionType, token: &Token, out: &mut Out) {
    if word_parts(token).iter().any(|p| is_brace_expansion(p)) {
        if typ == ConditionType::SingleBracket {
            warn(
                out,
                token.id(),
                2200,
                "Brace expansions don't work as operands in [ ]. Use a loop.",
            );
        } else {
            err(
                out,
                token.id(),
                2201,
                "Brace expansion doesn't happen in [[ ]]. Use a loop.",
            );
        }
    }
}

fn tas_check_globs(_params: &Parameters, typ: ConditionType, token: &Token, out: &mut Out) {
    if is_glob(token) {
        if typ == ConditionType::SingleBracket {
            warn(
                out,
                token.id(),
                2202,
                "Globs don't work as operands in [ ]. Use a loop.",
            );
        } else {
            err(
                out,
                token.id(),
                2203,
                "Globs are ignored in [[ ]] except right of =/!=. Use a loop.",
            );
        }
    }
}

fn tas_check_all(params: &Parameters, typ: ConditionType, token: &Token, out: &mut Out) {
    tas_check_arrays(params, typ, token, out);
    tas_check_braces(params, typ, token, out);
    tas_check_globs(params, typ, token, out);
}

fn tas_check_numerical_glob(params: &Parameters, token: &Token, out: &mut Out) {
    // Only the SingleBracket clause exists in Haskell; callers only pass SingleBracket.
    if params.shell != Shell::Ksh && is_glob(token) {
        err(
            out,
            token.id(),
            2255,
            "[ ] does not apply arithmetic evaluation. Evaluate with $((..)) for numbers, or use string comparator for strings.",
        );
    }
}

fn sst_is_command_test(t: &Token) -> bool {
    is_command(t, "test")
}

fn sst_is_test_command(t: &Token) -> bool {
    if let InnerToken::T_Pipeline {
        separators,
        commands,
    } = &*t.inner
    {
        if separators.is_empty() && commands.len() == 1 {
            if let InnerToken::T_Redirecting { cmd, .. } = &*commands[0].inner {
                return matches!(&*cmd.inner, InnerToken::T_Condition { .. })
                    || sst_is_command_test(cmd);
            }
        }
    }
    false
}

fn sst_is_test_structure(t: &Token) -> bool {
    match &*t.inner {
        InnerToken::T_Banged(w) => sst_is_test_structure(w),
        InnerToken::T_AndIf { lhs, rhs } | InnerToken::T_OrIf { lhs, rhs } => {
            sst_is_test_structure(lhs) && sst_is_test_structure(rhs)
        }
        InnerToken::T_Pipeline {
            separators,
            commands,
        } if separators.is_empty() && commands.len() == 1 => {
            if let InnerToken::T_Redirecting { cmd, .. } = &*commands[0].inner {
                match &*cmd.inner {
                    InnerToken::T_BraceGroup(ts) => ts.iter().all(sst_is_test_structure),
                    InnerToken::T_Subshell(ts) => ts.iter().all(sst_is_test_structure),
                    _ => sst_is_test_command(t),
                }
            } else {
                sst_is_test_command(t)
            }
        }
        _ => sst_is_test_command(t),
    }
}

fn sst_is_single_test(cmds: &[Token]) -> bool {
    cmds.len() == 1 && sst_is_test_command(&cmds[0])
}

fn is_function_tok(t: &Token) -> bool {
    matches!(&*t.inner, InnerToken::T_Function { .. })
}

fn sst_is_function_body(path: &[Token]) -> bool {
    // path[0] is the subshell itself; path[1] is its immediate parent.
    path.get(1).is_some_and(is_function_tok)
}

fn sst_skippable(t: &Token) -> bool {
    match &*t.inner {
        InnerToken::T_Redirecting { redirs, .. } => redirs.is_empty(),
        InnerToken::T_Pipeline { separators, .. } => separators.is_empty(),
        InnerToken::T_Annotation { .. } => true,
        _ => false,
    }
}

fn sst_is_compound_condition(path: &[Token]) -> bool {
    // dropWhile skippable over the tail (parents) of the path.
    let tail = if path.len() > 1 { &path[1..] } else { &[][..] };
    let mut iter = tail.iter().skip_while(|t| sst_skippable(t));
    match iter.next() {
        Some(t) => matches!(
            &*t.inner,
            InnerToken::T_IfExpression { .. }
                | InnerToken::T_WhileExpression { .. }
                | InnerToken::T_UntilExpression { .. }
        ),
        None => false,
    }
}

fn sst_is_assignment_node(t: &Token) -> bool {
    match &*t.inner {
        InnerToken::TA_Assignment { .. } => true,
        InnerToken::TA_Unary { op, .. } => op.contains("++") || op.contains("--"),
        InnerToken::T_DollarBraced { op, .. } => {
            let str = crate::ast_lib::oversimplify(op).concat();
            let modifier = crate::cfg::get_braced_modifier(&str);
            modifier.starts_with('=') || modifier.starts_with(":=")
        }
        InnerToken::T_DollarBraceCommandExpansion { .. } => true,
        _ => false,
    }
}

fn sst_has_assignment(t: &Token) -> bool {
    let mut found = false;
    t.visit_preorder(&mut |n| {
        if sst_is_assignment_node(n) {
            found = true;
        }
    });
    found
}

const BINARY_TEST_OPS: &[&str] = &[
    "-nt", "-ot", "-ef", "==", "!=", "<=", ">=", "-eq", "-ne", "-lt", "-le", "-gt", "-ge", "=~",
    ">", "<", "=", "\\<", "\\>", "\\<=", "\\>=",
];

const UNARY_TEST_OPS: &[&str] = &[
    "!", "-a", "-b", "-c", "-d", "-e", "-f", "-g", "-h", "-L", "-k", "-p", "-r", "-s", "-S", "-t",
    "-u", "-w", "-x", "-O", "-G", "-N", "-z", "-n", "-o", "-v", "-R",
];

/// Recursive literal extractor mirroring Haskell `getLiteralStringExt (const Nothing)`,
/// including the `TA_Expansion` and `T_ParamSubSpecialChar` cases (which the
/// crate's `ast_lib::get_literal_string` omits).
fn get_literal_string_local(t: &Token) -> Option<String> {
    use InnerToken::*;
    fn go(t: &Token, out: &mut String) -> bool {
        match &*t.inner {
            T_DoubleQuoted(l) | T_DollarDoubleQuoted(l) | T_NormalWord(l) | TA_Expansion(l) => {
                l.iter().all(|p| go(p, out))
            }
            T_SingleQuoted(s)
            | T_Literal(s)
            | T_ParamSubSpecialChar(s)
            | T_DollarSingleQuoted(s) => {
                out.push_str(s);
                true
            }
            _ => false,
        }
    }
    let mut s = String::new();
    if go(t, &mut s) { Some(s) } else { None }
}

/// `isLiteralNumber`.
fn is_literal_number(t: &Token) -> bool {
    match get_literal_string_local(t) {
        Some(s) => s.chars().all(|c| c.is_ascii_digit()),
        None => false,
    }
}

fn is_command_match(t: &Token, matcher: impl Fn(&str) -> bool) -> bool {
    match get_command_name(t) {
        Some(cmd) => matcher(&cmd),
        None => false,
    }
}

/// `isDereferencingBinaryOp`.
fn is_dereferencing_binary_op(op: &str) -> bool {
    ARITHMETIC_BINARY_TEST_OPS.contains(&op)
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum PseudoGlob {
    Any,
    Many,
    Char(char),
}

/// `wordToPseudoGlob`.
fn word_to_pseudo_glob(word: &Token) -> Vec<PseudoGlob> {
    word_to_pseudo_glob_impl(false, word).unwrap_or_else(|| vec![PseudoGlob::Many])
}

/// `wordToExactPseudoGlob`.
fn word_to_exact_pseudo_glob(word: &Token) -> Option<Vec<PseudoGlob>> {
    word_to_pseudo_glob_impl(true, word)
}

fn word_to_pseudo_glob_impl(exact: bool, word: &Token) -> Option<Vec<PseudoGlob>> {
    to_glob(exact, word).map(|g| simplify_pseudo_glob(&g))
}

fn to_glob(exact: bool, word: &Token) -> Option<Vec<PseudoGlob>> {
    use InnerToken::*;
    // Special-case: T_NormalWord starting with a literal `~...`.
    if let T_NormalWord(list) = &*word.inner {
        if let Some((first, rest)) = list.split_first() {
            if let T_Literal(s) = &*first.inner {
                if s.starts_with('~') {
                    if exact {
                        return None;
                    }
                    let mut this = vec![PseudoGlob::Many];
                    // map PGChar $ dropWhile (/= '/') str  (str is the whole literal incl '~')
                    let after: String = s.chars().skip_while(|c| *c != '/').collect();
                    this.extend(after.chars().map(PseudoGlob::Char));
                    // tail: concatMap getWordParts rest, then f each
                    let mut tail = Vec::new();
                    for part in rest.iter().flat_map(get_word_parts) {
                        let mut g = glob_part(exact, part)?;
                        tail.append(&mut g);
                    }
                    this.append(&mut tail);
                    return Some(this);
                }
            }
        }
    }
    let mut out = Vec::new();
    for part in get_word_parts(word) {
        let mut g = glob_part(exact, part)?;
        out.append(&mut g);
    }
    Some(out)
}

fn glob_part(exact: bool, x: &Token) -> Option<Vec<PseudoGlob>> {
    use InnerToken::*;
    match &*x.inner {
        T_Literal(s) | T_SingleQuoted(s) => Some(s.chars().map(PseudoGlob::Char).collect()),
        T_Glob(g) if g == "?" => Some(vec![PseudoGlob::Any]),
        T_Glob(g) if g == "*" => Some(vec![PseudoGlob::Many]),
        T_Glob(g) if g.starts_with('[') && !exact => Some(vec![PseudoGlob::Any]),
        _ => {
            if exact {
                None
            } else {
                Some(vec![PseudoGlob::Many])
            }
        }
    }
}

/// `simplifyPseudoGlob`.
fn simplify_pseudo_glob(list: &[PseudoGlob]) -> Vec<PseudoGlob> {
    let mut out = Vec::new();
    let mut i = 0;
    while i < list.len() {
        match list[i] {
            PseudoGlob::Char(_) => {
                out.push(list[i]);
                i += 1;
            }
            _ => {
                // span of Many/Any
                let start = i;
                while i < list.len() && matches!(list[i], PseudoGlob::Many | PseudoGlob::Any) {
                    i += 1;
                }
                let seg = &list[start..i];
                // order: all PGAny first, then take 1 PGMany
                for g in seg.iter().filter(|g| matches!(g, PseudoGlob::Any)) {
                    out.push(*g);
                }
                if seg.iter().any(|g| matches!(g, PseudoGlob::Many)) {
                    out.push(PseudoGlob::Many);
                }
            }
        }
    }
    out
}

/// `pseudoGlobsCanOverlap`.
fn pseudo_globs_can_overlap(x: &[PseudoGlob], y: &[PseudoGlob]) -> bool {
    match (x.first(), y.first()) {
        (Some(xf), Some(yf)) => match (xf, yf) {
            (PseudoGlob::Many, _) => {
                pseudo_globs_can_overlap(x, &y[1..]) || pseudo_globs_can_overlap(&x[1..], y)
            }
            (_, PseudoGlob::Many) => {
                pseudo_globs_can_overlap(x, &y[1..]) || pseudo_globs_can_overlap(&x[1..], y)
            }
            (PseudoGlob::Any, _) => pseudo_globs_can_overlap(&x[1..], &y[1..]),
            (_, PseudoGlob::Any) => pseudo_globs_can_overlap(&x[1..], &y[1..]),
            (a, b) => a == b && pseudo_globs_can_overlap(&x[1..], &y[1..]),
        },
        (None, None) => true,
        (Some(PseudoGlob::Many), None) => pseudo_globs_can_overlap(&x[1..], &[]),
        (Some(_), None) => false,
        (None, Some(_)) => pseudo_globs_can_overlap(y, &[]),
    }
}

/// `pseudoGlobIsSuperSetof`.
fn pseudo_glob_is_superset_of(x: &[PseudoGlob], y: &[PseudoGlob]) -> bool {
    match (x.first(), y.first()) {
        (Some(xf), Some(yf)) => match (xf, yf) {
            (PseudoGlob::Many, PseudoGlob::Many) => pseudo_glob_is_superset_of(x, &y[1..]),
            (PseudoGlob::Many, _) => {
                pseudo_glob_is_superset_of(x, &y[1..]) || pseudo_glob_is_superset_of(&x[1..], y)
            }
            (_, PseudoGlob::Many) => false,
            (PseudoGlob::Any, _) => pseudo_glob_is_superset_of(&x[1..], &y[1..]),
            (_, PseudoGlob::Any) => false,
            (a, b) => a == b && pseudo_glob_is_superset_of(&x[1..], &y[1..]),
        },
        (None, None) => true,
        (Some(PseudoGlob::Many), None) => pseudo_glob_is_superset_of(&x[1..], &[]),
        _ => false,
    }
}

/// `wordsCanBeEqual`.
fn words_can_be_equal(x: &Token, y: &Token) -> bool {
    pseudo_globs_can_overlap(&word_to_pseudo_glob(x), &word_to_pseudo_glob(y))
}

/// getExpr + orient for command-level and/or checks.
fn or_get_expr(x: &Token) -> Option<(Token, String, Token)> {
    cmd_level_get_expr(x)
}

fn cmd_level_get_expr(x: &Token) -> Option<(Token, String, Token)> {
    use InnerToken::*;
    match &*x.inner {
        T_OrIf { lhs, .. } => cmd_level_get_expr(lhs),
        T_AndIf { lhs, .. } => cmd_level_get_expr(lhs),
        T_Pipeline { commands, .. } if commands.len() == 1 => cmd_level_get_expr(&commands[0]),
        T_Redirecting { cmd, .. } => cmd_level_get_expr(cmd),
        T_Condition { token, .. } => cmd_level_get_expr(token),
        TC_Binary { op, lhs, rhs, .. } => orient(lhs, op, rhs),
        _ => None,
    }
}

fn orient(lhs: &Token, op: &str, rhs: &Token) -> Option<(Token, String, Token)> {
    match (is_constant(lhs), is_constant(rhs)) {
        (true, false) => Some((rhs.clone(), op.to_string(), lhs.clone())),
        (false, true) => Some((lhs.clone(), op.to_string(), rhs.clone())),
        _ => None,
    }
}

fn check_and_eq_operands(op: &str, rhs1: &Token, rhs2: &Token) -> bool {
    if op == "-eq" {
        is_literal_number(rhs1) && is_literal_number(rhs2)
    } else if op == "=" || op == "==" {
        is_literal(rhs1) && is_literal(rhs2)
    } else {
        false
    }
}

fn subshell_check(id: Id, t: &Token, out: &mut Out) {
    use InnerToken::*;
    match &*t.inner {
        T_Banged(w) => subshell_check(id, w, out),
        T_AndIf { lhs, .. } => subshell_check(id, lhs, out),
        T_OrIf { lhs, .. } => subshell_check(id, lhs, out),
        T_Pipeline { commands, .. } if commands.len() == 1 => {
            if let T_Redirecting { cmd, .. } = &*commands[0].inner {
                if let T_SimpleCommand { assignments, words } = &*cmd.inner {
                    if assignments.is_empty() && words.len() >= 2 {
                        subshell_check_params(id, &words[0], &words[1], out);
                    }
                }
            }
        }
        _ => {}
    }
}

fn subshell_check_params(id: Id, first: &Token, second: &Token, out: &mut Out) {
    if ast_lib::get_literal_string(first).is_some_and(|s| UNARY_TEST_OPS.contains(&s.as_str())) {
        err(
            out,
            id,
            2204,
            "(..) is a subshell. Did you mean [ .. ], a test expression?",
        );
    }
    if ast_lib::get_literal_string(second).is_some_and(|s| BINARY_TEST_OPS.contains(&s.as_str())) {
        warn(
            out,
            id,
            2205,
            "(..) is a subshell. Did you mean [ .. ], a test expression?",
        );
    }
}

fn check_pipe(params: &Parameters, sep: &Token, out: &mut Out) {
    if let InnerToken::T_Pipe(s) = &*sep.inner {
        if s == "|" {
            warn_with_fix(
                out,
                sep.id(),
                2266,
                "Use || for logical OR. Single | will pipe.",
                fix_with(vec![replace_end(params, sep.id(), 0, "|")]),
            );
        }
    }
}

fn check_ands(params: &Parameters, id: Id, t: &Token, out: &mut Out) {
    use InnerToken::*;
    match &*t.inner {
        T_AndIf { rhs, .. } => check_ands(params, id, rhs, out),
        T_OrIf { rhs, .. } => check_ands(params, id, rhs, out),
        T_Pipeline { commands, .. } if !commands.is_empty() => {
            check_ands(params, id, commands.last().unwrap(), out)
        }
        _cmd => {
            if is_test_command(t) {
                err_with_fix(
                    out,
                    id,
                    2265,
                    "Use && for logical AND. Single & will background and return true.",
                    fix_with(vec![replace_end(params, id, 0, "&")]),
                );
            }
        }
    }
}

fn trailing_check(word: &Token, command: &Token, out: &mut Out) {
    if let InnerToken::T_NormalWord(list) = &*word.inner {
        if list.len() == 1 {
            if let InnerToken::T_Literal(str) = &*list[0].inner {
                if str == "]]" || str == "]" {
                    let opposite = invert_bracket(str);
                    let parameters = oversimplify(command);
                    if !parameters.iter().any(|p| p == opposite) {
                        warn(
                            out,
                            list[0].id(),
                            2171,
                            &format!(
                                "Found trailing {} outside test. Add missing {} or quote if intentional.",
                                str, opposite
                            ),
                        );
                    }
                }
            }
        }
    }
}

fn invert_bracket(s: &str) -> &'static str {
    match s {
        "]]" => "[[",
        "]" => "[",
        _ => "",
    }
}

fn pattern_context(params: &Parameters, id: Id) -> String {
    match params.token_positions.get(&id) {
        Some((start, _)) => format!(" on line {}.", start.line),
        None => ".".to_string(),
    }
}

fn drop_negation(s: &str) -> String {
    match s.chars().next() {
        Some('!') | Some('^') => s.chars().skip(1).collect(),
        _ => s.to_string(),
    }
}

fn has_dupes(contents: &str) -> bool {
    let mut counts = std::collections::HashMap::new();
    for c in contents.chars().filter(|c| *c != '-') {
        *counts.entry(c).or_insert(0usize) += 1;
    }
    counts.values().any(|&v| v > 1)
}

fn is_ignored_command(params: &Parameters, t: &Token) -> bool {
    match get_closest_command(params, t) {
        Some(cmd) => is_command_match(cmd, |s| s == "tr" || s == "read"),
        None => false,
    }
}

fn is_dereferenced(params: &Parameters, t: &Token) -> bool {
    use InnerToken::*;
    for node in get_path(params, t) {
        match &*node.inner {
            TC_Binary {
                typ: ConditionType::DoubleBracket,
                op,
                ..
            } => {
                return is_dereferencing_binary_op(op);
            }
            TC_Unary { op, .. } => return op == "-v",
            T_SimpleCommand { .. } => return false,
            _ => {}
        }
    }
    false
}

fn check_unary_test_a_impl(params: &Parameters, t: &Token, out: &mut Out) {
    if let InnerToken::TC_Unary { op, .. } = &*t.inner {
        if op == "-a" {
            style_with_fix(
                out,
                t.id(),
                2331,
                "For file existence, prefer standard -e over legacy -a.",
                fix_with(vec![replace_start(params, t.id(), 2, "-e")]),
            );
        }
    }
}

/// `checkRequireDoubleBracket` (optional: `require-double-brackets`): a tree
/// check, since it does nothing at all outside the shells that have `[[ ]]`.
pub(super) fn check_require_double_bracket(params: &Parameters, root: &Token, out: &mut Out) {
    if !matches!(params.shell, Shell::Bash | Shell::Ksh | Shell::BusyboxSh) {
        return;
    }
    // `isSimple`: operators like `<` and `-o` are not tagged well enough to
    // rewrite, so only the straightforward conditions get a fix.
    fn is_simple(t: &Token) -> bool {
        match &*t.inner {
            InnerToken::T_Condition { token, .. } => is_simple(token),
            InnerToken::TC_Binary { op, .. } => !op.contains(['<', '>']),
            InnerToken::TC_Unary { .. } | InnerToken::TC_Nullary { .. } => true,
            _ => false,
        }
    }
    root.visit_preorder(&mut |t: &Token| {
        if let InnerToken::T_Condition {
            typ: ConditionType::SingleBracket,
            ..
        } = &*t.inner
        {
            let fix = if is_simple(t) {
                fix_with(vec![
                    replace_start(params, t.id(), 0, "["),
                    replace_end(params, t.id(), 0, "]"),
                ])
            } else {
                fix_with(Vec::new())
            };
            style_with_fix(
                out,
                t.id(),
                2292,
                "Prefer [[ ]] over [ ] for tests in Bash/Ksh/Busybox.",
                fix,
            );
        }
    });
}

/// `checkNullaryExpansionTest` (optional: `avoid-nullary-conditions`).
pub(super) fn check_nullary_expansion_test(params: &Parameters, t: &Token, out: &mut Out) {
    let InnerToken::TC_Nullary { token: word, .. } = &*t.inner else {
        return;
    };
    let id = word.id();
    let fix = fix_with(vec![replace_start(params, id, 0, "-n ")]);
    let parts = ast_lib::get_word_parts(word);
    if let [only] = parts.as_slice() {
        if ast_lib::is_command_substitution(only) {
            style_with_fix(
                out,
                id,
                2243,
                "Prefer explicit -n to check for output (or run command without [/[[ to check for success).",
                fix,
            );
            return;
        }
    }
    // Constant operands are SC2157's business, not this one's.
    if !parts.is_empty() && !parts.iter().any(|p| ast_lib::is_constant(p)) {
        style_with_fix(
            out,
            id,
            2244,
            "Prefer explicit -n to check non-empty string (or use =/-ne to check boolean/integer).",
            fix,
        );
    }
}

/// `inversionMap`: the comparison each operator becomes when the `!` is folded
/// into it.
fn inverted_operator(op: &str) -> Option<&'static str> {
    Some(match op {
        "=" | "==" => "!=",
        "!=" => "=",
        "-eq" => "-ne",
        "-ne" => "-eq",
        "-le" => "-gt",
        "-gt" => "-le",
        "-ge" => "-lt",
        "-lt" => "-ge",
        _ => return None,
    })
}

/// `checkUnnecessarilyInvertedTest` (optional: `avoid-negated-conditions`).
pub(super) fn check_unnecessarily_inverted_test(_params: &Parameters, t: &Token, out: &mut Out) {
    // `! [ .. ]` as a whole pipeline, which is the T_Banged shape.
    fn banged_condition(t: &Token) -> Option<&Token> {
        let InnerToken::T_Banged(inner) = &*t.inner else {
            return None;
        };
        let InnerToken::T_Pipeline { commands, .. } = &*inner.inner else {
            return None;
        };
        let [only] = commands.as_slice() else {
            return None;
        };
        let InnerToken::T_Redirecting { cmd, .. } = &*only.inner else {
            return None;
        };
        let InnerToken::T_Condition { token, .. } = &*cmd.inner else {
            return None;
        };
        Some(token)
    }

    let suggest_rewrite = |bang_inside: bool, typ: &ConditionType, op: &str, out: &mut Out| {
        let Some(new_op) = inverted_operator(op) else {
            return;
        };
        let bracket = |s: &str| match typ {
            ConditionType::SingleBracket => format!("[ {s} ]"),
            ConditionType::DoubleBracket => format!("[[ {s} ]]"),
        };
        let old_expr = format!("a {op} b");
        let new_expr = format!("a {new_op} b");
        let msg = if bang_inside {
            format!("Use {new_expr} instead of ! {old_expr}.")
        } else {
            format!(
                "Use {} instead of ! {}.",
                bracket(&new_expr),
                bracket(&old_expr)
            )
        };
        style(out, t.id(), 2335, &msg);
    };

    if let InnerToken::TC_Unary { op, token, .. } = &*t.inner {
        if op == "!" {
            match &*token.inner {
                InnerToken::TC_Unary { op: inner_op, .. } => match inner_op.as_str() {
                    "-n" => style(out, t.id(), 2236, "Use -z instead of ! -n."),
                    "-z" => style(out, t.id(), 2236, "Use -n instead of ! -z."),
                    _ => {}
                },
                InnerToken::TC_Binary {
                    typ, op: inner_op, ..
                } => suggest_rewrite(true, typ, inner_op, out),
                _ => {}
            }
        }
        return;
    }
    if let Some(cond) = banged_condition(t) {
        match &*cond.inner {
            InnerToken::TC_Unary { op, .. } => match op.as_str() {
                "-n" => style(out, t.id(), 2237, "Use [ -z .. ] instead of ! [ -n .. ]."),
                "-z" => style(out, t.id(), 2237, "Use [ -n .. ] instead of ! [ -z .. ]."),
                _ => {}
            },
            InnerToken::TC_Binary { typ, op, .. } => suggest_rewrite(false, typ, op, out),
            _ => {}
        }
    }
}

#[cfg(test)]
#[allow(non_snake_case)]
mod tests {
    use super::*;
    use crate::test_support::*;

    #[test]
    fn prop_checkNullaryExpansionTest1_6() {
        for s in ["[[ $(a) ]]", "[[ $a ]]", "[[ \"$a$b\" ]]", "[[ `x` ]]"] {
            assert!(emits(check_nullary_expansion_test, s), "{s}");
        }
        for s in ["[[ $a=1 ]]", "[[ -n $(a) ]]"] {
            assert!(!emits(check_nullary_expansion_test, s), "{s}");
        }
    }

    #[test]
    fn prop_checkUnnecessarilyInvertedTest1_10() {
        for s in [
            "[ ! -z $var ]",
            "! [[ -n $var ]]",
            "! [ $var != foo ]",
            "[[ ! $var == foo ]]",
            "[ ! $var -eq 0 ]",
            "! [[ $var -gt 3 ]]",
        ] {
            assert!(emits(check_unnecessarily_inverted_test, s), "{s}");
        }
        for s in [
            "! [ -x $var ]",
            "[[ ! -w $var ]]",
            "[ -z $var ]",
            "! [[ $var =~ .* ]]",
        ] {
            assert!(!emits(check_unnecessarily_inverted_test, s), "{s}");
        }
    }

    #[test]
    fn prop_checkTestRedirects1() {
        assert!(emits(check_test_redirects, "test 3 > 1"));
    }

    #[test]
    fn prop_checkTestRedirects2() {
        assert!(!emits(check_test_redirects, "test 3 \\> 1"));
    }

    #[test]
    fn prop_checkTestRedirects3() {
        assert!(emits(check_test_redirects, "/usr/bin/test $var > $foo"));
    }

    #[test]
    fn prop_checkTestRedirects4() {
        assert!(!emits(check_test_redirects, "test 1 -eq 2 2> file"));
    }

    #[test]
    fn prop_checkNumberComparisons1() {
        assert!(emits(check_number_comparisons, "[[ $foo < 3 ]]"));
    }

    #[test]
    fn prop_checkNumberComparisons2() {
        assert!(emits(check_number_comparisons, "[[ 0 >= $(cmd) ]]"));
    }

    #[test]
    fn prop_checkNumberComparisons3() {
        assert!(!emits(check_number_comparisons, "[[ $foo ]] > 3"));
    }

    #[test]
    fn prop_checkNumberComparisons4() {
        assert!(emits(check_number_comparisons, "[[ $foo > 2.72 ]]"));
    }

    #[test]
    fn prop_checkNumberComparisons5() {
        assert!(emits(check_number_comparisons, "[[ $foo -le 2.72 ]]"));
    }

    #[test]
    fn prop_checkNumberComparisons6() {
        assert!(emits(check_number_comparisons, "[[ 3.14 -eq $foo ]]"));
    }

    #[test]
    fn prop_checkNumberComparisons7() {
        assert!(!emits(check_number_comparisons, "[[ 3.14 == $foo ]]"));
    }

    #[test]
    fn prop_checkNumberComparisons8() {
        assert!(emits(check_number_comparisons, "[ foo <= bar ]"));
    }

    #[test]
    fn prop_checkNumberComparisons9() {
        assert!(emits(check_number_comparisons, "[ foo \\>= bar ]"));
    }

    #[test]
    fn prop_checkNumberComparisons11() {
        assert!(emits(check_number_comparisons, "[ $foo -eq 'N' ]"));
    }

    #[test]
    fn prop_checkNumberComparisons12() {
        assert!(emits(check_number_comparisons, "[ x$foo -gt x${N} ]"));
    }

    #[test]
    fn prop_checkNumberComparisons13() {
        assert!(emits(check_number_comparisons, "[ $foo > $bar ]"));
    }

    #[test]
    fn prop_checkNumberComparisons14() {
        assert!(!emits(check_number_comparisons, "[[ foo < bar ]]"));
    }

    #[test]
    fn prop_checkNumberComparisons15() {
        assert!(!emits(check_number_comparisons, "[ $foo '>' $bar ]"));
    }

    #[test]
    fn prop_checkNumberComparisons16() {
        assert!(emits(check_number_comparisons, "[ foo -eq 'y' ]"));
    }

    #[test]
    fn prop_checkNumberComparisons17() {
        assert!(emits(check_number_comparisons, "[[ 'foo' -eq 2 ]]"));
    }

    #[test]
    fn prop_checkNumberComparisons18() {
        assert!(emits(check_number_comparisons, "[[ foo -eq 2 ]]"));
    }

    #[test]
    fn prop_checkNumberComparisons19() {
        assert!(!emits(check_number_comparisons, "foo=1; [[ foo -eq 2 ]]"));
    }

    #[test]
    fn prop_checkNumberComparisons20() {
        assert!(emits(check_number_comparisons, "[[ 2 -eq / ]]"));
    }

    #[test]
    fn prop_checkNumberComparisons21() {
        assert!(emits(check_number_comparisons, "[[ foo -eq foo ]]"));
    }

    #[test]
    fn prop_checkNumberComparisons22() {
        assert!(emits(check_number_comparisons, "x=10; [[ $x > $z ]]"));
    }

    #[test]
    fn prop_checkNumberComparisons23() {
        assert!(emits(
            check_number_comparisons,
            "x=0; if [[ -n $def ]]; then x=$def; fi; while [ $x > $z ]; do lol; done"
        ));
    }

    #[test]
    fn prop_checkNumberComparisons24() {
        assert!(emits(check_number_comparisons, "x=$RANDOM; [ $x > $z ]"));
    }

    #[test]
    fn prop_checkNumberComparisons25() {
        assert!(emits(check_number_comparisons, "[[ $((n++)) > $x ]]"));
    }

    #[test]
    fn prop_checkComparisonWithLeadingX1() {
        assert!(emits(check_comparison_with_leading_x, "[ x$foo = xlol ]"));
    }

    #[test]
    fn prop_checkComparisonWithLeadingX2() {
        assert!(emits(check_comparison_with_leading_x, "test x$foo = xlol"));
    }

    #[test]
    fn prop_checkComparisonWithLeadingX3() {
        assert!(!emits(check_comparison_with_leading_x, "[ $foo = xbar ]"));
    }

    #[test]
    fn prop_checkComparisonWithLeadingX4() {
        assert!(!emits(check_comparison_with_leading_x, "test $foo = xbar"));
    }

    #[test]
    fn prop_checkComparisonWithLeadingX5() {
        assert!(emits(
            check_comparison_with_leading_x,
            "[ \"x$foo\" = 'xlol' ]"
        ));
    }

    #[test]
    fn prop_checkComparisonWithLeadingX6() {
        assert!(emits(
            check_comparison_with_leading_x,
            "[ x\"$foo\" = x'lol' ]"
        ));
    }

    #[test]
    fn prop_checkComparisonWithLeadingX7() {
        assert!(emits(check_comparison_with_leading_x, "[ X$foo != Xbar ]"));
    }

    // ---- SC2001 checkEchoSed ----

    #[test]
    fn prop_checkTestArgumentSplitting1() {
        assert!(emits(check_test_argument_splitting, "[ -e *.mp3 ]"));
    }

    #[test]
    fn prop_checkTestArgumentSplitting2() {
        assert!(!emits(check_test_argument_splitting, "[[ $a == *b* ]]"));
    }

    #[test]
    fn prop_checkTestArgumentSplitting3() {
        assert!(emits(check_test_argument_splitting, "[[ *.png == '' ]]"));
    }

    #[test]
    fn prop_checkTestArgumentSplitting4() {
        assert!(emits(
            check_test_argument_splitting,
            "[[ foo == f{o,oo,ooo} ]]"
        ));
    }

    #[test]
    fn prop_checkTestArgumentSplitting5() {
        assert!(emits(check_test_argument_splitting, "[[ $@ ]]"));
    }

    #[test]
    fn prop_checkTestArgumentSplitting6() {
        assert!(emits(check_test_argument_splitting, "[ -e $@ ]"));
    }

    #[test]
    fn prop_checkTestArgumentSplitting7() {
        assert!(emits(check_test_argument_splitting, "[ $@ == $@ ]"));
    }

    #[test]
    fn prop_checkTestArgumentSplitting8() {
        assert!(emits(check_test_argument_splitting, "[[ $@ = $@ ]]"));
    }

    #[test]
    fn prop_checkTestArgumentSplitting9() {
        assert!(!emits(
            check_test_argument_splitting,
            "[[ foo =~ bar{1,2} ]]"
        ));
    }

    #[test]
    fn prop_checkTestArgumentSplitting10() {
        assert!(!emits(check_test_argument_splitting, "[ \"$@\" ]"));
    }

    #[test]
    fn prop_checkTestArgumentSplitting11() {
        assert!(emits(check_test_argument_splitting, "[[ \"$@\" ]]"));
    }

    #[test]
    fn prop_checkTestArgumentSplitting12() {
        assert!(emits(check_test_argument_splitting, "[ *.png ]"));
    }

    #[test]
    fn prop_checkTestArgumentSplitting13() {
        assert!(emits(check_test_argument_splitting, "[ \"$@\" == \"\" ]"));
    }

    #[test]
    fn prop_checkTestArgumentSplitting14() {
        assert!(emits(check_test_argument_splitting, "[[ \"$@\" == \"\" ]]"));
    }

    #[test]
    fn prop_checkTestArgumentSplitting15() {
        assert!(!emits(
            check_test_argument_splitting,
            "[[ \"$*\" == \"\" ]]"
        ));
    }

    #[test]
    fn prop_checkTestArgumentSplitting16() {
        assert!(!emits(check_test_argument_splitting, "[[ -v foo[123] ]]"));
    }

    #[test]
    fn prop_checkTestArgumentSplitting17() {
        assert!(!emits(
            check_test_argument_splitting,
            "#!/bin/ksh\n[ -e foo* ]"
        ));
    }

    #[test]
    fn prop_checkTestArgumentSplitting18() {
        assert!(emits(
            check_test_argument_splitting,
            "#!/bin/ksh\n[ -d foo* ]"
        ));
    }

    #[test]
    fn prop_checkTestArgumentSplitting19() {
        assert!(!emits(
            check_test_argument_splitting,
            "[[ var[x] -eq 2*3 ]]"
        ));
    }

    #[test]
    fn prop_checkTestArgumentSplitting20() {
        assert!(emits(check_test_argument_splitting, "[ var[x] -eq 2 ]"));
    }

    #[test]
    fn prop_checkTestArgumentSplitting21() {
        assert!(emits(check_test_argument_splitting, "[ 6 -eq 2*3 ]"));
    }

    // ---- SC2216/2217/2259/2260/2261 checkPipeToNowhere ----

    // ---- SC2233/2234/2235 checkSubshelledTests ----

    #[test]
    fn prop_checkSubshelledTests1() {
        assert!(emits(check_subshelled_tests, "a && ( [ b ] || ! [ c ] )"));
    }

    #[test]
    fn prop_checkSubshelledTests2() {
        assert!(emits(check_subshelled_tests, "( [ a ] )"));
    }

    #[test]
    fn prop_checkSubshelledTests3() {
        assert!(emits(
            check_subshelled_tests,
            "( [ a ] && [ b ] || test c )"
        ));
    }

    #[test]
    fn prop_checkSubshelledTests4() {
        assert!(emits(
            check_subshelled_tests,
            "( [ a ] && { [ b ] && [ c ]; } )"
        ));
    }

    #[test]
    fn prop_checkSubshelledTests5() {
        assert!(!emits(check_subshelled_tests, "( [[ ${var:=x} = y ]] )"));
    }

    #[test]
    fn prop_checkSubshelledTests6() {
        assert!(!emits(check_subshelled_tests, "( [[ $((i++)) = 10 ]] )"));
    }

    #[test]
    fn prop_checkSubshelledTests7() {
        assert!(!emits(check_subshelled_tests, "( [[ $((i+=1)) = 10 ]] )"));
    }

    #[test]
    fn prop_checkSubshelledTests8() {
        assert!(emits(
            check_subshelled_tests,
            "# shellcheck disable=SC2234\nf() ( [[ x ]] )"
        ));
    }

    #[test]
    fn prop_checkSingleBracketOperators1() {
        assert!(emits(check_single_bracket_operators, "[ test =~ foo ]"));
    }

    // ---- SC2075 checkDoubleBracketOperators ----

    #[test]
    fn prop_checkDoubleBracketOperators1() {
        assert!(emits(check_double_bracket_operators, "[[ 3 \\< 4 ]]"));
    }

    #[test]
    fn prop_checkDoubleBracketOperators3() {
        assert!(!emits(check_double_bracket_operators, "[[ foo < bar ]]"));
    }

    // ---- SC2107/2108/2109/2110/2166 checkConditionalAndOrs ----

    #[test]
    fn prop_checkConditionalAndOrs1() {
        assert!(emits(check_conditional_and_ors, "[ foo && bar ]"));
    }

    #[test]
    fn prop_checkConditionalAndOrs2() {
        assert!(emits(check_conditional_and_ors, "[[ foo -o bar ]]"));
    }

    #[test]
    fn prop_checkConditionalAndOrs3() {
        assert!(!emits(check_conditional_and_ors, "[[ foo || bar ]]"));
    }

    #[test]
    fn prop_checkConditionalAndOrs4() {
        assert!(emits(check_conditional_and_ors, "[ foo -a bar ]"));
    }

    #[test]
    fn prop_checkConditionalAndOrs5() {
        assert!(emits(check_conditional_and_ors, "[ -z 3 -o a = b ]"));
    }

    // ---- SC2049 checkGlobbedRegex ----

    #[test]
    fn prop_checkGlobbedRegex1() {
        assert!(emits(check_globbed_regex, "[[ $foo =~ *foo* ]]"));
    }

    #[test]
    fn prop_checkGlobbedRegex2() {
        assert!(emits(check_globbed_regex, "[[ $foo =~ f* ]]"));
    }

    #[test]
    fn prop_checkGlobbedRegex3() {
        assert!(!emits(check_globbed_regex, "[[ $foo =~ $foo ]]"));
    }

    #[test]
    fn prop_checkGlobbedRegex4() {
        assert!(!emits(check_globbed_regex, "[[ $foo =~ ^c.* ]]"));
    }

    #[test]
    fn prop_checkGlobbedRegex5() {
        assert!(!emits(check_globbed_regex, "[[ $foo =~ \\* ]]"));
    }

    #[test]
    fn prop_checkGlobbedRegex6() {
        assert!(!emits(check_globbed_regex, "[[ $foo =~ (o*) ]]"));
    }

    #[test]
    fn prop_checkGlobbedRegex7() {
        assert!(!emits(check_globbed_regex, "[[ $foo =~ \\*foo ]]"));
    }

    #[test]
    fn prop_checkGlobbedRegex8() {
        assert!(!emits(check_globbed_regex, "[[ $foo =~ x\\* ]]"));
    }

    // ---- SC2050/2193 checkConstantIfs ----

    #[test]
    fn prop_checkConstantIfs1() {
        assert!(emits(check_constant_ifs, "[[ foo != bar ]]"));
    }

    #[test]
    fn prop_checkConstantIfs2a() {
        assert!(emits(check_constant_ifs, "[ n -le 4 ]"));
    }

    #[test]
    fn prop_checkConstantIfs2b() {
        assert!(!emits(check_constant_ifs, "[[ n -le 4 ]]"));
    }

    #[test]
    fn prop_checkConstantIfs3() {
        assert!(emits(check_constant_ifs, "[[ $n -le 4 && n != 2 ]]"));
    }

    #[test]
    fn prop_checkConstantIfs4() {
        assert!(!emits(check_constant_ifs, "[[ $n -le 3 ]]"));
    }

    #[test]
    fn prop_checkConstantIfs5() {
        assert!(!emits(check_constant_ifs, "[[ $n -le $n ]]"));
    }

    #[test]
    fn prop_checkConstantIfs6() {
        assert!(!emits(check_constant_ifs, "[[ a -ot b ]]"));
    }

    #[test]
    fn prop_checkConstantIfs7() {
        assert!(!emits(check_constant_ifs, "[ a -nt b ]"));
    }

    #[test]
    fn prop_checkConstantIfs8() {
        assert!(!emits(check_constant_ifs, "[[ ~foo == '~foo' ]]"));
    }

    #[test]
    fn prop_checkConstantIfs9() {
        assert!(emits(check_constant_ifs, "[[ *.png == [a-z] ]]"));
    }

    #[test]
    fn prop_checkConstantIfs10() {
        assert!(!emits(check_constant_ifs, "[[ ~me == ~+ ]]"));
    }

    #[test]
    fn prop_checkConstantIfs11() {
        assert!(!emits(check_constant_ifs, "[[ ~ == ~+ ]]"));
    }

    #[test]
    fn prop_checkConstantIfs12() {
        assert!(emits(check_constant_ifs, "[[ '~' == x ]]"));
    }

    // ---- SC2158/2159/2160/2161/2078 checkConstantNullary ----

    #[test]
    fn prop_checkConstantNullary() {
        assert!(emits(check_constant_nullary, "[[ '$(foo)' ]]"));
    }

    #[test]
    fn prop_checkConstantNullary2() {
        assert!(emits(check_constant_nullary, "[ \"-f lol\" ]"));
    }

    #[test]
    fn prop_checkConstantNullary3() {
        assert!(emits(check_constant_nullary, "[[ cmd ]]"));
    }

    #[test]
    fn prop_checkConstantNullary4() {
        assert!(emits(check_constant_nullary, "[[ ! cmd ]]"));
    }

    #[test]
    fn prop_checkConstantNullary5() {
        assert!(emits_code(check_constant_nullary, "[[ true ]]", 2160));
    }

    #[test]
    fn prop_checkConstantNullary6() {
        assert!(emits_code(check_constant_nullary, "[ 1 ]", 2161));
    }

    #[test]
    fn prop_checkConstantNullary7() {
        assert!(emits_code(check_constant_nullary, "[ false ]", 2158));
    }

    // ---- SC2057/2058 checkValidCondOps ----

    #[test]
    fn prop_checkValidCondOps1() {
        assert!(emits(check_valid_cond_ops, "[[ a -xz b ]]"));
    }

    #[test]
    fn prop_checkValidCondOps2() {
        assert!(emits(check_valid_cond_ops, "[ -M a ]"));
    }

    #[test]
    fn prop_checkValidCondOps2a() {
        assert!(!emits(check_valid_cond_ops, "[ 3 \\> 2 ]"));
    }

    #[test]
    fn prop_checkValidCondOps3() {
        assert!(!emits(check_valid_cond_ops, "[ 1 = 2 -a 3 -ge 4 ]"));
    }

    #[test]
    fn prop_checkValidCondOps4() {
        assert!(!emits(check_valid_cond_ops, "[[ ! -v foo ]]"));
    }

    // ---- SC2053/2081/2330 checkComparisonAgainstGlob ----

    #[test]
    fn prop_checkComparisonAgainstGlob() {
        assert!(emits(check_comparison_against_glob, "[[ $cow == $bar ]]"));
    }

    #[test]
    fn prop_checkComparisonAgainstGlob2() {
        assert!(!emits(
            check_comparison_against_glob,
            "[[ $cow == \"$bar\" ]]"
        ));
    }

    #[test]
    fn prop_checkComparisonAgainstGlob3() {
        assert!(emits(check_comparison_against_glob, "[ $cow = *foo* ]"));
    }

    #[test]
    fn prop_checkComparisonAgainstGlob4() {
        assert!(!emits(check_comparison_against_glob, "[ $cow = foo ]"));
    }

    #[test]
    fn prop_checkComparisonAgainstGlob5() {
        assert!(emits(check_comparison_against_glob, "[[ $cow != $bar ]]"));
    }

    #[test]
    fn prop_checkComparisonAgainstGlob6() {
        assert!(emits(check_comparison_against_glob, "[ $f != /* ]"));
    }

    #[test]
    fn prop_checkComparisonAgainstGlob7() {
        assert!(emits_code(
            check_comparison_against_glob,
            "#!/bin/busybox sh\n[[ $f == *foo* ]]",
            2330
        ));
    }

    // ---- SC2254 checkCaseAgainstGlob ----

    #[test]
    fn prop_checkCaseAgainstGlob1() {
        assert!(emits(
            check_case_against_glob,
            "case foo in lol$n) foo;; esac"
        ));
    }

    #[test]
    fn prop_checkCaseAgainstGlob2() {
        assert!(emits(
            check_case_against_glob,
            "case foo in $(foo)) foo;; esac"
        ));
    }

    #[test]
    fn prop_checkCaseAgainstGlob3() {
        assert!(!emits(
            check_case_against_glob,
            "case foo in *$bar*) foo;; esac"
        ));
    }

    // ---- SC2055/2056/2252 checkOrNeq ----

    #[test]
    fn prop_checkOrNeq1() {
        assert!(emits(
            check_or_neq,
            "if [[ $lol -ne cow || $lol -ne foo ]]; then echo foo; fi"
        ));
    }

    #[test]
    fn prop_checkOrNeq2() {
        assert!(emits(check_or_neq, "(( a!=lol || a!=foo ))"));
    }

    #[test]
    fn prop_checkOrNeq3() {
        assert!(emits(check_or_neq, "[ \"$a\" != lol || \"$a\" != foo ]"));
    }

    #[test]
    fn prop_checkOrNeq4() {
        assert!(!emits(check_or_neq, "[ a != $cow || b != $foo ]"));
    }

    #[test]
    fn prop_checkOrNeq5() {
        assert!(!emits(
            check_or_neq,
            "[[ $a != /home || $a != */public_html/* ]]"
        ));
    }

    #[test]
    fn prop_checkOrNeq6() {
        assert!(emits(check_or_neq, "[ $a != a ] || [ $a != b ]"));
    }

    #[test]
    fn prop_checkOrNeq7() {
        assert!(emits(check_or_neq, "[ $a != a ] || [ $a != b ] || true"));
    }

    #[test]
    fn prop_checkOrNeq8() {
        assert!(!emits(check_or_neq, "[[ $a != x || $a != x ]]"));
    }

    #[test]
    fn prop_checkOrNeq9() {
        assert!(!emits(check_or_neq, "[ 0 -ne $FOO ] || [ 0 -ne $BAR ]"));
    }

    // ---- SC2333/2334 checkAndEq ----

    #[test]
    fn prop_checkAndEq1() {
        assert!(!emits(
            check_and_eq,
            "cow=0; foo=0; if [[ $lol -eq cow && $lol -eq foo ]]; then echo foo; fi"
        ));
    }

    #[test]
    fn prop_checkAndEq2() {
        assert!(!emits(check_and_eq, "lol=0 foo=0; (( a==lol && a==foo ))"));
    }

    #[test]
    fn prop_checkAndEq3() {
        assert!(emits(check_and_eq, "[ \"$a\" = lol && \"$a\" = foo ]"));
    }

    #[test]
    fn prop_checkAndEq4() {
        assert!(!emits(check_and_eq, "[ a = $cow && b = $foo ]"));
    }

    #[test]
    fn prop_checkAndEq5() {
        assert!(!emits(
            check_and_eq,
            "[[ $a = /home && $a = */public_html/* ]]"
        ));
    }

    #[test]
    fn prop_checkAndEq6() {
        assert!(emits(check_and_eq, "[ $a = a ] && [ $a = b ]"));
    }

    #[test]
    fn prop_checkAndEq7() {
        assert!(emits(check_and_eq, "[ $a = a ] && [ $a = b ] || true"));
    }

    #[test]
    fn prop_checkAndEq8() {
        assert!(!emits(check_and_eq, "[[ $a == x && $a == x ]]"));
    }

    #[test]
    fn prop_checkAndEq9() {
        assert!(!emits(check_and_eq, "[ 0 -eq $FOO ] && [ 0 -eq $BAR ]"));
    }

    #[test]
    fn prop_checkAndEq10() {
        assert!(emits(check_and_eq, "(( a == 1 && a == 2 ))"));
    }

    #[test]
    fn prop_checkAndEq11() {
        assert!(emits(check_and_eq, "[ $x -eq 1 ] && [ $x -eq 2 ]"));
    }

    #[test]
    fn prop_checkAndEq12() {
        assert!(emits(check_and_eq, "[ 1 -eq $x ] && [ $x -eq 2 ]"));
    }

    #[test]
    fn prop_checkAndEq13() {
        assert!(!emits(check_and_eq, "[ 1 -eq $x ] && [ $x -eq 1 ]"));
    }

    #[test]
    fn prop_checkAndEq14() {
        assert!(!emits(check_and_eq, "[ $a = $b ] && [ $a = $c ]"));
    }

    // ---- SC2204/2205 checkSubshellAsTest ----

    #[test]
    fn prop_checkSubshellAsTest1() {
        assert!(emits(check_subshell_as_test, "( -e file )"));
    }

    #[test]
    fn prop_checkSubshellAsTest2() {
        assert!(emits(check_subshell_as_test, "( 1 -gt 2 )"));
    }

    #[test]
    fn prop_checkSubshellAsTest3() {
        assert!(!emits(check_subshell_as_test, "( grep -c foo bar )"));
    }

    #[test]
    fn prop_checkSubshellAsTest4() {
        assert!(!emits(check_subshell_as_test, "[ 1 -gt 2 ]"));
    }

    #[test]
    fn prop_checkSubshellAsTest5() {
        assert!(emits(check_subshell_as_test, "( -e file && -x file )"));
    }

    #[test]
    fn prop_checkSubshellAsTest6() {
        assert!(emits(
            check_subshell_as_test,
            "( -e file || -x file && -t 1 )"
        ));
    }

    #[test]
    fn prop_checkSubshellAsTest7() {
        assert!(emits(check_subshell_as_test, "( ! -d file )"));
    }

    // ---- SC2212 checkEmptyCondition ----

    #[test]
    fn prop_checkEmptyCondition1() {
        assert!(emits(check_empty_condition, "if [ ]; then ..; fi"));
    }

    #[test]
    fn prop_checkEmptyCondition2() {
        assert!(!emits(check_empty_condition, "[ foo -o bar ]"));
    }

    // ---- SC2265/2266 checkBadTestAndOr ----

    #[test]
    fn prop_checkBadTestAndOr1() {
        assert!(emits(check_bad_test_and_or, "[ x ] & [ y ]"));
    }

    #[test]
    fn prop_checkBadTestAndOr2() {
        assert!(emits(check_bad_test_and_or, "test -e foo & [ y ]"));
    }

    #[test]
    fn prop_checkBadTestAndOr3() {
        assert!(emits(check_bad_test_and_or, "[ x ] | [ y ]"));
    }

    // ---- SC2283/2284/2285 checkSecondArgIsComparison ----

    #[test]
    fn prop_checkSecondArgIsComparison1() {
        assert!(emits(check_second_arg_is_comparison, "foo = $bar"));
    }

    #[test]
    fn prop_checkSecondArgIsComparison2() {
        assert!(emits(check_second_arg_is_comparison, "$foo = $bar"));
    }

    #[test]
    fn prop_checkSecondArgIsComparison3() {
        assert!(emits(check_second_arg_is_comparison, "2f == $bar"));
    }

    #[test]
    fn prop_checkSecondArgIsComparison4() {
        assert!(emits(check_second_arg_is_comparison, "'var' =$bar"));
    }

    #[test]
    fn prop_checkSecondArgIsComparison5() {
        assert!(emits(check_second_arg_is_comparison, "foo ='$bar'"));
    }

    #[test]
    fn prop_checkSecondArgIsComparison6() {
        assert!(emits(check_second_arg_is_comparison, "$foo =$bar"));
    }

    #[test]
    fn prop_checkSecondArgIsComparison7() {
        assert!(emits(check_second_arg_is_comparison, "2f ==$bar"));
    }

    #[test]
    fn prop_checkSecondArgIsComparison8() {
        assert!(emits(check_second_arg_is_comparison, "'var' =$bar"));
    }

    #[test]
    fn prop_checkSecondArgIsComparison9() {
        assert!(emits(check_second_arg_is_comparison, "var += $(foo)"));
    }

    #[test]
    fn prop_checkSecondArgIsComparison10() {
        assert!(emits(check_second_arg_is_comparison, "var +=$(foo)"));
    }

    // ---- SC2171 checkTrailingBracket ----

    #[test]
    fn prop_checkTrailingBracket1() {
        assert!(emits(check_trailing_bracket, "if -z n ]]; then true; fi "));
    }

    #[test]
    fn prop_checkTrailingBracket2() {
        assert!(!emits(
            check_trailing_bracket,
            "if [[ -z n ]]; then true; fi "
        ));
    }

    #[test]
    fn prop_checkTrailingBracket3() {
        assert!(emits(check_trailing_bracket, "a || b ] && thing"));
    }

    #[test]
    fn prop_checkTrailingBracket4() {
        assert!(!emits(check_trailing_bracket, "run [ foo ]"));
    }

    #[test]
    fn prop_checkTrailingBracket5() {
        assert!(!emits(check_trailing_bracket, "run bar ']'"));
    }

    // ---- SC2331 checkUnaryTestA ----

    #[test]
    fn prop_checkUnaryTestA1() {
        assert!(emits(check_unary_test_a, "[ -a foo ]"));
    }

    #[test]
    fn prop_checkUnaryTestA2() {
        assert!(emits(check_unary_test_a, "[ ! -a foo ]"));
    }

    #[test]
    fn prop_checkUnaryTestA3() {
        assert!(!emits(check_unary_test_a, "[ foo -a bar ]"));
    }

    // ---- SC2194/2195/2221/2222 checkUnmatchableCases ----

    #[test]
    fn prop_checkUnmatchableCases1() {
        assert!(emits(
            check_unmatchable_cases,
            "case foo in bar) true; esac"
        ));
    }

    #[test]
    fn prop_checkUnmatchableCases2() {
        assert!(emits(
            check_unmatchable_cases,
            "case foo-$bar in ??|*) true; esac"
        ));
    }

    #[test]
    fn prop_checkUnmatchableCases3() {
        assert!(emits(
            check_unmatchable_cases,
            "case foo in foo) true; esac"
        ));
    }

    #[test]
    fn prop_checkUnmatchableCases4() {
        assert!(!emits(
            check_unmatchable_cases,
            "case foo-$bar in foo*|*bar|*baz*) true; esac"
        ));
    }

    #[test]
    fn prop_checkUnmatchableCases5() {
        assert!(emits(
            check_unmatchable_cases,
            "case $f in *.txt) true;; f??.txt) false;; esac"
        ));
    }

    #[test]
    fn prop_checkUnmatchableCases6() {
        assert!(!emits(
            check_unmatchable_cases,
            "case $f in ?*) true;; *) false;; esac"
        ));
    }

    #[test]
    fn prop_checkUnmatchableCases7() {
        assert!(!emits(
            check_unmatchable_cases,
            "case $f in $(x)) true;; asdf) false;; esac"
        ));
    }

    #[test]
    fn prop_checkUnmatchableCases8() {
        assert!(emits(
            check_unmatchable_cases,
            "case $f in cow) true;; bar|cow) false;; esac"
        ));
    }

    #[test]
    fn prop_checkUnmatchableCases9() {
        assert!(!emits(
            check_unmatchable_cases,
            "case $f in x) true;;& x) false;; esac"
        ));
    }

    // ---- SC2101/2102 checkCharRangeGlob ----

    #[test]
    fn prop_checkCharRangeGlob1() {
        assert!(emits(check_char_range_glob, "ls *[:digit:].jpg"));
    }

    #[test]
    fn prop_checkCharRangeGlob2() {
        assert!(!emits(check_char_range_glob, "ls *[[:digit:]].jpg"));
    }

    #[test]
    fn prop_checkCharRangeGlob3() {
        assert!(emits(check_char_range_glob, "ls [10-15]"));
    }

    #[test]
    fn prop_checkCharRangeGlob4() {
        assert!(!emits(check_char_range_glob, "ls [a-zA-Z]"));
    }

    #[test]
    fn prop_checkCharRangeGlob5() {
        assert!(!emits(check_char_range_glob, "tr -d [aa]"));
    }

    #[test]
    fn prop_checkCharRangeGlob6() {
        assert!(!emits(check_char_range_glob, "[[ $x == [!!]* ]]"));
    }

    #[test]
    fn prop_checkCharRangeGlob7() {
        assert!(!emits(check_char_range_glob, "[[ -v arr[keykey] ]]"));
    }

    #[test]
    fn prop_checkCharRangeGlob8() {
        assert!(!emits(check_char_range_glob, "[[ arr[keykey] -gt 1 ]]"));
    }

    #[test]
    fn prop_checkCharRangeGlob9() {
        assert!(!emits(check_char_range_glob, "read arr[keykey]"));
    }
}
