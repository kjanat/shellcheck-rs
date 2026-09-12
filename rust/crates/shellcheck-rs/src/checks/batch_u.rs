//! Ported check batch u. See rust/PORTING.md.
//!
//! Conditional / test-expression checks ported from Analytics.hs. Each function
//! is a faithful, complete port (with all prop_ tests). Some SC codes are
//! already emitted by earlier batches; to keep `extra == 0` those checks are
//! registered through a thin closure that filters the full function's output
//! down to the codes not already covered elsewhere. The full functions and
//! their tests remain unweakened.
//!
//! - SC2074       checkSingleBracketOperators   (register: full)
//! - SC2075       checkDoubleBracketOperators   (register: full)
//! - SC2107/8/9/10/2166 checkConditionalAndOrs   (register: SC2109 only; rest in b_f/g/k)
//! - SC2049       checkGlobbedRegex             (register: full)
//! - SC2050/2193  checkConstantIfs              (register: SC2193 only; SC2050 in b_c)
//! - SC2158/9/60/61/2078 checkConstantNullary   (register: SC2158/9/60/61; SC2078 in b_c)
//! - SC2057/2058  checkValidCondOps             (register: full)
//! - SC2053/2081/2330 checkComparisonAgainstGlob(register: SC2330 only; 2053/2081 in b_c)
//! - SC2254       checkCaseAgainstGlob          (register: full)
//! - SC2055/2056/2252 checkOrNeq                (register: full)
//! - SC2333/2334  checkAndEq                    (register: full)
//! - SC2204/2205  checkSubshellAsTest           (register: full)
//! - SC2212       checkEmptyCondition           (register: full)
//! - SC2265/2266  checkBadTestAndOr             (register: full)
//! - SC2283/2284/2285 checkSecondArgIsComparison(NOT registered; fully in b_n)
//! - SC2171       checkTrailingBracket          (register: full)
//! - SC2331       checkUnaryTestA               (register: full)
//! - SC2194/2195/2221/2222 checkUnmatchableCases(register: SC2195/2221/2222; SC2194 in b_n)
//! - SC2101/2102  checkCharRangeGlob            (register: full)
#![allow(unused_imports, unused_variables, dead_code)]
use crate::analyzer_lib::get_closest_command;
use crate::analyzer_lib::head_id;
use crate::analyzer_lib::is_command;
use crate::analyzer_lib::is_confused_glob_regex;
use crate::analyzer_lib::is_test_command;
use crate::analyzer_lib::*;
use crate::ast::*;
use crate::astlib;
use crate::astlib::get_leading_unquoted_string;
use crate::astlib::get_word_parts;
use crate::astlib::has_split_range;
use crate::astlib::is_closing_range;
use crate::astlib::is_constant;
use crate::astlib::is_glob;
use crate::astlib::is_half_open_range;
use crate::astlib::is_literal;
use crate::astlib::oversimplify;
use crate::cfg::get_unquoted_literal;
use crate::interface::Shell;

// ===========================================================================
// Registration
// ===========================================================================

pub fn register(c: &mut Checker) {
    c.node(check_single_bracket_operators);
    c.node(check_double_bracket_operators);

    c.node(check_conditional_and_ors);

    // checkGlobbedRegex (SC2049): now registered. The shared parser preserves
    // backslash escapes on the regex RHS, so `[[ $x =~ \* ]]` keeps the raw
    // "\*" and is distinguishable from the glob `[[ $x =~ * ]]`. No extra.
    c.node(check_globbed_regex);

    c.node(check_constant_ifs);

    c.node(check_constant_nullary);

    c.node(check_valid_cond_ops);

    c.node(check_comparison_against_glob);

    c.node(check_case_against_glob);
    c.node(check_or_neq);
    c.node(check_and_eq);
    c.node(check_subshell_as_test);
    c.node(check_empty_condition);
    c.node(check_bad_test_and_or);
    c.node(check_second_arg_is_comparison);
    c.node(check_trailing_bracket);
    // checkUnaryTestA (SC2331): now registered. The shared parser anchors the
    // TC_Unary node on the `-a` operator alone (cols 3-5 in `[ -a foo ]`),
    // matching the oracle span; the autofix (replaceStart) was already correct.
    c.node(check_unary_test_a);

    c.node(check_unmatchable_cases);

    c.node(check_char_range_glob);
}

// ===========================================================================
// Local helpers (ported from ASTLib / AnalyzerLib / Data; kept private).
// ===========================================================================

const ARITHMETIC_BINARY_TEST_OPS: &[&str] = &["-eq", "-ne", "-lt", "-le", "-gt", "-ge"];

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
/// crate's `astlib::get_literal_string` omits).
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

/// `isQuoteableExpansion`.
fn is_quoteable_expansion(t: &Token) -> bool {
    use InnerToken::*;
    matches!(
        &*t.inner,
        T_DollarBraced { .. }
            | T_DollarExpansion(_)
            | T_DollarBraceCommandExpansion { .. }
            | T_Backticked(_)
    )
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

// ---- Pseudoglobs (ASTLib) --------------------------------------------------

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

// ===========================================================================
// Checks
// ===========================================================================

/// SC2074 — `checkSingleBracketOperators`.
fn check_single_bracket_operators(params: &Parameters, t: &Token, out: &mut Out) {
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
fn check_double_bracket_operators(params: &Parameters, t: &Token, out: &mut Out) {
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

/// SC2107/2108/2109/2110/2166 — `checkConditionalAndOrs`.
fn check_conditional_and_ors(params: &Parameters, t: &Token, out: &mut Out) {
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

/// SC2049 — `checkGlobbedRegex`.
fn check_globbed_regex(params: &Parameters, t: &Token, out: &mut Out) {
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

/// SC2050 / SC2193 — `checkConstantIfs`.
fn check_constant_ifs(params: &Parameters, t: &Token, out: &mut Out) {
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

/// SC2158/2159/2160/2161/2078 — `checkConstantNullary`.
fn check_constant_nullary(params: &Parameters, t: &Token, out: &mut Out) {
    if let InnerToken::TC_Nullary { token, .. } = &*t.inner {
        if is_constant(token) {
            match astlib::only_literal_string(token).as_str() {
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

/// SC2057 / SC2058 — `checkValidCondOps`.
fn check_valid_cond_ops(params: &Parameters, t: &Token, out: &mut Out) {
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

/// SC2053 / SC2081 / SC2330 — `checkComparisonAgainstGlob`.
fn check_comparison_against_glob(params: &Parameters, t: &Token, out: &mut Out) {
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
fn check_case_against_glob(params: &Parameters, t: &Token, out: &mut Out) {
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
fn check_or_neq(params: &Parameters, t: &Token, out: &mut Out) {
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

/// SC2333 / SC2334 — `checkAndEq`.
fn check_and_eq(params: &Parameters, t: &Token, out: &mut Out) {
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

/// SC2204 / SC2205 — `checkSubshellAsTest`.
fn check_subshell_as_test(params: &Parameters, t: &Token, out: &mut Out) {
    if let InnerToken::T_Subshell(list) = &*t.inner {
        if list.len() == 1 {
            subshell_check(t.id(), &list[0], out);
        }
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
    if astlib::get_literal_string(first).is_some_and(|s| UNARY_TEST_OPS.contains(&s.as_str())) {
        err(
            out,
            id,
            2204,
            "(..) is a subshell. Did you mean [ .. ], a test expression?",
        );
    }
    if astlib::get_literal_string(second).is_some_and(|s| BINARY_TEST_OPS.contains(&s.as_str())) {
        warn(
            out,
            id,
            2205,
            "(..) is a subshell. Did you mean [ .. ], a test expression?",
        );
    }
}

/// SC2212 — `checkEmptyCondition`.
fn check_empty_condition(params: &Parameters, t: &Token, out: &mut Out) {
    if let InnerToken::TC_Empty { .. } = &*t.inner {
        style(
            out,
            t.id(),
            2212,
            "Use 'false' instead of empty [/[[ conditionals.",
        );
    }
}

/// SC2265 / SC2266 — `checkBadTestAndOr`.
fn check_bad_test_and_or(params: &Parameters, t: &Token, out: &mut Out) {
    use InnerToken::*;
    match &*t.inner {
        T_Pipeline {
            separators,
            commands,
        } if commands.len() >= 2 => {
            // zip3 (Nothing:seps) cmds (seps ++ [Nothing])
            let n = commands.len();
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
        cmd => {
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

/// SC2283 / SC2284 / SC2285 — `checkSecondArgIsComparison`.
fn check_second_arg_is_comparison(params: &Parameters, t: &Token, out: &mut Out) {
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

/// SC2171 — `checkTrailingBracket`.
fn check_trailing_bracket(params: &Parameters, t: &Token, out: &mut Out) {
    if let InnerToken::T_SimpleCommand { words, .. } = &*t.inner {
        if let Some(last) = words.last() {
            trailing_check(last, t, out);
        }
    }
}

fn trailing_check(word: &Token, command: &Token, out: &mut Out) {
    if let InnerToken::T_NormalWord(list) = &*word.inner {
        if list.len() == 1 {
            if let InnerToken::T_Literal(str) = &*list[0].inner {
                if str == "]]" || str == "]" {
                    let opposite = invert(str);
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

fn invert(s: &str) -> &'static str {
    match s {
        "]]" => "[[",
        "]" => "[",
        _ => "",
    }
}

/// SC2331 — `checkUnaryTestA`.
fn check_unary_test_a(params: &Parameters, t: &Token, out: &mut Out) {
    // See Haskell definition below (~5265).
    check_unary_test_a_impl(params, t, out);
}

/// SC2194 / SC2195 / SC2221 / SC2222 — `checkUnmatchableCases`.
fn check_unmatchable_cases(params: &Parameters, t: &Token, out: &mut Out) {
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

fn pattern_context(params: &Parameters, id: Id) -> String {
    match params.token_positions.get(&id) {
        Some((start, _)) => format!(" on line {}.", start.line),
        None => ".".to_string(),
    }
}

/// SC2101 / SC2102 — `checkCharRangeGlob`.
fn check_char_range_glob(params: &Parameters, t: &Token, out: &mut Out) {
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

// ===========================================================================
// checkUnaryTestA (SC2331)
// ===========================================================================

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

#[cfg(test)]
#[allow(non_snake_case)]
mod tests {
    use super::*;
    use crate::analyzer_lib::make_parameters;
    use crate::interface::Shell;
    use crate::parser::parse_script;

    fn params_for(script: &str) -> Parameters {
        let p = parse_script("test", script);
        let root = p.root.expect("parse produced no root");
        make_parameters(root, p.positions, None, None)
    }
    fn emits(f: fn(&Parameters, &Token, &mut Out), s: &str) -> bool {
        let params = params_for(s);
        let mut out = Out::new();
        params.root.visit_preorder(&mut |t| f(&params, t, &mut out));
        !out.is_empty()
    }
    fn emits_code(f: fn(&Parameters, &Token, &mut Out), s: &str, code: i64) -> bool {
        let params = params_for(s);
        let mut out = Out::new();
        params.root.visit_preorder(&mut |t| f(&params, t, &mut out));
        out.iter().any(|c| c.comment.code == code)
    }

    // ---- SC2074 checkSingleBracketOperators ----
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
