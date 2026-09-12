//! Ported check batch o. See rust/PORTING.md.
//!
//! Ported: `checkNumberComparisons` (Analytics.hs) in full, emitting:
//! - SC2071  `>`/`<` used as a numeric comparison in a context with a numeric operand
//! - SC2072  decimals in a `<`/`>`/`<=`/`>=` comparison (non-ksh)
//! - SC2073  `<`/`>` in `[ ]` must be escaped (dash/busybox/other)
//! - SC2122  `<=`/`>=` is not a valid test operator
//! - SC2170  numeric operator (`-eq` ...) on a non-number in `[ ]`
//! - SC2309  numeric operator treats operand as a variable/arithmetic in `[[ ]]`
//!
//! This mirrors the single Haskell function; all of its branches share the
//! `isNum` / `isNonNum` machinery (cfg numerical status + `variableFlow`
//! assigned-variable set), so they are ported together.
use crate::analyzer_lib::*;
use crate::ast::*;
use crate::astlib;
use crate::astlib::is_quotes;
use crate::astlib::{get_literal_string_def, oversimplify};
use crate::cfg::{get_braced_reference, get_word_parts, is_variable_name};
use crate::cfg_analysis::NumericalStatus;
use crate::interface::Shell;

pub fn register(c: &mut Checker) {
    c.node(check_number_comparisons);
}

const ARITHMETIC_BINARY_TEST_OPS: &[&str] = &["-eq", "-ne", "-lt", "-le", "-gt", "-ge"];

fn is_lt_gt(op: &str) -> bool {
    matches!(op, "<" | "\\<" | ">" | "\\>")
}
fn is_le_ge(op: &str) -> bool {
    matches!(op, "<=" | "\\<=" | ">=" | "\\>=")
}

/// `hasFloatingPoint params = shellType params == Ksh`.
fn has_floating_point(params: &Parameters) -> bool {
    params.shell == Shell::Ksh
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
fn invert(op: &str) -> &'static str {
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
    !astlib::only_literal_string(t).chars().all(num_char)
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
            let any_quotes = get_word_parts(t).iter().any(is_quotes);
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

fn check_number_comparisons(params: &Parameters, t: &Token, out: &mut Out) {
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
                    invert(op)
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

#[allow(non_snake_case)]
#[cfg(test)]
mod tests {
    use super::*;
    use crate::analyzer_lib::make_parameters;
    use crate::parser::parse_script;

    fn params_for(script: &str) -> Parameters {
        let p = parse_script("test", script);
        let root = p.root.expect("parse produced no root");
        make_parameters(root, p.positions, None, None)
    }

    fn collect(f: fn(&Parameters, &Token, &mut Out), s: &str) -> Out {
        let params = params_for(s);
        let mut out = Out::new();
        fn walk(
            f: fn(&Parameters, &Token, &mut Out),
            params: &Parameters,
            t: &Token,
            out: &mut Out,
        ) {
            f(params, t, out);
            for c in t.children() {
                walk(f, params, c, out);
            }
        }
        walk(f, &params, &params.root, &mut out);
        out
    }

    fn emits(f: fn(&Parameters, &Token, &mut Out), s: &str) -> bool {
        !collect(f, s).is_empty()
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
}
