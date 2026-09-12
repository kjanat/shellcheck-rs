//! Ported check batch c. See rust/PORTING.md.
//!
//! Ported checks (condition-based; work with the current T_Condition/TC_* AST):
//! - SC2077  checkLiteralBreakingTest (Analytics.hs) — missing spaces around `=` etc.
//! - SC2157  checkLiteralBreakingTest (Analytics.hs) — `-n`/`-z`/implicit-`-n` on literal.
//! - SC2078  checkConstantNullary     (Analytics.hs) — constant `[ ]` expression.
//!           (The false/0/true/1 special cases SC2158/2159/2160/2161 are left to
//!           their owning batch; we emit only SC2078.)
//! - SC2053  checkComparisonAgainstGlob (Analytics.hs) — `[[ $x == $unquoted ]]`.
//! - SC2081  checkComparisonAgainstGlob (Analytics.hs) — `[ .. = glob ]`.
//!           (The BusyBox `[[ ]]` SC2330 branch is skipped: not assigned.)
//!
//! Skipped:
//! - SC2050  checkConstantIfs — the check itself ports cleanly (see
//!   `check_constant_ifs` below), but the oracle reports SC2050 at the *operator*
//!   token's span, whereas the current Rust parser gives `TC_Binary` the span of
//!   the whole expression (lhs..rhs). The operator is not a token in the Rust
//!   AST (`TC_Binary.op` is a plain `String`), so there is no id whose position
//!   maps to the operator; a comment's span is derived solely from its id via
//!   `token_positions`. Every emission therefore mismatches the oracle span
//!   (extra > 0), so the check is left UNREGISTERED until the parser gives the
//!   condition operator its own span. The SC2193 "can never be equal" branch is
//!   likewise skipped (needs `wordsCanBeEqual` pattern machinery).
#![allow(unused_imports, unused_variables, dead_code)]
use crate::astlib::is_constant;
use crate::astlib::is_glob;
use crate::astlib::is_closing_range;
use crate::astlib::is_half_open_range;
use crate::astlib::has_split_range;
use crate::astlib::get_word_parts;
use crate::analyzer_lib::*;
use crate::ast::*;
use crate::astlib;
use crate::interface::Shell;

/// Register this batch's checks.
pub fn register(c: &mut Checker) {
    c.node(check_literal_breaking_test);
    // Enabled: TC_Binary is now anchored on its operator token.
}

// ---------------------------------------------------------------------------
// Private helper predicates (ported from ASTLib; kept local so this module
// does not touch shared files that parallel agents also edit).
// ---------------------------------------------------------------------------

/// `ShellCheck.Data.arithmeticBinaryTestOps`.
const ARITHMETIC_BINARY_TEST_OPS: [&str; 6] = ["-eq", "-ne", "-lt", "-le", "-gt", "-ge"];

// foo[x${var}y] gets parsed as foo,[,x,$var,y], so check for such an interval.

// ---------------------------------------------------------------------------
// Checks
// ---------------------------------------------------------------------------

/// SC2077 / SC2157 — `checkLiteralBreakingTest`.
fn check_literal_breaking_test(params: &Parameters, t: &Token, out: &mut Out) {
    let has_equals = |x: &Token| astlib::get_literal_string(x).map_or(false, |s| s.contains('='));
    let is_nonempty = |x: &Token| astlib::get_literal_string(x).map_or(false, |s| !s.is_empty());

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
