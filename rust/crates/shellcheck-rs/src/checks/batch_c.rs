//! Ported check batch c. See rust/PORTING.md.
//!
//! Ported checks (condition-based; work with the current T_Condition/TC_* AST):
//! - SC2077  checkLiteralBreakingTest (Analytics.hs) — missing spaces around `=` etc.
//! - SC2157  checkLiteralBreakingTest (Analytics.hs) — `-n`/`-z`/implicit-`-n` on literal.
//!
//! The other checks this batch once carried (checkConstantNullary,
//! checkComparisonAgainstGlob, checkConstantIfs) now live in batch_u as single
//! complete ports.
use crate::analyzer_lib::*;
use crate::ast::*;
use crate::astlib;
use crate::astlib::get_word_parts;
use crate::astlib::is_constant;

/// Register this batch's checks.
pub fn register(c: &mut Checker) {
    c.node(check_literal_breaking_test);
    // Enabled: TC_Binary is now anchored on its operator token.
}

// ---------------------------------------------------------------------------
// Private helper predicates (ported from ASTLib; kept local so this module
// does not touch shared files that parallel agents also edit).
// ---------------------------------------------------------------------------

// foo[x${var}y] gets parsed as foo,[,x,$var,y], so check for such an interval.

// ---------------------------------------------------------------------------
// Checks
// ---------------------------------------------------------------------------

/// SC2077 / SC2157 — `checkLiteralBreakingTest`.
fn check_literal_breaking_test(_params: &Parameters, t: &Token, out: &mut Out) {
    let has_equals = |x: &Token| astlib::get_literal_string(x).is_some_and(|s| s.contains('='));
    let is_nonempty = |x: &Token| astlib::get_literal_string(x).is_some_and(|s| !s.is_empty());

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
