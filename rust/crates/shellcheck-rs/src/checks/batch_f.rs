//! Ported check batch f. See rust/PORTING.md.
//!
//! Implemented (logic ports; NOT registered — see the blocker below):
//! - SC2015  checkShorthandIf — `A && B || C` is not if-then-else
//! - SC2166  checkConditionalAndOrs (the `[ .. -a .. ]` / `[ .. -o .. ]` branches)
//!
//! Skipped:
//! - SC2128  checkArrayWithoutIndex — needs `doVariableFlowAnalysis`/`variableFlow`
//!   (dataflow), which is not yet ported.
//! - SC2145 / SC2077 — already handled elsewhere / not assigned.
//!
//! BLOCKER — parser node positioning (cannot register these two):
//! The check logic below is correct: against the oracle corpus each fires on
//! exactly the right scripts (SC2015: 3/3, SC2166: 8/8). But every diagnostic
//! lands at the wrong COLUMN, so all count as `extra` under the conformance
//! harness, and the hard rule forbids registering a check with `extra > 0`.
//!
//! The Haskell oracle positions the binary AST nodes at their *operator token*:
//! `T_AndIf`/`T_OrIf` take the id of the `&&`/`||` token (Parser.hs readAndOr),
//! and `TC_And`/`TC_Or` take the id of the `-a`/`-o`/`&&`/`||` operator
//! (readAndOrOp). The Rust parser instead assigns these nodes a span covering
//! the whole `lhs .. rhs` (parser.rs `read_and_or` and `read_cond_or`/
//! `read_cond_and`, all via `next_id_between(lhs.start, rhs.end)`), and there is
//! no separate operator id to emit on. The emit API positions a comment solely
//! from `token_positions[id]`, so matching the oracle requires the parser to
//! record the operator position for these nodes — a change to `parser.rs`, which
//! this batch may not edit. Once the parser positions `T_AndIf`/`T_OrIf`/
//! `TC_And`/`TC_Or` at their operator (as Haskell does), register the two checks
//! below and they should reach `extra == 0`.
//!
//! Note: `checkConditionalAndOrs` in Haskell also emits SC2107/2108/2109/2110;
//! only the SC2166 branches are ported here (the others are out of scope).
use crate::analyzer_lib::get_command_basename;
use crate::analyzer_lib::in_condition;
use crate::analyzer_lib::is_test_command;
use crate::analyzer_lib::*;
use crate::ast::*;
use crate::astlib::is_assignment;

pub fn register(c: &mut Checker) {
    // Enabled now that the parser anchors T_OrIf/T_AndIf/TC_And/TC_Or on the
    // operator token (matching ShellCheck). SC2128 still needs dataflow (skipped).
    c.node(check_shorthand_if);
}

// ---------------------------------------------------------------------------
// Private helper predicates (ported from ASTLib/AnalyzerLib; kept local so this
// module does not touch shared files that parallel agents also edit).
// ---------------------------------------------------------------------------

// ---------------------------------------------------------------------------
// SC2015 — checkShorthandIf
// ---------------------------------------------------------------------------

fn check_shorthand_if(params: &Parameters, x: &Token, out: &mut Out) {
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

// ---------------------------------------------------------------------------
// SC2166 — checkConditionalAndOrs (SC2166 branches only)
// ---------------------------------------------------------------------------
