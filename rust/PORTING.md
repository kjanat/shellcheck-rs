# Porting checks to the Rust port (harness-driven loop)

This is the repeatable loop for converting ShellCheck's remaining checks to Rust
and **proving** each one against the Haskell oracle. The conformance harness is
the fitness function: a check is "done" only when the harness shows its SC codes
matching the oracle with `extra == 0`.

## The loop

1. **Pick** a check (or small group) from `src/ShellCheck/*.hs`. Note its SC
   code(s) and `prop_` tests.
2. **Classify** it:
   - *Pure AST pattern* (matches on `T_*`/`TC_*`/`TA_*`, uses `oversimplify` /
     `get_literal_string` / parent lookups): port now.
   - *Needs conditions* (`TC_*` from `[[ ]]`/`[ ]`): SUPPORTED — the parser now
     produces `T_Condition`/`TC_*`.
   - *Needs arithmetic* (`TA_*`): blocked until arithmetic parsing lands
     (`$((..))`, `((..))`, `for ((;;))`, and array indices are currently a
     placeholder `T_Literal`, not a `TA_*` tree).
   - *Needs dataflow/CFG* (`variableFlow`, `cfgAnalysis` — SC2154, SC2086,
     SC2034, ...): blocked until the CFG subsystem is ported.
     Skip blocked checks and record them.
3. **Port** it into the module that mirrors its Haskell home (see
   `DESIGN.md`, "Workspace layout"):
   - `Analytics.hs` checks go in `src/analytics/<theme>.rs` and are registered
     in `src/analytics/mod.rs`, at the position the Haskell `nodeChecks` /
     `treeChecks` list gives them.
   - `Checks/Commands.hs` checks go in `src/checks/commands/<group>.rs` as
     `pub(super) fn check_x() -> CommandCheck { CommandCheck::new(Basename("x"), |params, t, out| { .. }) }`
     — the same `CommandCheck (Basename "x") f` shape as Haskell — and are
     registered in `src/checks/commands/mod.rs` in `commandChecks` order.
     Parametrised checks (`checkSudoArgs cmd`) take the name as an argument.
   - `Checks/ShellSupport.hs` checks go in `src/checks/shell_support.rs` as
     `pub(super) fn check_x() -> ForShell { ForShell::new(&[Shell::Sh, ..], body) }`.
   - Shared word lists belong in `src/data.rs` (`ShellCheck.Data`); helpers
     that several themes of one family need go in that family's `common.rs`;
     helpers from `ASTLib` / `AnalyzerLib` go in `ast_lib.rs` / `analyzer_lib.rs`.
     Never copy a helper into a check module: grep for it first.
     Emit via `warn/err/info/style[_with_fix]`. Build fixes with `replace_start` /
     `replace_end` / `replace_token` + `fix_with` (precedence is computed from the
     parent-path depth automatically). Port the check's `prop_` tests next to it,
     using `crate::test_support::{produces, tree_emits, ..}` (`verify` /
     `verifyTree`); parametrised checks are tested as in Haskell:
     `produces(check_sudo_args("sudo"), "sudo cd /root")`.
4. **Build**: `cargo build -p shellcheck-rs` (from `rust/`).
5. **Verify** against the oracle:

   ```sh
   cargo build --release -p shellcheck-cli
   cd rust/harness
   ORACLE=$(cabal list-bin shellcheck) \
   PORT=../target/release/shellcheck-rs python3 run_conformance.py
   # gate the change (exits nonzero on any regression vs baseline.json):
   ORACLE=$(cabal list-bin shellcheck) \
   PORT=../target/release/shellcheck-rs python3 run_conformance.py --gate
   ```

   Inspect `coverage.json -> port.per_code["<code>"]`. Requirement to keep a
   check: `extra == 0` for every code it can emit. `matched` should rise toward
   `oracle`; residual `missing` is usually a parser gap on those scripts.
   Comparison is **strict**: diagnostics must match as an *ordered* sequence
   (ShellCheck's deterministic sort), and the process **exit code** must match
   too. If your change legitimately raises `exact_scripts` or `matched`, refresh
   the committed baseline with `--write-baseline`.
6. **Iterate** until `exact_pct == 100` and every code has `missing == extra == 0`.

## Conformance-safety rule

**Never register a check that produces `extra > 0`.** A false positive regresses
the whole tool. If a port over-fires, tighten it or leave it out and record why.
The port has held **0 spurious diagnostics** (outside bounded parser gaps) since
the pipeline landed; keep it that way.

## The check-authoring API (`analyzer_lib`)

- `Checker::node(|params, token, out| { ... })` — runs on every AST node.
- `Checker::tree(|params, root, out| { ... })` — runs once on the root.
- `Parameters`: `shell`, `shell_type_specified`, `root`, `token_positions`,
  `parent_map` (Id->Id), `id_map` (Id->Token), `has_set_e`, `has_pipefail`,
  `has_lastpipe`. `params.parent(t)` returns the parent token.
- Emit: `err/warn/info/style(out, id, code, msg)` and the `*_with_fix` variants.
- AST: `token.inner` is an `InnerToken`; match with the Haskell constructor
  names (`T_SimpleCommand { assignments, words }`, `T_DollarBraced { braced, op }`,
  ...). `token.children()` yields child refs; equality on `Token` ignores ids.
- Helpers in `ast_lib`: `get_literal_string`, `oversimplify`,
  `executable_from_shebang`, `shell_for_executable`. Add more as needed.

## Reference port

`analytics::quoting::check_backticks` (SC2006, with an autofix),
`analytics::script::check_shebang` (SC2148, a tree check),
`checks::commands::coreutils::check_tr` (a `CommandCheck`) and
`checks::shell_support::check_bashisms` (a `ForShell`) are worked examples that
match the oracle exactly, including fix replacements and precedence.

## Current status

These figures are **measured, oracle-pinned, and machine-regenerated** by
`run_conformance.py --gate` against the Haskell oracle at the git SHA recorded
in `harness/baseline.json` (`provenance.oracle.git`). They are not
hand-maintained — do not edit them by hand; re-run `--write-baseline` to refresh
`baseline.json` and paste the printed numbers here.

Strict comparison = ordered comment-key sequence identical **and** process exit
code identical, over the scripts the oracle itself parses (oracle-errored
scripts are counted in their own bucket, not silently folded into the rate).

- **Strict exact-match parity: 1659 / 1659 comparable scripts (100%)**, with
  **0 check-level false positives** (`extra == 0` on every code), **0 order
  mismatches**, **0 exit-code mismatches** and **0 oracle-errored scripts**.
- Every check the Haskell registers in `nodeChecks`, `treeChecks`,
  `commandChecks` and ShellSupport's `checks` is ported and registered; the
  registration lists in `analytics/mod.rs` and `checks/commands/mod.rs` are
  generated from the Haskell lists, so a missing check would appear there as a
  `not ported` line.
- Not yet ported, in order of impact: (1) `source`-file resolution (`-x`, `-P`,
  `-a`; SC1091/SC1094 are emitted from a placeholder check until then), (2) the
  optional checks (`--enable`, `optionalTreeChecks` / `optionalCommandChecks`),
  (3) the remaining SC1xxx parser notes (SC1008/SC1014/SC1071/SC1082/SC1127).

The gate baseline (`harness/baseline.json`) is committed; the derived caches
(`goldens.jsonl`, `port.jsonl`, `coverage.json`) are regenerated and gitignored.
