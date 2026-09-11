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
   - *Needs conditions* (`TC_*` from `[[ ]]`/`[ ]`): blocked until the parser's
     `readCondition` port lands (produces `T_Condition`/`TC_*`).
   - *Needs arithmetic* (`TA_*`): blocked until arithmetic parsing lands.
   - *Needs dataflow/CFG* (`variableFlow`, `cfgAnalysis` — SC2154, SC2086,
     SC2034, ...): blocked until the CFG subsystem is ported.
   Skip blocked checks and record them.
3. **Port** into a batch module under `crates/shellcheck-rs/src/checks/` with a
   `pub fn register(c: &mut Checker)`. Emit via `warn/err/info/style[_with_fix]`.
   Build fixes with `replace_start` / `replace_end` / `replace_token` +
   `fix_with` (precedence is computed from the parent-path depth automatically).
4. **Build**: `cargo build -p shellcheck-rs` (from `rust/`).
5. **Verify** against the oracle:
   ```sh
   cargo build --release -p shellcheck-cli
   cd rust/harness
   PORT=../target/release/shellcheck-rs python3 run_conformance.py
   ```
   Inspect `coverage.json -> port.per_code["<code>"]`. Requirement to keep a
   check: `extra == 0` for every code it can emit. `matched` should rise toward
   `oracle`; residual `missing` is usually a parser gap on those scripts.
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
- Helpers in `astlib`: `get_literal_string`, `oversimplify`,
  `executable_from_shebang`, `shell_for_executable`. Add more as needed.

## Reference port

`analytics::check_backticks` (SC2006, with an autofix) and
`analytics::check_shebang` (SC2148, a tree check) are worked examples that match
the oracle exactly, including fix replacements and precedence.

## Current status (see harness/coverage.json)

- Parser handles the full corpus with 0 crashes; ~130 scripts still hit
  parser gaps (spurious SC1072) — mostly conditions, arithmetic-for, bats
  `@test`, and a few redirection forms.
- Ported & oracle-exact: SC2148, SC2006, SC2066 (partial), SC1xxx parse notes.
- Biggest unblocking work, in order: (1) `readCondition` -> `TC_*`,
  (2) arithmetic parsing -> `TA_*`, (3) the CFG subsystem for SC2154/2086/2034.
