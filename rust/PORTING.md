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
3. **Port** into a batch module under `crates/shellcheck-rs/src/checks/` with a
   `pub fn register(c: &mut Checker)`. Emit via `warn/err/info/style[_with_fix]`.
   Build fixes with `replace_start` / `replace_end` / `replace_token` +
   `fix_with` (precedence is computed from the parent-path depth automatically).
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
- Helpers in `astlib`: `get_literal_string`, `oversimplify`,
  `executable_from_shebang`, `shell_for_executable`. Add more as needed.

## Reference port

`analytics::check_backticks` (SC2006, with an autofix) and
`analytics::check_shebang` (SC2148, a tree check) are worked examples that match
the oracle exactly, including fix replacements and precedence.

## Current status

These figures are **measured, oracle-pinned, and machine-regenerated** by
`run_conformance.py --gate` against the Haskell oracle at the git SHA recorded
in `harness/baseline.json` (`provenance.oracle.git`). They are not
hand-maintained — do not edit them by hand; re-run `--write-baseline` to refresh
`baseline.json` and paste the printed numbers here.

Strict comparison = ordered comment-key sequence identical **and** process exit
code identical, over the scripts the oracle itself parses (oracle-errored
scripts are counted in their own bucket, not silently folded into the rate).

- **Strict exact-match parity: 1651 / 1659 comparable scripts (99.52%)**, with
  **0 check-level false positives** (`extra == 0` on every code), **0 order
  mismatches**, and **0 oracle-errored scripts**.
- The **8 non-exact scripts are all missing-only SC1xxx notes** (the port emits
  a strict subset of the oracle's diagnostics — never a spurious one):
  - `SC1091` ×5 — the port does not resolve/follow `source`d files, so it can't
    emit the informational "Not following sourced file" note.
  - `SC1008` ×1 — unrecognized-shebang note not yet ported.
  - `SC1014` ×1 — "test as command" parser note not yet ported.
  - `SC1127` ×1 — "comment/unexpected token" parser note not yet ported.
- **3 exit-code mismatches** (`prop_checkShebang16`, `prop_checkSourceArgs2`,
  `prop_checkSourceArgs3`) are a direct *consequence* of the above: on those
  scripts the un-ported SC1xxx note is the **only** diagnostic, so the port
  finds no issues and exits 0 while the oracle exits 1. They are pinned in
  `baseline.json` (`exit_mismatch_ids`); the gate still fails on any *new* exit
  mismatch or any increase in count.
- Conditions (`[ ]`/`[[ ]]`), `select`, POSIX `name(){}`, and bats `@test` all
  parse; the parser handles the full corpus with **0 crashes and 0 spurious
  SC1072** (the earlier `time (..)`/`coproc` parser gaps are closed).
- Biggest remaining work, in order: (1) `source`-file resolution to unblock the
  SC1091 notes and their 3 dependent exit-code cases, (2) the remaining SC1xxx
  parser notes (SC1008/SC1014/SC1127), (3) the long tail of self-contained
  checks (fan out via batches).

The gate baseline (`harness/baseline.json`) is committed; the derived caches
(`goldens.jsonl`, `port.jsonl`, `coverage.json`) are regenerated and gitignored.
