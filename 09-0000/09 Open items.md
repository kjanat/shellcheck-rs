<a name="idtop"></a>

# 9 Open items

*As of 2026-10-02.*

## 9.1 rust-port

*[PR #1], head [`0c9cb40`], CI green.*

1. **WP-R5** — make the invocation iteration order deterministic (`Ctx::invocations` → `BTreeMap<Vec<Node>, _>`), then gate, fuzz several seeds, snapshot. Correctness before further speed work. Spec in `rust/PERF.md`.
2. Next performance candidates, measure first: parser context-stack clones (176 M Ir on large), `build_graph` (`remove_unnecessary_structural_nodes`, `id_to_nodes` BTreeSet inserts), `Rc<str>` `memcmp` in `OrdMap`, the heavier node checks (`caai_get_associative_arrays`, `check_pipe_to_nowhere`, `check_redirect_to_same`, `check_number_comparisons`), `ForShell` as one dispatcher.
3. Decide whether to keep `im-rc` (MPL-2.0; Socket license score 70) or write an in-crate persistent tree.
4. The 22 unresolved review threads on PR #1 are answered and mostly outdated; resolving them in the GitHub UI is a human's call.
5. Run the bench branch's CI against the new head so the shared-runner numbers are on record.

**[⬆ Top](#idtop)**

## 9.2 h2r-compiler

*[PR #2], head [`f0009d0`].*

1. The incremental runtime programme is at its floor (~2 % per package). Remaining small packages, specified in `crates/h2r-rt/PERF.md`: **WP18** (closure shims call `b_` directly, ~2 %), **WP16** (non-allocating tail apply, ~3 %, touches every block signature), **WP17b** (never-forced thunks: per-site safety arguments, ~2 %).
2. The real gap (~8× to GHC) is representation: unboxed strict fields, packed strings (**WP5**, needs a census of `:` cells first), an arena or a real GC. A redesign, not an agent task.
3. Compiler items from `todo.md`: the IO story, method fields that are cast lambdas, more libraries compiled from source (`ghc-prim`, `text`, `filepath`, `regex-tdfa`, `aeson`, `fgl`, `Diff`, `vector`), `FCallId` in the dump, non-tail recursion stack cost, `Set.insert` loop performance, gate-8 attribution, milestone tags.
4. `crates/shellcheck-core/build.rs`'s three-line stats change (WP17a) was only verified by reading; a stats rebuild was done afterwards and produced the census, so it works, but the size of the ~46 500-row `SITES` table in the entry crate was never measured.

**[⬆ Top](#idtop)**

## 9.3 bench

1. Run CI once more now that both candidates moved (rust-port [`0c9cb40`], h2r [`f0009d0`]); archive the report under `bench/results/`.
2. Consider adding a `large-json1`-style scenario for the many-file case and a memory-only scenario, since memory is now the port's clearest win.

**[⬆ Top](#idtop)**

## 9.4 Housekeeping

*Needs a human; the agent was not permitted.*

- Delete `.bench/target/h2r-tests` (4 GB) and the 18 finished agent worktrees under `.claude/worktrees` (`git worktree remove --force` each, then `git worktree prune`); the `worktree-agent-*` branches can be deleted too.

**[⬆ Top](#idtop)**

[PR #1]: https://github.com/kjanat/shellcheck-rs/pull/1
[PR #2]: https://github.com/kjanat/shellcheck-rs/pull/2
[`0c9cb40`]: https://github.com/kjanat/shellcheck-rs/commit/0c9cb408023ad336c99b9778f40d85d7f1dd1dba
[`f0009d0`]: https://github.com/kjanat/shellcheck-rs/commit/f0009d075fb4815d01ff95f0a8fb3a024da960dd
<a name="idend"></a>
