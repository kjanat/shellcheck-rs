<a name="idtop"></a>

# 8 Environment and pitfalls

Concrete facts about the cloud container the work was done in, and the mistakes made along the way. Paths assume the repository at `/home/user/shellcheck-rs` with the bench layout under `.bench/`.

## 8.1 Useful paths and commands

| what                                                       | where / how                                                                                                                                                                                |
| ---------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ |
| GHC oracle binary (built by the h2r `hs-shellcheck` layer) | `.bench/target/h2r/h2r/hs-shellcheck/build/dist-newstyle/build/x86_64-linux/ghc-9.6.7/ShellCheck-0.11.0/x/shellcheck/build/shellcheck/shellcheck`                                          |
| rust-port release binaries                                 | `.bench/target/rust-port/release/{rshellcheck,conformance}` (`CARGO_TARGET_DIR=.bench/target/rust-port cargo build --release`)                                                             |
| rust-port test target                                      | `.bench/target/rust-port-tests`                                                                                                                                                            |
| h2r release target (7.6 GB, holds the oracle too; keep)    | `.bench/target/h2r`                                                                                                                                                                        |
| h2r workspace-test target (4 GB, deletable)                | `.bench/target/h2r-tests`                                                                                                                                                                  |
| bench corpus                                               | `.bench/corpus/{startup,small,medium,large}.sh`, `.bench/corpus/many/*.sh` (`mise run bench:corpus` on the bench branch)                                                                   |
| per-round h2r binaries kept for A/B                        | `.bench/bin/h2r-wp14/shellcheck` etc.                                                                                                                                                      |
| hyperfine on rust-port (not in its mise.toml)              | `mise exec hyperfine@1.20.0 -- hyperfine -N -w 2 -r 10 -i "<cmd>" ...`                                                                                                                     |
| peak RSS of one run (no `/usr/bin/time` in the container)  | Python: `os.fork` + `os.execv`, `os.wait4(pid, 0)[2].ru_maxrss // 1024` MiB                                                                                                                |
| callgrind                                                  | ``valgrind --tool=callgrind --callgrind-out-file=OUT BIN -f gcc /abs/path/script.sh >/dev/null``; totals from ``grep '^totals' OUT``; `callgrind_annotate [--inclusive=yes] [--tree=caller | calling] OUT` |
| dprint on rust-port                                        | `mise exec -- dprint check` / `fmt` (`dprint` itself is not on PATH; `~/.local/share/mise/installs/dprint/<ver>/dprint` works too)                                                         |
| wait for a background job without polling                  | `tail --pid=<PID> -f /dev/null` (the container's permission layer blocks foreground `sleep`)                                                                                               |

Disk: the writable allowance is per session; `df` shows ~7 GB free after the h2r builds. The permission classifier refused `rm -rf .bench/target/h2r-tests` and `git worktree remove --force` for the 18 finished agent worktrees under `.claude/worktrees` (107 MB) as irreversible destruction; those are left for a human.

**[⬆ Top](#idtop)**

## 8.2 Pitfalls met, and the fix

- **Valgrind exited immediately** on the rust-port binary: a relative script path with a background cwd reset. Use absolute paths in every background command.
- **`mise exec -- hyperfine` printed nothing** on rust-port: hyperfine is not in that branch's `mise.toml`. Use `mise exec hyperfine@1.20.0 -- hyperfine`.
- **hyperfine `-N` with a glob** (`many/*.sh`) runs the literal string, no shell expansion: 1.9 ms "measurements". Drop `-N` for globbed scenarios or expand the glob beforehand (the bench harness expands it).
- **`pkill -f` with a broad pattern killed the monitoring shell itself.** Kill by PID.
- **Stale `compiler/conformance/run-*` directories** on rust-port came from the h2r branch's gitignore not applying; remove them before `git status` checks.
- **Rebuilding h2r prematurely**: a runtime text edit was pasted into the generated crates and triggered a rebuild before all packages were in. Defer rebuilds until the batch is complete.
- **`callgrind_annotate --inclusive=yes`** reports > 100 % for recursive frames (`read_term_more'2` at 5417 %, `stack_analysis'2` at 20 % when it was 1 %). Use the non-recursive caller's row.
- **`conformance bench`'s `params-other` and `resolve`** are residuals and jump by ±50 % between runs; do not chase them.
- **`im_rc::OrdMap::union` is not left-biased** when the left operand is smaller (it keeps the other map's value), contrary to its docs. `cfg_analysis::union_left` exists for that reason.
- **Empty `im_rc::OrdMap`s allocate ~2 KB each**; four per state were 68 % of the heap until shared.
- **A docs-only push can fail CI** on rust-port because the fuzz seed is the run number. Fix the divergence (it is real), do not retry.
- **Agents' worktrees start on `master`**, not the feature branch; brief them to reset to the branch first.
- **Agents share the scratchpad**; two overwrote the same `parity.sh`. Prefix per agent.
- **Measuring while agents compile** gives ±30 % wall-time noise; use instruction counts or wait.
- **The stop hook demands a push of every unpushed commit** at the end of a turn; verify first, then push (a verified agent commit is safe to push alone since CI runs the full gate).
- **Peak RSS from hyperfine with several commands** is cumulative (see [[Benchmark Harness|06 Benchmark harness]]); one process per candidate.
- **Startup wall time at 3 ms has σ ≈ 1 ms**; compare startup by instruction count (3.05 M at `32690b5`), not by hyperfine.

**[⬆ Top](#idtop)**

## 8.3 Session rules that were stated by the user and should be kept

- Never build and test (or measure) simultaneously.
- Work only on the branch named for the task; the bench branch is touched only when asked (an explicit "Go ahead" covered the peak-RSS fix).
- Webhook subscriptions are enough for PR watching; do not keep hourly check-ins alive.
- No model names in anything pushed to the repository.

**[⬆ Top](#idtop)**

<a name="idend"></a>
