<a name="idtop"></a>

# 8 Benchmark harness

Branch `bench`. A Python project that measures upstream ShellCheck, the Rust port and the H2R compiled program on identical workloads and reports differences with uncertainty. `README.md` and `docs/design.md` on the branch are the references.

## 8.1 Candidates

`src/bench/candidates.toml`:

| Candidate     | Source                                                                                                                                                                           |
| ------------- | -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `upstream`    | Repository `koalaman/shellcheck` at the revision `tools/oracle.json` pins on `master`, built with Cabal (`ShellCheck:exe:shellcheck`); needs ghcup, GHC and Cabal. The baseline. |
| `rshellcheck` | Repository `kjanat/shellcheck-rs`, ref `master`, package `shellcheck-cli`, built with Cargo.                                                                                     |
| `h2r`         | Repository `kjanat/shellcheck-rs`, ref `h2r-compiler`, package `rshellcheck`; needs ghcup, GHC, Cabal and Rust.                                                                  |

A candidate's `build` field selects the Cargo or Cabal recipe. Moving the pin in `tools/oracle.json` on `master` also moves the `upstream` ref here, so output parity is judged against the revision the port follows. 🏆 in a report marks the lowest median only when at least two candidates have matching output.

**[⬆ Top](#idtop)**

## 8.2 Commands

Requires Linux, mise, git and GNU time. A cold h2r build needs GHC's system libraries and can take several hours.

```sh
mise install
uv run bench                               # prepare, corpus, run, report
uv run bench prepare                       # resolve exact revisions; reuse or build
uv run bench corpus --out .bench/corpus    # generate repeatable workloads
uv run bench run                           # measure prepared binaries; no compilation
uv run bench report .bench/results/<run>   # report from recorded samples
```

`bench prepare --binary h2r=/path/to/rshellcheck` measures a supplied binary; `--source h2r=ports/h2r` builds a local checkout and records its revision and dirty state. The mise tasks `bench`, `bench:prepare`, `bench:run`, `bench:report`, `bench:corpus`, `bench:selftest`, `test` and `check` wrap the same commands. Everything generated lands under the ignored `.bench/` directory; archived runs live under `results/` (one archive, `2026-09-28-local`, with `report.md`, `summary.json` and plots).

**[⬆ Top](#idtop)**

## 8.3 Workloads

Generated workloads come from a fixed seed and are checksummed before timing: startup, small, medium and large scripts, JSON formatting, and a batch of 120 files. Scaling probes only; they do not stand for every real script.

[Omarchy](https://github.com/omacom/omarchy) at commit `077ac1da939de00d061c1035e1a1d00587a119b8` (pinned in `src/bench/corpora.toml`) supplies real scripts: 1,228 shell files, 119,468 lines. Separate workloads cover runtime commands, installation scripts, migrations, tests, other shell files, the largest command, and the whole corpus in GCC and JSON output. Selection takes tracked files with a shell extension or shell shebang plus the explicit Bash setup, UWSM, mkinitcpio and Limine patterns; `default/bash/inputrc` is excluded. None of the scripts is executed. `bench corpus --omarchy` imports the checkout through `gh repo clone` and caches it under `.bench/corpora/`.

**[⬆ Top](#idtop)**

## 8.4 Measurement rules

- Every candidate runs on the same inputs in shuffled rounds, each under its own hyperfine process. hyperfine reports `ru_maxrss` cumulatively over every child it reaped, so one process per candidate is what makes peak RSS belong to that candidate.
- A pre-check runs each candidate once per workload under a peak-RSS watchdog and a timeout and compares stdout and exit status with the baseline. Mismatched output earns no speed verdict.
- Verdicts use seeded bootstrap intervals and Holm-adjusted Mann–Whitney tests. Noisy, drifting or undersampled timings are flagged.
- Sampling budgets: 15 seconds for generated workloads, 60 seconds for Omarchy; `--max-run-seconds` overrides both. Initial sweeps have a separate hard timeout of 20 minutes with Omarchy and 10 minutes without.
- A candidate that exceeds its batch budget keeps its completed samples; its report row becomes a single observation with the timeout reason and no interval.
- Routine CI runs four shuffled rounds of five timed runs with one warm-up per round, and repeats only pairs whose initial sweep takes at most two seconds. Upstream and the Rust port check every workload including the full Omarchy sweeps.
- h2r has a total measurement budget of 600 seconds across all workloads. Its complete Omarchy GCC sweep runs first; reaching the cap kills the process group and skips later h2r work, and the report marks those rows.

**[⬆ Top](#idtop)**

## 8.5 Reading the report

The report opens with correctness failures, reliable runtime priorities and observed memory costs. Each row shows output agreement, median time, the runtime ratio with a 95 % interval, peak RSS, the memory ratio and the measurement status. Both ratios are candidate divided by upstream: `2×` means twice the cost, `0.5×` half. Output differences link to diffs. CI publishes the summary after uploading the `bench-results` artifact; evidence links point into that archive.

A run directory holds `run.json` (immutable samples, settings, environment, candidate identities), `summary.json` (statistics and flags), `report.md`, `raw/` (hyperfine exports) and `precheck/` (outputs, errors, diffs). `bench report` regenerates the report from `run.json` without compiling.

**[⬆ Top](#idtop)**

## 8.6 CI and caching

`.github/workflows/bench.yml` has three jobs: `resolve` pins candidate identities, `prepare` builds each candidate in its own job, `measure` runs all candidates together on one runner. Completed binaries are cached by source identity, platform, locked toolchain and preparation recipe; a hit skips compilation. A second cache keeps compatible intermediate state (Cargo artifacts, h2r layers, Cabal store, dependency downloads). Changing workloads or report code never invalidates candidate builds. The design document records these choices as ADR-001 to ADR-005.

**[⬆ Top](#idtop)**

<a name="idend"></a>
