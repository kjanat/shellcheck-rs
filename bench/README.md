# ShellCheck benchmark

Compares three implementations of ShellCheck on the same inputs, on the same
machine, in the same session, and reports the difference with confidence
intervals and significance tests instead of a single "×" number.

| candidate | what it is | how it gets here |
|---|---|---|
| `upstream` | koalaman's latest GitHub release (the reference) | installed by mise (`shellcheck` in `mise.toml`, aqua backend, checksum-verified, version pinned in `mise.lock`) |
| `rust-port` | the hand-written Rust port on branch `rust-port` | git worktree + `cargo build --release` with the rust toolchain in `mise.toml` |
| `h2r` | ShellCheck compiled from GHC Core to Rust on branch `h2r-compiler` | git worktree + that branch's own `mise.lock` (GHC 9.6.7, cabal, rust) + `cargo build --release -p rshellcheck`, which drives the whole extraction/lowering pipeline |

Everything lands under `.bench/` (git-ignored): `src/<name>` checkouts,
`target/<name>` cargo targets, `bin/<name>/shellcheck` + `manifest.json`,
`corpus/`, `results/<timestamp>/`.

## Running it

Requires [mise](https://mise.jdx.dev) and, for `h2r`, the system libraries
GHC links against (`libgmp-dev libnuma-dev zlib1g-dev pkg-config` on
Debian/Ubuntu). Everything else is installed by mise.

```sh
mise install            # hyperfine, uv, python, rust, shellcheck (pinned in mise.lock)
mise run bench          # build all three, generate the corpus, measure, report
```

Step by step:

```sh
mise run bench:candidates          # what each candidate resolves to, its cache key, built or not
mise run bench:build [name...]     # build/fetch; a candidate whose manifest key matches is skipped
mise run bench:corpus              # deterministic corpus -> .bench/corpus (seeded, checksummed)
mise run bench:run --rounds 5 --runs 10 --warmup 3 [--scenarios small,large] [--candidates upstream,h2r] [--pin 2] [--max-run-seconds 15]
mise run bench:analyze [results-dir]   # report.md, summary.json, plots/ next to run.json
mise run bench:clean
```

`bench/build.sh` is the same entry point CI uses; `BENCH_SHA_RUST_PORT=<sha>`
/ `BENCH_SHA_H2R=<sha>` pin a git candidate to a commit instead of its branch
head.

## What makes the numbers trustworthy

**Same inputs, same machine, same session.** All candidates run the identical
argument list on the identical files, from the same directory, in one job.
Numbers from different machines or different runs are never mixed; CI caches
*binaries*, not measurements.

**Pre-check before timing** (`bench/run.py`). Each candidate runs each
scenario once under a peak-RSS watchdog (physical RAM minus 1 GiB by default) and a timeout. A
crash, hang or blown cap excludes it from that scenario, and the report says
why. A candidate that is correct but takes longer than the per-run budget
(`--max-run-seconds`, 15 s default) is not sampled fifty times either; that
single run is reported, clearly marked, without an interval. Its stdout and
exit code are compared with the baseline's (JSON formats structurally). A
difference does not exclude it, but voids the comparison in the report: a
faster program that computes something else is not a faster ShellCheck.

**Interleaved, shuffled rounds.** hyperfine runs all runs of one command
before the next, so a slow drift of the machine (thermal state, page cache,
a background job) would land on whichever candidate went last. The runner
therefore does several rounds, re-shuffling the candidate order every round
from a seeded PRNG, and keeps each round's samples separate so the analysis
can test for that drift (Kruskal–Wallis across rounds). `-N` means no shell
in the measurement; `--output null` treats every candidate's stdout the same.

**One hyperfine process per candidate.** hyperfine reports memory from
`getrusage(RUSAGE_CHILDREN).ru_maxrss`, the maximum over *every* child that
hyperfine process has reaped so far, not per command. Several commands in one
invocation would therefore make each later command report at least the peak of
all earlier ones (a 220 MiB candidate that ran after a 767 MiB one shows 767).
So within a round the runner starts a separate hyperfine process for each
candidate (same `-N`, warm-up and run counts, same shuffled order, one export
`raw/roundNN-<scenario>-<candidate>.json` each) and the peak RSS in the report
is the candidate's own. Timing is unaffected. `analyze.py` repairs runs made
by the older one-process-per-round runner: it reports the lower of the
isolated pre-check peak and the per-round medians, and says so in the report.

**Statistics** (`bench/analyze.py`, numpy + scipy via `uv run`):

- per cell: n, mean, sd, CV, median, MAD, min/max, p5/p95, **95 % BCa
  bootstrap intervals** (10 000 resamples) for the mean and the median, per-candidate peak RSS;
- per comparison: **speed-up with a 95 % percentile-bootstrap interval**
  (means and medians), **Mann–Whitney U** (primary: timing distributions are
  skewed), **Welch's t-test**, **Cliff's δ** with the usual magnitude labels,
  **Hedges' g**;
- **Holm correction** across every comparison in the report, one family per
  test, so a dozen scenarios do not manufacture a "significant" result;
- a verdict only when the Holm-adjusted Mann–Whitney p < 0.05 *and* the
  speed-up interval excludes 1; otherwise "no significant difference", with
  the interval showing how much could hide there;
- quality flags: CV > 10 %, > 5 % Tukey outliers, round drift (p < 0.01),
  < 20 samples, output mismatch, excluded.

The corpus (`bench/corpus.py`) is generated, not checked in: realistic-ish
bash assembled from a fixed set of blocks with seeded identifiers, mostly
wrapped in functions the way real scripts of that size are, about a third of
the blocks carrying classic findings. Its checksum is in every `run.json`.
Scenarios are in `bench/scenarios.toml`.

## Tests

`mise run bench:selftest` (`uv run bench/analyze.py --selftest`) feeds
synthetic runs with cumulative per-round memory values, and runs with isolated
ones, through the analysis and checks that the reported peak RSS of every
candidate equals its true isolated value. It does not need hyperfine or any
built candidate and takes a few seconds.

## CI

`.github/workflows/bench.yml` runs on pushes to `bench` that touch the
harness, and on demand (`workflow_dispatch` with rounds/runs/warmup/scenarios).

1. `resolve` pins every candidate (branch → commit, release → the version in
   `mise.lock`) and derives a **content key** = sha256(name, kind, ref, pin,
   `bench/build.sh`, the candidate's build script, platform).
2. `build` (one job per candidate) restores `.bench/bin/<name>` from the
   Actions cache under `bench-bin-<name>-<key>`. On a hit it uploads the
   binary and is done in seconds, so the h2r pipeline only reruns when the
   `h2r-compiler` branch, the build script or the platform changes. On a miss
   it also restores the candidate's intermediate layers (mise tool installs,
   cargo registry and target, cabal store and index) with `restore-keys`
   fallbacks, builds, and saves both caches.
3. `bench` downloads the three artifacts and runs corpus → run → analyze on
   one runner. The report goes to the job summary; `run.json`, `summary.json`,
   the per-round hyperfine exports, pre-check outputs/diffs and plots are the
   `bench-results` artifact.

GitHub Actions runners are shared VMs: expect a few percent of noise, which is
exactly what the intervals and flags are there to show. For a decision that
matters, run it on a quiet machine with `--pin` and more rounds.
