<a name="idtop"></a>

# 6 Benchmark harness

*Branch `bench`.*

Compares `upstream` (koalaman's release, installed by mise from `mise.lock`), `rust-port` (branch, cargo release build) and `h2r` (branch, its own `mise.lock` with GHC 9.6.7, `cargo build --release -p rshellcheck` drives the whole pipeline) on the same inputs, machine and session, and reports differences with confidence intervals and significance tests instead of a single "×". `bench/README.md` is the full description.

## 6.1 Files

| file                                               | role                                                                                                                                                                                                    |
| -------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `bench/candidates.toml`, `bench/candidates.py`     | what each candidate is, how it is resolved (branch → commit, release → version) and its cache key                                                                                                       |
| `bench/build.sh`, `bench/build/{h2r,rust-port}.sh` | build/fetch a candidate into `.bench/bin/<name>/shellcheck` + `manifest.json`; same entry point as CI; `BENCH_SHA_RUST_PORT`/`BENCH_SHA_H2R` pin a commit                                               |
| `bench/corpus.py`                                  | deterministic generated corpus (seed 20260928): startup (2 lines), small (~150), medium (~1500), large (~4000), `many/` (120 small scripts); checksum recorded in every `run.json`                      |
| `bench/scenarios.toml`                             | startup, small, medium, large, large-json1, many; all `-f gcc` except large-json1                                                                                                                       |
| `bench/run.py`                                     | pre-check, then shuffled rounds of hyperfine `-N`; one hyperfine process per candidate per round; exports `raw/roundNN-<scenario>-<candidate>.json`; `run.json` version 2 with `config.memory_isolated` |
| `bench/analyze.py`                                 | statistics, `report.md`, `summary.json`, plots; `--selftest`                                                                                                                                            |
| `.github/workflows/bench.yml`                      | resolve → build (one job per candidate, content-keyed binary cache) → bench on one runner                                                                                                               |
| `bench/results/2026-09-28-local/`                  | the first full local run, archived                                                                                                                                                                      |
| `mise.toml` tasks                                  | `bench`, `bench:candidates`, `bench:build`, `bench:corpus`, `bench:run`, `bench:analyze`, `bench:clean`, `bench:selftest`                                                                               |

Everything generated lands under `.bench/` (git-ignored): `src/<name>` worktrees, `target/<name>` cargo targets, `bin/<name>/`, `corpus/`, `results/<timestamp>/`.

**[⬆ Top](#idtop)**

## 6.2 What makes the numbers trustworthy

- **Same inputs, same machine, same session**; CI caches binaries, never measurements.
- **Pre-check before timing**: each candidate runs each scenario once under a peak-RSS watchdog (physical RAM − 1 GiB by default) and a timeout; a crash, hang or blown cap excludes it with the reason; over the per-run budget (`--max-run-seconds`, 15 s) means one reported run, marked, no interval. Stdout and exit code are compared with the baseline (JSON structurally); a mismatch voids the comparison ("a faster program that computes something else is not a faster ShellCheck").
- **Interleaved, shuffled rounds** from a seeded PRNG, samples kept per round so drift can be tested (Kruskal–Wallis across rounds).
- **One hyperfine process per candidate**: hyperfine reports memory from `getrusage(RUSAGE_CHILDREN).ru_maxrss`, the cumulative maximum over every child it has reaped, so several commands in one invocation make each later command report at least the peak of all earlier ones. This was a real bug in the first harness version (a 220 MiB candidate after a 767 MiB one showed 767); fixed in `04583c5`, with `analyze.py` repairing old runs (lower of isolated pre-check peak and per-round medians) and `bench:selftest` guarding it.
- **Statistics** (numpy + scipy via `uv run`): per cell n, mean, sd, CV, median, MAD, min/max, p5/p95, 95 % BCa bootstrap intervals (10 000 resamples) for mean and median, peak RSS; per comparison speed-up with percentile-bootstrap interval, Mann–Whitney U (primary), Welch's t, Cliff's δ, Hedges' g; Holm correction across all comparisons; a verdict only when adjusted p < 0.05 and the interval excludes 1. Flags: CV > 10 %, > 5 % Tukey outliers, round drift, < 20 samples, output mismatch, excluded.

**[⬆ Top](#idtop)**

## 6.3 CI design

1. `resolve` pins candidates and derives a content key = sha256(name, kind, ref, pin, `bench/build.sh`, the candidate's build script, platform).
2. `build` per candidate restores `.bench/bin/<name>` from the Actions cache under `bench-bin-<name>-<key>`; on a hit it is done in seconds, so the 30-minute h2r pipeline reruns only when its branch, build script or platform changes. On a miss it restores intermediate layers (mise installs, cargo registry/target, cabal store) with `restore-keys` fallbacks, builds, saves both.
3. `bench` downloads the three binaries and runs corpus → run → analyze; the report is the job summary; `run.json`, `summary.json`, per-round exports, pre-check outputs/diffs and plots are the `bench-results` artifact.

Workflow fixes that were needed: keep a runner-provided ghcup from shadowing mise's GHC in the h2r build; prefetch the h2r plugin's deps; tolerate lockfile churn; do not re-run the workflow for archived reports; default the memory cap to RAM − 1 GiB.

**[⬆ Top](#idtop)**

## 6.4 Results

**2026-09-28 local** (rust-port `5d3fe06`, h2r `1e14647`, 4 vCPU Xeon 2.1 GHz): rust-port 1.26× faster than upstream on small, 2.01× on many, 0.60× on startup, 0.50× on medium (1374 MiB), excluded on large (> 4 GiB); h2r 0.12× on startup, 0.05× on small, single over-budget runs on medium (26 s) and many (79 s), excluded on large.

**2026-10-02 CI** (h2r at `4fe2e71`, after WP1–WP14): h2r about 8× slower than upstream instead of 20×; this run also exposed the cumulative peak-RSS column bug above.

**After the rust-port rounds** (local container, not yet a bench-branch CI run): rust-port 6.5× (small), 8.4× (medium), 13.1× (large), 6.7× (many) faster than upstream, RSS 53 / 122 MiB on medium / large. The next bench CI run against `rust-port` head `0c9cb40` will show this on the shared runner (expect the container's numbers scaled by ~2.4×).

**[⬆ Top](#idtop)**

## 6.5 Reading the report

Speed-up = baseline mean time ÷ candidate mean time, > 1 is faster, with its interval; bold means significant after Holm. "excluded" names the cap that was hit; "single run, over budget" is a correct but slow candidate; "output vs baseline" must say identical for the comparison to mean anything. GitHub runners are shared VMs: expect a few percent of noise, which the intervals and flags are there to show. For a decision that matters, run locally with `--pin` and more rounds.

**[⬆ Top](#idtop)**

<a name="idend"></a>
