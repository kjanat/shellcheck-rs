# ShellCheck benchmark

Compare upstream ShellCheck with the handwritten Rust port and the GHC Core → Rust implementation. Measure output agreement, runtime, and peak memory on identical workloads, with uncertainty estimates and a compact report showing where to investigate next.

| Candidate   | Source                                   |
| ----------- | ---------------------------------------- |
| `upstream`  | ShellCheck release pinned by `mise.lock` |
| `rust-port` | `rust-port` branch                       |
| `h2r`       | `h2r-compiler` branch                    |

Requires Linux, [mise](https://mise.jdx.dev), git, and GNU time (`/usr/bin/time`). For a cold h2r build, install GHC's system dependencies (`libgmp-dev libnuma-dev zlib1g-dev pkg-config` on Debian/Ubuntu). The first h2r preparation can take several hours.

```sh
mise install
uv run bench
```

## Work independently

```sh
uv run bench prepare                      # resolve exact revisions; reuse or build
uv run bench corpus --out .bench/corpus    # generate repeatable workloads
uv run bench run                           # measure prepared binaries; no compilation
uv run bench report .bench/results/<run>   # report from recorded samples; no compilation
```

`bench` composes those stages. `mise run bench` invokes the same command. Each stage has `--help`.

For a focused run:

```sh
uv run bench run --candidates upstream,rust-port --scenarios startup,small \
  --rounds 5 --runs 10 --warmup 3 --pin 2
```

Prepare an already-built binary or a local checkout:

```sh
uv run bench prepare --binary h2r=/path/to/rshellcheck
uv run bench prepare --candidates h2r --source h2r=ports/h2r
uv run bench prepare --verify
```

Explicit local binaries are labelled as supplied binaries. A local checkout records its revision, modified state, and source fingerprint. Preparation leaves that checkout's changes intact. Supply `--binary` and `--source` together when you can attest that the binary was built from that source. Paths and candidate names are defined in `src/bench/candidates.toml`.

## Read the report

The report starts with correctness failures, reliable runtime priorities, and observed memory costs. Its table shows each workload's output agreement, median time, runtime ratio with a 95% interval, peak RSS, memory ratio, and measurement status.

Both ratios are **candidate ÷ upstream**: `2×` means twice the cost; `0.5×` means half. Output differences have links to diffs and earn no speed verdict. Noisy, drifting, or undersampled timings request another measurement. A single over-budget pre-check run is labelled separately, without a confidence interval.

CI publishes its summary after uploading `bench-results`. Evidence links use that artifact's download URL and show the file path to open after extracting the ZIP. The bundled `report.md` keeps relative links for local reading; candidate and source revisions link directly to GitHub.

If a candidate exceeds its batch budget during repeated timing, the remaining candidates and workloads continue. Its completed raw samples remain available, and its report uses the initial full sweep as a single observation with the timeout reason, without a confidence interval or winner badge. Incomplete Hyperfine exports are kept as `.incomplete` files.

Workloads cover startup, small/medium/large scripts, JSON formatting, and a batch of 120 files. They are generated from a fixed seed and checked against their checksums before timing. These are controlled workloads; their results do not establish performance on every real script.

## Omarchy: real shell workloads

CI also runs [Omarchy](https://github.com/omacom/omarchy) at the exact commit in [corpora.toml](src/bench/corpora.toml). The pinned snapshot contains **1,228 shell files and 119,468 lines**. Separate workloads cover runtime commands, installation scripts, migrations, tests, other shell files, the largest command, and the whole corpus in GCC and JSON formats. Test scripts are analyzed as source files; none of the Omarchy scripts are executed.

```sh
uv run bench corpus --omarchy --out .bench/corpus
uv run bench run --scenarios omarchy-commands,omarchy-installation,omarchy-migrations
uv run bench report .bench/results/<run>
```

Use `uv run bench --omarchy` to compose preparation, corpus import, measurement, and reporting. An existing clean checkout at the pinned commit can supply the inputs with `bench corpus --omarchy --omarchy-source /path/to/omarchy --out .bench/corpus`; otherwise the importer uses `gh repo clone` and caches the checkout under `.bench/corpora/`. Authentication follows the normal `gh` configuration; CI supplies its read-only token.

Selection includes tracked shell extensions and shell shebangs, even without execute permission, plus the explicit Bash setup, UWSM, mkinitcpio, and Limine source patterns in `corpora.toml`. Readline `inputrc`, symlinks, and other languages are excluded. Every selected file gets a checksum. Reports show the source commit as a hyperlink, workload purpose, exact file and line counts, output diffs, and observed winners qualified by measurement status. Glob expansion uses the recorded input inventory, so unrelated files cannot enter a timed batch.

Routine CI runs **four shuffled rounds of five timed runs, with one warm-up per round**, and repeats only workload/candidate pairs whose initial sweep takes at most **two seconds**. Upstream and the handwritten Rust port check every workload, including complete GCC and JSON sweeps of all 1,228 Omarchy files. Expensive completed workloads retain their timing, RSS, output, and diffs as single observations, without confidence intervals. Twenty samples remain available for cheaper workloads; noise and drift flags still qualify their results.

**h2r has a total measurement budget of 10 minutes**, including initial checks, warm-ups and timed samples across all workloads. Its complete Omarchy GCC sweep runs first, before overlapping groups can consume the budget. Every later process gets only the remaining allowance; reaching the cap kills the process group and skips subsequent h2r work. Reports show budget-limited and skipped rows explicitly. If the full sweep itself reaches the cap, coverage is incomplete; no successful sweep or output agreement is claimed. Other candidates continue. Compilation and cache restoration remain separate. `--h2r-budget-seconds` defaults to 600 locally, and CI explicitly sets 600.

Local defaults retain five rounds, ten timed runs, and three warm-ups, with sampling budgets of **60 seconds** for Omarchy and **15 seconds** for synthetic workloads. `--max-run-seconds` overrides all workload budgets; workflow inputs allow an explicitly larger benchmark. Initial output/RSS sweeps have a separate hard timeout: 20 minutes when Omarchy workloads are selected, or 10 minutes for synthetic-only runs; `--timeout` overrides that limit. Corpus changes do not invalidate candidate binaries; CI caches the pinned Omarchy source separately.

The previous CI run spent **25 minutes** on h2r's initial checks alone. With the total h2r cap and routine sampling policy, its recorded timings predict about **17 minutes of measurement**, or roughly **20–25 minutes including setup and runner variation**, with binary cache hits. This is an estimate, not a completed CI result. Uncached h2r compilation adds its separate build time.

Every candidate runs on the same inputs, in shuffled rounds, under its own hyperfine process so peak RSS belongs to that candidate. Verdicts use seeded bootstrap intervals and Holm-adjusted Mann–Whitney tests. Complete statistics and quality flags stay in `summary.json`.

Preparation, builds, workloads, and runs live under ignored `.bench/`. Each completed run contains:

```text
run.json       immutable samples, settings, environment, and candidate identities
summary.json   derived statistics and quality flags
report.md      compact comparison and investigation priorities
raw/           hyperfine exports
precheck/      outputs, errors, and diffs
```

`bench report` regenerates the report and statistics from `run.json`. Add `--plots` after `uv sync --extra plots` for optional timing plots. Archive a complete run under `results/`. The historical `2026-09-28-local` archive has no raw `run.json` and remains a historical snapshot.

## Expensive builds and caching

Preparation resolves refs once and builds the exact revision. Completed binaries and manifests are cached by source identity, platform/ABI, locked toolchain, and preparation recipe. A valid binary cache hit skips compilation. Changing report code or workloads does not invalidate candidate builds.

Tool versions come from the candidate's lockfile, with the harness lockfile supplying missing tools (the handwritten port currently has no lockfile). Builds use two Cargo workers by default. Prepared binaries have content-addressed paths, so preparing a new revision preserves binaries referenced by earlier runs.

Candidate toolchain hooks inherit locked mode and skip unrelated task auto-installs. Preparation checks source identity after toolchain setup, dependency preparation, and compilation; failures identify changed paths and publish no binary.

Compatible intermediate Cargo, h2r extraction, and Cabal state survives between builds at stable paths. Changed inputs may invalidate an entire extraction stage; restoring a cache does not guarantee a cheap rebuild. Failed builds retain their intermediate state and publish no completed binary.

CI resolves candidates, prepares them in separate jobs, and measures all three together on one runner. It caches finished binaries separately from compatible build layers and dependency downloads, and preserves partial build state when failure handling can finish. It does not cancel in-progress builds on a new benchmark push.

## Development

```sh
uv run python -m unittest discover -s tests -v
uv run ruff check src tests
uv run ty check
actionlint .github/workflows/bench.yml
dprint check
```

See [the architecture decisions](docs/design.md) for artifact contracts and cache boundaries.
