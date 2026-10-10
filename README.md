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

Workloads cover startup, small/medium/large scripts, JSON formatting, and a batch of 120 files. They are generated from a fixed seed and checked against their checksums before timing. These are controlled workloads; their results do not establish performance on every real script.

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
