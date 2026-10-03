# Binary conformance harness

Adapted from `rust-port` commit `5d3fe06964ee0bea47505e28de8a2dddbe281088`, `rust/crates/conformance`: the corpus extractor (including optional checks and coverage accounting), deterministic shell generator/mutator, and binary fingerprinting. Corpus tests are retained with the new checkout-relative path. Generator truncation now respects UTF-8 boundaries.

The in-process port adapter is replaced with two external binaries. Neither `shellcheck-rs` nor `shellcheck-cli` is a dependency. Port-specific deviation allowlists, parser-internal audits, phase benchmarks, snapshot baselines and the port-coupled shrinker are not copied. This harness currently checks the `json1` CLI path, not every formatter or CLI option.

From the repository root:

```sh
mise run conformance:corpus
mise run conformance --candidate path/to/emitted-shellcheck
mise run conformance:fuzz --candidate path/to/emitted-shellcheck --seed 1 --iterations 100 --all-shells
```

The default oracle is the existing `compiler/matrix/A/shellcheck`; override with `--oracle PATH`. No command builds a Haskell oracle or assumes that an emitted Rust binary exists. `--candidate` is mandatory for gate/fuzz. Use `--limit 10` for a corpus smoke test (optional-check examples still run). `--shell bash` selects one dialect; `--all-shells` checks inferred, bash, sh, dash, ksh and busybox. Fuzz inputs are analyzed, never executed as scripts.

Comparison includes the full JSON document (diagnostic order, codes, severity, spans, messages and replacements), exit status and stderr. Both binaries see the same input filename, `--norc`, a removed `SHELLCHECK_OPTS`, and a fixed locale. Processes have a configurable `--timeout` in seconds (default 10). Timeouts, signals, unexpected statuses and malformed JSON are errors even when both sides fail identically. Oracle version must match `ShellCheck.cabal`; that check alone does not establish source identity.

Exit codes: **0** agreement, **1** differences, **2** harness/checker errors. Runs retain `report.json`, failure inputs and both outputs in `compiler/conformance/run-<pid>/` (gitignored). The report includes binary paths, non-cryptographic fingerprints and fuzz seed. Identical fingerprints are explicitly labelled a self-check, not compiler conformance. Successful cases are counted; failing scripts and outputs are embedded in the report.

Validation with the existing format-5 and format-6 Haskell binaries: 2,026 extracted properties plus 22 optional-check cases agree; 226 properties have no replayable shell snippet and are reported as uncovered. A 20-input seeded fuzz smoke test across six dialect settings also agrees (120 comparisons). These runs validate the harness and Haskell build consistency, not the future compiler's output. Eighteen unit tests cover extraction, generation, exact comparison, subprocess statuses and timeouts.
