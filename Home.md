<a name="idtop"></a>

# shellcheck-rs knowledge base

`kjanat/shellcheck-rs` ships `rshellcheck`, a Rust port of [koalaman/shellcheck](https://github.com/koalaman/shellcheck), as GitHub release archives, npm and PyPI packages, container images, a Go installer and WASM bindings for JavaScript, Python and Go. This wiki records how the repository is laid out, how parity with upstream is proven, how releases are made, and what is still open.

| Branch         | What it is                                                                               | State (2026-10-15)                                                                                                                          |
| -------------- | ---------------------------------------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------- |
| `master`       | The Rust port: `crates/`, bindings, release pipeline, validity matrix, parity documents. | Upstream pin `c36c85a05ed3` (ShellCheck 0.11.0 line). Release `rshellcheck-v1.0.0` published 2026-10-15 to GitHub, npm, PyPI and ghcr.io.   |
| `bench`        | The benchmark harness comparing upstream, the port and the H2R program.                  | Candidates: the latest upstream release binary, upstream `master` HEAD built with Cabal (the baseline), `rshellcheck` from `master`, `h2r`. |
| `h2r-compiler` | A Haskell-to-Rust compiler that compiled all of ShellCheck through GHC Core.             | Finished. Head `d64c96bd` (2026-10-03). Output byte-identical to upstream; about 8× slower.                                                 |
| `wiki`         | These pages, mirrored into the wiki repository on push.                                  |                                                                                                                                             |

## Pages

- [[Repository Overview|01 Repository overview]]: layout of `master`, branches, tags, CI workflows, toolchain, licences.
- [[Rust Port|02 Rust port]]: crates, the source map from Haskell to Rust, test conventions, the `rshellcheck` command, the library, the WASM module and bindings, the native launchers.
- [[Additional Diagnostics|03 Additional diagnostics]]: SC9001, SC9002, RSC1001, json1 `sources`, parser messages, the SC2064 and SC2164 differences.
- [[Conformance and Parity|04 Conformance and parity]]: the oracle, the harness commands, the frozen corpus and snapshot, the divergence policy, the five deviation classes, the parity documents, syncing upstream.
- [[Validity Matrix|05 Validity matrix]]: 17 shells in 43 cells, specs and outcomes, the runner, the images, the `shells.yml` workflow.
- [[Releases and Distributions|06 Releases and distributions]]: version policy, the 15 targets, running and resuming a release, assets and verification, every registry, trusted publishing, upstream aliases.
- [[Performance|07 Performance]]: the measurements in `rust/PERF.md`, the method, the open work packages.
- [[Benchmark Harness|08 Benchmark harness]]: the `bench` branch: candidates, commands, workloads, measurement rules, reading the report, CI caching.
- [[H2R Compiler|09 H2R compiler]]: the finished compiler experiment: pipeline, crates, milestones, why it stopped.
- [[Working Method|10 Working method]]: build and test commands, rules for a change, issue handling, measuring, environment facts.
- [[Open Items|11 Open items]]: open divergences, the open boxes of issues #3 and #4, document gaps, pending work packages.

## The one-paragraph summary

The port reproduces ShellCheck module by module in Rust and is held to the pinned upstream revision by a differential harness: a gate that replays every extracted upstream property through both tools, a seeded fuzzer, and an offline behaviour snapshot. The port deviates only through classes the harness can prove from the AST or from a shell's own verdict, and every deviation is written down in `PARITY-NOTES.md`. A validity matrix runs each diagnostic's reproducer in 43 shell builds, so a claim about a shell is proven by executing it. Releases are versioned independently of upstream from 1.0.0; one workflow builds 15 targets, signs them with Sigstore through GitHub OIDC, and publishes archives, npm and PyPI packages, container images and a Go installer, with `upstream-<version>` aliases naming the newest port release of each upstream version.

<a name="idend"></a>
