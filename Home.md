<a name="idtop"></a>

# shellcheck-rs knowledge base

`kjanat/shellcheck-rs` ships `rshellcheck`, a Rust port of [koalaman/shellcheck](https://github.com/koalaman/shellcheck), as GitHub release archives, npm and PyPI packages, container images, a Go installer and WASM bindings for JavaScript, Python and Go. This wiki records how the repository is laid out, how parity with the Haskell original is proven, how versions are shipped, and what is still open.

| Branch         | What it is                                                                                                                                                                                                                                |
| -------------- | ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `master`       | The Rust port: `crates/`, bindings, release pipeline, validity matrix, parity documents. `UPSTREAM.md` names the pinned upstream revision; the [releases page](https://github.com/kjanat/shellcheck-rs/releases) lists what is published. |
| `bench`        | The benchmark harness. Candidates: the latest upstream release binary, upstream `master` HEAD built with Cabal (the baseline), `rshellcheck` from `master`, `h2r`.                                                                        |
| `h2r-compiler` | A Haskell-to-Rust compiler that compiled all of ShellCheck through GHC Core. Finished. Output byte-identical to upstream; about 8× slower.                                                                                                |
| `wiki`         | These pages, mirrored into the wiki repository on push.                                                                                                                                                                                   |

## Pages

- [[Repository Overview|01 Repository overview]]: layout of `master`, branches, tags, CI workflows, toolchain, licences.
- [[Rust Port|02 Rust port]]: crates, the source map from Haskell to Rust, test conventions, the `rshellcheck` command, the library, the WASM module and bindings, the native launchers.
- [[Additional Diagnostics|03 Additional diagnostics]]: SC9001, SC9002, RSC1001, json1 `sources`, parser messages, the SC2064 and SC2164 differences.
- [[Conformance and Parity|04 Conformance and parity]]: the reference binary, the `conformance` commands, the frozen corpus and snapshot, the divergence policy, the five deviation classes, the parity documents, moving the tracked revision.
- [[Validity Matrix|05 Validity matrix]]: 17 shells in 43 cells, specs and outcomes, the runner, the images, the `shells.yml` workflow.
- [[Releases and Distributions|06 Releases and distributions]]: version policy, the 15 targets, running and resuming a publication, assets and verification, every registry, trusted publishing, the `upstream-<version>` aliases.
- [[Performance|07 Performance]]: the measurements in `rust/PERF.md`, the method, the open work packages.
- [[Benchmark Harness|08 Benchmark harness]]: the `bench` branch: candidates, commands, workloads, measurement rules, reading the report, CI caching.
- [[H2R Compiler|09 H2R compiler]]: the finished compiler experiment: pipeline, crates, milestones, why it stopped.
- [[Working Method|10 Working method]]: build and test commands, rules for a change, issue handling, measuring, environment facts.
- [[Open Items|11 Open items]]: open divergences, the open boxes of issues #3 and #4, document gaps, pending work packages.

## The one-paragraph summary

`rshellcheck` reproduces ShellCheck module by module in Rust. The `conformance` crate holds it to the reference revision: a gate that replays every extracted `prop_` script through both tools, a seeded fuzzer, and an offline behaviour snapshot. The Rust code deviates only through classes the comparison can prove from the AST or from a shell's own verdict, and `PARITY-NOTES.md` records every one. A validity matrix runs each diagnostic's reproducer in 43 shell builds. A claim about a shell is proven by executing it. Version numbers are the project's own from 1.0.0. One workflow builds 15 targets, signs them with Sigstore through GitHub OIDC, and publishes archives, npm and PyPI packages, container images and a Go installer. The `upstream-<version>` aliases name the newest `rshellcheck` version built from each ShellCheck version.

<a name="idend"></a>
