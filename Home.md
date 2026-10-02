<a name="idtop"></a>

# shellcheck-rs knowledge base

`kjanat/shellcheck-rs` is a fork of [koalaman/shellcheck](https://github.com/koalaman/shellcheck) that carries three experiments on top of the upstream Haskell code. This wiki distils what was learned while building, measuring and optimising them, so that anyone (a person or an agent) can pick the work up without re-deriving it.

| branch         | what it is                                                                             | PR                                                   | state (2026-10-02)                                                                                                      |
| -------------- | -------------------------------------------------------------------------------------- | ---------------------------------------------------- | ----------------------------------------------------------------------------------------------------------------------- |
| `master`       | mirror of upstream ShellCheck (0.11.0 line, head `9af7ee2`)                            |                                                      | the oracle every experiment is gated against                                                                            |
| `rust-port`    | a hand-written, structurally faithful Rust port under `rust/`                          | [#1](https://github.com/kjanat/shellcheck-rs/pull/1) | byte-identical to upstream on every gate; 6–13× faster than upstream, 2–10× less memory                                 |
| `h2r-compiler` | a Haskell→Rust compiler that consumes GHC Core and emits Rust (`compiler/`, `crates/`) | [#2](https://github.com/kjanat/shellcheck-rs/pull/2) | compiles all of ShellCheck, output byte-identical; ~8× slower than upstream, floor reached for incremental runtime work |
| `bench`        | a statistically rigorous benchmark harness comparing the three (`bench/`)              |                                                      | runs in CI, results trustworthy including per-candidate peak RSS                                                        |

## Pages

- [[Repository Overview|01 Repository overview]] — layout, branches, PRs, CI, tooling and conventions shared by all branches.
- [[Rust Port|02 Rust port]] — architecture of the hand-written port, the conformance harness (gate, fuzz, shells, audit, snapshot, bench), parity documents, rules for changing it.
- [[Rust Port Performance|03 Rust port performance]] — the profiling story: what was slow, what was changed (WP-R0…WP-R4), the numbers, and what is next.
- [[H2R Compiler|04 H2R compiler]] — the Core-to-Rust compiler: pipeline, milestones, crates, mise tasks, limits.
- [[H2R Runtime Performance|05 H2R runtime performance]] — the runtime (`h2r-rt`) optimisation programme: representation, invariants, WP1–WP18, census results, why it hit a floor.
- [[Benchmark Harness|06 Benchmark harness]] — how the bench branch measures, why its numbers can be trusted, the results so far, and the peak-RSS bug it had.
- [[Working Method|07 Working method]] — how the optimisation rounds were run: PERF.md-driven work packages, cheap agents in worktrees, one rebuild per round, verification chains, hand-back format.
- [[Environment and Pitfalls|08 Environment and pitfalls]] — concrete paths, commands, tool quirks and mistakes made along the way, so they are not repeated.
- [[Open Items|09 Open items]] — everything that is pending or was deliberately left for later, per branch.

## The one-paragraph summary

Upstream ShellCheck is the oracle. Two routes were taken to a Rust binary: a hand port (`rust-port`) that mirrors the Haskell module by module and is held to byte-identical output by a differential harness (an extracted upstream property corpus plus a seeded fuzzer, both run against the GHC binary), and a compiler (`h2r-compiler`) that lets GHC do parsing, typing and optimisation and translates the resulting Core into Rust with a small lazy runtime. The hand port is now the faster program by a wide margin; the compiled program is correct but pays for emulating laziness and allocation without a GC. A third branch (`bench`) measures all three on the same machine in the same session, with bootstrap intervals, non-parametric tests and Holm correction, and its CI job caches binaries per candidate commit so a run costs minutes.

<a name="idend"></a>
