<a name="idtop"></a>

# 7 Working method

How the optimisation rounds on both branches were organised. The method is the same on `h2r-compiler` and `rust-port`; only the costs differ (a 30-minute rebuild vs a 1-minute one).

## 7.1 A single living document per branch: PERF.md

`crates/h2r-rt/PERF.md` and `rust/PERF.md` each hold, in this order: measured facts (where the time goes, with the profiling commands and commit hashes), the invariants a change must keep, the verification loops cheapest first, and the **work packages**. A work package has a spec (what to change, in terms of representation, with the Haskell reference it must stay faithful to), an acceptance list (tests, gate, fuzz seeds, snapshot, byte parity, a callgrind or wall-time target), and, once done, an **"As built"** paragraph written by whoever did it (what was actually changed, what was decided against, the before/after numbers, any trap found). Negative results stay in the file (WP6, WP15, the forwarding scheme): a reader must not retry them by accident.

The document is written for someone who has not read the code and may be a cheaper model: it says which files, which functions, which cases, and what "done" looks like.

**[⬆ Top](#idtop)**

## 7.2 Measure first, pick packages from the profile

Each round begins with callgrind on the corpus (`valgrind --tool=callgrind`, totals + `callgrind_annotate` inclusive and self, `--tree=caller` for the hot ones) and, where memory matters, massif or `ru_maxrss`. The profile is pasted into PERF.md as a table with shares, and the packages are ranked by the share they can remove. Per-phase timers (`conformance bench`) and the microbench (`rt-instrs`) narrow where the general profile is coarse. Allocation *counts* (the h2r census) were the better guide than wall time once the sizes were small.

Rules of thumb that held: an O(n²) in a port of structurally-shared Haskell code is almost always a cloned persistent structure (BTreeMap/String clones); SipHash on integer keys is ~5–10 % whenever `HashMap<usize, _>` is on a hot path; "run every registered check on every node" is a dispatch bug, not a check cost; recursive frames in `callgrind_annotate --inclusive` lie.

**[⬆ Top](#idtop)**

## 7.3 Delegate packages to agents in isolated worktrees

Each package went to a subagent (`Agent` with `isolation: worktree`), cheaper models for mechanical packages (hasher, dispatch table), a stronger one for the representation change (WP-R2). Every brief contained: the PERF.md sections to read, the exact scope (files), what not to do (no algorithm changes, no new deps, do not restructure functions another agent is editing), absolute paths to the oracle and corpus, a **dedicated `CARGO_TARGET_DIR`** so parallel builds do not collide, the verification list in order with expected outputs, the baseline numbers, and the deliverable: one commit on the worktree branch, a `git format-patch` file in the scratchpad, an "As built" paragraph, and the exact verification outputs.

Observed: agents' worktrees were created from `master`, not the feature branch, so every agent had to `git reset --hard rust-port` first; say so in the brief. Agents overwrote each other's helper scripts in the shared scratchpad; give each a prefix. Agents reliably met acceptance targets when the spec named the cases to mirror; the one briefing error (misdescribing a divergence as an SC1054 parse failure) was caught by the agent reading the code, so always tell them to verify the brief against the source.

**[⬆ Top](#idtop)**

## 7.4 Integrate in a fixed order, verify once as a whole

Patches are applied with `git am --3way` in the order least-invasive first (R3 hasher, R4 dispatch, then R2 which touched the same file as R3; one conflict, resolved by taking R2's loop with R3's map types). Then **one** verification chain on the combined head, as a single background script with a log, waited on with `tail --pid` (no polling):

tests → release build → gate → fuzz (seed 0 ×2000, a wide seed ×4000) → snapshot → byte parity (sha256 of stdout for `-f gcc` and `-f json1` on every corpus script and the 120-file set) → callgrind totals medium/large → peak RSS (wait4) → hyperfine before/after/oracle on every scenario → per-phase bench → clippy, fmt, dprint.

Then the PERF.md "Round N landed" table, a commit, and a push. Each agent's commit was pushed as soon as its own verification was clean, so CI could run on it.

**[⬆ Top](#idtop)**

## 7.5 One rebuild per round, and never build while measuring

On h2r the 25–35-minute rebuild is the bottleneck, so packages were batched: fast loops per package (unit tests, Miri, emitter tests, microbench), one rebuild for the batch, one gate, one A/B. The standing rule from the user: **never run the rebuild concurrently with tests or measurements**; timing and RSS are measured only when nothing else is compiling. On rust-port the same rule applies to measurements: instruction counts are immune to load, wall-clock numbers are not.

**[⬆ Top](#idtop)**

## 7.6 A/B currency

Instruction counts (callgrind) are the primary before/after number: deterministic, comparable across sessions, not affected by other processes. Wall time (hyperfine `-N`, ≥ 10 runs with warm-up, `-i` for non-zero exit codes) and peak RSS are reported alongside, always with the oracle measured in the same session so ratios are comparable. Per-row "vs the binary before it" plus a cumulative line.

**[⬆ Top](#idtop)**

## 7.7 PR hygiene

PRs were watched through the server-side GitHub subscription (events wake the session; no polling, no hourly check-ins once the user said the webhook suffices). CI results were read from the check runs after each push. Bot comments (Socket dependency tables) were read and ignored when informational. Nothing was posted to the PRs unless necessary; the branch and PERF.md are the record.

**[⬆ Top](#idtop)**

## 7.8 Reporting

Every round ended with: what landed (commits), the verification chain's outputs, a before/after/oracle table, what the next round should do and why, and anything the user must decide or do (a dependency with a non-MIT license, a disk cleanup the agent was not allowed to perform).

**[⬆ Top](#idtop)**

<a name="idend"></a>
