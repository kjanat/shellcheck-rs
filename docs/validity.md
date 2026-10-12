# Validity matrix

The oracle proves the port equals upstream. The validity matrix proves a
diagnostic's claim by running its reproducer in real shells, one container per
shell and version.

## Pieces

| Path                               | Holds                                                                 |
| ---------------------------------- | --------------------------------------------------------------------- |
| `validity/matrix.toml`             | Every cell: shell, version, image, argv, mode, shipped flag.          |
| `validity/specs/SC<code>.toml`     | One spec per diagnostic: snippet, fix, claim, observable.             |
| `validity/outcomes.toml`           | Recorded outcome per spec per cell. Committed. Reviewed in diffs.     |
| `validity/REPORT.md`               | Generated from outcomes. Per code: where it reproduces, where not.    |
| `docker/shells/<shell>/Dockerfile` | Builds one interpreter from a pinned upstream tarball. `ARG VERSION`. |
| `.github/workflows/shells.yml`     | Builds and pushes images to GHCR. Runs the matrix weekly.             |
| `crates/conformance/src/validity/` | The runner. `cargo validity`.                                         |

## Cells

```toml
[[cell]]
shell   = "zsh"
version = "5.9"
image   = "ghcr.io/kjanat/shellcheck-rs/shell-zsh:5.9"
argv    = ["zsh", "-c", "emulate -R sh; . /dev/stdin"]
mode    = "emulate-sh"
shipped = false
dialect = "sh"
```

`shipped` says whether the port has a `--shell` value for this cell. `dialect`
names the port shell the cell stands in for when checking the snippet. An
unshipped cell with no stand-in leaves `dialect` out and skips the port
assertions.

Floor cells, all `shipped = true`: bash 3.2 4.0 4.2 4.4 5.0 5.1 5.2 5.3, dash
0.5.8 to 0.5.12, ksh 93u+ and the ksh93/ksh releases 1.0.0 to current,
busybox 1.30 to 1.37.

Unshipped cells: zsh native and emulate-sh, mksh, oksh, loksh, yash, posh,
bosh, FreeBSD sh, NetBSD sh, osh, brush, tcsh.

tcsh is the default root shell on TrueNAS CORE and FreeBSD. Its grammar is
unrelated to sh, so every POSIX spec records `unparsable` there. The cells
exist to record what a TrueNAS user running a script under the wrong shell
sees, and to hold csh specs once the port has a csh parser. TrueNAS SCALE
ships zsh for the admin account; the zsh cells cover it.

BSD sh cells build the FreeBSD and NetBSD `bin/sh` sources on Linux with the
upstream `libedit` and a small Makefile under `docker/shells/freebsd-sh/`
and `docker/shells/netbsd-sh/`. The source tarball is a pinned export of the
`bin/sh` tree from the release tag.

## Specs

```toml
code  = 2086
claim = "an unquoted expansion word-splits and globs"

[snippet]
script = 'x="a b"; printf "<%s>" $x; echo'

[fixed]
script = 'x="a b"; printf "<%s>" "$x"; echo'

[observe]
kind    = "stdout"
snippet = "<a><b>\n"
fixed   = "<a b>\n"
```

`observe.kind` is one of `stdout`, `status`, `stderr-contains`. A spec may
carry several `[[observe]]` blocks. Scripts read stdin and finish in under a
second.

Filesystem: the root is read-only and `/tmp` is a 16 MiB tmpfs. Each run gets
a fresh directory in `TMPDIR` and starts there. A spec that needs a missing
path uses `$TMPDIR/missing`; one that needs files creates them under
`$TMPDIR`. `cd` into a missing path fails without writing anything, so SC2164
style claims need no writes at all. Nothing outside `TMPDIR` is writable and
the directory is discarded after the run.

## Assertions per spec per cell

1. The shell parses both scripts.
2. The snippet produces `observe.snippet`.
3. The fixed script produces `observe.fixed`.
4. On a cell with `dialect`: the port reports `code` on the snippet.
5. On a cell with `dialect`: the port reports nothing with `code` on the fix.

## Outcomes

| Outcome      | Meaning                                                              |
| ------------ | -------------------------------------------------------------------- |
| `reproduces` | Assertions 1 to 3 hold. The claim is true on this shell and version. |
| `absent`     | Both scripts produce the fixed observable. The shell lacks the bug.  |
| `differs`    | Some other output. Recorded verbatim.                                |
| `unparsable` | The shell rejects the snippet or the fix.                            |
| `timeout`    | Exceeded the per-run limit.                                          |
| `port-miss`  | Assertion 4 or 5 failed.                                             |

`outcomes.toml` stores one row per spec per cell. Running with `--record`
rewrites it. Running without compares and reports every row that changed.

## Gate

- A shipped cell: any change from `reproduces` fails. `port-miss` fails.
- An unshipped cell: changes are reported, never fatal. The recorded outcome
  is the rule the dialect will ship with. `absent` on zsh for SC2086 means
  SC2086 is off in zsh native mode when that dialect lands.
- A spec with no `reproduces` cell at all fails: the claim is false
  everywhere we can test, and the diagnostic needs rethinking.

## Report

`REPORT.md` has one section per code:

```
## SC2086
Claim: an unquoted expansion word-splits and globs.
reproduces: bash 3.2–5.3, dash 0.5.8–0.5.12, ksh93 u+ 2020, busybox 1.30–1.37,
            zsh emulate-sh 5.9, mksh R59, yash 2.56, osh 0.24
absent:     zsh native 5.9
```

The report is generated from `outcomes.toml` and committed with it.

## Runner

`cargo validity [--record] [--cell <shell>[:<version>]] [--code <n>]`.

For each cell the runner starts one container and reuses it:

```sh
docker run -d --rm --network none --read-only --tmpfs /tmp:size=16m \
  --cap-drop ALL --pids-limit 64 --memory 256m --cpus 1 \
  --user 65534:65534 <image> sleep infinity
docker exec -i <id> <argv...> < script
```

Per-run limit 5 s. Scripts arrive on stdin. Nothing is mounted. The runner
pulls images from GHCR by digest recorded in `matrix.toml`; a missing image
marks the cell `missing` and the run continues.

Parsing happens with the shell's `-n` first where the shell has one. For
`emulate-sh` cells the parse step runs the same argv with `-n` appended.

## Images

One Dockerfile per shell under `docker/shells/`, parameterised by `VERSION`,
building from the upstream release tarball with its checksum pinned in the
Dockerfile. `shells.yml` builds the matrix in `matrix.toml`, pushes
`ghcr.io/kjanat/shellcheck-rs/shell-<shell>:<version>`, and writes the digest
back into `matrix.toml` in a pull request. Images rebuild only when their
Dockerfile or version changes.

## Reproducibility

Every input is pinned in the tree and every step is one command.

- `matrix.toml` records each image by digest. The runner pulls by digest and
  refuses a tag.
- Each Dockerfile pins the source tarball URL and its SHA-256. A rebuild from
  the same Dockerfile yields the same interpreter.
- `outcomes.toml` and `REPORT.md` are committed. A fresh checkout plus Docker
  reproduces them with `cargo validity --record` and `git diff` shows drift.
- The runner uses no host shell. A host without Docker fails the run with one
  message.
- Container clocks, locale and environment are fixed: `LC_ALL=C`, `TZ=UTC`,
  empty environment apart from `PATH`, `HOME=/tmp`.
- Spec execution order is sorted by code then cell. Output is deterministic
  byte for byte.

Automation:

- `shells.yml` on a weekly cron and on changes under `docker/shells/`,
  `validity/`, or the conformance crate. Jobs: build changed images, push,
  update digests, run `cargo validity --record`, open a pull request with
  `peter-evans/create-pull-request` when `matrix.toml`, `outcomes.toml` or
  `REPORT.md` changed. The pull request body lists each changed row. The
  action authenticates with a GitHub App installation token, minted in the
  job with `actions/create-github-app-token`, so `rust.yml` runs on the drift
  pull request. The default workflow token cannot trigger that run.
- `rust.yml` runs `cargo validity --cell bash:5.3 --cell dash:0.5.12` on
  every push as a smoke test, pulling the two images by digest.
- Adding a shell version is one `[[cell]]` entry. The next `shells.yml` run
  builds it, records every spec against it, and opens the pull request.
- Adding a spec is one TOML file. Same flow.

## Fuzz

Fuzz scripts are never executed. The matrix runs curated specs only. The
syntax-only `conformance shells` pass gains the same cell list and reports
rejects-valid per cell.

## Relation to upstream

For floor cells the oracle's verdict on the snippet is recorded alongside,
as `oracle = "reports" | "silent"`. Where the port reports and the oracle
does not, the spec is the evidence a sanctioned deviation needs.
