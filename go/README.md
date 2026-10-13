# shellcheck: Go installer for the native rshellcheck binary

```sh
go install github.com/kjanat/shellcheck-rs/go/cmd/shellcheck@v0.11.0
```

The command installs as `shellcheck`. On its first run it downloads the
rshellcheck release that matches its own module version, verifies it and runs
it. Every later run starts the native binary directly, with the same arguments,
standard streams and exit code.

## pre-commit

```yaml
- repo: https://github.com/kjanat/actionlint
  rev: v1.17.0
  hooks:
    - id: actionlint-shellcheck
      additional_dependencies:
        - github.com/kjanat/shellcheck-rs/go/cmd/shellcheck@v0.11.0
```

actionlint looks for `shellcheck` on `PATH`, which is where `go install` puts
this command inside the hook environment.

## What the first run does

1. Reads the module version from the build info. `v0.11.0` selects the GitHub
   release tagged `rshellcheck-v0.11.0`.
2. Maps `GOOS/GOARCH` to a release target. Linux uses the static musl build.
   Supported: linux amd64, 386, arm64, arm; darwin amd64, arm64; windows
   amd64, 386, arm64; freebsd amd64, 386; android arm64, arm, amd64, 386.
3. Downloads `SHA256SUMS` and the archive for that target from
   `github.com/kjanat/shellcheck-rs/releases`, checks the archive's SHA-256
   against the checksum file, and unpacks `rshellcheck` into
   `<user cache dir>/rshellcheck/<version>/<target>/`. The cache dir is
   `$XDG_CACHE_HOME` or `~/.cache` on Linux, `~/Library/Caches` on macOS,
   `%LocalAppData%` on Windows.
4. Concurrent first runs share one download: one process holds a lock file,
   the others wait for the binary to appear.

The first run needs network access to github.com. A CI runner without a
persistent cache directory downloads once per job. The trust root is GitHub
over TLS plus the release's checksum file; the command does not verify the
release's sigstore attestations.

A build from an untagged revision (`@master`, `@<commit>`, `go run .`) has no
matching release and exits with a message asking for a tagged version.

## Releasing

Each release carries two tags on the same commit: `rshellcheck-v<version>`
for the binaries and `go/v<version>` for this module. The release workflow's
plan step fails when `go/v<version>` is absent or names another commit.

A fix to this command alone ships as `go/v<version>-wrapper.<n>` on the fix
commit, with `n` counting from 1, for a pre-release `go/v0.12.0-rc.1-wrapper.1`.
That build runs the same `rshellcheck-v<version>` binaries. Go treats the tag
as a pre-release, so users pin it explicitly:

```sh
go install github.com/kjanat/shellcheck-rs/go/cmd/shellcheck@v0.11.0-wrapper.1
```

## Exit codes

rshellcheck's exit code passes through unchanged. The command exits 69 with a
`shellcheck: ...` line on stderr when it cannot resolve, download, verify or
start the binary. ShellCheck itself never exits 69, so a CI log separates the
two failures.

## Development

```sh
cd go && go vet ./... && go test -race ./...
```

Tests use a local HTTP server and the test binary itself in place of
rshellcheck, so they run without network and on every supported OS.
