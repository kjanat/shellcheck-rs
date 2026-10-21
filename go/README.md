# shellcheck: Go installer for the native rshellcheck binary

```sh
go install github.com/kjanat/shellcheck-rs/go/cmd/shellcheck@v1.0.0
```

The command installs as `shellcheck`. On its first run it downloads the
rshellcheck release that matches its own module version, verifies it and runs
it. Every later run starts the native binary directly, with the same arguments,
standard streams and exit code.

The bundled `0.11.0` release requires GitHub CLI (`gh`) for its first-run
signature verification. No GitHub token is required. Verified cache hits
need neither `gh` nor network access.

## pre-commit

```yaml
- repo: https://github.com/kjanat/actionlint
  rev: v1.17.0
  hooks:
    - id: actionlint-shellcheck
      additional_dependencies:
        - github.com/kjanat/shellcheck-rs/go/cmd/shellcheck@v1.0.0
```

actionlint looks for `shellcheck` on `PATH`, which is where `go install` puts
this command inside the hook environment.

## What the first run does

1. Reads the module version from the build info. `v1.0.0` selects the GitHub
   release tagged `rshellcheck-v1.0.0`. Source-pinned Go pseudo-versions select
   the native version bundled with that wrapper source: currently `0.11.0`.
2. Maps `GOOS/GOARCH` to a release target. Linux uses the static musl build.
   Supported: linux amd64, 386, arm64, arm; darwin amd64, arm64; windows
   amd64, 386, arm64; freebsd amd64, 386; android arm64, arm, amd64, 386.
3. For `0.11.0`, downloads only the archive from the exact release URL and
   checks its SHA-256 against the reviewed pin embedded in the wrapper.
   Other versions download `SHA256SUMS` and check the archive against it.
4. For `0.11.0`, requires `gh` on `PATH` and verifies SLSA provenance using
   the embedded attestation bundle and trusted roots. This verification needs
   neither GitHub authentication nor network access. It checks the repository,
   release workflow, tag, exact source and signer commits, predicate type and
   GitHub-hosted runner identity. Verification has a one-minute deadline.

   Other versions retain online verification when `gh` is on `PATH`:

   ```sh
   gh attestation verify <archive> --repo kjanat/shellcheck-rs \
     --signer-workflow kjanat/shellcheck-rs/.github/workflows/release.yml \
     --source-ref refs/tags/rshellcheck-v<version>
   ```

   A failed verification aborts the install. For these other versions only,
   without `gh`, or with `gh` signed out, the install goes on and prints one
   `shellcheck: <archive>: provenance not verified, ...` line on stderr.
5. Unpacks `rshellcheck` into `<user cache dir>/rshellcheck/<version>/<target>/`.
   For `0.11.0`, checks the extracted binary against its independent embedded
   SHA-256 pin before installation and on every cache hit. Corrupt cache files
   fail closed; remove the indicated file and retry to install it again.
   The cache dir is `$XDG_CACHE_HOME` or `~/.cache` on Linux,
   `~/Library/Caches` on macOS, `%LocalAppData%` on Windows.
6. Concurrent first runs share one download: one process holds a lock file,
   the others wait for the binary to appear.

The first run needs network access to the release asset URL on github.com.
For the bundled version, no GitHub API request is needed, even with an empty
cache. A persistent cache avoids subsequent downloads. Go's module checksum
verification protects the wrapper source, including its reviewed asset pins,
attestation and trusted roots.

A Go build installed from `@<commit>` or `@master` receives a pseudo-version
and runs the wrapper source's bundled native release. Pin the full source
commit for repeatability. An unversioned build (`go run .`, `(devel)`) still
fails; it has no module identity.

### Updating bundled evidence

`cmd/shellcheck/proofs/0.11.0/provenance.sigstore.json` is the published
[`rshellcheck-v0.11.0` provenance bundle](https://github.com/kjanat/shellcheck-rs/releases/download/rshellcheck-v0.11.0/provenance.sigstore.json).
It authenticates all 15 native archives. `trusted-root.jsonl` contains the
reviewed GitHub/Sigstore trust roots. The exact release source is
`e0f0d77845e0bccfccf7ef2e46b50e968e534328`.

For a new bundled release, review the roots and workflow identity, verify
every archive against the bundle offline, then record each archive's SHA-256
and its extracted native binary's SHA-256 in `proof_assets.go`. Update the
embedded version and source commit together. Archive pins must match the
signed subjects; binary pins must come from those verified archives.

## Releasing

Each release carries two tags on the same commit: `rshellcheck-v<version>`
for the binaries and `go/v<version>` for this module. The release workflow's
plan step fails when `go/v<version>` is absent or names another commit.

A fix to this command alone ships as `go/v<version>-wrapper.<n>` on the fix
commit, with `n` counting from 1, for a pre-release `go/v1.1.0-rc.1-wrapper.1`.
That build runs the same `rshellcheck-v<version>` binaries. Go treats the tag
as a pre-release, so users pin it explicitly:

```sh
go install github.com/kjanat/shellcheck-rs/go/cmd/shellcheck@v1.0.0-wrapper.1
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

To verify every real release archive with network blocked for `gh`, first
download all 15 native archives from the pinned release into one directory:

```sh
RSHELLCHECK_RELEASE_ARCHIVES=/path/to/archives go test -count=1 -run TestPublishedReleaseOfflineVerification ./cmd/shellcheck
```

This tests cold installation, actual offline signature verification, warm
cache verification, corrupt archives and cache files, and execution of the
native archive matching the host. No executable is added to `PATH`.

Tests use a local HTTP server and the test binary itself in place of
rshellcheck, so they run without network and on every supported OS.
