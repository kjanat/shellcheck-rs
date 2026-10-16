<a name="idtop"></a>

# 6 Releases and distributions

`.github/workflows/release.yml` builds, verifies, signs and publishes every distribution from one tag. `.github/release/README.md` on `master` is the operator's reference. `.github/release/*.py` is the tooling.

## 6.1 Version policy

Versions are this project's own, semver from 1.0.0: patch for fixes in the Rust code, minor for a newly tracked ShellCheck revision or new diagnostics, major for breaking CLI or API changes. `rshellcheck --version` prints the tracked ShellCheck version on its `upstream:` line. The first tag, `rshellcheck-v0.11.0` (2026-10-12), carried ShellCheck's version number. `rshellcheck-v1.0.0` (2026-10-15) started the independent scheme.

Each version has two tags on the same commit: `rshellcheck-v<version>` for the binaries and `go/v<version>` for the Go module. A fix to the Go command alone ships as `go/v<version>-wrapper.<n>` on the fix commit and runs the same binaries. Prerelease versions use tags such as `rshellcheck-v1.1.0-rc.1` and `go/v1.1.0-rc.1` and become GitHub prereleases.

**[⬆ Top](#idtop)**

## 6.2 Targets

The matrix in `release.py` has 15 targets:

| OS      | Targets                                                                                                                | Runner, builder                                       | Runtime                                             |
| ------- | ---------------------------------------------------------------------------------------------------------------------- | ----------------------------------------------------- | --------------------------------------------------- |
| Windows | `x86_64-pc-windows-msvc`, `i686-pc-windows-msvc`, `aarch64-pc-windows-msvc`                                            | `windows-2025-vs2026`, `windows-11-vs2026-arm`; cargo | MSVC, static C runtime, Windows 10+                 |
| Linux   | `x86_64-unknown-linux-musl`, `i686-unknown-linux-musl`, `aarch64-unknown-linux-musl`, `armv7-unknown-linux-musleabihf` | `ubuntu-26.04`; cross                                 | Static musl binaries                                |
| macOS   | `x86_64-apple-darwin`, `aarch64-apple-darwin`                                                                          | `macos-15-intel`, `macos-15`; cargo                   | macOS 11+                                           |
| FreeBSD | `x86_64-unknown-freebsd`, `i686-unknown-freebsd`                                                                       | `ubuntu-26.04`; cross 0.2.5                           | FreeBSD 12.3+ sysroot, system libc                  |
| Android | `aarch64-linux-android`, `armv7-linux-androideabi`, `x86_64-linux-android`, `i686-linux-android`                       | `ubuntu-26.04`; NDK r30                               | API 23+, command-line executables for adb or Termux |

The Rust toolchain is the workspace's `rust-version` expanded to a patch version. Builds use `Cargo.lock`, fixed cross and NDK versions, and at most six concurrent build jobs. Windows and macOS assets are not Authenticode-signed or notarized.

Every binary gets clean-script and diagnostic smoke tests. Windows, macOS and x86 Linux run natively; ARM Linux under QEMU from its cross image; Android under QEMU user mode with the Android 9 system libraries; FreeBSD in a FreeBSD 15.1 VM. Assembly checks that Linux musl archives hold static ELF binaries without a dynamic interpreter, Android binaries load through the bionic linker, and Windows binaries import no dynamic C runtime DLL.

**[⬆ Top](#idtop)**

## 6.3 Running a release

1. Set the same version in the `shellcheck-cli`, `shellcheck-rs` and `shellcheck-wasm` manifests and in the four binding manifests under `bindings/`. Refresh `Cargo.lock` with `cargo check -p shellcheck-cli` and `package-lock.json` with `npm install --package-lock-only`; commit both. Builds in `release.yml` use `--locked`.
2. Review the pull request's tests and artifacts. The workflow builds all 15 targets on relevant pull request changes and runs the workspace unit tests and the 4,067-entry behaviour snapshot.
3. After the commit is merged, verify its signature, then create and push `rshellcheck-v<version>` and `go/v<version>` on that commit. The `plan` job fails before any build when the versions disagree or the Go tag is absent or names another commit.
4. All targets must succeed. `assemble` verifies target headers, binary hashes, version, toolchain and source commit for every archive, then adds the source archive and `SHA256SUMS`.
5. Syft scans the exact source archive into `source.spdx.json` (SPDX 2.3) and `DEPENDENCY-LICENSES.md`.
6. `publish` alone receives `contents: write`, `id-token: write` and `attestations: write`. GitHub OIDC issues short-lived Sigstore credentials; no long-lived signing secret exists. The job generates SLSA provenance for every payload file and an SBOM attestation for the source archive, verifies signatures, repository, workflow, source SHA and tag, uploads the set to a draft and publishes it. A rerun recovers an interrupted draft and refuses to overwrite anything already published.

Manual **Run workflow** invocations only build artifacts, also on a tag. They never publish and request no signing credentials.

Local checks of the tooling:

```sh
uv run --locked --package rshellcheck-release python -m unittest discover -s .github/release -p 'test_*.py' -v
uv run --locked --package rshellcheck-release rshellcheck-release plan
```

**[⬆ Top](#idtop)**

## 6.4 Release assets

Each archive holds `rshellcheck` (or `rshellcheck.exe`), `LICENSE.txt` and `BUILD.json` (source commit, Cargo version, Rust toolchain, binary SHA-256). Alongside the archives sit the source archive, `source.spdx.json`, `DEPENDENCY-LICENSES.md`, `SHA256SUMS`, the Sigstore bundles, the npm tarballs, the Python wheels and source distribution, `binding-packages.json` and `native-packages.json`. Bundles are published after checksumming. `SHA256SUMS` does not list them. The checksum file is itself a signed subject.

Verify an archive:

```sh
gh attestation verify rshellcheck-VERSION-x86_64-unknown-linux-musl.tar.gz \
  --repo kjanat/shellcheck-rs \
  --signer-workflow kjanat/shellcheck-rs/.github/workflows/release.yml \
  --source-ref refs/tags/rshellcheck-vVERSION \
  --bundle provenance.sigstore.json
```

`--source-digest COMMIT_SHA` requires a particular commit. Without `--bundle` the attestation comes from GitHub. The SBOM attestation verifies the same way with `--predicate-type https://spdx.dev/Document/v2.3 --bundle source-sbom.sigstore.json`. The SBOM inventories the shipped source and lockfiles, including development dependencies. It is not a per-target inventory of linked code. The project claims no certified SLSA level and no reproducible builds. Signing happens in the publication job after build and assembly. The `rshellcheck-v0.11.0` assets predate attestations and stay unchanged.

**[⬆ Top](#idtop)**

## 6.5 Registries

| Registry | Package                                                                                                        | Job             | Notes                                                                                                                                                      |
| -------- | -------------------------------------------------------------------------------------------------------------- | --------------- | ---------------------------------------------------------------------------------------------------------------------------------------------------------- |
| npm      | `@rshellcheck/rshellcheck-<os>-<arch>`, 15 platform packages holding the verified binaries                     | `npm`           | One matrix job per package. `native-packages.json` records checksums and source identity.                                                                  |
| npm      | `@kjanat/rshellcheck`, the launcher with the platform packages as optional dependencies                        | `npm-launcher`  | Runs after the platform packages.                                                                                                                          |
| npm      | `@kjanat/rshellcheck-wasm`                                                                                     | `npm-wasm`      | Bundles the WASM module; `createChecker()` needs no bytes.                                                                                                 |
| PyPI     | `rshellcheck-wasm`, wheel and source distribution                                                              | `pypi`          | `uv publish` checks existing files by content, then both SHA-256 digests are verified through PyPI's API.                                                  |
| PyPI     | `rshellcheck`, platform wheels holding the native executable                                                   | `pypi-native`   | After `native-wheel-smoke` installs a wheel on each runner.                                                                                                |
| ghcr.io  | `ghcr.io/kjanat/shellcheck-rs:VERSION` for linux amd64, arm64, 386, arm/v7; stable releases also move `latest` | `container`     | Runs `rshellcheck` directly, defaults to `/w`, holds the static CLI and licence only. BuildKit SBOM and provenance attestations plus a GitHub attestation. |
| ghcr.io  | `ghcr.io/kjanat/shellcheck-rs/binaries:VERSION-TARGET`, one copy-only image per target                         | `binary-images` | `docker create` then `docker cp /rshellcheck`; the image is never started. `COPY --from=` works for Linux targets.                                         |
| Go proxy | `github.com/kjanat/shellcheck-rs/go/cmd/shellcheck@v<version>`                                                 | tags            | The `go/v<version>` tag is the publication.                                                                                                                |

Prerelease versions use the npm dist-tag `next`. Stable versions use `latest`. Existing npm versions are skipped only when their registry integrity matches the tarball among the tag's assets. `npm-plan` lists the publications a registry lacks. A partial publication resumes by rerunning the failed job.

```sh
docker run --rm -v "${PWD}:/w:ro" ghcr.io/kjanat/shellcheck-rs:1.0.0 script.sh
```

**[⬆ Top](#idtop)**

## 6.6 Trusted publishing

npm and PyPI publish through OIDC. The workflow needs no permanent registry token.

- npm: each package's trusted publisher is repository `kjanat/shellcheck-rs`, workflow `release.yml`, environment `npm`, with direct publishing and **Allow npm dist-tag** enabled. `npm trust github @kjanat/rshellcheck --repo kjanat/shellcheck-rs --file release.yml --environment npm --allow-publish`, repeated for `@kjanat/rshellcheck-wasm` and every platform package in `bindings/native/npm/platforms.json`. A package's first publication needs an authorized npm account. A short-lived granular token in the GitHub `npm` environment covers that bootstrap run and is removed afterwards.
- PyPI: a pending trusted publisher for `rshellcheck-wasm` with owner `kjanat`, repository `shellcheck-rs`, workflow `release.yml`, environment `pypi`. PyPI creates the project on the first OIDC publication.

**[⬆ Top](#idtop)**

## 6.7 Upstream aliases

After every distribution of a stable version publishes, `upstream-aliases` advances aliases derived from `tools/oracle.json`:

- npm dist-tag `upstream-<version>` on `@kjanat/rshellcheck`, `@kjanat/rshellcheck-wasm` and every platform package.
- `ghcr.io/kjanat/shellcheck-rs:upstream-<version>` and `ghcr.io/kjanat/shellcheck-rs/binaries:upstream-<version>-TARGET`.
- The moving git tag `upstream-<version>` on the tagged commit. `rshellcheck-v*` tags never move.

Prereleases do not advance them. Promotion checks the previous git alias version, requires a verified tagged commit, and verifies the resulting npm versions, OCI digests and git target. PyPI has no equivalent. `pip install rshellcheck-wasm==1.0.0` fixes a version, and the package description names the ShellCheck revision it was built from.

**[⬆ Top](#idtop)**

## 6.8 Resuming a publication

`workflow_dispatch` takes `publish_existing` (a published immutable `rshellcheck-v*` tag), `registry` (`all`, `npm` or `pypi`) and `artifact_run_id` (a finished `release.yml` run whose payload to reuse). With `publish_existing` set, `plan` marks the run registry-only, skips `check`, `build` and `bindings`, and `registry-payload` repackages the verified GitHub assets for the registry jobs. The dispatched ref must carry that tag's package version, and the tag's commit signature must verify.

**[⬆ Top](#idtop)**

<a name="idend"></a>
