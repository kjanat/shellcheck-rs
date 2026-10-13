# rshellcheck binary releases

`rshellcheck` is the Rust ShellCheck port. Extract the archive, put `rshellcheck`
(or `rshellcheck.exe`) on your PATH, and run `rshellcheck --version`.

The binary is GPL-3.0-or-later; see `LICENSE.txt`. `BUILD.json` records the source
commit, Cargo version, Rust toolchain and binary SHA-256. Each GitHub release
also includes the corresponding source archive, `source.spdx.json`,
`DEPENDENCY-LICENSES.md`, `SHA256SUMS`, and Sigstore attestation bundles.

## Platforms

| OS      | Architectures                       | Runtime / compatibility                                     |
| ------- | ----------------------------------- | ----------------------------------------------------------- |
| Windows | x86, x64, ARM64                     | MSVC, static C runtime; Windows 10+                         |
| Linux   | x86, x64, ARMv7 hard-float, ARM64   | Static musl binaries; no glibc dependency                   |
| macOS   | Intel x64, Apple Silicon            | macOS 11+; separate native binaries                         |
| FreeBSD | x86, x64                            | FreeBSD 12.3+ sysroot via cross 0.2.5; system libc required |
| Android | armeabi-v7a, arm64-v8a, x86, x86_64 | NDK r30, API 23+; command-line executables, not APKs        |

There are no 32-bit macOS builds. Windows ARM32 and obsolete ARMv5/ARMv6 variants
are omitted. FreeBSD ARM64 is not in this matrix because the pinned cross
release does not ship that image. Android binaries require an Android shell
(such as adb or Termux); they are not ordinary Linux executables.

Windows and macOS assets are not Authenticode-signed or Apple-notarized.

## Release flow

The [release workflow](../workflows/release.yml) uses the target list in
[release.py](release.py). The Rust toolchain is the exact minimum version from
the workspace manifest, expanded to a patch version (`1.99` → `1.99.0`).
Builds use `Cargo.lock`, pinned cross/NDK versions, target-specific Cargo caches,
and at most six concurrent build jobs. Only the Rust CLI is cross-compiled;
no Haskell oracle or H2R compiler is built.

1. Set the same version in both `shellcheck-cli` and `shellcheck-rs` manifests.
   Refresh `Cargo.lock` with `cargo check -p shellcheck-cli` and include it
   in the version commit; release builds use `--locked`.
2. Review the tests and build artifacts from the pull request. The workflow
   builds all 15 targets on relevant PR changes and checks workspace unit tests
   and the 4,067-entry behavior snapshot.
3. After the intended commit is merged, verify its required signature, then
   create and push a tag such as `rshellcheck-v0.11.0`, and on the same commit
   the Go installer's tag `go/v0.11.0`. A mismatched version or a missing
   `go/v<version>` tag fails before any build job starts. Prerelease versions
   use tags such as `rshellcheck-v0.12.0-rc.1` and `go/v0.12.0-rc.1` and
   become GitHub prereleases.
4. All targets must succeed. Assembly verifies target headers, binary hashes,
   version, toolchain and source commit for every archive, then adds the source
   archive and SHA-256 checksums. Linux musl archives must contain static ELF
   binaries without a dynamic interpreter, Android binaries must load through
   the bionic linker, and Windows binaries must import no dynamic C runtime DLL.
5. Scan the exact source archive with pinned Syft to produce an SPDX 2.3 SBOM
   and a declared-license inventory. Checksums cover both alongside the archives.
6. Only the publication job receives `contents: write`, `id-token: write` and
   `attestations: write`. GitHub OIDC issues short-lived Sigstore signing
   credentials; no long-lived signing secret is configured. The job generates
   SLSA provenance for every payload file and an SBOM attestation for the source
   archive. It verifies signatures, repository, workflow, source SHA and tag
   before uploading the complete set to a draft and publishing it. A rerun can recover an interrupted
   draft, but refuses to replace an already-published release.

Manual **Run workflow** invocations only build downloadable artifacts, including
when run on a tag; they never publish. PR/manual archive names include the commit
SHA. They generate SBOMs but do not request signing credentials or attestations.

Every binary receives clean-script and diagnostic smoke tests, including version
and exit status. Windows, macOS and x86 Linux binaries run natively. ARM Linux
binaries run under QEMU from their cross image. Each Android binary runs under
QEMU user mode with the Android 9 system libraries from its own cross image.
FreeBSD binaries run in a FreeBSD 15.1 VM, the x86 one through its 32-bit
compatibility libraries. The Rust release gate
runs local behavior snapshots; the separate conformance workflow compares
against the Haskell oracle.

Release tooling is the private `rshellcheck-release` uv workspace package.
It shares the root `uv.lock` and `.venv`; `uv sync` installs it with the dev
group for editor discovery. Run it from this checkout, using the editable
workspace installation. CI selects only this package with `--no-dev`.

For local release-tooling checks:

```sh
uv run --locked --package rshellcheck-release python -m unittest discover -s .github/release -p 'test_*.py' -v
uv run --locked --package rshellcheck-release rshellcheck-release plan
```

The platform choices follow [Rust's supported targets](https://doc.rust-lang.org/rustc/platform-support.html),
[GitHub's hosted runner labels](https://docs.github.com/en/actions/reference/runners/github-hosted-runners),
and the [Android NDK LTS](https://developer.android.com/ndk/downloads).

## Verify a release

These guarantees apply to releases built with this workflow update; the original
`rshellcheck-v0.11.0` assets have no attestations and remain unchanged.

Download your archive, `SHA256SUMS`, and `provenance.sigstore.json`. Verify the
archive against the release workflow identity (replace the example version):

```sh
gh attestation verify rshellcheck-VERSION-x86_64-unknown-linux-musl.tar.gz \
  --repo kjanat/shellcheck-rs \
  --signer-workflow kjanat/shellcheck-rs/.github/workflows/release.yml \
  --source-ref refs/tags/rshellcheck-vVERSION \
  --bundle provenance.sigstore.json
```

Supply `--source-digest COMMIT_SHA` to require a particular reviewed commit.
Omit `--bundle` to retrieve the attestation from GitHub instead. The bundle
contains a signed statement binding each subject's digest to the workflow;
this authenticates the bytes without separate `.asc` signatures. Bundles are
published after checksumming, so `SHA256SUMS` does not list the bundles themselves.
The checksum file is itself a signed provenance subject.

To verify the source SBOM attestation:

```sh
gh attestation verify rshellcheck-VERSION-source.tar.gz \
  --repo kjanat/shellcheck-rs \
  --signer-workflow kjanat/shellcheck-rs/.github/workflows/release.yml \
  --source-ref refs/tags/rshellcheck-vVERSION \
  --predicate-type https://spdx.dev/Document/v2.3 \
  --bundle source-sbom.sigstore.json
```

`source.spdx.json` inventories dependencies discoverable from the released source
and lockfiles, including workspace and development dependencies. It is **not** a
per-target inventory of linked binary code, system libraries, SDKs or cross images.
It is attested against the source archive only. `DEPENDENCY-LICENSES.md` lists
scanner-reported license expressions; `NOASSERTION` remains explicit. It does not
replace dependency license texts or establish license compliance. The project's
full license remains in every binary archive.

## SLSA scope

[SLSA provenance v1](https://slsa.dev/spec/v1.0/provenance) is the signed statement
format. It records the GitHub Actions build identity and source revision.
[Build levels](https://slsa.dev/spec/v1.1/levels) describe broader guarantees about
the builder and its isolation; using the format alone does not establish a level.
This project does not claim a certified SLSA level, reproducible builds, or a
hardened isolated builder. Signing occurs in the publication job after the build
and assembly jobs complete; it is not an independent observation of each compiler
invocation. Build caches and cross-compilation images remain part of the trust
boundary. Authenticode signing and Apple notarization are not provided.

See [GitHub artifact attestations](https://docs.github.com/en/actions/how-tos/secure-your-work/use-artifact-attestations/use-artifact-attestations)
for the signing and verification model.

## JavaScript and Python distributions

Each release also includes three separate installable assets:

- `kjanat-rshellcheck-wasm-VERSION.tgz` — install with `npm install ./FILE.tgz`.
- `rshellcheck_wasm-VERSION-py3-none-any.whl` — install with `pip install ./FILE.whl`.
- `rshellcheck_wasm-VERSION.tar.gz` — Python source distribution; installation
  builds a wheel without requiring Rust, because the WASM module is included.

All three contain the same core WASM binary and the project license. Installed
JavaScript callers can use `await createChecker()` and Python callers can use
`Checker()` without supplying WASM bytes. Passing explicit bytes remains supported.
Browsers fetch the WASM next to `shellcheck.mjs`; bundlers must preserve that asset,
which is also exported as `@kjanat/rshellcheck-wasm/wasm`.

CI builds the WASM with the release Rust toolchain, builds the npm tarball and both
Python formats, then installs each into a separate temporary environment and
checks clean and diagnostic-producing scripts. Package completeness, source SHA,
archive hashes, bundled WASM equality and license contents gate assembly.
`binding-packages.json` records their source identity and hashes. Packages and the
manifest are covered by release checksums and tagged-release provenance attestations.
The manual/PR workflow exposes separate npm, wheel and sdist artifacts as well.
This does not publish packages to npm or PyPI, and does not change older releases.
