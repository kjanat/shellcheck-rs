# rshellcheck binary releases

`rshellcheck` is the Rust ShellCheck port. Extract the archive, put `rshellcheck`
(or `rshellcheck.exe`) on your PATH, and run `rshellcheck --version`.

The binary is GPL-3.0-or-later; see `LICENSE.txt`. `BUILD.json` records the source
commit, Cargo version, Rust toolchain and binary SHA-256. Each GitHub release
also includes the corresponding source archive and `SHA256SUMS`.

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
   builds all 15 targets on relevant PR changes and checks workspace tests
   and the 4,062-entry behavior snapshot.
3. After the intended commit is merged, verify its required signature, then
   create and push a tag such as `rshellcheck-v0.11.0`. A mismatched version
   fails before any build job starts. Prerelease versions use tags such as
   `rshellcheck-v0.12.0-rc.1` and become GitHub prereleases.
4. All targets must succeed. Assembly verifies target headers, binary hashes,
   version, toolchain and source commit for every archive, then adds the source
   archive and SHA-256 checksums. Linux musl archives must contain static ELF
   binaries without a dynamic interpreter.
5. Only the publication job receives `contents: write`. It uploads the complete
   set to a draft before publishing it. A rerun can recover an interrupted
   draft, but refuses to replace an already-published release.

Manual **Run workflow** invocations only build downloadable artifacts, including
when run on a tag; they never publish. PR/manual archive names include the commit
SHA. Rust tags are excluded from the Haskell release workflow.

Native Windows/macOS and x86 Linux binaries receive clean-script and diagnostic
smoke tests, including version and exit status. ARM Linux smoke tests use QEMU
through cross. FreeBSD and Android binaries are architecture-checked and
cross-linked, **not runtime-tested** by this workflow. The Rust release gate
runs local behavior snapshots; the separate conformance workflow compares
against the Haskell oracle.

For local release-tooling checks:

```sh
python -m unittest discover -s .github/release -p 'test_*.py' -v
python .github/release/release.py plan
```

The platform choices follow [Rust's supported targets](https://doc.rust-lang.org/rustc/platform-support.html),
[GitHub's hosted runner labels](https://docs.github.com/en/actions/reference/runners/github-hosted-runners),
and the [Android NDK LTS](https://developer.android.com/ndk/downloads).
