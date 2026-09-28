#!/usr/bin/env bash
# Build ShellCheck-compiled-to-Rust from the `h2r-compiler` branch.
#
# `cargo build -p rshellcheck` there drives the whole pipeline through build
# scripts: GHC 9.6.7 compiles ShellCheck and its libraries with the Core-dump
# plugin, the dumps are lowered to Rust, and that Rust is compiled. It takes a
# long time and needs the branch's own toolchain, so it runs inside that
# checkout's mise environment (its mise.lock pins GHC, cabal and rust).
# Called by bench/build.sh with BENCH_SRC (checkout), BENCH_OUT, BENCH_TARGET.
set -euo pipefail

cd "$BENCH_SRC"
export CARGO_TARGET_DIR=$BENCH_TARGET
# The branch's ghcup post-install hook installs the Haskell language server
# unless CI is set; a benchmark build never wants an editor server.
export CI=${CI:-1}
export MISE_YES=1

# GHC links against the system GMP; fail early with a useful message instead
# of deep inside cabal. (compiler/setup-toolchain.sh on that branch lists the
# packages: libgmp-dev libnuma-dev zlib1g-dev pkg-config on Debian/Ubuntu.)
if command -v ldconfig >/dev/null && ! ldconfig -p | grep -q 'libgmp\.so$'; then
    if ! ls /usr/lib/*/libgmp.so /usr/lib/libgmp.so /usr/local/lib/libgmp.so >/dev/null 2>&1; then
        echo "bench: libgmp.so (the -dev package) is required to link GHC-built code; install libgmp-dev" >&2
        exit 1
    fi
fi

mise trust -q
mise install
# mise install adds platform checksums to the lockfile; keep the checkout pristine.
git checkout -q -- mise.lock 2>/dev/null || true
# cabal needs the Hackage index once to plan ShellCheck's dependencies.
if ! ls "${XDG_CACHE_HOME:-$HOME/.cache}"/cabal/packages/*/01-index.tar* >/dev/null 2>&1; then
    mise exec -- cabal update
fi
# The layer build scripts compile the Core-dump plugin with `cabal --offline`,
# so its dependencies (aeson & co.) have to be in the cabal store already.
(cd compiler/canary && mise exec -- cabal build --only-dependencies h2r-plugin)
mise exec -- cargo build --release --locked -p rshellcheck
install -m 755 "$BENCH_TARGET/release/rshellcheck" "$BENCH_OUT/shellcheck"
{
    mise exec -- ghc --version
    mise exec -- cabal --version | head -1
    mise exec -- rustc --version
    mise exec -- cargo --version
} >"$BENCH_OUT/toolchain.txt"
