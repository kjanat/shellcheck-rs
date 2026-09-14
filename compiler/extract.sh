#!/usr/bin/env bash
# Extract optimised GHC Core for the whole ShellCheck program as JSON.
#
#   1. copy the ShellCheck sources into a scratch tree
#   2. run upstream's ./striptests there (drops QuickCheck + Template Haskell)
#   3. build that tree with h2r-plugin enabled
#   4. the plugin writes one <Module>.core.json per module
#
# The source tree at the repo root is never modified.
set -euo pipefail

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
build_dir=${H2R_BUILD_DIR:-$repo_root/compiler/build}
out_dir=${H2R_CORE_DIR:-$repo_root/compiler/core-json}
opt=${H2R_OPT:--O1}

command -v cabal >/dev/null || { echo "cabal not on PATH (source ~/.ghcup/env)" >&2; exit 1; }

echo "==> staging sources in $build_dir"
rm -rf "$build_dir" "$out_dir"
mkdir -p "$build_dir" "$out_dir"
for item in src shellcheck.hs ShellCheck.cabal striptests LICENSE README.md CHANGELOG.md shellcheck.1.md manpage; do
  cp -r "$repo_root/$item" "$build_dir/"
done

echo "==> stripping tests (removes Template Haskell and QuickCheck)"
( cd "$build_dir" && ./striptests )

echo "==> wiring in the Core dump plugin"
# The plugin has to be an ordinary dependency for GHC to be able to load it.
sed -i 's/^\( *\)build-depends:/\1build-depends:\n\1  h2r-plugin,/' "$build_dir/ShellCheck.cabal"
cat > "$build_dir/cabal.project" <<EOF
packages:
  .
  $repo_root/compiler/h2r-plugin

package ShellCheck
  ghc-options: $opt -fplugin=H2R.CorePlugin -fplugin-opt=H2R.CorePlugin:outdir=$out_dir
EOF

echo "==> building (this runs the full optimisation pipeline)"
( cd "$build_dir" && cabal build -j"$(nproc)" shellcheck )

echo
echo "==> wrote $(find "$out_dir" -name '*.core.json' | wc -l) module dumps to $out_dir"
du -sh "$out_dir"
