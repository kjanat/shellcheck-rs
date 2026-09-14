#!/usr/bin/env bash
# Extract optimised GHC Core for the whole ShellCheck program as JSON.
#
#   1. copy the ShellCheck sources into a scratch tree
#   2. run upstream's ./striptests there (drops QuickCheck + Template Haskell)
#   3. build that tree with h2r-plugin enabled
#   4. the plugin writes one <Module>.core.json per module
#
# The source tree at the repo root is never modified.
#
# Environment:
#   H2R_BUILD_DIR   scratch build tree        (default compiler/build)
#   H2R_CORE_DIR    where the dumps go        (default compiler/core-json)
#   H2R_OPT         GHC optimisation flags    (default -O1)
#   H2R_KEEP_DIR    if set, the built binary, cabal's build plan and a
#                   provenance record are copied here so the profile can be
#                   compared and measured without rebuilding it
#
# The flags apply to the ShellCheck package only. Dependencies (parsec,
# containers, mtl, ...) are built with their Hackage defaults, so a profile
# answers "what Core does this produce against the dependency interfaces as
# shipped", not "what would exposing more of the dependencies' unfoldings do".
set -euo pipefail

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
build_dir=${H2R_BUILD_DIR:-$repo_root/compiler/build}
out_dir=${H2R_CORE_DIR:-$repo_root/compiler/core-json}
opt=${H2R_OPT:--O1}
keep_dir=${H2R_KEEP_DIR:-}

# ghcup installs are not on PATH in non-interactive shells.
[ -f "$HOME/.ghcup/env" ] && . "$HOME/.ghcup/env"

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

binary=$(cd "$build_dir" && cabal list-bin shellcheck)
echo "==> binary: $binary"

if [ -n "$keep_dir" ]; then
  echo "==> keeping binary, build plan and provenance in $keep_dir"
  mkdir -p "$keep_dir"
  cp "$binary" "$keep_dir/shellcheck"
  cp "$build_dir/dist-newstyle/cache/plan.json" "$keep_dir/plan.json"
  find "$out_dir" -name '*.core.json' -printf '%f\n' | sort > "$keep_dir/modules"
  {
    echo "date=$(date -u +%Y-%m-%dT%H:%M:%SZ)"
    echo "flags=$opt"
    echo "flags_scope=package ShellCheck only; dependencies at Hackage defaults"
    echo "repo_head=$(git -C "$repo_root" rev-parse HEAD)"
    echo "repo_dirty_inputs=$(git -C "$repo_root" status --porcelain -- src shellcheck.hs ShellCheck.cabal striptests compiler/h2r-plugin | wc -l)"
    echo "plugin_sha256=$(cat "$repo_root"/compiler/h2r-plugin/h2r-plugin.cabal "$repo_root"/compiler/h2r-plugin/src/H2R/*.hs | sha256sum | cut -d' ' -f1)"
    echo "stripped_source_sha256=$(cd "$build_dir" && find src shellcheck.hs ShellCheck.cabal -type f | sort | xargs cat | sha256sum | cut -d' ' -f1)"
    echo "ghc=$(ghc --numeric-version)"
    echo "cabal=$(cabal --numeric-version)"
    echo "modules=$(wc -l < "$keep_dir/modules")"
    echo "binary_sha256=$(sha256sum "$keep_dir/shellcheck" | cut -d' ' -f1)"
    echo "binary_version=$("$keep_dir/shellcheck" --version | tr '\n' ' ')"
  } > "$keep_dir/provenance"
  cat "$keep_dir/provenance"
fi
