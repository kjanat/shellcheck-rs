#!/usr/bin/env bash
# Run the Core extraction under several GHC optimisation profiles, so the
# census can say which profile produces the most Rust-shaped Core.
#
#   ./compiler/matrix.sh            # all profiles
#   ./compiler/matrix.sh C D        # a subset
#
# Output: compiler/matrix/<profile>/core-json and compiler/matrix/<profile>/time
set -euo pipefail

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
matrix_dir=$repo_root/compiler/matrix

declare -A PROFILES=(
  [A]="-O1"
  [B]="-O2"
  [C]="-O2 -fno-full-laziness"
  [D]="-O2 -fno-full-laziness -fspecialise-aggressively -fexpose-all-unfoldings -fcross-module-specialise"
  [E]="-O2 -fno-full-laziness -fspecialise-aggressively -fexpose-all-unfoldings -fcross-module-specialise -fstatic-argument-transformation"
  [F]="-O2 -fno-full-laziness -fspecialise-aggressively -fexpose-all-unfoldings -fcross-module-specialise -fstatic-argument-transformation -fstrictness-before=2"
)
ORDER=(A B C D E F)

selected=("$@")
[ ${#selected[@]} -eq 0 ] && selected=("${ORDER[@]}")

for p in "${selected[@]}"; do
  flags=${PROFILES[$p]:?unknown profile $p}
  dir=$matrix_dir/$p
  mkdir -p "$dir"
  echo "$flags" > "$dir/flags"
  echo "==> profile $p: $flags"
  start=$(date +%s)
  H2R_OPT="$flags" \
  H2R_BUILD_DIR="$dir/build" \
  H2R_CORE_DIR="$dir/core-json" \
    "$repo_root/compiler/extract.sh" > "$dir/extract.log" 2>&1
  end=$(date +%s)
  echo $((end - start)) > "$dir/time"
  echo "    done in $((end - start))s, $(du -sh "$dir/core-json" | cut -f1) of Core"
  # The build tree is large and only the dumps matter.
  rm -rf "$dir/build"
done
