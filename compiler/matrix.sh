#!/usr/bin/env bash
# Run the Core extraction under several GHC optimisation profiles, so the
# census can say which profile produces the most Rust-shaped Core.
#
#   ./compiler/matrix.sh            # all profiles
#   ./compiler/matrix.sh C D        # a subset
#
# Output, per profile, in compiler/matrix/<profile>/:
#   flags        the GHC flags (applied to the ShellCheck package only; the
#                dependencies are built with their Hackage defaults)
#   core-json/   the Core dumps
#   `shellcheck` the built binary, for behavioural comparison and timing
#   plan.json    cabal's build plan (every dependency version and flag)
#   provenance   source, plugin and toolchain revisions the dumps came from
#   modules      the module list, so profiles can be checked for the same set
#   time         extraction wall-clock seconds
#   extract.log
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
	echo "$flags" >"$dir/flags"
	echo "==> profile $p: $flags"
	start=$(date +%s)
	if ! H2R_OPT="$flags" \
		H2R_BUILD_DIR="$dir/build" \
		H2R_CORE_DIR="$dir/core-json" \
		H2R_KEEP_DIR="$dir" \
		"$repo_root/compiler/extract.sh" >"$dir/extract.log.next" 2>&1; then
		mv "$dir/extract.log.next" "$dir/extract.log"
		echo "    extraction failed; see $dir/extract.log" >&2
		exit 1
	fi
	if grep -q '^==> extraction unchanged:' "$dir/extract.log.next"; then
		cat "$dir/extract.log.next"
		rm -- "$dir/extract.log.next"
		continue
	fi
	mv "$dir/extract.log.next" "$dir/extract.log"
	end=$(date +%s)
	echo $((end - start)) >"$dir/time"
	echo "    done in $((end - start))s, $(du -sh "$dir/core-json" | cut -f1) of Core"
	# Keep Cabal's build tree so an interrupted extraction can resume.
done

echo
echo "==> module sets"
for p in "${selected[@]}"; do
	echo "    $p: $(wc -l <"$matrix_dir/$p/modules") modules, list sha $(sha256sum "$matrix_dir/$p/modules" | cut -c1-12)"
done
