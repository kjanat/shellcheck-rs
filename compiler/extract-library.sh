#!/usr/bin/env bash
# Extract GHC Core for one installed Haskell library as JSON, under the unit
# id the program's own dumps refer to it by.
#
#   extract-library.sh <package>
#
# The library is rebuilt from its Hackage source with h2r-plugin, and the
# dumps go to compiler/library-json/<package>/. `h2r lower --with` loads them
# beside the program's.
#
# The module list is the installed package's own (`ghc-pkg field`), so the
# modules compiled are the ones the program linked. GHC cannot compile a home
# unit whose id is one the loaded plugin depends on, so the build uses a
# stand-in unit id and the plugin's `unit=` option names the dumps after the
# installed one. `-fplugin-trustworthy` keeps Safe Haskell modules importable:
# GHC otherwise marks every module a plugin touched as unsafe.
#
# Per-package source layout and flags come from the package's own .cabal file
# and are listed below; a package without an entry is refused. The source is
# compiled from the relative path hadrian built it from, because GHC writes
# that path into the SrcLoc of every HasCallStack call site.
set -euo pipefail

package=${1:?usage: extract-library.sh <package>}
repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
build_dir="$repo_root/compiler/build/libraries"
out_dir="$repo_root/compiler/library-json/$package"

case "$package" in
	containers)
		hadrian_path=libraries/containers/containers
		source_dirs=(src)
		include_dirs=(include)
		flags=(-O2 -XHaskell2010)
		;;
	*)
		echo "extract-library.sh: no source layout recorded for $package" >&2
		exit 1
		;;
esac

unit=$(ghc-pkg field "$package" id --simple-output)
version=$(ghc-pkg field "$package" version --simple-output)
read -r -a modules <<<"$(ghc-pkg field "$package" exposed-modules,hidden-modules --simple-output | tr '\n' ' ')"
source="$build_dir/$package-$version"

fingerprint=$(
	{
		printf '%s\n' "$unit" "$hadrian_path" "${flags[@]}" "${modules[@]}"
		ghc --numeric-version
		(cd "$repo_root" && find compiler/h2r-plugin/src -type f -print0 | sort -z | xargs -0 sha256sum)
		sha256sum "$repo_root/compiler/extract-library.sh"
	} | sha256sum
)
if [ -f "$out_dir/inputs.sha256" ] && [ "$(cat "$out_dir/inputs.sha256")" = "$fingerprint" ] \
	&& (cd "$out_dir" && sha256sum --check --status outputs.sha256); then
	echo "==> $package unchanged: $out_dir"
	exit 0
fi

if [ ! -d "$source" ]; then
	mkdir -p "$build_dir"
	cabal get --destdir="$build_dir" "$package-$version"
fi

echo "==> building the h2r plugin"
(cd "$repo_root/compiler/canary" && cabal build --offline --builddir=../build/canary/cabal h2r-plugin)

work="$build_dir/$package-$version-h2r"
root="$build_dir/$package-$version-root"
rm -rf "$out_dir" "$work" "$root"
mkdir -p "$out_dir" "$work" "$root/$(dirname "$hadrian_path")"
ln -s "$source" "$root/$hadrian_path"
search=()
for dir in "${source_dirs[@]}"; do search+=("-i$hadrian_path/$dir"); done
for dir in "${include_dirs[@]}"; do search+=("-I$hadrian_path/$dir"); done

echo "==> compiling $unit (${#modules[@]} modules)"
(cd "$repo_root/compiler/canary" && cabal exec --builddir=../build/canary/cabal -- \
	sh -c 'cd "$1" && shift && exec "$@"' sh "$root" \
	ghc --make -j -no-link \
	-this-unit-id "$package-h2r" -hide-package "$package" \
	"${flags[@]}" "${search[@]}" \
	-package h2r-plugin -fplugin=H2R.CorePlugin -fplugin-trustworthy \
	-fplugin-opt="H2R.CorePlugin:outdir=$out_dir" \
	-fplugin-opt="H2R.CorePlugin:unit=$unit" \
	-odir "$work" -hidir "$work" \
	"${modules[@]}")

count=$(find "$out_dir" -name '*.core.json' | wc -l)
if [ "$count" -ne "${#modules[@]}" ]; then
	echo "extract-library.sh: $count dumps for ${#modules[@]} modules" >&2
	exit 1
fi
echo "==> wrote $count module dumps to $out_dir"
(cd "$out_dir" && sha256sum -- *.core.json *.tidy-align.txt) >"$out_dir/outputs.sha256"
printf '%s\n' "$fingerprint" >"$out_dir/inputs.sha256"
