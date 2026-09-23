#!/usr/bin/env bash
#   extract-library.sh <package>
#
# GHC deadlocks compiling a home unit that a plugin loaded with -fplugin depends on.
# GHC writes the path a module was compiled from into each HasCallStack SrcLoc.
set -euo pipefail

package=${1:?usage: extract-library.sh <package>}
repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
build_dir="$repo_root/compiler/build/libraries"
out_dir="$repo_root/compiler/library-json/$package"
plugin_db="$build_dir/cabal/packagedb/ghc-$(ghc --numeric-version)"

case "$package" in
	containers)
		hadrian_path=libraries/containers/containers
		source_dirs=(src)
		include_dirs=(include)
		flags=(-O2 -XHaskell2010)
		;;
	transformers)
		hadrian_path=libraries/transformers
		source_dirs=(.)
		include_dirs=()
		flags=(-O2 -XHaskell2010)
		;;
	mtl)
		hadrian_path=libraries/mtl
		source_dirs=(.)
		include_dirs=()
		flags=(-O2 -XHaskell2010)
		;;
	base)
		hadrian_path=libraries/base
		source_dirs=(.)
		include_dirs=(include)
		flags=(-O2 -XHaskell2010)
		unit=base
		;;
	*)
		echo "extract-library.sh: no source layout recorded for $package" >&2
		exit 1
		;;
esac

unit=${unit:-$(ghc-pkg field "$package" id --simple-output)}
version=$(ghc-pkg field "$package" version --simple-output)
installed=$(ghc-pkg field "$package" library-dirs --simple-output)
read -r -a installed_includes <<<"$(ghc-pkg field "$package" include-dirs --simple-output | tr '\n' ' ')"
read -r -a rts_includes <<<"$(ghc-pkg field rts include-dirs --simple-output | tr '\n' ' ')"
read -r -a modules <<<"$(ghc-pkg field "$package" exposed-modules,hidden-modules --simple-output | tr ',\n' '  ' \
	| awk '{ for (i = 1; i <= NF; i++) { if ($(i + 1) == "from") { i += 2; continue } printf "%s ", $i } }')"
source="$build_dir/$package-$version"

fingerprint=$(
	{
		printf '%s\n' "$unit" "$hadrian_path" "${flags[@]}" "${modules[@]}"
		ghc --numeric-version
		(cd "$repo_root" && find compiler/h2r-plugin/src -type f -print0 | sort -z | xargs -0 sha256sum)
		sha256sum "$repo_root/compiler/extract-library.sh" "$repo_root/compiler/compare-interfaces.sh"
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
(cd "$repo_root/compiler/canary" && cabal build --offline --builddir="$build_dir/cabal" h2r-plugin)
plugin_unit=$(ghc-pkg --package-db="$plugin_db" field h2r-plugin id --simple-output)
plugin_dir=$(ghc-pkg --package-db="$plugin_db" field h2r-plugin dynamic-library-dirs --simple-output)
plugin_lib=$(ghc-pkg --package-db="$plugin_db" field h2r-plugin hs-libraries --simple-output)
plugin_so="$plugin_dir/lib$plugin_lib-ghc$(ghc --numeric-version).so"

work="$build_dir/$package-$version-h2r"
root="$build_dir/$package-$version-root"
rm -rf "$out_dir" "$work" "$root"
mkdir -p "$out_dir" "$work" "$root/$(dirname "$hadrian_path")"
ln -s "$source" "$root/$hadrian_path"
search=()
under() { if [ "$1" = . ]; then echo "$hadrian_path"; else echo "$hadrian_path/$1"; fi; }
for dir in "${source_dirs[@]}"; do search+=("-i$(under "$dir")"); done
for dir in "${include_dirs[@]}"; do search+=("-I$(under "$dir")"); done
for dir in "${installed_includes[@]}"; do search+=("-I$dir"); done

version_macro=$(ghc --numeric-version | awk -F. '{ print $1 * 100 + $2 }')
hsc_flags=("--cflag=-D__GLASGOW_HASKELL__=$version_macro" --cflag=-Dx86_64_HOST_ARCH=1 --cflag=-Dlinux_HOST_OS=1)
for dir in "${search[@]}"; do case "$dir" in -I*) hsc_flags+=("$dir") ;; esac done
for dir in "${rts_includes[@]}"; do hsc_flags+=("-I$dir"); done
for module in "${modules[@]}"; do
	for dir in "${source_dirs[@]}"; do
		hsc="$(under "$dir")/${module//.//}.hsc"
		if [ -f "$root/$hsc" ]; then
			mkdir -p "$work/hsc/$(dirname "${module//.//}")"
			(cd "$root" && hsc2hs "${hsc_flags[@]}" -o "$work/hsc/${module//.//}.hs" "$hsc")
			[ ! -f "$root/${hsc%.hsc}.hs-boot" ] || ln -s "$root/${hsc%.hsc}.hs-boot" "$work/hsc/${module//.//}.hs-boot"
		fi
	done
done
[ ! -d "$work/hsc" ] || search+=("-i$work/hsc")

echo "==> compiling $unit (${#modules[@]} modules)"
(cd "$root" && ghc --make -j -no-link -this-unit-id "$unit" \
	"${flags[@]}" "${search[@]}" \
	"-fplugin-library=$plugin_so;$plugin_unit;H2R.CorePlugin;[\"outdir=$out_dir\"]" \
	-fplugin-trustworthy \
	-odir "$work" -hidir "$work" \
	"${modules[@]}")

count=$(find "$out_dir" -name '*.core.json' | wc -l)
if [ "$count" -ne "${#modules[@]}" ]; then
	echo "extract-library.sh: $count dumps for ${#modules[@]} modules" >&2
	exit 1
fi
echo "==> comparing $count interfaces with the installed $unit"
"$repo_root/compiler/compare-interfaces.sh" "$installed" "$work"
echo "==> wrote $count module dumps to $out_dir"
(cd "$out_dir" && sha256sum -- *.core.json *.tidy-align.txt) >"$out_dir/outputs.sha256"
printf '%s\n' "$fingerprint" >"$out_dir/inputs.sha256"
