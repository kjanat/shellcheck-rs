#!/usr/bin/env bash
#   compare-interfaces.sh <installed-dir> <rebuilt-dir>
set -euo pipefail

installed=${1:?usage: compare-interfaces.sh <installed-dir> <rebuilt-dir>}
rebuilt=${2:?usage: compare-interfaces.sh <installed-dir> <rebuilt-dir>}

normalize() {
	ghc --show-iface "$1" \
		| awk '/^docs:$/ { skip = 1 } /^extensible fields:$/ { skip = 0 } !skip' \
		| grep -v -e '^addDependentFile ' -e '^plugin package dependencies:' \
		| sed -E 's/[0-9a-f]{32}//g'
}

same=0
different=0
while IFS= read -r -d '' interface; do
	relative=${interface#"$installed"/}
	if [ ! -f "$rebuilt/$relative" ]; then
		echo "missing: $relative"
		different=$((different + 1))
	elif diff -u --label "installed/$relative" --label "rebuilt/$relative" \
		<(normalize "$interface") <(normalize "$rebuilt/$relative"); then
		same=$((same + 1))
	else
		different=$((different + 1))
	fi
done < <(find "$installed" -name '*.hi' -print0 | sort -z)

echo "interfaces: $same identical, $different different"
[ "$different" -eq 0 ]
