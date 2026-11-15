#!/usr/bin/env bash
# Fetch and build the exact upstream oracle outside the tracked source tree.
#
# Usage: tools/oracle.sh [--fetch-only | --verify-only]
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cache="${root}/.cache"
source="${cache}/upstream-shellcheck"
binary="${cache}/shellcheck-oracle"
metadata="${cache}/shellcheck-oracle.json"
scratch=""

die() {
	printf 'oracle: %s\n' "$1" >&2
	exit 1
}

cleanup() {
	if [[ -n "${scratch}" ]]; then rm -rf "${scratch}"; fi
}
trap cleanup EXIT

pin() {
	jq -er --arg key "$1" '.[$key] | strings' "${root}/tools/oracle.json" \
		|| die "Oracle pin needs string repository, revision and version"
}

# The metadata a binary built from the pin carries.
identity() {
	local digest
	# macOS ships `shasum` and no `sha256sum`.
	if command -v sha256sum >/dev/null; then
		digest="$(sha256sum "${binary}")" || return 1
	else
		digest="$(shasum -a 256 "${binary}")" || return 1
	fi
	jq -n --arg repository "${repository}" --arg revision "${revision}" \
		--arg version "${version}" --arg sha256 "${digest%% *}" \
		'{repository: $repository, revision: $revision, version: $version, sha256: $sha256}'
}

mode="${1:-}"
case "${mode}" in
	"" | --fetch-only | --verify-only) ;;
	*) die "usage: tools/oracle.sh [--fetch-only | --verify-only]" ;;
esac

repository="$(pin repository)"
revision="$(pin revision)"
version="$(pin version)"
[[ "${revision}" =~ ^[0-9a-f]{40}$ ]] || die "Oracle revision must be a full commit SHA"

mkdir -p "${cache}"
if [[ ! -e "${source}" ]]; then
	scratch="$(mktemp -d "${cache}/oracle-fetch-XXXXXX")"
	gh repo clone "${repository}" "${scratch}/source" -- --filter=blob:none --no-checkout --depth=1
	git -C "${scratch}/source" fetch --depth=1 origin "${revision}"
	git -C "${scratch}/source" checkout --detach "${revision}"
	mv "${scratch}/source" "${source}"
fi
if [[ "$(git -C "${source}" rev-parse HEAD)" != "${revision}" ]]; then
	die "${source} has a different revision; preserve it elsewhere before fetching"
fi
if [[ -n "$(git -C "${source}" status --porcelain --untracked-files=normal)" ]]; then
	die "${source} has local changes; refusing to use a modified oracle"
fi
echo "Oracle source: ${source} at ${revision}"

if [[ "${mode}" == --fetch-only ]]; then exit 0; fi

if [[ "${mode}" == --verify-only ]]; then
	expected="$(identity)"
	jq -e --argjson expected "${expected}" '. == $expected' "${metadata}" >/dev/null \
		|| die "Cached oracle does not match pinned source and binary digest"
	echo "Cached oracle identity verified"
	exit 0
fi

(cd "${source}" && cabal build exe:shellcheck)
built="$(cd "${source}" && cabal list-bin exe:shellcheck)"
reported="$("${built}" --version)"
grep -qxF "version: ${version}" <<<"${reported}" \
	|| die "Built oracle version differs from the pin"
scratch="$(mktemp -d "${cache}/oracle-build-XXXXXX")"
cp -p "${built}" "${scratch}/shellcheck-oracle"
mv "${scratch}/shellcheck-oracle" "${binary}"
identity >"${scratch}/record"
mv "${scratch}/record" "${metadata}"
echo "Oracle built: ${binary}"
