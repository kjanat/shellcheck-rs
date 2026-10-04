#!/usr/bin/env bash
# Build (or fetch) the benchmark candidates.
#
#   bench/build.sh resolve [name...]        show what each candidate resolves to and its cache key
#   bench/build.sh build   [name...]        build into .bench/bin/<name>/ (no-op when the manifest's key matches)
#   bench/build.sh key     <name>           print only the cache key
#   bench/build.sh clean                    remove .bench/ (worktrees, targets, binaries, corpus, results)
#
# Environment:
#   BENCH_ROOT            where everything goes (default: <repo>/.bench)
#   BENCH_SHA_<NAME>      pin a git candidate to a commit instead of resolving its branch
#                         (NAME upper-cased, dashes as underscores, e.g. BENCH_SHA_RUST_PORT)
#   GITHUB_OUTPUT         when set, `resolve` also appends candidates=<json> for the workflow
set -euo pipefail

ROOT=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
BENCH=${BENCH_ROOT:-${ROOT}/.bench}
PY=${PYTHON:-python3}
CANDIDATES="uv run --project ${ROOT} candidates"

log() { printf '\033[1;34m==> %s\033[0m\n' "$*" >&2; }
die() {
	printf 'bench: %s\n' "$*" >&2
	exit 1
}

field() { ${CANDIDATES} get "$1" "$2"; }

# --- resolution -------------------------------------------------------------

# For a git candidate: the commit its branch points at (remote first, local mirror as fallback).
resolve_sha() {
	local name=$1 ref var
	var="BENCH_SHA_$(tr 'a-z-' 'A-Z_' <<<"${name}")"
	if [[ -n "${!var:-}" ]]; then
		printf '%s\n' "${!var}"
		return
	fi
	ref=$(field "${name}" ref)
	git -C "${ROOT}" ls-remote --exit-code origin "refs/heads/${ref}" 2>/dev/null | cut -f1 \
		|| git -C "${ROOT}" rev-parse --verify "origin/${ref}^{commit}" 2>/dev/null \
		|| die "cannot resolve branch '${ref}' for candidate '${name}' (offline and never fetched?)"
}

# For the release candidate: the version mise.lock pins `shellcheck` to (so
# every job agrees even before the tool is installed), else whatever mise
# resolves "latest" to.
resolve_version() {
	local v=""
	[[ ! -f "${ROOT}/mise.lock" ]] || v=$("${PY}" -c 'import sys,tomllib; d=tomllib.load(open(sys.argv[1],"rb")); print(d.get("tools",{}).get("shellcheck",[{}])[0].get("version",""))' "${ROOT}/mise.lock")
	[[ -n "${v}" ]] || v=$(cd "${ROOT}" && mise latest shellcheck)
	printf '%s\n' "${v}"
}

# What a candidate is pinned to: a commit or a release version.
resolve() {
	case $(field "$1" kind) in
		git) resolve_sha "$1" ;;
		release) resolve_version "$1" ;;
		*) die "unknown kind for '$1'" ;;
	esac
}

# Content key: everything that determines the produced binary, so CI can cache
# it. Bump BENCH_KEY_SCHEMA in this file to invalidate every cache at once.
BENCH_KEY_SCHEMA=1
key_for() {
	local name=$1 pin=$2 builder kind ref platform
	builder=$(field "${name}" build)
	kind=$(field "${name}" kind)
	ref=$(field "${name}" ref)
	platform=$(uname -sm)
	{
		printf 'schema=%s\nname=%s\nkind=%s\nref=%s\npin=%s\nplatform=%s\n' \
			"${BENCH_KEY_SCHEMA}" "${name}" "${kind}" "${ref}" "${pin}" "${platform}"
		cat "${ROOT}/bench/build.sh"
		[[ -z "${builder}" ]] || cat "${ROOT}/${builder}"
	} | sha256sum | cut -c1-16
}

manifest_key() { [[ -f "$1/manifest.json" ]] && "${PY}" -c 'import json,sys; print(json.load(open(sys.argv[1])).get("key",""))' "$1/manifest.json" || true; }

status_of() { # built | stale | missing
	local out=${BENCH}/bin/$1 key=$2 have
	if [[ -x "${out}/shellcheck" ]]; then
		have=$(manifest_key "${out}")
		if [[ "${have}" == "${key}" ]]; then echo built; else echo stale; fi
	else
		echo missing
	fi
}

cmd_resolve() {
	local names=("$@") listed name kind ref pin key st json="{"
	if [[ ${#names[@]} -eq 0 ]]; then
		listed=$(${CANDIDATES} names)
		mapfile -t names <<<"${listed}"
	fi
	printf '%-10s %-8s %-13s %-42s %-16s %s\n' NAME KIND REF PIN KEY STATUS
	for name in "${names[@]}"; do
		kind=$(field "${name}" kind)
		ref=$(field "${name}" ref)
		pin=$(resolve "${name}")
		key=$(key_for "${name}" "${pin}")
		st=$(status_of "${name}" "${key}")
		printf '%-10s %-8s %-13s %-42s %-16s %s\n' "${name}" "${kind}" "${ref}" "${pin}" "${key}" "${st}"
		json+="\"${name}\":{\"kind\":\"${kind}\",\"pin\":\"${pin}\",\"key\":\"${key}\"},"
	done
	json="${json%,}}"
	if [[ -n "${GITHUB_OUTPUT:-}" ]]; then echo "candidates=${json}" >>"${GITHUB_OUTPUT}"; fi
}

# --- sources ----------------------------------------------------------------

# Make .bench/src/<name> a checkout of exactly <sha>. Reuses a checkout that is
# already there (CI's actions/checkout, or an earlier worktree); otherwise adds
# a git worktree that shares this repository's objects.
ensure_source() {
	local name=$1 sha=$2 ref dir head dirty
	ref=$(field "${name}" ref)
	dir=${BENCH}/src/${name}
	if [[ -e "${dir}/.git" ]]; then
		head=$(git -C "${dir}" rev-parse HEAD)
		if [[ "${head}" != "${sha}" ]]; then
			log "${name}: moving checkout to ${sha}"
			git -C "${dir}" fetch -q origin "${sha}" 2>/dev/null || git -C "${dir}" fetch -q origin "${ref}"
			git -C "${dir}" checkout -q --detach "${sha}"
		fi
	else
		log "${name}: adding worktree at ${sha}"
		git -C "${ROOT}" worktree prune
		git -C "${ROOT}" fetch -q origin "${sha}" 2>/dev/null || git -C "${ROOT}" fetch -q origin "${ref}"
		mkdir -p "${BENCH}/src"
		git -C "${ROOT}" worktree add -q --detach "${dir}" "${sha}"
	fi
	# (mise install rewrites a branch's mise.lock with platform checksums; that is bookkeeping, not a source change.)
	dirty=$(git -C "${dir}" status --porcelain -- . ':!mise.lock')
	[[ -z "${dirty}" ]] || die "${dir} has local modifications; refusing to benchmark a dirty tree"
}

# --- building ---------------------------------------------------------------

build_one() {
	local name=$1 kind ref builder pin key out st bin mise_version
	kind=$(field "${name}" kind)
	ref=$(field "${name}" ref)
	builder=$(field "${name}" build)
	pin=$(resolve "${name}")
	key=$(key_for "${name}" "${pin}")
	out=${BENCH}/bin/${name}
	st=$(status_of "${name}" "${key}")
	if [[ "${st}" == built ]]; then
		log "${name}: up to date (key ${key})"
		return
	fi
	rm -rf "${out}"
	mkdir -p "${out}"
	case ${kind} in
		release)
			log "${name}: installing shellcheck@${pin} through mise"
			(cd "${ROOT}" && mise install -q "shellcheck@${pin}")
			bin=$(cd "${ROOT}" && mise which --tool "shellcheck@${pin}" shellcheck)
			install -m 755 "${bin}" "${out}/shellcheck"
			mise_version=$(mise version 2>/dev/null)
			echo "mise ${mise_version%%$'\n'*}" >"${out}/toolchain.txt"
			;;
		git)
			ensure_source "${name}" "${pin}"
			log "${name}: building ${ref}@${pin:0:12} with ${builder}"
			BENCH_ROOT=${BENCH} BENCH_SRC=${BENCH}/src/${name} BENCH_OUT=${out} BENCH_TARGET=${BENCH}/target/${name} \
				bash "${ROOT}/${builder}"
			;;
		*) die "unknown kind for '${name}'" ;;
	esac
	[[ -x "${out}/shellcheck" ]] || die "${name}: builder produced no ${out}/shellcheck"
	"${out}/shellcheck" --version >/dev/null || die "${name}: binary does not run"
	${CANDIDATES} manifest "${out}" name="${name}" kind="${kind}" ref="${ref}" pin="${pin}" key="${key}" >/dev/null
	log "${name}: built ${out}/shellcheck (key ${key})"
}

cmd_build() {
	local names=("$@") listed name
	if [[ ${#names[@]} -eq 0 ]]; then
		listed=$(${CANDIDATES} names)
		mapfile -t names <<<"${listed}"
	fi
	for name in "${names[@]}"; do build_one "${name}"; done
}

cmd_clean() {
	local dir
	for dir in "${BENCH}"/src/*/; do
		[[ -d "${dir}" ]] || continue
		git -C "${ROOT}" worktree remove --force "${dir}" 2>/dev/null || rm -rf "${dir}"
	done
	git -C "${ROOT}" worktree prune
	rm -rf "${BENCH}"
	log "removed ${BENCH}"
}

case ${1:-} in
	resolve)
		shift
		cmd_resolve "$@"
		;;
	build)
		shift
		cmd_build "$@"
		;;
	key)
		[[ -n "${2:-}" ]] || die "key needs a candidate name"
		pin=$(resolve "$2")
		key_for "$2" "${pin}"
		;;
	clean) cmd_clean ;;
	*)
		sed -n '2,14p' "${BASH_SOURCE[0]}"
		exit 2
		;;
esac
