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
BENCH=${BENCH_ROOT:-$ROOT/.bench}
PY=${PYTHON:-python3}
CANDIDATES="$PY $ROOT/bench/candidates.py"

log() { printf '\033[1;34m==> %s\033[0m\n' "$*" >&2; }
die() { printf 'bench: %s\n' "$*" >&2; exit 1; }

field() { $CANDIDATES get "$1" "$2"; }

# --- resolution -------------------------------------------------------------

# For a git candidate: the commit its branch points at (remote first, local mirror as fallback).
resolve_sha() {
    local name=$1 ref var
    var="BENCH_SHA_$(tr 'a-z-' 'A-Z_' <<<"$name")"
    if [ -n "${!var:-}" ]; then printf '%s\n' "${!var}"; return; fi
    ref=$(field "$name" ref)
    git -C "$ROOT" ls-remote --exit-code origin "refs/heads/$ref" 2>/dev/null | cut -f1 \
        || git -C "$ROOT" rev-parse --verify "origin/$ref^{commit}" 2>/dev/null \
        || die "cannot resolve branch '$ref' for candidate '$name' (offline and never fetched?)"
}

# For the release candidate: the version mise.lock pins `shellcheck` to (so
# every job agrees even before the tool is installed), else whatever mise
# resolves "latest" to.
resolve_version() {
    local v=""
    [ ! -f "$ROOT/mise.lock" ] || v=$("$PY" -c 'import sys,tomllib; d=tomllib.load(open(sys.argv[1],"rb")); print(d.get("tools",{}).get("shellcheck",[{}])[0].get("version",""))' "$ROOT/mise.lock")
    [ -n "$v" ] || v=$(cd "$ROOT" && mise latest shellcheck)
    printf '%s\n' "$v"
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
    local name=$1 pin=$2 builder
    builder=$(field "$name" build)
    {
        printf 'schema=%s\nname=%s\nkind=%s\nref=%s\npin=%s\nplatform=%s\n' \
            "$BENCH_KEY_SCHEMA" "$name" "$(field "$name" kind)" "$(field "$name" ref)" "$pin" "$(uname -sm)"
        cat "$ROOT/bench/build.sh"
        [ -z "$builder" ] || cat "$ROOT/$builder"
    } | sha256sum | cut -c1-16
}

manifest_key() { [ -f "$1/manifest.json" ] && "$PY" -c 'import json,sys; print(json.load(open(sys.argv[1])).get("key",""))' "$1/manifest.json" || true; }

status_of() { # built | stale | missing
    local out=$BENCH/bin/$1 key=$2
    if [ -x "$out/shellcheck" ]; then
        [ "$(manifest_key "$out")" = "$key" ] && echo built || echo stale
    else
        echo missing
    fi
}

cmd_resolve() {
    local names=("$@") name pin key st json="{"
    [ ${#names[@]} -gt 0 ] || mapfile -t names < <($CANDIDATES names)
    printf '%-10s %-8s %-13s %-42s %-16s %s\n' NAME KIND REF PIN KEY STATUS
    for name in "${names[@]}"; do
        pin=$(resolve "$name"); key=$(key_for "$name" "$pin"); st=$(status_of "$name" "$key")
        printf '%-10s %-8s %-13s %-42s %-16s %s\n' "$name" "$(field "$name" kind)" "$(field "$name" ref)" "$pin" "$key" "$st"
        json+="\"$name\":{\"kind\":\"$(field "$name" kind)\",\"pin\":\"$pin\",\"key\":\"$key\"},"
    done
    json="${json%,}}"
    if [ -n "${GITHUB_OUTPUT:-}" ]; then echo "candidates=$json" >>"$GITHUB_OUTPUT"; fi
}

# --- sources ----------------------------------------------------------------

# Make .bench/src/<name> a checkout of exactly <sha>. Reuses a checkout that is
# already there (CI's actions/checkout, or an earlier worktree); otherwise adds
# a git worktree that shares this repository's objects.
ensure_source() {
    local name=$1 sha=$2 ref dir
    ref=$(field "$name" ref); dir=$BENCH/src/$name
    if [ -e "$dir/.git" ]; then
        if [ "$(git -C "$dir" rev-parse HEAD)" != "$sha" ]; then
            log "$name: moving checkout to $sha"
            git -C "$dir" fetch -q origin "$sha" 2>/dev/null || git -C "$dir" fetch -q origin "$ref"
            git -C "$dir" checkout -q --detach "$sha"
        fi
    else
        log "$name: adding worktree at $sha"
        git -C "$ROOT" worktree prune
        git -C "$ROOT" fetch -q origin "$sha" 2>/dev/null || git -C "$ROOT" fetch -q origin "$ref"
        mkdir -p "$BENCH/src"
        git -C "$ROOT" worktree add -q --detach "$dir" "$sha"
    fi
    [ -z "$(git -C "$dir" status --porcelain)" ] || die "$dir has local modifications; refusing to benchmark a dirty tree"
}

# --- building ---------------------------------------------------------------

build_one() {
    local name=$1 kind pin key out
    kind=$(field "$name" kind); pin=$(resolve "$name"); key=$(key_for "$name" "$pin"); out=$BENCH/bin/$name
    if [ "$(status_of "$name" "$key")" = built ]; then
        log "$name: up to date (key $key)"; return
    fi
    rm -rf "$out"; mkdir -p "$out"
    case $kind in
        release)
            log "$name: installing shellcheck@$pin through mise"
            (cd "$ROOT" && mise install -q "shellcheck@$pin")
            install -m 755 "$(cd "$ROOT" && mise which --tool "shellcheck@$pin" shellcheck)" "$out/shellcheck"
            echo "mise $(mise version 2>/dev/null | head -1)" >"$out/toolchain.txt"
            ;;
        git)
            ensure_source "$name" "$pin"
            log "$name: building $(field "$name" ref)@${pin:0:12} with $(field "$name" build)"
            BENCH_ROOT=$BENCH BENCH_SRC=$BENCH/src/$name BENCH_OUT=$out BENCH_TARGET=$BENCH/target/$name \
                bash "$ROOT/$(field "$name" build)"
            ;;
    esac
    [ -x "$out/shellcheck" ] || die "$name: builder produced no $out/shellcheck"
    "$out/shellcheck" --version >/dev/null || die "$name: binary does not run"
    $CANDIDATES manifest "$out" name="$name" kind="$kind" ref="$(field "$name" ref)" pin="$pin" key="$key" >/dev/null
    log "$name: built $out/shellcheck (key $key)"
}

cmd_build() {
    local names=("$@")
    [ ${#names[@]} -gt 0 ] || mapfile -t names < <($CANDIDATES names)
    for name in "${names[@]}"; do build_one "$name"; done
}

cmd_clean() {
    local dir
    for dir in "$BENCH"/src/*/; do
        [ -d "$dir" ] || continue
        git -C "$ROOT" worktree remove --force "$dir" 2>/dev/null || rm -rf "$dir"
    done
    git -C "$ROOT" worktree prune
    rm -rf "$BENCH"
    log "removed $BENCH"
}

case ${1:-} in
    resolve) shift; cmd_resolve "$@" ;;
    build) shift; cmd_build "$@" ;;
    key) [ -n "${2:-}" ] || die "key needs a candidate name"; key_for "$2" "$(resolve "$2")" ;;
    clean) cmd_clean ;;
    *) sed -n '2,14p' "${BASH_SOURCE[0]}"; exit 2 ;;
esac
