#!/usr/bin/env bash
# Extract optimised GHC Core for the whole ShellCheck program as JSON.
#
#   1. copy the ShellCheck sources into a scratch tree
#   2. run upstream's ./striptests there (drops QuickCheck + Template Haskell)
#   3. build that tree with h2r-plugin enabled
#   4. the plugin writes one <Module>.core.json per module, plus one
#      <Module>.tidy-align.txt beside it
#
# What the dumps contain (dump format 6): the Core *after* GHC's CoreTidy --
# the program GHC hands to codegen -- so a top-level binding carries, in its
# own module's dump, the very name every downstream module refers to it by.
# The plugin runs CoreTidy itself and hands the pipeline back the original
# ModGuts, so the compilation still sees its own tidy. The IdInfo CoreTidy
# discards is joined back on from the pre-tidy program, binder by binder: the
# per-binder demand on top-level, lambda, case and alternative binders,
# oneShot on top-level and let binders, and exported. Everything else is
# CoreTidy's finalised value. The .tidy-align.txt sidecar records the
# alignment that join was proved against; the Rust loader reads *.core.json
# only, so it is inert.
#
# The extra tidy is not side-effect free: it consumes uniques from the
# process-global name cache. Measured, it leaves every module's ABI hash and
# export-list hash unchanged and the executable's behaviour identical; what
# moves is internal uniques. See compiler/README.md, section M3a'.
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
#   H2R_JOBS        concurrent build jobs (default number of available CPUs)
#
# Successful output is reused only when inputs and output checksums match.
# An interrupted build with the same inputs resumes through Cabal.
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
# shellcheck source=/dev/null
[ -f "$HOME/.ghcup/env" ] && . "$HOME/.ghcup/env"

command -v cabal >/dev/null || {
	echo "cabal not on PATH (source ~/.ghcup/env)" >&2
	exit 1
}

fingerprint=$(
	{
		printf '%s\n' "$opt" "$out_dir" "$keep_dir"
		ghc --numeric-version
		cabal --numeric-version
		(cd "$repo_root" && {
			find src compiler/h2r-plugin/src -type f -print0
			printf '%s\0' shellcheck.hs ShellCheck.cabal striptests LICENSE README.md CHANGELOG.md shellcheck.1.md manpage compiler/h2r-plugin/h2r-plugin.cabal compiler/extract.sh
		} | sort -z | xargs -0 sha256sum)
	} | sha256sum
)

if [ -f "$out_dir/inputs.sha256" ] && [ "$(cat "$out_dir/inputs.sha256")" = "$fingerprint" ] \
	&& (cd "$out_dir" && sha256sum --check --status outputs.sha256); then
	echo "==> extraction unchanged: $out_dir"
	exit 0
fi

if [ -f "$build_dir/inputs.sha256" ] && [ "$(cat "$build_dir/inputs.sha256")" = "$fingerprint" ] \
	&& [ ! -f "$out_dir/outputs.sha256" ]; then
	echo "==> resuming extraction in $build_dir"
else
	echo "==> staging sources in $build_dir"
	rm -rf "$build_dir" "$out_dir"
	mkdir -p "$build_dir" "$out_dir"
	for item in src shellcheck.hs ShellCheck.cabal striptests LICENSE README.md CHANGELOG.md shellcheck.1.md manpage; do
		cp -r "$repo_root/$item" "$build_dir/"
	done

	echo "==> stripping tests (removes Template Haskell and QuickCheck)"
	(cd "$build_dir" && ./striptests)

	echo "==> wiring in the Core dump plugin"
	# The plugin has to be an ordinary dependency for GHC to be able to load it.
	sed -i 's/^\( *\)build-depends:/\1build-depends:\n\1  h2r-plugin,/' "$build_dir/ShellCheck.cabal"
	cat >"$build_dir/cabal.project" <<EOF
packages:
  .
  $repo_root/compiler/h2r-plugin

package ShellCheck
  ghc-options: $opt -fplugin=H2R.CorePlugin -fplugin-opt=H2R.CorePlugin:outdir=$out_dir
EOF
	printf '%s\n' "$fingerprint" >"$build_dir/inputs.sha256"
fi

echo "==> building (this runs the full optimisation pipeline)"
(cd "$build_dir" && cabal build -j"${H2R_JOBS:-$(nproc)}" shellcheck)

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
	find "$out_dir" -name '*.core.json' -printf '%f\n' | sort >"$keep_dir/modules"
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
		echo "modules=$(wc -l <"$keep_dir/modules")"
		echo "binary_sha256=$(sha256sum "$keep_dir/shellcheck" | cut -d' ' -f1)"
		echo "binary_version=$("$keep_dir/shellcheck" --version | tr '\n' ' ')"
	} >"$keep_dir/provenance"
	cat "$keep_dir/provenance"
fi

# Commit the completion record only after extraction and artifact copying succeed.
test -s "$out_dir/Main.core.json"
(
	cd "$out_dir"
	sha256sum -- *.core.json *.tidy-align.txt
	if [ -n "$keep_dir" ]; then
		sha256sum "$keep_dir/shellcheck" "$keep_dir/plan.json" "$keep_dir/modules" "$keep_dir/provenance"
	else
		sha256sum "$binary" "$build_dir/dist-newstyle/cache/plan.json"
	fi
) >"$out_dir/outputs.sha256.tmp"
mv "$out_dir/outputs.sha256.tmp" "$out_dir/outputs.sha256"
printf '%s\n' "$fingerprint" >"$out_dir/inputs.sha256"
