#!/usr/bin/env sh
set -e

if [ -z "${CI:-}" ]; then
	mise install
	mise exec ghcup -- ghcup install hls
fi
