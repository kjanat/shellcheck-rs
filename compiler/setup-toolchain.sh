#!/usr/bin/env bash
# Install everything this project needs to build ShellCheck and extract Core.
# Safe to re-run; each step is a no-op if already done.
set -euo pipefail

GHC_VERSION=${GHC_VERSION:-9.6.7}

if command -v apt-get >/dev/null && [ "$(id -u)" = 0 ]; then
  echo "==> system libraries"
  apt-get install -y -qq libgmp-dev libnuma-dev zlib1g-dev pkg-config
fi

if [ ! -x "$HOME/.ghcup/bin/ghcup" ]; then
  echo "==> ghcup"
  mkdir -p "$HOME/.ghcup/bin"
  curl -sSL -o "$HOME/.ghcup/bin/ghcup" https://downloads.haskell.org/~ghcup/x86_64-linux-ghcup
  chmod +x "$HOME/.ghcup/bin/ghcup"
fi
export PATH="$HOME/.ghcup/bin:$PATH"

[ -f "$HOME/.ghcup/env" ] || printf 'export PATH="$HOME/.ghcup/bin:$HOME/.cabal/bin:$PATH"\n' > "$HOME/.ghcup/env"
grep -q '.ghcup/env' "$HOME/.bashrc" 2>/dev/null || \
  echo '[ -f "$HOME/.ghcup/env" ] && . "$HOME/.ghcup/env"' >> "$HOME/.bashrc"

command -v ghc   >/dev/null || ghcup install ghc "$GHC_VERSION" --set
command -v cabal >/dev/null || ghcup install cabal latest --set
cabal update

command -v cargo >/dev/null || {
  echo "==> rustup"
  curl -sSf https://sh.rustup.rs | sh -s -- -y --no-modify-path
  export PATH="$HOME/.cargo/bin:$PATH"
}

echo
echo "ghc   $(ghc --version)"
echo "cabal $(cabal --version | head -1)"
echo "cargo $(cargo --version)"
echo
echo "Next: cabal build && cabal test    # baseline ShellCheck"
echo "      ./compiler/extract.sh        # Core JSON"
