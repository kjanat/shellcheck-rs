"""Run the native executable bundled with the platform wheel."""

import os
import subprocess
import sys
from pathlib import Path


def main() -> None:
    name = "rshellcheck.exe" if os.name == "nt" else "rshellcheck"
    binary = Path(__file__).parent / "bin" / name
    args = [str(binary), *sys.argv[1:]]
    if os.name == "nt":
        sys.exit(subprocess.call(args))
    os.execv(binary, args)
