# Native rshellcheck

Install the native ShellCheck CLI:

```sh
uv tool install rshellcheck
rshellcheck script.sh
```

Or use `pip install rshellcheck` in a virtual environment.

Each platform wheel contains the executable from the corresponding rshellcheck
release. Installation needs no compiler and downloads no additional executable.
Supported wheels cover Windows (x64, x86, ARM64), macOS (Intel and Apple Silicon),
and Linux (x64, x86, ARM64, ARMv7) on glibc and musl.

For the in-process Python API, install `rshellcheck-wasm` instead.
