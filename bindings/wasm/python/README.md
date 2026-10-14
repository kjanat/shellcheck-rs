# rshellcheck-wasm

Run the Rust ShellCheck analysis core from Python through WebAssembly.

```sh
pip install rshellcheck-wasm
```

```python
from rshellcheck_wasm import Checker

with Checker() as checker:
    result = checker.check({"script": "#!/bin/sh\necho $value\n"})
    print(result["comments"])
```

The wheel includes the WASM module and uses Wasmtime. No Rust compiler or
ShellCheck executable is required. Python 3.12 or later is supported.

See the [binding documentation](https://github.com/kjanat/shellcheck-rs/tree/master/bindings/wasm)
for source-file handling, configuration and the request/response format.
