# ShellCheck core for Go, Python and browsers

One `shellcheck_wasm.wasm` runs in all three hosts. It contains the Rust analysis
core and JSON adapter, with **no CLI, Haskell, H2R, WASI, filesystem or JavaScript
imports**. No host callback is required. Licensed GPL-3.0-or-later, like the core;
embedding it does not change its license.

## Build

```sh
rustup target add wasm32-unknown-unknown
cargo build --release --locked -p shellcheck-wasm --target wasm32-unknown-unknown
```

Output: `target/wasm32-unknown-unknown/release/shellcheck_wasm.wasm`.
The **WASM core** CI workflow builds this module, tests all hosts and uploads a
bundle of the module, wrappers, license, source commit and checksum. This is a
CI artifact; npm/PyPI packages are not published automatically.

## JavaScript / browser

```js
import { createChecker } from './js/shellcheck.mjs';

const bytes = await (await fetch('./shellcheck_wasm.wasm')).arrayBuffer();
const checker = await createChecker(bytes);
console.log(checker.check({ script: '#!/bin/sh\necho $value\n' }));
checker.close();
```

For a UI, use `js/worker.mjs` as a module Worker. Send `{id, wasm: bytes}` and
wait for `{id, ready: true}`, then send `{id, request: {...}}`. Replies contain
`{id, result}` or `{id, error}`. Serve the `.mjs` files as JavaScript over HTTP(S).
Terminate the worker to cancel a long check. In Node, pass `readFile` bytes to
the same `createChecker` function.

## Go (wazero, no CGO)

The Go module is `github.com/kjanat/shellcheck-rs/bindings/wasm/go` and its package
name is `shellcheck`. Until published on the default branch, use a local `replace`
directive pointing to `bindings/wasm/go` or pin the integration commit.

```go
wasm, err := os.ReadFile("shellcheck_wasm.wasm")
if err != nil { return err }
checker, err := shellcheck.New(ctx, wasm)
if err != nil { return err }
defer checker.Close(context.Background())
result, err := checker.Check(ctx, json.RawMessage(`{"script":"echo $value","shell":"sh"}`))
```

Use `context.WithTimeout` for execution deadlines. Cancellation invalidates that
instance. Calls are serialized by a mutex; use separate instances for parallelism.

## Python (Wasmtime)

Install the local package with `pip install ./python` (from the artifact) or
`uv pip install ./bindings/wasm/python` (from this checkout).

```python
from pathlib import Path
from rshellcheck_wasm import Checker

with Checker(Path("shellcheck_wasm.wasm").read_bytes()) as checker:
    result = checker.check({"script": "#!/bin/sh\necho $value\n"})
    print(result["comments"])
```

Calls are serialized by a lock. Each call replenishes the configurable `fuel`
budget (default one billion Wasmtime fuel units, not milliseconds). Exhausting
fuel or another WASM trap closes the instance; construct another to continue.

## Request and result

`script` is required. Optional fields:

| Field              | Default     | Meaning                                      |
| ------------------ | ----------- | -------------------------------------------- |
| `filename`         | `script.sh` | Diagnostic filename                          |
| `shell`            | inferred    | `bash`, `sh`, `dash`, `ksh`, `busybox`       |
| `files`            | `{}`        | Virtual source filename → content            |
| `checkSourced`     | `false`     | Report diagnostics in supplied source files  |
| `exclude`          | `[]`        | Diagnostic codes to omit                     |
| `include`          | `null`      | Optional allowlist of diagnostic codes       |
| `optionalChecks`   | `[]`        | Optional core check names                    |
| `extendedAnalysis` | `null`      | Override extended analysis                   |
| `severity`         | `style`     | Minimum: `error`, `warning`, `info`, `style` |

Virtual filenames match the sourced name exactly (including `./` if present).
There is no filesystem search, `source-path` resolution, rc-file or EditorConfig
loading. Supply options explicitly and use inline ShellCheck directives. Missing
source files yield diagnostics; the module never reads host files.

Success returns `{comments: [...], dataflowError: null}`. Comments include `file`,
`line`, `column`, `endLine`, `endColumn`, `level`, numeric `code`, `message` and
`fix`. Fix replacements include source file, range, text, insertion point and
precedence. Positions are **1-based character columns with eight-column tab
stops**, not UTF-8 bytes or UTF-16 offsets. A non-null `dataflowError` means some
analysis was skipped; do not treat an empty comments array as a clean result then.

Invalid requests return `{error: "..."}` at the ABI boundary; wrappers raise an
exception/return an error. Such errors leave the instance reusable. WASM traps
do not: wrappers invalidate the instance. Input is limited to 16 MiB serialized
UTF-8 JSON. This is not a bound on analysis memory or time; use host execution
limits for untrusted or deeply nested input.

## ABI v1

Exports: `memory`, `sc_abi_version() -> 1`, `sc_prepare(len) -> ptr`,
`sc_check() -> ptr`, `sc_output_len() -> len`, `sc_reset()`.

1. Call `sc_prepare` with the byte length; zero means rejected.
2. Write exactly that many UTF-8 JSON bytes to the returned range.
3. Call `sc_check`, then copy `sc_output_len` bytes from its result pointer.
4. Parse the response before the next call. `sc_reset` frees retained buffers.

No arbitrary host pointer is accepted by the Rust code. Treat pointers as unsigned
wasm32 offsets. Reacquire memory views after calls: allocations can grow memory.
Each instance permits one request at a time; do not retain pointers between calls.
Never reuse an instance after a trap. The ABI export attributes are the adapter's
only unsafe-code lint exception; the core's unsafe-code prohibition is unchanged.

## Workspace setup

Development uses Node 26, Go 1.27.2 and Python 3.14 (`mise install`).
The Python pin also selects 3.14 for uv. Library minimum versions remain separate.

Run `uv sync --locked` and `npm ci --include=dev` from the repository root.
The Python binding is installed editably into the root `.venv`; select
`.venv/bin/python` in your editor (Windows: `.venv/Scripts/python.exe`).
Both ecosystems share root lockfiles, while binding packages retain their own
metadata. Run Python commands with `uv run` from the root or a workspace member.

## Validation

```sh
cargo build --release -p shellcheck-wasm --example check
python bindings/wasm/fixtures.py
npm run test:wasm
uv run --locked python -m unittest discover -s bindings/wasm/python -v
(cd bindings/wasm/go && go test -race ./...)
npm run install:browser --workspace=@kjanat/rshellcheck-wasm
npm run test:browser
```

The same 26 cases are compared with the native core in Go, Python, Node and a real
Chromium module worker. They cover diagnostics, fixes, Unicode/tabs, shell variants,
source files, options, parse errors and invalid requests. Additional tests cover
repeated calls, memory growth, ABI misuse, cancellation and fuel exhaustion.

Runtime references: [Rust target](https://doc.rust-lang.org/rustc/platform-support/wasm32-unknown-unknown.html),
[wazero](https://pkg.go.dev/github.com/tetratelabs/wazero),
[Wasmtime Python](https://bytecodealliance.github.io/wasmtime-py/).
