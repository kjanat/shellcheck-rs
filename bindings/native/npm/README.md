# Native rshellcheck

Install the Rust ShellCheck CLI with npm:

```sh
npm install --save-dev @kjanat/rshellcheck
npx rshellcheck script.sh
```

The package selects a prebuilt binary for your operating system and CPU.
Keep npm's optional dependencies enabled. No compiler or install script is
required. Linux binaries are statically linked with musl and work on glibc
and musl systems.

For programmatic use, `binaryPath()` returns the installed executable path:

```js
import { binaryPath } from '@kjanat/rshellcheck';
import { spawnSync } from 'node:child_process';
spawnSync(binaryPath(), ['script.sh'], { stdio: 'inherit' });
```

For an in-process JavaScript or browser API, use `@kjanat/rshellcheck-wasm`.
