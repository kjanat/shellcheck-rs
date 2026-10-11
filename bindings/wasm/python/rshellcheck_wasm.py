"""Reusable, serialized ShellCheck instance; no WASI or filesystem imports."""

import json
from threading import Lock

import wasmtime


class Checker:
    def __init__(self, wasm: bytes, *, fuel: int = 1_000_000_000):
        config = wasmtime.Config()
        config.consume_fuel = True
        self._engine = wasmtime.Engine(config)
        self._module = wasmtime.Module(self._engine, wasm)
        if self._module.imports:
            raise ValueError("Unexpected WASM imports")
        self._store = wasmtime.Store(self._engine)
        self._store.set_fuel(fuel)
        self._exports = wasmtime.Instance(self._store, self._module, []).exports(
            self._store
        )
        if self._exports["sc_abi_version"](self._store) != 1:
            raise ValueError("Unsupported ShellCheck ABI")
        self._fuel = fuel
        self._closed = False
        self._lock = Lock()

    def check(self, request: dict) -> dict:
        data = json.dumps(request, ensure_ascii=False).encode("utf-8")
        if len(data) > 16 * 1024 * 1024:
            raise ValueError("Request exceeds 16 MiB")
        with self._lock:
            if self._closed:
                raise RuntimeError("Checker closed; create a new instance")
            store, e = self._store, self._exports
            try:
                store.set_fuel(self._fuel)
                ptr = e["sc_prepare"](store, len(data)) & 0xFFFFFFFF
                if not ptr:
                    raise RuntimeError("Request rejected")
                e["memory"].write(store, data, ptr)
                ptr = e["sc_check"](store) & 0xFFFFFFFF
                size = e["sc_output_len"](store) & 0xFFFFFFFF
                result = json.loads(bytes(e["memory"].read(store, ptr, ptr + size)))
            except Exception:
                self._closed = True
                store.close()
                raise
            if "error" in result:
                raise ValueError(result["error"])
            return result

    def close(self):
        with self._lock:
            if not self._closed:
                self._store.close()
            self._closed = True

    def __enter__(self):
        return self

    def __exit__(self, *_):
        self.close()
