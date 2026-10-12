"""Reusable, serialized ShellCheck instance; no WASI or filesystem imports."""

import json
from collections.abc import Mapping
from importlib.resources import files
from threading import Lock
from typing import cast, final

import wasmtime

type JSON = bool | int | float | str | list[JSON] | dict[str, JSON] | None


def _export[T: (wasmtime.Func, wasmtime.Memory)](
    exports: Mapping[str, object], name: str, kind: type[T]
) -> T:
    value = exports[name]
    if not isinstance(value, kind):
        raise TypeError(f"WASM export {name} is not a {kind.__name__}")
    return value


def _call_u32(func: wasmtime.Func, store: wasmtime.Store, *args: int) -> int:
    value = cast(object, func(store, *args))
    if not isinstance(value, int):
        raise TypeError("WASM export returned a non-integer")
    return value & 0xFFFFFFFF


@final
class Checker:
    def __init__(self, wasm: bytes | None = None, *, fuel: int = 1_000_000_000):
        if wasm is None:
            wasm = (
                files("rshellcheck_wasm_data")
                .joinpath("shellcheck_wasm.wasm")
                .read_bytes()
            )
        config = wasmtime.Config()
        config.consume_fuel = True
        self._engine = wasmtime.Engine(config)
        self._module = wasmtime.Module(self._engine, wasm)
        if self._module.imports:
            raise ValueError("Unexpected WASM imports")
        self._store = wasmtime.Store(self._engine)
        self._store.set_fuel(fuel)
        exports = wasmtime.Instance(self._store, self._module, []).exports(self._store)
        self._memory = _export(exports, "memory", wasmtime.Memory)
        self._prepare = _export(exports, "sc_prepare", wasmtime.Func)
        self._check = _export(exports, "sc_check", wasmtime.Func)
        self._output_len = _export(exports, "sc_output_len", wasmtime.Func)
        abi_version = _export(exports, "sc_abi_version", wasmtime.Func)
        if _call_u32(abi_version, self._store) != 1:
            raise ValueError("Unsupported ShellCheck ABI")
        self._fuel = fuel
        self._closed = False
        self._lock = Lock()

    def check(self, request: dict[str, JSON]) -> dict[str, JSON]:
        data = json.dumps(request, ensure_ascii=False).encode("utf-8")
        if len(data) > 16 * 1024 * 1024:
            raise ValueError("Request exceeds 16 MiB")
        with self._lock:
            if self._closed:
                raise RuntimeError("Checker closed; create a new instance")
            store = self._store
            try:
                store.set_fuel(self._fuel)
                ptr = _call_u32(self._prepare, store, len(data))
                if not ptr:
                    raise RuntimeError("Request rejected")
                _ = self._memory.write(store, data, ptr)
                ptr = _call_u32(self._check, store)
                size = _call_u32(self._output_len, store)
                output = bytes(self._memory.read(store, ptr, ptr + size))
                result = cast(JSON, json.loads(output))
            except Exception:
                self._closed = True
                store.close()
                raise
            if not isinstance(result, dict):
                raise TypeError("ShellCheck result is not a JSON object")
            if "error" in result:
                raise ValueError(result["error"])
            return result

    def close(self) -> None:
        with self._lock:
            if not self._closed:
                self._store.close()
            self._closed = True

    def __enter__(self) -> "Checker":
        return self

    def __exit__(self, *_: object) -> None:
        self.close()
