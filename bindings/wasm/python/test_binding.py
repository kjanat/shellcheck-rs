import json
import unittest
from pathlib import Path
from typing import cast

import wasmtime

from rshellcheck_wasm import JSON, Checker

ROOT = Path(__file__).resolve().parents[3]
WASM = ROOT / "target/wasm32-unknown-unknown/release/shellcheck_wasm.wasm"


def load_fixtures() -> list[tuple[dict[str, JSON], dict[str, JSON]]]:
    data = cast(JSON, json.loads((ROOT / ".cache/wasm-parity.json").read_text()))
    if not isinstance(data, list):
        raise TypeError("Parity fixtures are not a JSON array")
    fixtures: list[tuple[dict[str, JSON], dict[str, JSON]]] = []
    for fixture in data:
        if not isinstance(fixture, dict):
            raise TypeError("Parity fixture is not a JSON object")
        request, result = fixture.get("request"), fixture.get("result")
        if not isinstance(request, dict) or not isinstance(result, dict):
            raise TypeError("Parity fixture lacks a request or result object")
        fixtures.append((request, result))
    return fixtures


class BindingTests(unittest.TestCase):
    def test_native_parity_and_reuse(self):
        fixtures = load_fixtures()
        with Checker(WASM.read_bytes()) as checker:
            for request, result in fixtures:
                with self.subTest(request=str(request)[:100]):
                    if "error" in result:
                        with self.assertRaises(ValueError) as error:
                            _ = checker.check(request)
                        self.assertEqual(str(error.exception), result["error"])
                    else:
                        self.assertEqual(checker.check(request), result)
            request, result = fixtures[1]
            for _ in range(100):
                self.assertEqual(checker.check(request), result)
        with self.assertRaises(RuntimeError):
            _ = checker.check({"script": "true"})

    def test_fuel_trap_invalidates_instance(self):
        with Checker(WASM.read_bytes(), fuel=100) as checker:
            with self.assertRaises(wasmtime.Trap):
                _ = checker.check({"script": "echo $foo"})
            with self.assertRaises(RuntimeError):
                _ = checker.check({"script": "true"})


if __name__ == "__main__":
    _ = unittest.main()
