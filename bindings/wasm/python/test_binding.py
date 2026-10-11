import json
import unittest
from pathlib import Path

import wasmtime
from rshellcheck_wasm import Checker

ROOT = Path(__file__).resolve().parents[3]
WASM = ROOT / "target/wasm32-unknown-unknown/release/shellcheck_wasm.wasm"


class BindingTests(unittest.TestCase):
    def test_native_parity_and_reuse(self):
        fixtures = json.loads((ROOT / ".cache/wasm-parity.json").read_text())
        with Checker(WASM.read_bytes()) as checker:
            for fixture in fixtures:
                with self.subTest(request=str(fixture["request"])[:100]):
                    if "error" in fixture["result"]:
                        with self.assertRaises(ValueError) as error:
                            checker.check(fixture["request"])
                        self.assertEqual(
                            str(error.exception), fixture["result"]["error"]
                        )
                    else:
                        self.assertEqual(
                            checker.check(fixture["request"]), fixture["result"]
                        )
            for _ in range(100):
                self.assertEqual(
                    checker.check(fixtures[1]["request"]), fixtures[1]["result"]
                )
        with self.assertRaises(RuntimeError):
            checker.check({"script": "true"})

    def test_fuel_trap_invalidates_instance(self):
        with Checker(WASM.read_bytes(), fuel=100) as checker:
            with self.assertRaises(wasmtime.Trap):
                checker.check({"script": "echo $foo"})
            with self.assertRaises(RuntimeError):
                checker.check({"script": "true"})


if __name__ == "__main__":
    unittest.main()
