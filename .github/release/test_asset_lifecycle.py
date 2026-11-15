"""Real Cargo lifecycle coverage; enabled in the release check job."""

import json
import os
import shutil
import subprocess
import tempfile
import unittest
from pathlib import Path
from typing import cast

import release


@unittest.skipUnless(
    os.environ.get("RSHELLCHECK_TEST_ASSET_LIFECYCLE"), "explicit Cargo lifecycle gate"
)
class AssetLifecycleTests(unittest.TestCase):
    def test_assets_follow_the_final_binary_across_build_instances(self):
        host = (
            subprocess
            .check_output(["rustc", "-vV"], text=True)
            .split("host: ")[1]
            .splitlines()[0]
        )
        target = cast(release.Triple, host)
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            shared = root / "target"
            checkout = root / "other-checkout"
            shutil.copytree(
                release.ROOT,
                checkout,
                ignore=shutil.ignore_patterns(
                    ".git", "target", ".cache", "node_modules", ".venv", "__pycache__"
                ),
            )
            env = {**os.environ, "CARGO_TARGET_DIR": str(shared)}

            def cargo(cwd: Path, operation: str = "build", *options: str) -> str:
                return subprocess.check_output(
                    [
                        "cargo",
                        operation,
                        "--locked",
                        "-p",
                        "rshellcheck",
                        "--target",
                        host,
                        "--message-format=json-render-diagnostics",
                        *options,
                    ],
                    cwd=cwd,
                    env=env,
                    text=True,
                    timeout=180,
                )

            binary = (
                shared
                / host
                / "debug"
                / ("rshellcheck.exe" if os.name == "nt" else "rshellcheck")
            )
            sidecar = binary.with_suffix(".assets.json")

            def exported(messages: str, enabled: bool):
                release.export_assets(messages, binary, host)
                files = json.loads(sidecar.read_text())["files"]
                self.assertEqual(bool(files), enabled)
                if enabled:
                    for shell, name in (
                        ("bash", "rshellcheck.bash"),
                        ("zsh", "_rshellcheck"),
                        ("fish", "rshellcheck.fish"),
                        ("powershell", "rshellcheck.ps1"),
                    ):
                        output = subprocess.check_output(
                            [str(binary), "--generate-completions", shell],
                            env={**env, "SHELLCHECK_OPTS": ""},
                            timeout=10,
                        )
                        self.assertEqual(
                            output, files[f"completions/{name}"]["text"].encode()
                        )
                else:
                    result = subprocess.run(
                        [str(binary), "--generate-completions", "bash"],
                        capture_output=True,
                        check=False,
                        timeout=10,
                    )
                    self.assertEqual(result.returncode, 3)
                _ = release.pack(target, "test", binary, root / "dist")
                return sidecar.read_bytes()

            enabled = cargo(release.ROOT, "build", "--bin", "rshellcheck")
            first = exported(enabled, True)
            # A check-only configuration must never remove the linked build's assets.
            _ = cargo(release.ROOT, "check", "--lib", "--no-default-features")
            self.assertEqual(sidecar.read_bytes(), first)
            # An unexported replacement is rejected rather than silently paired.
            off = cargo(
                release.ROOT, "build", "--bin", "rshellcheck", "--no-default-features"
            )
            with self.assertRaisesRegex(ValueError, "another binary"):
                _ = release.pack(target, "test", binary, root / "dist")
            # Export must reject this interleaving too: hashing the new binary
            # cannot establish that it was linked from the old producer output.
            with self.assertRaisesRegex(ValueError, "(?i)(producer|identity|another)"):
                release.export_assets(enabled, binary, host)
            self.assertEqual(sidecar.read_bytes(), first)
            _ = exported(off, False)
            messages = cargo(release.ROOT, "build", "--bin", "rshellcheck")
            restored = exported(messages, True)
            # Cache restoration or damage is repaired in the selected OUT_DIR.
            events = [json.loads(line) for line in messages.splitlines()]
            producer = next(
                Path(event["out_dir"])
                for event in events
                if event.get("reason") == "build-script-executed"
                and "#rshellcheck@" in event["package_id"]
            )
            (producer / "release-assets.json").unlink()
            self.assertEqual(
                exported(cargo(release.ROOT, "build", "--bin", "rshellcheck"), True),
                restored,
            )
            # Another checkout shares the target directory, but not build outputs.
            _ = cargo(checkout, "check", "--lib", "--no-default-features")
            self.assertEqual(sidecar.read_bytes(), restored)
            _ = exported(cargo(checkout, "build", "--bin", "rshellcheck"), True)
            _ = exported(cargo(release.ROOT, "build", "--bin", "rshellcheck"), True)
