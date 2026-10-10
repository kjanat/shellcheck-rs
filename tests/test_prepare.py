"""Exercise preparation through the CLI with disposable repositories and a build fixture."""

import json
import os
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path


class PreparationTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.source = self.root / "source"
        self.source.mkdir()
        self.state = self.root / "state"
        self.prepared = self.root / "prepared"
        self.counter = self.root / "builds"
        self.tools = self.root / "tools"
        self.tools.mkdir()
        self.environment = os.environ.copy()
        self.environment.update(
            PATH=str(self.tools) + os.pathsep + self.environment["PATH"],
            TEST_BUILD_COUNTER=str(self.counter),
            TEST_BUILD_FAILURE=str(self.root / "fail"),
        )
        self.binary = self.root / "reference"
        self.binary.write_text(
            '#!/bin/sh\nif [ "$1" = "--version" ]; then echo "version: fixture"; fi\n'
        )
        self.binary.chmod(0o755)
        mise = self.tools / "mise"
        mise.write_text(f"""#!{sys.executable}
import os
import pathlib
import shutil
import sys
mutation = pathlib.Path({str(self.root / "mutation")!r})
if sys.argv[1] == 'install' and mutation.exists() and mutation.read_text() == 'setup':
    pathlib.Path('main.rs').write_text('changed by setup')
if sys.argv[1] == 'install' and mutation.exists() and mutation.read_text() == 'postinstall':
    if os.environ.get('MISE_LOCKED') != '1' or os.environ.get('MISE_TASK_RUN_AUTO_INSTALL') != 'false':
        with pathlib.Path('mise.lock').open('a') as output:
            output.write('\\n# nested mise task rewrote the lockfile\\n')
if sys.argv[1:3] == ['which', 'shellcheck']:
    print({str(self.binary)!r})
    sys.exit(0)
if '--' in sys.argv and sys.argv[sys.argv.index('--') + 1] == 'cargo':
    counter = pathlib.Path(os.environ['TEST_BUILD_COUNTER'])
    counter.write_text(str(int(counter.read_text()) + 1 if counter.exists() else 1))
    target = pathlib.Path(os.environ['CARGO_TARGET_DIR'])
    target.mkdir(parents=True, exist_ok=True)
    (target / 'partial').write_text('preserved')
    if pathlib.Path(os.environ['TEST_BUILD_FAILURE']).exists():
        sys.exit(7)
    (target / 'release').mkdir(exist_ok=True)
    binary = target / 'release' / 'rshellcheck'
    shutil.copy2({str(self.binary)!r}, binary)
    with binary.open('a') as output:
        output.write('# ' + pathlib.Path('main.rs').read_text() + '\\n')
    if mutation.exists() and mutation.read_text() == 'build':
        pathlib.Path('main.rs').write_text('changed by build')
""")
        mise.chmod(0o755)
        self.git("init", "-b", "main")
        self.git("config", "user.name", "Fixture")
        self.git("config", "user.email", "fixture@example.invalid")
        (self.source / "main.rs").write_text("initial")
        (self.source / "Cargo.lock").write_text("version = 4\n")
        (self.source / "mise.toml").write_text('[tools]\nrust = "1.0"\n')
        (self.source / "mise.lock").write_text('[[tools.rust]]\nversion = "1.0"\n')
        self.commit()
        self.config = self.root / "candidates.toml"
        self.config.write_text(f"""[candidates.upstream]
binary = "shellcheck"
tool = "shellcheck"
baseline = true
[candidates.rust-port]
repo = {json.dumps(str(self.source))}
ref = "main"
package = "shellcheck-cli"
tools = ["rust"]
""")
        self.flags = [
            "--config",
            str(self.config),
            "--state",
            str(self.state),
            "--prepared",
            str(self.prepared),
        ]

    def git(self, *arguments):
        return subprocess.run(
            ["git", "-C", str(self.source), *arguments],
            capture_output=True,
            text=True,
            check=True,
        ).stdout.strip()

    def commit(self):
        self.git("add", ".")
        self.git("commit", "-m", "Fixture change")

    def cli(self, *arguments, success=True):
        result = subprocess.run(
            [sys.executable, "-m", "bench.cli", *arguments],
            env=self.environment,
            capture_output=True,
            text=True,
            timeout=30,
            check=False,
        )
        if success:
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        else:
            self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
        return result

    def prepare(self, *arguments, success=True):
        return self.cli(
            "prepare",
            *self.flags,
            "--candidates",
            "rust-port",
            *arguments,
            success=success,
        )

    def manifest(self):
        return json.loads((self.prepared / "rust-port/manifest.json").read_text())

    def count(self):
        return int(self.counter.read_text()) if self.counter.exists() else 0

    def test_identical_input_executes_no_second_build(self):
        cold = self.prepare()
        first = self.manifest()
        self.assertIn("cold build", cold.stderr)
        (self.root / "report.md").write_text("a new rendering")
        warm = self.prepare()
        self.assertIn("binary cache hit", warm.stderr)
        self.assertEqual(self.count(), 1)
        self.assertEqual(first, self.manifest())

    def test_missing_candidate_tool_lock_uses_harness_fallback(self):
        (self.source / "mise.lock").unlink()
        self.commit()
        self.prepare()
        self.assertEqual(self.count(), 1)
        self.assertIn("binary cache hit", self.prepare().stderr)

    def test_partial_candidate_lock_uses_harness_fallback(self):
        (self.source / "mise.lock").write_text('[[tools.python]]\nversion = "3.14.0"\n')
        self.commit()
        self.prepare()
        self.assertEqual(self.count(), 1)

    def test_baseline_resolves_pinned_mise_tool(self):
        self.cli("prepare", *self.flags, "--candidates", "upstream")
        manifest = json.loads((self.prepared / "upstream/manifest.json").read_text())
        self.assertEqual(manifest["kind"], "release")
        self.assertEqual(manifest["ref"], str(self.binary))
        self.assertEqual(self.count(), 0)

    def test_new_revision_reuses_build_directory_and_changes_binary_key(self):
        self.prepare()
        first = self.manifest()
        (self.source / "main.rs").write_text("new revision")
        self.commit()
        second = self.prepare()
        self.assertIn("incremental build", second.stderr)
        self.assertEqual(self.count(), 2)
        self.assertNotEqual(first["build_key"], self.manifest()["build_key"])
        self.assertNotEqual(first["binary_sha256"], self.manifest()["binary_sha256"])
        import hashlib

        old_binary = self.prepared / "rust-port" / first["binary"]
        self.assertEqual(
            hashlib.sha256(old_binary.read_bytes()).hexdigest(), first["binary_sha256"]
        )

    def test_local_modifications_are_identified_and_preserved(self):
        (self.source / "main.rs").write_text("modified")
        (self.source / "extra.rs").write_text("local addition")
        before = self.git("status", "--porcelain")
        self.prepare("--source", f"rust-port={self.source}")
        first = self.manifest()
        self.assertTrue(first["dirty"])
        self.assertEqual(before, self.git("status", "--porcelain"))
        (self.source / "extra.rs").write_text("different local addition")
        self.prepare("--source", f"rust-port={self.source}")
        self.assertNotEqual(first["build_key"], self.manifest()["build_key"])
        self.assertEqual(self.count(), 2)

    def test_locked_toolchain_change_invalidates_binary_and_layers_identity(self):
        plan = self.root / "plan.json"
        self.prepare("--resolve-only", "--plan", str(plan))
        first = json.loads(plan.read_text())["builds"][0]
        (self.source / "mise.lock").write_text('[[tools.rust]]\nversion = "2.0"\n')
        self.commit()
        self.prepare("--resolve-only", "--plan", str(plan))
        second = json.loads(plan.read_text())["builds"][0]
        self.assertNotEqual(first["key"], second["key"])
        self.assertNotEqual(first["layers_key"], second["layers_key"])

    def test_plan_builds_resolved_sha_even_after_remote_branch_moves(self):
        plan = self.root / "plan.json"
        self.prepare("--resolve-only", "--plan", str(plan))
        resolved = json.loads(plan.read_text())["builds"][0]
        (self.source / "main.rs").write_text("branch moved")
        self.commit()
        shutil.rmtree(Path(resolved["source"]))
        self.prepare("--plan", str(plan))
        self.assertEqual(resolved["pin"], self.manifest()["pin"])
        self.assertNotEqual(self.git("rev-parse", "HEAD"), self.manifest()["pin"])

    def test_source_change_after_resolution_rejects_publication(self):
        plan = self.root / "plan.json"
        self.prepare(
            "--source",
            f"rust-port={self.source}",
            "--resolve-only",
            "--plan",
            str(plan),
        )
        (self.source / "main.rs").write_text("changed after resolution")
        result = self.prepare("--plan", str(plan), success=False)
        self.assertIn("source changed after resolution", result.stderr)
        self.assertEqual(self.count(), 0)
        self.assertFalse((self.prepared / "rust-port/manifest.json").exists())

    def test_corrupt_binary_cache_is_rebuilt(self):
        self.prepare()
        key = self.manifest()["build_key"]
        (self.state / "cache/rust-port" / key / self.manifest()["binary"]).write_text(
            "corrupt"
        )
        self.prepare()
        self.assertEqual(self.count(), 2)
        self.prepare("--verify")

    def test_failed_build_preserves_partial_state_without_publishing(self):
        (self.root / "fail").touch()
        self.prepare(success=False)
        self.assertTrue((self.state / "build/rust-port/partial").exists())
        self.assertFalse((self.prepared / "rust-port/manifest.json").exists())
        self.assertFalse(any(self.state.glob("cache/*/*/manifest.json")))
        (self.root / "fail").unlink()
        result = self.prepare()
        self.assertIn("incremental build", result.stderr)
        self.assertEqual(self.count(), 2)

    def test_setup_mutation_fails_before_compilation_with_changed_paths(self):
        (self.root / "mutation").write_text("setup")
        result = self.prepare(success=False)
        self.assertIn("during toolchain setup", result.stderr)
        self.assertIn("main.rs", result.stderr)
        self.assertEqual(self.count(), 0)
        self.assertFalse((self.prepared / "rust-port/manifest.json").exists())

    def test_postinstall_inherits_locked_mode_without_unrelated_auto_installs(self):
        (self.root / "mutation").write_text("postinstall")
        self.prepare()
        self.assertEqual(self.count(), 1)
        self.assertFalse(self.manifest()["dirty"])
        self.assertIn("binary cache hit", self.prepare().stderr)

    def test_build_mutation_rejects_publication_with_changed_paths(self):
        (self.root / "mutation").write_text("build")
        result = self.prepare(success=False)
        self.assertIn("source changed during preparation", result.stderr)
        self.assertIn("main.rs", result.stderr)
        self.assertEqual(self.count(), 1)
        self.assertFalse((self.prepared / "rust-port/manifest.json").exists())

    def test_concurrent_preparation_builds_only_once(self):
        plan = self.root / "plan.json"
        self.prepare("--resolve-only", "--plan", str(plan))
        argv = [
            sys.executable,
            "-m",
            "bench.cli",
            "prepare",
            *self.flags,
            "--candidates",
            "rust-port",
            "--plan",
            str(plan),
        ]
        processes = [
            subprocess.Popen(
                argv,
                env=self.environment,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
            )
            for _ in range(2)
        ]
        for process in processes:
            stdout, stderr = process.communicate(timeout=30)
            self.assertEqual(process.returncode, 0, stdout + stderr)
        self.assertEqual(self.count(), 1)

    def test_supplied_binary_change_after_resolution_is_rejected(self):
        plan = self.root / "plan.json"
        self.prepare(
            "--binary",
            f"rust-port={self.binary}",
            "--resolve-only",
            "--plan",
            str(plan),
        )
        self.binary.write_text(self.binary.read_text() + "# changed\n")
        result = self.prepare("--plan", str(plan), success=False)
        self.assertIn("supplied binary changed", result.stderr)
        self.assertEqual(self.count(), 0)

    def test_run_and_report_do_not_invoke_preparation(self):
        self.prepare()
        self.cli(
            "prepare",
            *self.flags,
            "--candidates",
            "upstream",
            "--binary",
            f"upstream={self.binary}",
        )
        corpus = self.root / "corpus"
        out = self.root / "run"
        self.cli("corpus", "--out", str(corpus))
        # Fail if either command touches the build adapter.
        (self.tools / "mise").write_text("#!/bin/sh\nexit 99\n")
        self.cli(
            "run",
            "--config",
            str(self.config),
            "--prepared",
            str(self.prepared),
            "--corpus",
            str(corpus),
            "--out",
            str(out),
            "--scenarios",
            "startup",
            "--rounds",
            "2",
            "--runs",
            "2",
            "--warmup",
            "0",
        )
        raw = (out / "run.json").read_bytes()
        self.cli("report", str(out))
        report = (out / "report.md").read_bytes()
        summary = (out / "summary.json").read_bytes()
        self.cli("report", str(out))
        self.assertEqual(raw, (out / "run.json").read_bytes())
        self.assertEqual(report, (out / "report.md").read_bytes())
        self.assertEqual(summary, (out / "summary.json").read_bytes())
        self.assertEqual(self.count(), 1)
        result = self.cli(
            "run",
            "--config",
            str(self.config),
            "--prepared",
            str(self.prepared),
            "--corpus",
            str(corpus),
            "--out",
            str(out),
            success=False,
        )
        self.assertIn("already contains a run", result.stderr)

    def test_default_command_composes_all_stages(self):
        output = self.root / "composed"
        self.cli(
            *self.flags,
            "--binary",
            f"upstream={self.binary}",
            "--source",
            f"rust-port={self.source}",
            "--corpus",
            str(self.root / "corpus"),
            "--out",
            str(output),
            "--scenarios",
            "startup",
            "--rounds",
            "1",
            "--runs",
            "2",
            "--warmup",
            "0",
        )
        for filename in ("run.json", "summary.json", "report.md"):
            self.assertTrue((output / filename).is_file())
        self.assertEqual(self.count(), 1)


if __name__ == "__main__":
    unittest.main()
