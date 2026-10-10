"""Prove pinned input selection, provenance, and snapshot-relative execution."""

import contextlib
import hashlib
import io
import subprocess
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from bench.analyze import analyze
from bench.measure import load_scenarios, precheck
from bench.omarchy import prepare, snapshot
from bench.schema import CorpusManifest, CorpusSource, Manifest, Scenario
from tests.test_memory import SELFTEST_ORDERS, _synthetic_run


class OmarchyTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.source = self.root / "source"
        self.source.mkdir()
        self.out = self.root / "corpus"
        files = {
            "bin/no-execute-bit": b"#!/bin/bash\nprintf 'command\\n'\n",
            "bin/python": b"#!/usr/bin/python3\nprint('not shell')\n",
            "install/nested/fragment.sh": b"printf 'sourced fragment\\n'\n",
            "migrations/1.sh": b"#!/bin/bash\ntrue\n",
            "test/nested/check.sh": b"#!/bin/bash\ntrue\n",
            "default/bash/rc": b'source "$OMARCHY_PATH/default/bash/envs"\n',
            "default/bash/fns/helper": b"helper() { true; }\n",
            "default/bash/inputrc": b"set editing-mode emacs\n",
            "etc/mkinitcpio.conf.d/hooks.conf": b"HOOKS=(base udev)\n",
            "etc/systemd/example.conf": b"[Service]\nType=simple\n",
            "notes.txt": b"not a shell script\n",
        }
        for name, data in files.items():
            path = self.source / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(data)
        (self.source / "bin/link").symlink_to("no-execute-bit")
        self.git("init", "-b", "fixture")
        self.git("add", ".")
        self.git(
            "-c",
            "user.name=Fixture",
            "-c",
            "user.email=fixture@example.invalid",
            "-c",
            "commit.gpgsign=false",
            "commit",
            "-m",
            "Fixture",
        )
        self.identity = CorpusSource(
            repo="https://github.com/omacom/omarchy",
            pin=self.git("rev-parse", "HEAD"),
            prefix="omarchy",
            shell_globs=["default/bash/**", "etc/mkinitcpio.conf.d/*.conf"],
            exclude_globs=["default/bash/inputrc"],
        )

    def git(self, *args: str) -> str:
        return subprocess.check_output(
            ["git", "-C", str(self.source), *args], text=True, stderr=subprocess.DEVNULL
        ).strip()

    def import_corpus(self):
        entries = snapshot(self.source, self.out, self.identity)
        manifest = CorpusManifest(
            seed=0,
            generator="fixture",
            files=entries,
            sha256="0" * 64,
            sources={"omarchy": self.identity},
        )
        (self.out / "corpus.json").write_text(manifest.model_dump_json())
        return manifest

    def test_complete_selection_includes_nonexecutables_and_excludes_links(self):
        manifest = self.import_corpus()
        self.assertEqual(
            set(manifest.files),
            {
                "omarchy/bin/no-execute-bit",
                "omarchy/install/nested/fragment.sh",
                "omarchy/migrations/1.sh",
                "omarchy/test/nested/check.sh",
                "omarchy/default/bash/rc",
                "omarchy/default/bash/fns/helper",
                "omarchy/etc/mkinitcpio.conf.d/hooks.conf",
            },
        )
        for name, entry in manifest.files.items():
            original = (self.source / name.removeprefix("omarchy/")).read_bytes()
            self.assertEqual((self.out / name).read_bytes(), original)
            self.assertEqual(entry.sha256, hashlib.sha256(original).hexdigest())
        self.assertEqual(self.git("status", "--porcelain"), "")

    def test_wrong_revision_and_dirty_source_are_rejected_without_overwriting(self):
        wrong = self.identity.model_copy(update={"pin": "f" * 40})
        with self.assertRaisesRegex(ValueError, "expected"):
            snapshot(self.source, self.out, wrong)
        path = self.source / "bin/no-execute-bit"
        path.write_bytes(b"local changes\n")
        with self.assertRaisesRegex(ValueError, "local changes"):
            snapshot(self.source, self.out, self.identity)
        self.assertEqual(path.read_bytes(), b"local changes\n")
        self.assertFalse(self.out.exists())

    def test_cold_import_checks_out_pin_and_cache_hit_needs_no_remote_access(self):
        cache = self.root / "cache"

        def clone(argv):
            self.assertEqual(argv[:3], ["gh", "repo", "clone"])
            subprocess.run(
                ["git", "clone", "--no-checkout", str(self.source), str(cache)],
                check=True,
                capture_output=True,
            )
            return ""

        with (
            patch("bench.omarchy.spec", return_value=self.identity),
            patch("bench.omarchy.CHECKOUT", cache),
            patch("bench.omarchy.STATE", self.root / "state"),
        ):
            with patch("bench.omarchy.command", side_effect=clone) as remote:
                first, identity = prepare(self.out)
                remote.assert_called_once()
            with patch(
                "bench.omarchy.command",
                side_effect=AssertionError("unexpected remote access"),
            ):
                second, _ = prepare(self.root / "repeat")
            self.assertEqual(first, second)
            self.assertEqual(identity.pin, self.identity.pin)
            self.assertEqual(
                subprocess.check_output(
                    ["git", "-C", str(cache), "rev-parse", "HEAD"], text=True
                ).strip(),
                identity.pin,
            )
            self.assertEqual(self.git("branch", "--show-current"), "fixture")

    def test_recursive_groups_use_only_recorded_inputs_and_keep_budget(self):
        manifest = self.import_corpus()
        (self.out / "omarchy/bin/unrecorded").write_text("#!/bin/bash\nfalse\n")
        scenarios = load_scenarios(
            self.out, ["omarchy-commands", "omarchy-installation", "omarchy-all"]
        )
        self.assertEqual(
            scenarios["omarchy-commands"].args[4:], ["omarchy/bin/no-execute-bit"]
        )
        self.assertEqual(
            scenarios["omarchy-installation"].args[4:],
            ["omarchy/install/nested/fragment.sh"],
        )
        self.assertEqual(scenarios["omarchy-all"].args[4:], sorted(manifest.files))
        self.assertEqual(scenarios["omarchy-all"].cwd, "omarchy")
        self.assertEqual(scenarios["omarchy-all"].max_run_seconds, 60)

    def test_explicit_missing_dataset_has_actionable_error(self):
        self.out.mkdir()
        manifest = CorpusManifest(
            seed=0, generator="fixture", files={}, sha256="0" * 64
        )
        (self.out / "corpus.json").write_text(manifest.model_dump_json())
        with self.assertRaisesRegex(ValueError, "bench corpus --omarchy"):
            load_scenarios(self.out, ["omarchy-all"])

    def test_precheck_runs_from_snapshot_root_with_original_relative_paths(self):
        self.import_corpus()
        binary = self.root / "analyzer"
        binary.write_text('#!/bin/sh\nprintf \'%s\\n\' "$PWD" "$@"\n')
        binary.chmod(0o755)
        candidate = Manifest(
            name="upstream",
            kind="path",
            ref="fixture",
            pin="",
            binary=str(binary),
            binary_sha256="0" * 64,
            binary_bytes=binary.stat().st_size,
            version_output="fixture",
        )
        scenario = Scenario(
            description="fixture",
            label="Omarchy commands",
            args=["-f", "gcc", "omarchy/bin/no-execute-bit"],
            format="gcc",
            cwd="omarchy",
            max_run_seconds=60,
        )
        results = precheck(
            [candidate],
            "upstream",
            {"commands": scenario},
            self.out,
            self.root / "results",
            2,
            2**30,
            None,
            15,
        )
        output = (
            (self.root / "results/precheck/commands/upstream.stdout")
            .read_text()
            .splitlines()
        )
        self.assertEqual(
            output, [str(self.out / "omarchy"), "-f", "gcc", "bin/no-execute-bit"]
        )
        self.assertEqual(results["commands"]["upstream"].status, "ok")
        limited = precheck(
            [candidate],
            "upstream",
            {"commands": scenario.model_copy(update={"max_run_seconds": 0.000001})},
            self.out,
            self.root / "limited",
            2,
            2**30,
            None,
            15,
        )
        self.assertEqual(limited["commands"]["upstream"].status, "slow")

    def test_report_has_source_link_workload_label_and_exact_counts(self):
        run, _ = _synthetic_run(True, SELFTEST_ORDERS)
        run.corpus.sources = {"omarchy": self.identity}
        run.corpus.files = {"omarchy/bin/command": 23}
        run.scenarios["medium"].args = ["-f", "gcc", "omarchy/bin/command"]
        run.scenarios["medium"].format = "gcc"
        run.scenarios["medium"].label = "Omarchy runtime commands"
        results = self.root / "report"
        results.mkdir()
        (results / "run.json").write_text(run.model_dump_json())
        with (
            contextlib.redirect_stdout(io.StringIO()),
            contextlib.redirect_stderr(io.StringIO()),
        ):
            analyze(results, plots=False, resamples=200)
        report = (results / "report.md").read_text()
        self.assertIn(f"{self.identity.repo}/commit/{self.identity.pin}", report)
        self.assertIn("1 shell file, 23 lines", report)
        self.assertIn(
            "Omarchy runtime commands · 23-line script · GCC diagnostics", report
        )


if __name__ == "__main__":
    unittest.main()
