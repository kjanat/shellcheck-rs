import contextlib
import io
import tempfile
import unittest
from pathlib import Path

from bench.cli import main
from bench.report import actions_summary


class SummaryTests(unittest.TestCase):
    def test_ci_links_download_existing_evidence_and_keep_revision_links(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            diff = "precheck/omarchy-commands/rust-port.diff"
            (root / diff).parent.mkdir(parents=True)
            for file in (diff, "run.json", "summary.json", "timing.svg"):
                (root / file).write_text("evidence")
            revision = "https://github.com/omacom/omarchy/commit/abc123"
            report = (
                f"[source]({revision})\n"
                f"[output diff]({diff})\n"
                f"| rust-port | [diff]({diff}) |\n"
                "[raw run](run.json), [statistics](summary.json), [plot](timing.svg)\n"
            )
            (root / "report.md").write_text(report)
            artifact = (
                "https://github.com/kjanat/shellcheck-rs/actions/runs/123/artifacts/456"
            )
            output = io.StringIO()
            with contextlib.redirect_stdout(output):
                main(["summary", str(root), "--artifact-url", artifact])
            rendered = output.getvalue()
            self.assertIn(f"[source]({revision})", rendered)
            self.assertIn(f"[diff · `{diff}`]({artifact})", rendered)
            for file in (diff, "run.json", "summary.json", "timing.svg"):
                self.assertIn(f"`{file}`]({artifact})", rendered)
                self.assertNotIn(f"]({file})", rendered)
            self.assertIn("extract it", rendered)
            self.assertEqual((root / "report.md").read_text(), report)

    def test_missing_evidence_cannot_be_published_as_a_working_link(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "report.md").write_text("[diff](precheck/missing.diff)")
            with self.assertRaisesRegex(ValueError, "linked evidence is missing"):
                actions_summary(root, "https://github.com/repo/artifacts/123")

    def test_relative_artifact_url_is_rejected(self):
        with self.assertRaisesRegex(ValueError, "absolute HTTPS URL"):
            actions_summary(Path("unused"), "actions/runs/123/artifacts/456")
