# pyright: reportUnusedCallResult=false

import subprocess
import tempfile
import unittest
from pathlib import Path
from typing import Final, final, override

from affected_shell_cells import SelectorError, affected

MATRIX: Final = """\
[[cell]]
shell = "bash"
version = "5"
image = "shell-bash:5"
digest = "sha256:bash"
base = "debian@sha256:a"
dockerfile = "bash"
source = { kind = "tarball" }

[[cell]]
shell = "zsh"
version = "5.9"
image = "shell-zsh:5.9"
digest = "sha256:zsh"
base = "debian@sha256:a"
dockerfile = "zsh"
source = { kind = "tarball" }

[[cell]]
shell = "zsh-sh"
version = "5.9"
image = "shell-zsh-sh:5.9"
digest = "sha256:zsh-sh"
base = "debian@sha256:a"
dockerfile = "zsh"
source = { kind = "tarball" }

[[cell]]
shell = "netbsd-sh"
version = "11"
image = "shell-netbsd-sh:11"
digest = "sha256:netbsd"
base = "debian@sha256:a"
dockerfile = "netbsd-sh"
vm = true
source = { kind = "image" }
"""


@final
class SelectorTests(unittest.TestCase):
    tmp: tempfile.TemporaryDirectory[str]
    root: Path = Path()
    base: str = ""

    def __init__(self, methodName: str = "runTest") -> None:
        super().__init__(methodName)
        self.tmp = tempfile.TemporaryDirectory()

    @override
    def setUp(self):
        self.tmp.cleanup()
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name)
        (self.root / "validity").mkdir()
        (self.root / "docker/shells/zsh").mkdir(parents=True)
        (self.root / "docker/shells/netbsd-sh").mkdir(parents=True)
        (self.root / "validity/matrix.toml").write_text(MATRIX)
        (self.root / "validity/sources.toml").write_text(
            "[defaults]\nbase = 'debian'\n\n[shell.bash]\nversions=['5']\n\n[shell.zsh]\nversions=['5.9']\n"
        )
        self.git_run("git", "init", "-q")
        self.git_run("git", "config", "user.email", "test@example.invalid")
        self.git_run("git", "config", "user.name", "Test")
        self.git_run("git", "add", ".")
        self.git_run("git", "commit", "-qm", "base")
        self.base = self.git_run("git", "rev-parse", "HEAD").stdout.strip()

    @override
    def tearDown(self) -> None:
        self.tmp.cleanup()

    def git_run(self, *args: str) -> subprocess.CompletedProcess[str]:
        return subprocess.run(
            args, cwd=self.root, text=True, capture_output=True, check=True
        )

    def change(self, path: str, text: str) -> None:
        target = self.root / path
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(text)
        self.git_run("git", "add", ".")
        self.git_run("git", "commit", "-qm", "change")

    def test_matrix_field_change_selects_only_that_cell(self):
        changed = MATRIX.replace(
            'base = "debian@sha256:a"', 'base = "debian@sha256:b"', 1
        )
        self.change("validity/matrix.toml", changed)
        self.assertEqual(affected(self.base, cwd=self.root), ["bash:5"])

    def test_shared_dockerfile_selects_both_zsh_cells(self):
        self.change("docker/shells/zsh/Dockerfile", "FROM alpine\n")
        self.assertEqual(affected(self.base, cwd=self.root), ["zsh:5.9", "zsh-sh:5.9"])

    def test_vm_helper_selects_vm_cells_only(self):
        self.change("docker/shells/vm/vmsh", "changed\n")
        self.assertEqual(affected(self.base, cwd=self.root), ["netbsd-sh:11"])

    def test_fetch_script_selects_every_cell(self):
        self.change("docker/shells/fetch.sh", "changed\n")
        self.assertEqual(
            affected(self.base, cwd=self.root),
            ["bash:5", "zsh:5.9", "zsh-sh:5.9", "netbsd-sh:11"],
        )

    def test_source_shell_change_selects_that_shell(self):
        source = (
            (self.root / "validity/sources.toml")
            .read_text()
            .replace("versions=['5']", "versions=['6']")
        )
        self.change("validity/sources.toml", source)
        self.assertEqual(affected(self.base, cwd=self.root), ["bash:5"])

    def test_source_defaults_change_selects_every_cell(self):
        source = (
            (self.root / "validity/sources.toml")
            .read_text()
            .replace("base = 'debian'", "base = 'alpine'")
        )
        self.change("validity/sources.toml", source)
        self.assertEqual(
            affected(self.base, cwd=self.root),
            ["bash:5", "zsh:5.9", "zsh-sh:5.9", "netbsd-sh:11"],
        )

    def test_tooling_config_does_not_rebuild_images(self):
        self.change(".cargo/config.toml", "[build]\ntarget-dir = 'target'\n")
        self.assertEqual(affected(self.base, cwd=self.root), [])

    def test_image_builder_change_selects_every_cell(self):
        self.change("crates/conformance/src/validity/docker.rs", "changed\n")
        self.assertEqual(len(affected(self.base, cwd=self.root)), 4)

    def test_workflow_change_does_not_rebuild_images(self):
        self.change(".github/workflows/shells.yml", "changed\n")
        self.assertEqual(affected(self.base, cwd=self.root), [])

    def test_planner_change_does_not_rebuild_images(self):
        self.change("tools/affected_shell_cells.py", "changed\n")
        self.assertEqual(affected(self.base, cwd=self.root), [])

    def test_docs_do_not_build_images(self):
        self.change("docs/validity.md", "changed\n")
        self.assertEqual(affected(self.base, cwd=self.root), [])

    def test_deleted_cell_is_not_selected(self):
        self.change(
            "validity/matrix.toml",
            MATRIX.split('\n[[cell]]\nshell = "netbsd-sh"', 1)[0],
        )
        self.assertNotIn("netbsd-sh:11", affected(self.base, cwd=self.root))

    def test_digest_only_change_does_not_build(self):
        changed = MATRIX.replace('digest = "sha256:bash"', 'digest = "sha256:new"')
        self.change("validity/matrix.toml", changed)
        self.assertEqual(affected(self.base, cwd=self.root), [])

    def test_missing_registry_digest_is_always_selected(self):
        changed = MATRIX.replace('digest = "sha256:bash"\n', "", 1)
        (self.root / "validity/matrix.toml").write_text(changed)
        self.assertEqual(affected(None, cwd=self.root), ["bash:5"])

    def test_pin_only_current_matrix_change_is_detected(self):
        changed = MATRIX.replace(
            'base = "debian@sha256:a"', 'base = "debian@sha256:pinned"', 1
        )
        (self.root / "validity/matrix.toml").write_text(changed)
        self.assertEqual(affected(self.base, cwd=self.root), ["bash:5"])

    def test_merge_base_is_used_for_divergent_base(self):
        self.git_run("git", "checkout", "-qb", "other")
        self.change(
            "validity/matrix.toml",
            MATRIX.replace(
                'base = "debian@sha256:a"', 'base = "debian@sha256:other"', 1
            ),
        )
        divergent = self.git_run("git", "rev-parse", "HEAD").stdout.strip()
        self.git_run("git", "checkout", "-q", "-b", "feature", self.base)
        self.change(
            "validity/matrix.toml",
            MATRIX.replace(
                'base = "debian@sha256:a"', 'base = "debian@sha256:feature"', 1
            ),
        )
        self.assertEqual(affected(divergent, cwd=self.root), ["bash:5"])

    def test_missing_base_matrix_builds_all_current_cells(self):
        self.git_run("git", "rm", "-q", "validity/matrix.toml")
        self.git_run("git", "commit", "-qm", "remove matrix")
        missing_matrix_base = self.git_run("git", "rev-parse", "HEAD").stdout.strip()
        (self.root / "validity/matrix.toml").write_text(MATRIX)
        self.git_run("git", "add", "validity/matrix.toml")
        self.git_run("git", "commit", "-qm", "add matrix")
        self.assertEqual(
            affected(missing_matrix_base, cwd=self.root),
            ["bash:5", "zsh:5.9", "zsh-sh:5.9", "netbsd-sh:11"],
        )

    def test_malformed_current_matrix_fails(self):
        (self.root / "validity/matrix.toml").write_text("[[cell]\n")
        with self.assertRaises(SelectorError):
            affected(self.base, cwd=self.root)


if __name__ == "__main__":
    unittest.main()
