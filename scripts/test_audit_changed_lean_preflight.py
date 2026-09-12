#!/usr/bin/env python3
"""Regression tests for changed-Lean deletion handling."""

from __future__ import annotations

import shutil
import subprocess
import tempfile
import textwrap
import unittest
from pathlib import Path


PREFLIGHT_SCRIPT = Path(__file__).with_name("audit_changed_lean_preflight.sh")
FAST_CHECK_SCRIPT = Path(__file__).with_name("check_changed_lean.sh")


def init_repo(root: Path) -> None:
    subprocess.run(["git", "init", "-q"], cwd=root, check=True)
    subprocess.run(
        ["git", "config", "user.email", "preflight-test@example.invalid"],
        cwd=root,
        check=True,
    )
    subprocess.run(
        ["git", "config", "user.name", "preflight-test"],
        cwd=root,
        check=True,
    )


def commit(root: Path, message: str) -> str:
    subprocess.run(["git", "add", "-A"], cwd=root, check=True)
    subprocess.run(["git", "commit", "-qm", message], cwd=root, check=True)
    return subprocess.run(
        ["git", "rev-parse", "HEAD"],
        cwd=root,
        check=True,
        capture_output=True,
        text=True,
    ).stdout.strip()


class ChangedLeanPreflightTest(unittest.TestCase):
    def test_deleted_lean_files_are_not_audited(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            root = Path(raw_dir)
            scripts = root / "scripts"
            lean_dir = root / "MGAP4D"
            scripts.mkdir()
            lean_dir.mkdir()

            shutil.copy2(PREFLIGHT_SCRIPT, scripts / PREFLIGHT_SCRIPT.name)
            (scripts / "audit_lean_source_integrity.py").write_text(
                textwrap.dedent(
                    """\
                    from pathlib import Path
                    import sys

                    missing = [path for path in sys.argv[1:] if not Path(path).is_file()]
                    if missing:
                        print("missing changed Lean files:", *missing)
                        raise SystemExit(1)
                    """
                ),
                encoding="utf-8",
            )
            (scripts / "audit_changed_lean_preflight.py").write_text(
                "raise SystemExit(0)\n",
                encoding="utf-8",
            )

            init_repo(root)
            deleted = lean_dir / "Deleted.lean"
            deleted.write_text("theorem old : True := by trivial\n", encoding="utf-8")
            base = commit(root, "base")

            deleted.unlink()
            (lean_dir / "Added.lean").write_text(
                "theorem new : True := by trivial\n",
                encoding="utf-8",
            )
            commit(root, "head")

            result = subprocess.run(
                ["bash", f"scripts/{PREFLIGHT_SCRIPT.name}", base],
                cwd=root,
                capture_output=True,
                text=True,
                check=False,
            )
            output = result.stdout + result.stderr

            self.assertEqual(result.returncode, 0, output)
            self.assertIn("MGAP4D/Added.lean", output)
            self.assertNotIn("MGAP4D/Deleted.lean", output)

    def test_fast_check_ignores_deleted_lean_files(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            root = Path(raw_dir)
            scripts = root / "scripts"
            lean_dir = root / "MGAP4D"
            scripts.mkdir()
            lean_dir.mkdir()

            shutil.copy2(FAST_CHECK_SCRIPT, scripts / FAST_CHECK_SCRIPT.name)
            for name in (
                "audit_lean_forbidden_tokens.py",
                "audit_hard_physical_residual_ledger.py",
                "audit_bridge_coherence.py",
                "audit_final_physical_carrier_routing.py",
                "audit_os_wightman_mass_gap_bridge.py",
            ):
                (scripts / name).write_text("raise SystemExit(0)\n", encoding="utf-8")
            (scripts / "audit_changed_lean_preflight.py").write_text(
                "raise SystemExit('deleted Lean path reached changed-file audit')\n",
                encoding="utf-8",
            )

            init_repo(root)
            deleted = lean_dir / "Deleted.lean"
            deleted.write_text("theorem old : True := by trivial\n", encoding="utf-8")
            base = commit(root, "base")

            deleted.unlink()
            commit(root, "delete Lean file")

            result = subprocess.run(
                ["bash", f"scripts/{FAST_CHECK_SCRIPT.name}", base],
                cwd=root,
                capture_output=True,
                text=True,
                check=False,
            )
            output = result.stdout + result.stderr

            self.assertEqual(result.returncode, 0, output)
            self.assertIn("[fast] changed Lean files:\n<none>", output)
            self.assertIn("[fast] no Lean files changed", output)
            self.assertNotIn("deleted Lean path reached changed-file audit", output)


if __name__ == "__main__":
    unittest.main()
