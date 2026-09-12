#!/usr/bin/env python3
"""Regression test for changed-Lean preflight deletion handling."""

from __future__ import annotations

import shutil
import subprocess
import tempfile
import textwrap
import unittest
from pathlib import Path


SCRIPT = Path(__file__).with_name("audit_changed_lean_preflight.sh")


class ChangedLeanPreflightTest(unittest.TestCase):
    def test_deleted_lean_files_are_not_audited(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            root = Path(raw_dir)
            scripts = root / "scripts"
            lean_dir = root / "MGAP4D"
            scripts.mkdir()
            lean_dir.mkdir()

            shutil.copy2(SCRIPT, scripts / SCRIPT.name)
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

            deleted = lean_dir / "Deleted.lean"
            deleted.write_text("theorem old : True := by trivial\n", encoding="utf-8")
            subprocess.run(["git", "add", "."], cwd=root, check=True)
            subprocess.run(["git", "commit", "-qm", "base"], cwd=root, check=True)
            base = subprocess.run(
                ["git", "rev-parse", "HEAD"],
                cwd=root,
                check=True,
                capture_output=True,
                text=True,
            ).stdout.strip()

            deleted.unlink()
            (lean_dir / "Added.lean").write_text(
                "theorem new : True := by trivial\n",
                encoding="utf-8",
            )
            subprocess.run(["git", "add", "-A"], cwd=root, check=True)
            subprocess.run(["git", "commit", "-qm", "head"], cwd=root, check=True)

            result = subprocess.run(
                ["bash", f"scripts/{SCRIPT.name}", base],
                cwd=root,
                capture_output=True,
                text=True,
                check=False,
            )
            output = result.stdout + result.stderr

            self.assertEqual(result.returncode, 0, output)
            self.assertIn("MGAP4D/Added.lean", output)
            self.assertNotIn("MGAP4D/Deleted.lean", output)


if __name__ == "__main__":
    unittest.main()
