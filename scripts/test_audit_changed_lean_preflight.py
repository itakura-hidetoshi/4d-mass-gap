#!/usr/bin/env python3
"""Regression tests for changed-Lean deletion, reuse, and bulk-check handling."""

from __future__ import annotations

import os
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


def install_fast_audit_stubs(scripts: Path) -> None:
    (scripts / "audit_changed_lean_preflight.py").write_text(
        "raise SystemExit(0)\n", encoding="utf-8"
    )
    for name in (
        "audit_lean_forbidden_tokens.py",
        "audit_hard_physical_residual_ledger.py",
        "audit_bridge_coherence.py",
        "audit_final_physical_carrier_routing.py",
        "audit_os_wightman_mass_gap_bridge.py",
    ):
        (scripts / name).write_text("raise SystemExit(0)\n", encoding="utf-8")


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
            install_fast_audit_stubs(scripts)
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

    def test_fast_check_reuses_identical_authoritative_lean_tree(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            root = Path(raw_dir)
            scripts = root / "scripts"
            lean_dir = root / "MGAP4D"
            scripts.mkdir()
            lean_dir.mkdir()

            shutil.copy2(FAST_CHECK_SCRIPT, scripts / FAST_CHECK_SCRIPT.name)
            install_fast_audit_stubs(scripts)
            init_repo(root)
            (root / "README.md").write_text("base\n", encoding="utf-8")
            base = commit(root, "main base")

            (lean_dir / "Authoritative.lean").write_text(
                "theorem authoritative : True := by trivial\n", encoding="utf-8"
            )
            theorem_ref = commit(root, "validated theorem tree")
            (root / "README.md").write_text("sync docs only\n", encoding="utf-8")
            commit(root, "docs after theorem tree")

            env = os.environ.copy()
            env["AUTHORITATIVE_THEOREM_REF"] = theorem_ref
            result = subprocess.run(
                ["bash", f"scripts/{FAST_CHECK_SCRIPT.name}", base],
                cwd=root,
                env=env,
                capture_output=True,
                text=True,
                check=False,
            )
            output = result.stdout + result.stderr

            self.assertEqual(result.returncode, 0, output)
            self.assertIn("reusing authoritative Lean/toolchain tree", output)
            self.assertIn("[fast] changed Lean files:\n<none>", output)
            self.assertIn("[fast] no Lean files changed", output)

    def test_fast_check_uses_lake_build_for_bulk_changed_leaf_set(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            root = Path(raw_dir)
            scripts = root / "scripts"
            lean_dir = root / "MGAP4D"
            fake_bin = root / "bin"
            scripts.mkdir()
            lean_dir.mkdir()
            fake_bin.mkdir()

            shutil.copy2(FAST_CHECK_SCRIPT, scripts / FAST_CHECK_SCRIPT.name)
            install_fast_audit_stubs(scripts)
            (root / "lake-manifest.json").write_text('{"packages": []}\n', encoding="utf-8")
            lake_log = root / "lake.log"
            fake_lake = fake_bin / "lake"
            fake_lake.write_text(
                '#!/usr/bin/env bash\nprintf "%s\\n" "$*" >> "$FAKE_LAKE_LOG"\nexit 0\n',
                encoding="utf-8",
            )
            fake_lake.chmod(0o755)

            init_repo(root)
            (root / "README.md").write_text("base\n", encoding="utf-8")
            base = commit(root, "base")
            for index in range(5):
                (lean_dir / f"Bulk{index}.lean").write_text(
                    f"theorem bulk{index} : True := by trivial\n",
                    encoding="utf-8",
                )
            commit(root, "bulk Lean change")

            env = os.environ.copy()
            env["PATH"] = f"{fake_bin}{os.pathsep}{env['PATH']}"
            env["FAKE_LAKE_LOG"] = str(lake_log)
            env["DIRECT_LEAN_MAX_FILES"] = "4"
            env["AUTHORITATIVE_THEOREM_REF"] = ""
            result = subprocess.run(
                ["bash", f"scripts/{FAST_CHECK_SCRIPT.name}", base],
                cwd=root,
                env=env,
                capture_output=True,
                text=True,
                check=False,
            )
            output = result.stdout + result.stderr

            self.assertEqual(result.returncode, 0, output)
            self.assertIn("5 changed Lean leaf files exceed direct elaboration limit 4", output)
            self.assertNotIn("[fast] direct Lean elaboration:", output)
            self.assertIn("build", lake_log.read_text(encoding="utf-8"))


if __name__ == "__main__":
    unittest.main()
