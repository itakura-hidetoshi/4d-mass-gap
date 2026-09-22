#!/usr/bin/env python3
"""Regression tests for changed-Lean CI routing, not for Lean theorem validity.

Run the real Bash checker in temporary Git repositories. A controlled Lake
executable models a direct check accepting stale imports while a dependency-
aware build fails. No network, Lean installation, or repository writes are used.
"""
from __future__ import annotations

import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

SCRIPT = Path(__file__).resolve().with_name("check_changed_lean.sh")
AUDITS = (
    "audit_changed_lean_preflight.py",
    "audit_lean_forbidden_tokens.py",
    "audit_hard_physical_residual_ledger.py",
    "audit_bridge_coherence.py",
    "audit_final_physical_carrier_routing.py",
    "audit_os_wightman_mass_gap_bridge.py",
)
BRIDGE = "MGAP4D.MathlibAnalytic.EuclideanYangMillsMeasureConstructionExternalAuditBridge"


class ChangedLeanDependencyCheck(unittest.TestCase):
    def setUp(self) -> None:
        self.tmp = tempfile.TemporaryDirectory(prefix="changed-lean-test-")
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        (self.root / "scripts").mkdir()
        shutil.copyfile(SCRIPT, self.root / "scripts/check_changed_lean.sh")
        for name in AUDITS:
            (self.root / "scripts" / name).write_text("# fixture audit\n", encoding="utf-8")
        (self.root / "lakefile.lean").write_text("require mathlib\n", encoding="utf-8")
        (self.root / "lake-manifest.json").write_text(
            '{"packages":[{"name":"mathlib"}]}\n', encoding="utf-8"
        )
        (self.root / "lean-toolchain").write_text("fixture-toolchain\n", encoding="utf-8")
        (self.root / "MGAP4D").mkdir()
        (self.root / "MGAP4D/A.lean").write_text("example : True := trivial\n", encoding="utf-8")
        (self.root / "MGAP4D/B.lean").write_text("import MGAP4D.A\n", encoding="utf-8")
        self.git("init", "-q")
        self.git("config", "user.name", "CI regression fixture")
        self.git("config", "user.email", "fixture@example.invalid")
        self.git("config", "commit.gpgsign", "false")
        self.commit()
        self.base = self.git("rev-parse", "HEAD").stdout.strip()
        (self.root / ".lake/packages/mathlib/.lake/build/lib/lean/Mathlib").mkdir(parents=True)
        (self.root / ".lake/build/lib/lean/MGAP4D").mkdir(parents=True)
        self.bin = self.root / "test-bin"
        self.bin.mkdir()
        lake = self.bin / "lake"
        lake.write_text(
            '#!/usr/bin/env bash\n'
            'printf "%s\\n" "$*" >> "$LAKE_CALLS"\n'
            'case "$1" in\n'
            '  env) exit "${DIRECT_EXIT:-0}" ;;\n'
            '  build) exit "${BUILD_EXIT:-0}" ;;\n'
            '  *) exit 0 ;;\n'
            'esac\n', encoding="utf-8"
        )
        lake.chmod(0o755)

    def git(self, *args: str) -> subprocess.CompletedProcess[str]:
        return subprocess.run(
            ["git", *args], cwd=self.root, capture_output=True, text=True,
            check=True, timeout=20,
        )

    def commit(self) -> None:
        self.git("add", "scripts", "MGAP4D", "lakefile.lean", "lake-manifest.json", "lean-toolchain")
        self.git("commit", "-qm", "fixture")

    def change(self, path: str, text: str) -> None:
        p = self.root / path
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(text, encoding="utf-8")
        self.git("add", path)
        self.git("commit", "-qm", "change fixture")

    def run_check(self, *, direct: int = 0, build: int = 0) -> tuple[subprocess.CompletedProcess[str], list[str]]:
        calls_path = self.root / "lake-calls.txt"
        env = os.environ.copy()
        env.update(
            PATH=str(self.bin) + os.pathsep + env["PATH"],
            LAKE_CALLS=str(calls_path), DIRECT_EXIT=str(direct), BUILD_EXIT=str(build),
        )
        result = subprocess.run(
            ["bash", "scripts/check_changed_lean.sh", self.base], cwd=self.root,
            env=env, capture_output=True, text=True, timeout=30,
        )
        calls = calls_path.read_text(encoding="utf-8").splitlines() if calls_path.exists() else []
        return result, calls

    def test_direct_success_does_not_bypass_dependency_build(self) -> None:
        self.change("MGAP4D/A.lean", "example : True := by trivial\n")
        self.change("MGAP4D/B.lean", "import MGAP4D.A\n-- changed consumer\n")
        result, calls = self.run_check()
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("build MGAP4D.B", calls)
        self.assertNotIn("build MGAP4D.A MGAP4D.B", calls)

    def test_dependency_failure_is_not_hidden_by_direct_success(self) -> None:
        self.change("MGAP4D/B.lean", "import MGAP4D.A\n-- changed consumer\n")
        result, _ = self.run_check(direct=0, build=17)
        self.assertEqual(result.returncode, 17, result.stdout + result.stderr)

    def test_cold_project_cache_skips_predictably_failing_direct_check(self) -> None:
        shutil.rmtree(self.root / ".lake/build")
        self.change("MGAP4D/B.lean", "import MGAP4D.A\n-- cold build\n")
        result, calls = self.run_check(direct=2)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertFalse(any(c.startswith("env lean") for c in calls), calls)
        self.assertIn("build MGAP4D.B", calls)

    def test_build_error_is_preserved_after_direct_error(self) -> None:
        self.change("MGAP4D/B.lean", "import MGAP4D.A\n-- invalid fixture\n")
        result, _ = self.run_check(direct=1, build=23)
        self.assertEqual(result.returncode, 23)

    def test_lake_inputs_require_dependency_build(self) -> None:
        self.change("MGAP4D/B.lean", "import MGAP4D.A\n-- new toolchain\n")
        self.change("lean-toolchain", "other-fixture-toolchain\n")
        result, calls = self.run_check()
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(calls, ["build MGAP4D.B"])

    def test_docs_only_keeps_static_lane(self) -> None:
        self.change("README.md", "Documentation-only fixture.\n")
        result, calls = self.run_check()
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(calls, [])

    def test_aggregate_only_keeps_static_lane(self) -> None:
        self.change("MGAP4D/MathlibAnalytic.lean", "import MGAP4D.B\n")
        result, calls = self.run_check()
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(calls, [])

    def test_sensitive_audit_keeps_its_build_target(self) -> None:
        self.change("scripts/audit_os_wightman_mass_gap_bridge.py", "# changed audit fixture\n")
        result, calls = self.run_check()
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(calls, ["build " + BRIDGE])


if __name__ == "__main__":
    unittest.main()
