#!/usr/bin/env python3
"""Evidence gates must reject false greens and changed candidate bytes."""
import tempfile
import unittest
from pathlib import Path

from pz37aoa_codeai_candidate_pipeline import audit_lean_output, require_exact_source, verify_original_lean_tree, run_captured
from pz37aoa_codeai_learning_handoff import build_aoa_learning_handoff

DECLS = ["MGAP4D.MathlibAnalytic.testA", "MGAP4D.MathlibAnalytic.testB"]
GOOD = "\n".join("'" + d + "' depends on axioms: [propext, Classical.choice, Quot.sound]" for d in DECLS)


class EvidenceGateTests(unittest.TestCase):
    def test_accepts_complete_standard_axiom_prints(self):
        self.assertEqual(audit_lean_output(GOOD, 0, DECLS)["audited_declarations"], DECLS)

    def test_rejects_failed_exit_even_with_axiom_prints(self):
        with self.assertRaisesRegex(ValueError, "exit"):
            audit_lean_output(GOOD, 1, DECLS)

    def test_rejects_missing_print(self):
        with self.assertRaisesRegex(ValueError, "missing"):
            audit_lean_output(GOOD.splitlines()[0], 0, DECLS)

    def test_rejects_sorry_axiom(self):
        with self.assertRaisesRegex(ValueError, "axiom"):
            audit_lean_output(GOOD.replace("Quot.sound", "sorryAx"), 0, DECLS)

    def test_rejects_nonstandard_axiom(self):
        with self.assertRaisesRegex(ValueError, "axiom"):
            audit_lean_output(GOOD.replace("Quot.sound", "unexpectedAssumption"), 0, DECLS)

    def test_rejects_warning_anywhere_in_full_log(self):
        with self.assertRaisesRegex(ValueError, "diagnostic"):
            audit_lean_output("Candidate.lean:1:0: warning: incomplete audit\n" + "x" * 10000 + "\n" + GOOD, 0, DECLS)

    def test_rejects_same_filename_with_changed_source(self):
        with tempfile.TemporaryDirectory() as temp:
            path = Path(temp) / "Candidate.lean"
            path.write_text("original\n")
            import hashlib
            digest = hashlib.sha256(path.read_bytes()).hexdigest()
            self.assertEqual(require_exact_source(path, digest), b"original\n")
            path.write_text("different\n")
            with self.assertRaisesRegex(ValueError, "source"):
                require_exact_source(path, digest)

    def handoff_fixture(self, direct=None, mcp=None):
        import hashlib
        source = "fixture only; no Lean execution"
        digest = hashlib.sha256(source.encode()).hexdigest()
        return build_aoa_learning_handoff(
            source_binding={"repository_full_name": "fixture/repo",
                            "source_commit_sha": "0" * 40, "source_tree_sha": "0" * 40,
                            "source_actor_id": None, "runner_id": None},
            candidate_patch=None, candidate_source=source, context_files={},
            direct_lean_receipt=None if direct is None else dict(direct, candidate_source_sha256=digest),
            lean_mcp_receipt=None if mcp is None else dict(mcp, candidate_source_sha256=digest),
            toolchain_receipt=None, environment_receipt=None, observed_epoch=1)

    def test_learning_does_not_count_exit_zero_without_axiom_audit(self):
        result = self.handoff_fixture(direct={"exit_code": 0})
        self.assertFalse(result["observed_checks"]["direct_lean_passed"])

    def test_learning_does_not_count_mcp_success_with_warning(self):
        result = self.handoff_fixture(mcp={"success": True, "partial": False,
            "failed_dependencies": [], "items": [{"severity": "warning", "message": "fixture"}]})
        self.assertFalse(result["observed_checks"]["real_lean_mcp_passed"])

    def test_rejects_changed_transitive_physical_source(self):
        import hashlib
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            path = root / "MGAP4D/Original.lean"
            path.parent.mkdir()
            raw = b"original physical definition\n"
            path.write_bytes(raw)
            blob = hashlib.sha1(b"blob " + str(len(raw)).encode() + b"\0" + raw).digest()
            entry = b"100644 Original.lean\0" + blob
            expected = hashlib.sha1(b"tree " + str(len(entry)).encode() + b"\0" + entry).hexdigest()
            self.assertEqual(verify_original_lean_tree(root, expected, "MGAP4D/New.lean"), 1)
            path.write_bytes(b"changed physical definition\n")
            with self.assertRaisesRegex(ValueError, "baseline"):
                verify_original_lean_tree(root, expected, "MGAP4D/New.lean")

    def test_rejects_unaccounted_new_lean_file(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            (root / "MGAP4D").mkdir()
            (root / "MGAP4D/Unrelated.lean").write_text("unexpected\n")
            with self.assertRaisesRegex(ValueError, "baseline"):
                verify_original_lean_tree(root, "4b825dc642cb6eb9a060e54bf8d69288fbee4904", "MGAP4D/New.lean")

    def test_timeout_preserves_partial_output_and_is_not_complete(self):
        import sys
        result = run_captured([sys.executable, "-c",
            "import time; print('partial diagnostic', flush=True); time.sleep(2)"], Path.cwd(), 0.3)
        self.assertIsNone(result["exit_code"])
        self.assertFalse(result["complete"])
        self.assertIn("partial diagnostic", result["stdout"])


if __name__ == "__main__":
    unittest.main()
