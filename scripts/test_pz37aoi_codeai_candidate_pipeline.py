#!/usr/bin/env python3
"""AOI source-bound CodeAI gates: regression checks against false certification."""
from __future__ import annotations
import hashlib
import json
from copy import deepcopy
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent))
import pz37aoi_codeai_candidate_pipeline as gates


class AOIGateTests(unittest.TestCase):
    def pack(self):
        root = Path(__file__).resolve().parents[1]
        return root, json.loads((root / "scripts/pz37aoi_candidate_strategies.json").read_text())

    def test_candidate_contracts_equal_and_explicit(self):
        root, pack = self.pack()
        gates.validate_candidate_contracts(pack)
        self.assertEqual(len(pack["declarations"]), 1)
        self.assertNotEqual(pack["strategies"]["A"], pack["strategies"]["B"])
        self.assertEqual((root / pack["target"]).read_bytes(), pack["strategies"]["A"].encode())
        for source in pack["strategies"].values():
            for decl in pack["declarations"]:
                self.assertIn("#print axioms " + decl, source)
            self.assertIn("norm_integral_le_of_norm_le_const", source)
            self.assertNotIn("sorry", source)

    def test_reject_changed_public_theorem(self):
        _, pack = self.pack()
        pack["strategies"]["B"] = pack["strategies"]["B"].replace(
            "64 * beta^2 *", "65 * beta^2 *", 1)
        with self.assertRaisesRegex(ValueError, "statements"):
            gates.validate_candidate_contracts(pack)

    def test_reject_unbound_unresolved_slot(self):
        _, pack = self.pack()
        pack["unresolved_binding_slots"] = ["strategies.B"]
        with self.assertRaisesRegex(ValueError, "unresolved"):
            gates.validate_candidate_contracts(pack)

    def test_exact_context_and_native_version_binding(self):
        from runtime.kuuos_codeai_candidate_patch_envelope_v0_1 import canonical_digest
        root, pack = self.pack()
        raw = gates.snapshot(root, pack)
        native, auxiliary, projection = gates.prepare_native_context(raw, pack)
        self.assertEqual(len(raw), 8)
        self.assertEqual(len(native), 8)
        self.assertEqual(auxiliary["sources"], [])
        self.assertEqual(projection["raw_source_snapshot_digest"], canonical_digest(raw))
        self.assertEqual(projection["native_repository_snapshot_digest"], canonical_digest(native))
        self.assertFalse(projection["source_normalization_performed"])

    def test_reject_changed_original_blob(self):
        root, pack = self.pack()
        raw = gates.snapshot(root, pack)
        path = next(iter(raw))
        raw[path] += "-- changed\n"
        with self.assertRaisesRegex(ValueError, "source byte identity"):
            gates.prepare_native_context(raw, pack)

    def test_source_sha_gate(self):
        with tempfile.TemporaryDirectory() as temp:
            path = Path(temp) / "source.lean"
            path.write_bytes(b"theorem a : True := by trivial\n")
            digest = hashlib.sha256(path.read_bytes()).hexdigest()
            self.assertEqual(gates.require_exact_source(path, digest), path.read_bytes())
            path.write_bytes(path.read_bytes() + b"\n")
            with self.assertRaisesRegex(ValueError, "source changed"):
                gates.require_exact_source(path, digest)

    def test_audit_rejects_sorry_and_warning(self):
        decls = ["MGAP4D.MathlibAnalytic.a"]
        ok = "'MGAP4D.MathlibAnalytic.a' depends on axioms: [propext, Classical.choice, Quot.sound]"
        self.assertEqual(gates.audit_lean_output(ok, 0, decls)["warning_count"], 0)
        for bad in [ok + "\nCandidate.lean:1:0: warning: uncertain",
                    "'MGAP4D.MathlibAnalytic.a' depends on axioms: [sorryAx]"]:
            with self.assertRaises(ValueError):
                gates.audit_lean_output(bad, 0, decls)

    def test_mcp_rejects_incomplete_semantics(self):
        decls = ["MGAP4D.MathlibAnalytic.a"]
        ok = "'MGAP4D.MathlibAnalytic.a' depends on axioms: [propext, Classical.choice, Quot.sound]"
        direct = gates.audit_lean_output(ok, 0, decls)
        valid = {"success": True, "partial": False, "timed_out": False,
                 "still_elaborating_lines": None, "failed_dependencies": [],
                 "items": [{"severity": "info", "message": ok}]}
        self.assertEqual(gates.audit_complete_mcp_output(valid, decls, direct), direct)
        for key, value in [("partial", True), ("timed_out", True),
                           ("still_elaborating_lines", [1]), ("failed_dependencies", ["/tmp/a"])]:
            body = deepcopy(valid)
            body[key] = value
            with self.assertRaises(ValueError):
                gates.audit_complete_mcp_output(body, decls, direct)


if __name__ == "__main__":
    unittest.main()
