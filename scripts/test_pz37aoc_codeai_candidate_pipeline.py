#!/usr/bin/env python3
"""Evidence gates must reject false greens and changed candidate bytes."""
import tempfile
import unittest
import pz37aoc_codeai_candidate_pipeline as gates
from pathlib import Path
from copy import deepcopy
import hashlib
import json

from pz37aoc_codeai_candidate_pipeline import audit_lean_output, require_exact_source, verify_original_lean_tree, run_captured
from pz37aoc_codeai_learning_handoff import build_aoc_learning_handoff

DECLS = ["MGAP4D.MathlibAnalytic.testA", "MGAP4D.MathlibAnalytic.testB"]
GOOD = "\n".join("'" + d + "' depends on axioms: [propext, Classical.choice, Quot.sound]" for d in DECLS)


class EvidenceGateTests(unittest.TestCase):
    def raw_context_fixture(self):
        root = Path(__file__).resolve().parents[1]
        pack = json.loads((root / "scripts/pz37aoc_candidate_strategies.json").read_text())
        source_root = root if (root / "MGAP4D").exists() else root / "observed-baseline"
        return gates.snapshot(source_root, pack), pack

    def prepare_context(self, raw, pack):
        self.assertTrue(hasattr(gates, "prepare_native_context"),
                        "raw source needs an explicit non-normalizing native representation")
        return gates.prepare_native_context(raw, pack)

    def test_raw_dependency_attachment_roundtrips_exact_original_bytes(self):
        raw, pack = self.raw_context_fixture()
        native, auxiliary, projection = self.prepare_context(raw, pack)
        path = pack["local_harnack_path"]
        original = raw[path].encode("utf-8")
        encoded = json.dumps(auxiliary, ensure_ascii=False, sort_keys=True)
        recovered = json.loads(encoded)["raw_source_utf8"].encode("utf-8")
        self.assertEqual(original, recovered)
        self.assertEqual(len(recovered), 22995)
        self.assertFalse(recovered.endswith(b"\n"))
        self.assertEqual(auxiliary["original_git_blob_sha1"],
                         "26867ad34c6a9f6e2f7ae25f7b6a388db4606870")
        self.assertEqual(auxiliary["original_source_sha256"], hashlib.sha256(original).hexdigest())
        self.assertNotIn(path, native)
        self.assertFalse(projection["source_normalization_performed"])
        self.assertEqual(raw[path].encode("utf-8"), original)

    def test_native_projection_binds_six_paths_and_all_seven_observed_sources(self):
        from runtime.kuuos_codeai_candidate_patch_envelope_v0_1 import canonical_digest
        from runtime.kuuos_codeai_autonomous_structured_edit_types_v0_1 import validate_repository
        raw, pack = self.raw_context_fixture()
        native, auxiliary, projection = self.prepare_context(raw, pack)
        self.assertEqual(len(raw), 7)
        self.assertEqual(len(native), 6)
        self.assertEqual(validate_repository(native)[1], [])
        self.assertEqual(projection["raw_source_snapshot_digest"], canonical_digest(raw))
        self.assertEqual(projection["native_repository_snapshot_digest"], canonical_digest(native))
        self.assertEqual(projection["native_observed_paths"], sorted(native))
        self.assertEqual(projection["auxiliary_source_digest"], auxiliary[gates.AUXILIARY_DIGEST_FIELD])
        self.assertEqual(projection[gates.PROJECTION_DIGEST_FIELD], canonical_digest(
            {k: v for k, v in projection.items() if k != gates.PROJECTION_DIGEST_FIELD}))

    def test_projection_rejects_another_noncanonical_dependency(self):
        raw, pack = self.raw_context_fixture()
        raw["lean-toolchain"] = raw["lean-toolchain"].rstrip("\n")
        modified = raw["lean-toolchain"].encode()
        pack = deepcopy(pack)
        pack["baseline_blobs"]["lean-toolchain"] = hashlib.sha1(
            b"blob " + str(len(modified)).encode() + b"\0" + modified).hexdigest()
        with self.assertRaisesRegex(ValueError, "unexpected noncanonical"):
            self.prepare_context(raw, pack)

    def test_projection_rejects_normalizing_the_original_dependency(self):
        raw, pack = self.raw_context_fixture()
        path = pack["local_harnack_path"]
        raw[path] += "\n"
        modified = raw[path].encode()
        pack = deepcopy(pack)
        pack["baseline_blobs"][path] = hashlib.sha1(
            b"blob " + str(len(modified)).encode() + b"\0" + modified).hexdigest()
        with self.assertRaisesRegex(ValueError, "exact auxiliary source"):
            self.prepare_context(raw, pack)

    def test_provider_prompt_rejects_changed_auxiliary_representation(self):
        from runtime.kuuos_codeai_candidate_patch_envelope_v0_1 import canonical_digest
        raw, pack = self.raw_context_fixture()
        native, auxiliary, _ = self.prepare_context(raw, pack)
        text = gates.intent_with_auxiliary_source("candidate-only request", auxiliary)
        self.assertLess(len(text.encode()), 40000)
        prompt = {"repository_files": native,
                  "repository_snapshot_digest": canonical_digest(native), "intent_text": text}
        gates.verify_native_prompt_context(prompt, native, text)
        prompt["intent_text"] = text + "\n"
        with self.assertRaisesRegex(ValueError, "auxiliary source transport"):
            gates.verify_native_prompt_context(prompt, native, text)

    def strategy_fixture(self):
        source = ("import Mathlib\nnamespace MGAP4D.MathlibAnalytic\n"
                  "noncomputable def coupling : Nat := 1\n"
                  "theorem result (n : Nat) : n = n := by\n  rfl\n"
                  "end MGAP4D.MathlibAnalytic\n")
        return {"declarations": ["MGAP4D.MathlibAnalytic.coupling",
                                  "MGAP4D.MathlibAnalytic.result"],
                "strategies": {"A": source, "B": source.replace("  rfl", "  exact rfl")}}

    def repair_fixture(self):
        from runtime.kuuos_codeai_candidate_patch_envelope_v0_1 import seal
        pack = self.strategy_fixture()
        pack.update(repository="fixture/repo", baseline_commit="0" * 40, target="MGAP4D/New.lean")
        source = pack["strategies"]["A"]
        log = "Candidate.lean:1:0: error: fixture only; no Lean was executed\n"
        attempt = {"proposal_id": "AOC-A", "run_id": 1, "head_sha": "1" * 40,
                   "job_id": 2, "artifact_id": 3, "artifact_archive_sha256": "2" * 64,
                   "source_artifact_path": "aoc-codeai/AOC-A.lean",
                   "failed_source_utf8": source, "failed_source_sha256": gates.sha256(source),
                   "direct_log_artifact_path": "aoc-codeai/AOC-A-direct.log",
                   "full_direct_log_utf8": log, "direct_log_sha256": gates.sha256(log),
                   "direct_exit_code": 1, "direct_complete": True, "failed_status": "DIRECT_FAILED",
                   "prior_candidate_patch_digest": "3" * 64, "prior_producer_session_id": "fixture-old-session"}
        context = {"schema_version": "aoc-observed-failed-lean-attempts-v1",
                   "repository_full_name": pack["repository"], "baseline_commit_sha": pack["baseline_commit"],
                   "target": pack["target"], "observed_failed_attempts": [attempt],
                   "external_artifact_reobservation_performed_by_kernel": False,
                   "full_failed_sources_and_diagnostics_preserved": True, "memory_promotion": "HOLD"}
        pack["repair_context"] = seal(context, "aoc_repair_context_digest")
        return pack

    def prepare_repair(self, pack):
        self.assertTrue(hasattr(gates, "prepare_repair_context"),
                        "repair requests must validate and carry complete failed source and diagnostics")
        return gates.prepare_repair_context(pack)

    def reseal_repair(self, pack):
        from runtime.kuuos_codeai_candidate_patch_envelope_v0_1 import seal
        pack["repair_context"] = seal(pack["repair_context"], "aoc_repair_context_digest")

    def test_repair_context_preserves_complete_failed_source_and_log(self):
        pack = self.repair_fixture()
        context = self.prepare_repair(pack)
        self.assertEqual(context, pack["repair_context"])
        text = gates.intent_with_auxiliary_source("repair request", {"fixture": True}, context)
        encoded = text.split("OBSERVED_FAILED_LEAN_ATTEMPTS_JSON\n", 1)[1]
        self.assertEqual(json.loads(encoded), context)

    def test_repair_context_rejects_changed_failed_source(self):
        pack = self.repair_fixture()
        pack["repair_context"]["observed_failed_attempts"][0]["failed_source_utf8"] += "\n"
        self.reseal_repair(pack)
        with self.assertRaisesRegex(ValueError, "failed source hash"):
            self.prepare_repair(pack)

    def test_repair_context_rejects_changed_full_diagnostics(self):
        pack = self.repair_fixture()
        pack["repair_context"]["observed_failed_attempts"][0]["full_direct_log_utf8"] += "tampered\n"
        self.reseal_repair(pack)
        with self.assertRaisesRegex(ValueError, "direct log hash"):
            self.prepare_repair(pack)

    def test_repair_context_rejects_changed_failed_public_contract(self):
        pack = self.repair_fixture()
        attempt = pack["repair_context"]["observed_failed_attempts"][0]
        attempt["failed_source_utf8"] = attempt["failed_source_utf8"].replace("n = n", "True")
        attempt["failed_source_sha256"] = gates.sha256(attempt["failed_source_utf8"])
        self.reseal_repair(pack)
        with self.assertRaisesRegex(ValueError, "failed source public contract"):
            self.prepare_repair(pack)

    def validate_fixture(self, pack):
        self.assertTrue(hasattr(gates, "validate_candidate_contracts"),
                        "public definitions require an explicit immutable candidate contract")
        gates.validate_candidate_contracts(pack)

    def test_accepts_identical_definition_and_statements_with_different_proofs(self):
        self.validate_fixture(self.strategy_fixture())

    def test_rejects_unresolved_draft_binding_slots(self):
        pack = self.strategy_fixture()
        pack["unresolved_binding_slots"] = ["strategies.B"]
        with self.assertRaisesRegex(ValueError, "unresolved binding"):
            self.validate_fixture(pack)

    def test_rejects_absent_second_complete_strategy(self):
        pack = self.strategy_fixture()
        pack["strategies"]["B"] = None
        with self.assertRaisesRegex(ValueError, "two complete"):
            self.validate_fixture(pack)

    def test_rejects_changed_coupling_definition_between_candidates(self):
        pack = self.strategy_fixture()
        pack["strategies"]["B"] = pack["strategies"]["B"].replace("coupling : Nat := 1", "coupling : Nat := 2")
        with self.assertRaisesRegex(ValueError, "definition|preamble"):
            self.validate_fixture(pack)

    def test_rejects_weakened_statement_between_candidates(self):
        pack = self.strategy_fixture()
        pack["strategies"]["B"] = pack["strategies"]["B"].replace("n = n", "True")
        with self.assertRaisesRegex(ValueError, "statement"):
            self.validate_fixture(pack)

    def test_rejects_unaudited_public_definition(self):
        pack = self.strategy_fixture()
        pack["declarations"] = pack["declarations"][1:]
        with self.assertRaisesRegex(ValueError, "declaration"):
            self.validate_fixture(pack)

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
        return build_aoc_learning_handoff(
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
