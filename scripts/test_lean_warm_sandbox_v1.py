#!/usr/bin/env python3
"""Regression tests for the warm runner's evidence boundaries, not Lean proof tests."""
import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent))
import lean_warm_sandbox_v1 as warm

DECL = "MGAP4D.MathlibAnalytic.example_theorem"
SOURCE = (f"import Mathlib.Tactic\nnamespace MGAP4D.MathlibAnalytic\n"
          f"set_option autoImplicit false\n"
          f"theorem example_theorem : True := by\n  trivial\n"
          f"#print axioms {DECL}\nend MGAP4D.MathlibAnalytic\n").encode()
AXIOMS = f"'{DECL}' depends on axioms: [propext, Classical.choice, Quot.sound]\n"

class FakeMCP:
    def __init__(self, reject=False):
        self.starts = 0
        self.calls = 0
        self.reject = reject

    def verify(self, path, raw, declarations, direct, out):
        if self.calls == 0:
            self.starts += 1
        self.calls += 1
        if self.reject:
            raise ValueError("partial or conflicting MCP evidence")
        self.path = path
        assert path.read_bytes() == raw
        return direct

class WarmGates(unittest.TestCase):
    def test_exact_source_and_strict_settings(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            p = root / "diagnostics" / "candidate.lean.txt"
            p.parent.mkdir()
            p.write_bytes(SOURCE)
            c = {"path": str(p.relative_to(root)), "blob": warm.blob(SOURCE)}
            self.assertEqual(warm.read_candidate(root, c, [DECL], ["Mathlib.Tactic"]), SOURCE)
            p.write_bytes(SOURCE + b"\n")
            with self.assertRaisesRegex(ValueError, "blob mismatch"):
                warm.read_candidate(root, c, [DECL], ["Mathlib.Tactic"])
            for bad in (b"set_option autoImplicit true\n", b"set_option warningAsError false\n",
                        b"set_option linter.unusedSimpArgs false\n", b"axiom extra : True\n"):
                raw = SOURCE + bad
                p.write_bytes(raw)
                c["blob"] = warm.blob(raw)
                with self.assertRaises(ValueError):
                    warm.read_candidate(root, c, [DECL], ["Mathlib.Tactic"])

    def test_statement_and_import_outline_detects_changes(self):
        first = warm.source_contract(SOURCE.decode())
        self.assertNotEqual(first, warm.source_contract(SOURCE.decode().replace(": True", ": False")))
        self.assertNotEqual(first, warm.source_contract(SOURCE.decode().replace("import Mathlib.Tactic", "import Mathlib")))

    def evaluate(self, statuses, reject_mcp=False):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            output = root / "evidence"
            output.mkdir()
            entries = [({"id": "R" + str(i+1)}, SOURCE) for i in range(len(statuses))]
            groups = {"test": ({"declarations": [DECL]}, entries)}
            calls = []
            def compile_candidate(command, cwd, timeout):
                self.assertEqual(command[:5], ["lake", "env", "lean", "-DautoImplicit=false",
                                               "-DwarningAsError=true"])
                status = statuses[len(calls)]
                calls.append(command)
                if status == "failed":
                    return {"complete": True, "exit_code": 1, "stdout": "error: invalid\n", "stderr": ""}
                if status == "timeout":
                    return {"complete": False, "exit_code": None, "stdout": AXIOMS, "stderr": ""}
                if status == "sorry":
                    return {"complete": True, "exit_code": 0, "stdout": AXIOMS.replace("propext", "sorryAx"), "stderr": ""}
                return {"complete": True, "exit_code": 0, "stdout": AXIOMS, "stderr": ""}
            mcp = FakeMCP(reject_mcp)
            result = warm.evaluate(root, output, {"baseline_commit": "fixed"}, groups, mcp, compile_candidate)
            return result, calls, mcp.calls

    def test_failed_candidate_does_not_call_mcp_and_first_green_stops(self):
        result, calls, mcp_calls = self.evaluate(["failed", "green", "green"])
        self.assertEqual(len(calls), 2)
        self.assertEqual(mcp_calls, 1)
        self.assertEqual(result["records"][0]["status"], "DIRECT_FAILED")
        self.assertEqual(result["records"][1]["status"], warm.GREEN)
        self.assertFalse(result["independent_ci_success"])
        self.assertFalse(result["source_promoted"])

    def test_timeout_and_sorry_are_not_green(self):
        result, calls, mcp_calls = self.evaluate(["timeout", "sorry"])
        self.assertEqual(mcp_calls, 0)
        self.assertEqual(result["winners"], {})

    def test_direct_green_is_not_complete_without_mcp(self):
        result, calls, mcp_calls = self.evaluate(["green", "green"], reject_mcp=True)
        self.assertEqual(mcp_calls, 1)
        self.assertEqual(len(calls), 1)
        self.assertEqual(result["records"][0]["status"], "MCP_OBSTRUCTION")
        self.assertEqual(result["winners"], {})

if __name__ == "__main__":
    unittest.main()
