import copy
import unittest
import lean_compact_cache_binding_v2 as gate

SHA = "a" * 40
def good():
    run = {"head_sha": SHA, "event": "push", "head_branch": gate.FORMAL_BRANCH,
           "status": "completed", "conclusion": "success"}
    jobs = [
        {"name": "Changed Lean fast check", "status": "completed", "conclusion": "success",
         "steps": [{"name": "Run changed Lean fast check", "status": "completed", "conclusion": "success"},
                   {"name": "Save MGAP4D project olean cache from trusted branches", "status": "completed", "conclusion": "success"}]},
        {"name": "Publish MCP CI completion receipt", "status": "completed", "conclusion": "success"}
    ]
    return run, jobs

class Gates(unittest.TestCase):
    def test_exact_push(self):
        run, jobs = good()
        self.assertTrue(gate.successful_push(run, jobs, SHA))
        for k, v in [("head_sha", "b"*40), ("event","pull_request"), ("head_branch","main"),
                     ("status","in_progress"), ("conclusion","failure")]:
            altered = dict(run, **{k:v})
            self.assertFalse(gate.successful_push(altered, jobs, SHA))
    def test_static_only_not_lean(self):
        run, jobs = good()
        jobs[0]["steps"][0]["conclusion"] = "skipped"
        self.assertFalse(gate.successful_push(run,jobs,SHA))
    def test_missing_receipt_or_steps(self):
        run, jobs = good()
        self.assertFalse(gate.successful_push(run,jobs[:1],SHA))
        jobs[0]["steps"] = []
        self.assertFalse(gate.successful_push(run,jobs,SHA))
    def test_skip_save_still_requires_exact_restore_in_workflow(self):
        run, jobs = good()
        jobs[0]["steps"][1]["conclusion"] = "skipped"
        self.assertTrue(gate.successful_push(run,jobs,SHA))
    def test_math_tree_and_pins_select_only_exact_lineage(self):
        old = {"baseline_mgap4d_tree": "m", "baseline_blobs": {"lean-toolchain": "l"}}
        self.assertEqual(gate.select_cache_base("b"*40, old, SHA, copy.deepcopy(old)), SHA)
        new = copy.deepcopy(old)
        new["baseline_blobs"]["lean-toolchain"] = "different"
        self.assertEqual(gate.select_cache_base("b"*40,new,SHA,old),"b"*40)
    def test_tree_binding_rejects_truncated(self):
        with self.assertRaisesRegex(ValueError,"truncated"):
            gate.source_binding({"truncated": True})
    def test_invalid_sha(self):
        with self.assertRaises(ValueError):
            gate.exact_sha("main")
if __name__ == "__main__":
    unittest.main()
