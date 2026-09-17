import pathlib
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[1]
RECEIVER = ROOT / ".github/workflows/chatgpt-ci-completion-dispatch-v0-1.yml"
PRIMARY = ROOT / ".github/workflows/chatgpt-ci-completion-push-v0-1.yml"
VALIDATION = ROOT / ".github/workflows/chatgpt-ci-completion-dispatch-validation-v0-1.yml"
SOURCE = ROOT / ".github/workflows/pr-lean-fast-check.yml"


class WorkflowWiringTests(unittest.TestCase):
    def test_receiver_uses_repository_dispatch_and_trusted_main(self):
        text = RECEIVER.read_text(encoding="utf-8")
        self.assertIn("repository_dispatch:", text)
        self.assertIn("types: [chatgpt_ci_completion_dispatch_v0_1]", text)
        self.assertIn("actions: read", text)
        self.assertIn("contents: read", text)
        self.assertIn("issues: write", text)
        self.assertIn("pull-requests: write", text)
        self.assertNotIn("pull-requests: read", text)
        self.assertIn("ref: main", text)
        self.assertIn("persist-credentials: false", text)
        self.assertIn(
            "python3 -m unittest -v tests.test_chatgpt_ci_completion_dispatch_v0_1",
            text,
        )
        self.assertIn("scripts/chatgpt_ci_completion_dispatch_v0_1.py", text)


    def test_primary_workflow_uses_pr_write_and_is_validation_tracked(self):
        primary = PRIMARY.read_text(encoding="utf-8")
        self.assertIn("issues: write", primary)
        self.assertIn("pull-requests: write", primary)
        self.assertNotIn("pull-requests: read", primary)
        validation = VALIDATION.read_text(encoding="utf-8")
        self.assertIn(
            '".github/workflows/chatgpt-ci-completion-push-v0-1.yml"',
            validation,
        )

    def test_mgap_source_gate_dispatches_exact_identity_nonfatally(self):
        text = SOURCE.read_text(encoding="utf-8")
        self.assertIn("chatgpt-completion-dispatch:", text)
        self.assertIn("needs: pr-lean-fast-check", text)
        self.assertIn("github.event_name == 'pull_request'", text)
        self.assertIn("contents: write", text)
        self.assertIn("chatgpt_ci_completion_dispatch_v0_1", text)
        self.assertIn("${{ github.event.pull_request.number }}", text)
        self.assertIn("${{ github.run_id }}", text)
        self.assertIn("${{ github.run_attempt }}", text)
        self.assertIn("${{ github.event.pull_request.head.sha }}", text)
        self.assertIn("${{ github.event.pull_request.head.ref }}", text)
        self.assertIn("PR Lean Fast Check", text)
        self.assertIn('if [ "${http_code}" != "204" ]; then', text)
        finalizer = text.split("chatgpt-completion-dispatch:", 1)[1]
        self.assertNotIn("exit 1", finalizer)


if __name__ == "__main__":
    unittest.main()
