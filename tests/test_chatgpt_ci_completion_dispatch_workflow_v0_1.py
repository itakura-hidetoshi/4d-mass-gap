import pathlib
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[1]
VALIDATION = ROOT / ".github/workflows/chatgpt-ci-completion-dispatch-validation-v0-1.yml"
SOURCE = ROOT / ".github/workflows/pr-lean-fast-check.yml"


class WorkflowWiringTests(unittest.TestCase):
    def test_source_publishes_exact_head_status_receipt(self):
        text = SOURCE.read_text(encoding="utf-8")
        self.assertIn("chatgpt-ci-status-receipt:", text)
        self.assertIn("needs: pr-lean-fast-check", text)
        self.assertIn("always() && github.event_name == 'pull_request'", text)
        self.assertIn(
            "github.event.pull_request.head.repo.full_name == github.repository",
            text,
        )
        self.assertIn("statuses: write", text)
        self.assertIn("contents: read", text)
        self.assertIn("${{ github.event.pull_request.head.sha }}", text)
        self.assertIn("${{ github.run_id }}", text)
        self.assertIn("${{ github.run_attempt }}", text)
        self.assertIn("chatgpt-ci-receipt/PR Lean Fast Check", text)
        self.assertIn("/statuses/${HEAD_SHA}", text)
        self.assertIn("wake-up receipt only", text)
        self.assertIn("curl --fail-with-body", text)

    def test_source_no_longer_emits_comment_or_repository_dispatch(self):
        text = SOURCE.read_text(encoding="utf-8")
        self.assertNotIn("chatgpt-completion-dispatch:", text)
        self.assertNotIn("repository_dispatch", text)
        self.assertNotIn("issues: write", text)
        self.assertNotIn("pull-requests: write", text)
        self.assertNotIn("/issues/${PR_NUMBER}/comments", text)

    def test_validation_tracks_direct_status_receipt_wiring(self):
        validation = VALIDATION.read_text(encoding="utf-8")
        self.assertIn('".github/workflows/pr-lean-fast-check.yml"', validation)
        self.assertIn(
            '"tests/test_chatgpt_ci_completion_dispatch_workflow_v0_1.py"',
            validation,
        )
        self.assertNotIn(
            '".github/workflows/chatgpt-ci-completion-push-v0-1.yml"',
            validation,
        )
        self.assertNotIn(
            '".github/workflows/chatgpt-ci-completion-dispatch-v0-1.yml"',
            validation,
        )


if __name__ == "__main__":
    unittest.main()
