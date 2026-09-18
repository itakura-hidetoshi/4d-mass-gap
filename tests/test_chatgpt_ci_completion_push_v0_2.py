import unittest

from scripts.chatgpt_ci_completion_push_v0_2 import (
    completion_status_context,
    completion_status_state,
    resolve_pr_numbers,
)


class ResolvePrNumbersTests(unittest.TestCase):
    def test_uses_workflow_run_pull_requests_when_present(self):
        event_pull_requests = [{"number": 4342}]
        associated_pull_requests = []

        self.assertEqual(
            resolve_pr_numbers(
                event_pull_requests,
                associated_pull_requests,
                head_sha="abc123",
                repository="itakura-hidetoshi/4d-mass-gap",
            ),
            [4342],
        )

    def test_falls_back_to_exact_commit_association_when_event_array_is_empty(self):
        associated_pull_requests = [
            {
                "number": 4342,
                "head": {
                    "sha": "abc123",
                    "repo": {"full_name": "itakura-hidetoshi/4d-mass-gap"},
                },
            }
        ]

        self.assertEqual(
            resolve_pr_numbers(
                [],
                associated_pull_requests,
                head_sha="abc123",
                repository="itakura-hidetoshi/4d-mass-gap",
            ),
            [4342],
        )

    def test_fallback_rejects_wrong_head_or_repository_and_deduplicates(self):
        associated_pull_requests = [
            {
                "number": 4342,
                "head": {
                    "sha": "abc123",
                    "repo": {"full_name": "itakura-hidetoshi/4d-mass-gap"},
                },
            },
            {
                "number": 4342,
                "head": {
                    "sha": "abc123",
                    "repo": {"full_name": "itakura-hidetoshi/4d-mass-gap"},
                },
            },
            {
                "number": 4343,
                "head": {
                    "sha": "wrong",
                    "repo": {"full_name": "itakura-hidetoshi/4d-mass-gap"},
                },
            },
            {
                "number": 4344,
                "head": {
                    "sha": "abc123",
                    "repo": {"full_name": "other/repo"},
                },
            },
        ]

        self.assertEqual(
            resolve_pr_numbers(
                [],
                associated_pull_requests,
                head_sha="abc123",
                repository="itakura-hidetoshi/4d-mass-gap",
            ),
            [4342],
        )


class CompletionStatusReceiptTests(unittest.TestCase):
    def test_success_maps_to_success(self):
        self.assertEqual(completion_status_state("success"), "success")

    def test_terminal_failures_map_to_failure(self):
        for conclusion in (
            "failure",
            "timed_out",
            "cancelled",
            "action_required",
            "startup_failure",
            "stale",
        ):
            with self.subTest(conclusion=conclusion):
                self.assertEqual(completion_status_state(conclusion), "failure")

    def test_non_green_terminal_values_do_not_look_successful(self):
        self.assertEqual(completion_status_state("neutral"), "error")
        self.assertEqual(completion_status_state("skipped"), "error")
        self.assertEqual(completion_status_state(""), "error")

    def test_context_is_stable_and_within_github_limit(self):
        context = completion_status_context("PR Lean Fast Check")
        self.assertEqual(context, "chatgpt-ci-receipt/PR Lean Fast Check")
        self.assertLessEqual(len(completion_status_context("x" * 200)), 100)


if __name__ == "__main__":
    unittest.main()
