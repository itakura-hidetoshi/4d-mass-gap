import unittest

from scripts.chatgpt_ci_completion_push_v0_2 import resolve_pr_numbers


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


if __name__ == "__main__":
    unittest.main()
