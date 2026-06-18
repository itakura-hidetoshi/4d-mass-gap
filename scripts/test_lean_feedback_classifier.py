#!/usr/bin/env python3
"""Dependency-free regression tests for the Lean feedback classifier."""

from __future__ import annotations

import unittest

from lean_feedback_classifier import classify_text


class LeanFeedbackClassifierTest(unittest.TestCase):
    def assert_category(self, log: str, expected: str, exit_code: int = 1) -> None:
        self.assertEqual(classify_text(log, exit_code).primary_category, expected)

    def test_parser_unicode_identifier_failure(self) -> None:
        self.assert_category("unexpected token 'λ'; expected '_' or identifier", "parser")

    def test_name_resolution(self) -> None:
        self.assert_category("error: unknown identifier 'FiniteFoo.bar'", "name_resolution")

    def test_auto_implicit(self) -> None:
        self.assert_category(
            "implicit variable declaration has been disabled by autoImplicit=false",
            "auto_implicit",
        )

    def test_typeclass(self) -> None:
        self.assert_category("failed to synthesize AddGroup α", "typeclass")

    def test_elaboration(self) -> None:
        self.assert_category("application type mismatch: argument h has type P", "elaboration")

    def test_tactic(self) -> None:
        self.assert_category("unsolved goals\n⊢ x = x", "tactic")

    def test_import(self) -> None:
        self.assert_category("unknown module prefix 'Mathlib.NotARealModule'", "import_build")

    def test_placeholder_has_strongest_penalty(self) -> None:
        feedback = classify_text("warning: declaration uses 'sorry'", exit_code=0)
        self.assertEqual(feedback.primary_category, "placeholder")
        self.assertEqual(feedback.reward, -100)

    def test_success(self) -> None:
        feedback = classify_text("Build completed successfully.", exit_code=0)
        self.assertEqual(feedback.primary_category, "build_success")
        self.assertEqual(feedback.reward, 8)

    def test_unknown_failure_is_retained(self) -> None:
        feedback = classify_text("process terminated", exit_code=137)
        self.assertEqual(feedback.primary_category, "unknown_failure")
        self.assertEqual(feedback.reward, -1)


if __name__ == "__main__":
    unittest.main()
