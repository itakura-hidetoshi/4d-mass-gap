#!/usr/bin/env python3
"""Regression tests for the narrow Lean source-integrity preflight."""

from __future__ import annotations

import tempfile
import unittest
from pathlib import Path

from audit_lean_source_integrity import audit_paths, suspicious_bare_source


class LeanSourceIntegrityTest(unittest.TestCase):
    def test_real_corruption_shape_is_rejected(self) -> None:
        self.assertEqual(suspicious_bare_source("invalid\n"), "invalid")

    def test_comments_do_not_hide_bare_replacement(self) -> None:
        source = "/- generated note -/\n-- another note\ninvalid\n"
        self.assertEqual(suspicious_bare_source(source), "invalid")

    def test_one_line_import_is_allowed(self) -> None:
        self.assertIsNone(suspicious_bare_source("import Mathlib\n"))

    def test_small_valid_declaration_is_allowed(self) -> None:
        self.assertIsNone(suspicious_bare_source("theorem ok : True := by trivial\n"))

    def test_comment_only_file_is_allowed(self) -> None:
        self.assertIsNone(suspicious_bare_source("/- documentation only -/\n"))

    def test_path_audit_reports_token_and_path(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            path = Path(raw_dir) / "Broken.lean"
            path.write_text("invalid\n", encoding="utf-8")
            errors = audit_paths([path])
        self.assertEqual(len(errors), 1)
        self.assertIn("Broken.lean", errors[0])
        self.assertIn("'invalid'", errors[0])


if __name__ == "__main__":
    unittest.main()
