"""Pure static regression tests: cached direct diagnostics must be opt-in.

These tests do not invoke Lean or Git. The mandatory dependency-aware Lake
checker must remain active independently of the optional direct diagnostics.
"""
from pathlib import Path
import re
import unittest

ROOT = Path(__file__).resolve().parents[1]
WORKFLOW = ROOT / '.github/workflows/pr-lean-fast-check.yml'


def workflow_steps(text: str) -> dict[str, str]:
    matches = list(re.finditer(r'^      - name: (.+)$', text, re.MULTILINE))
    return {
        m.group(1): text[m.start():matches[i + 1].start() if i + 1 < len(matches) else len(text)]
        for i, m in enumerate(matches)
    }


class DirectDiagnosticRoutingTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.text = WORKFLOW.read_text(encoding='utf-8')
        cls.steps = workflow_steps(cls.text)

    def test_direct_diagnostics_default_off(self) -> None:
        self.assertIn('  LEAN_FAST_DIRECT_ELAB: "false"', self.text)

    def test_every_direct_lean_step_is_opt_in(self) -> None:
        direct = {name: block for name, block in self.steps.items() if 'lake env lean ' in block}
        self.assertEqual(set(direct), {
            'Kernel-check changed finite incidence geometry',
            'Early elaboration of new PZ37O leaves',
        })
        for name, block in direct.items():
            with self.subTest(step=name):
                condition = re.search(r'^        if: (.+)$', block, re.MULTILINE)
                self.assertIsNotNone(condition)
                assert condition is not None
                self.assertIn("env.LEAN_FAST_DIRECT_ELAB == 'true'", condition.group(1))
                self.assertIn("steps.lake-mode.outputs.required == 'true'", condition.group(1))

    def test_authoritative_lake_check_is_not_opt_in(self) -> None:
        block = self.steps['Run changed Lean fast check']
        self.assertIn("if: ${{ steps.lake-mode.outputs.required == 'true' }}", block)
        self.assertNotIn('LEAN_FAST_DIRECT_ELAB', block)
        self.assertNotIn('continue-on-error', block)
        self.assertIn('set -euxo pipefail', block)
        self.assertIn('bash scripts/check_changed_lean.sh "${CHECK_CHANGED_LEAN_BASE_REF}"', block)


if __name__ == '__main__':
    unittest.main()
