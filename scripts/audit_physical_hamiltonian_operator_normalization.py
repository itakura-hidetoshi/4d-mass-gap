#!/usr/bin/env python3
"""Audit physical Hamiltonian operator-normalization anchors.

This is a syntactic/contract audit. Lean kernel checking remains `lake build`.
The audit ensures the operator-level normalization surface is present, imported,
documented, and boundary-preserving.
"""

from __future__ import annotations

from pathlib import Path
import re
import sys

STRING_RE = re.compile(r'"(?:[^"\\]|\\.)*"')
FORBIDDEN_TOKENS_RE = re.compile(r"\b(sorry|admit|axiom|constant)\b")

LEAN_PATH = Path("MGAP4D/MathlibAnalytic/PhysicalHamiltonianOperatorNormalization.lean")
ROOT_IMPORT_PATH = Path("MGAP4D/MathlibAnalytic.lean")
DOC_PATH = Path("docs/physical_hamiltonian_operator_normalization.md")
CHECK_PATH = Path("scripts/check.sh")

REQUIRED_IMPORTS = (
    "import MGAP4D.MathlibAnalytic.PhysicalHamiltonianNormalizationBridge",
)

REQUIRED_LEAN_ANCHORS = (
    "PhysicalHamiltonianOperatorNormalizationData",
    "physicalHamiltonianOperatorNormalizationData",
    "PhysicalHamiltonianOperatorNormalizationData.ready",
    "referenceEnergyScale",
    "physicalHamiltonianScale",
    "normalizedHamiltonianScale",
    "normalized_hamiltonian_scale_def",
    "physical_hamiltonian_scale_reconstruction",
    "dimensionalGap",
    "dimensional_gap_def",
    "dimensional_gap_eq_reference_mul_exact",
    "dimensional_gap_eq_reference_mul_3320",
    "internal_reference_scale_eq_one",
    "internal_dimensional_gap_eq_3320",
    "normalizedHamiltonianConventionVisible",
    "dimensionalGapReadingVisible",
    "theoremBodyUnchanged",
    "publicBoundaryHeld",
    "physical_hamiltonian_operator_normalization_ready",
    "physical_hamiltonian_operator_normalized_scale_def",
    "physical_hamiltonian_operator_scale_reconstruction",
    "physical_hamiltonian_operator_normalized_gap_eq_3320",
    "physical_hamiltonian_operator_dimensional_gap_eq_reference_mul_3320",
    "physical_hamiltonian_operator_internal_dimensional_gap_eq_3320",
)

REQUIRED_EQUATION_ANCHORS = (
    "normalizedHamiltonianScale = referenceEnergyScale⁻¹ * physicalHamiltonianScale",
    "physicalHamiltonianScale = referenceEnergyScale * normalizedHamiltonianScale",
    "dimensionalGap = referenceEnergyScale * normalizedGap",
    "dimensionalGap = referenceEnergyScale * ((33 : ℝ) / 20)",
)

REQUIRED_ROOT_IMPORTS = (
    "import MGAP4D.MathlibAnalytic.PhysicalHamiltonianOperatorNormalization",
)

REQUIRED_DOC_ANCHORS = (
    "H_norm = E0^{-1} * H_phys",
    "H_phys = E0 * H_norm",
    "Delta_phys(E0) = E0 * (33/20)",
    "physical_hamiltonian_operator_normalization_ready",
    "the theorem body",
    "the public release gate",
)

REQUIRED_CHECK_ANCHORS = (
    "audit physical Hamiltonian operator normalization",
    "scripts/audit_physical_hamiltonian_operator_normalization.py",
)


def strip_lean_comments(text: str) -> str:
    out: list[str] = []
    i = 0
    depth = 0
    while i < len(text):
        if depth == 0 and text.startswith("--", i):
            while i < len(text) and text[i] != "\n":
                i += 1
            if i < len(text):
                out.append("\n")
                i += 1
            continue
        if text.startswith("/-", i):
            depth += 1
            i += 2
            continue
        if depth > 0 and text.startswith("-/", i):
            depth -= 1
            i += 2
            continue
        if depth == 0:
            out.append(text[i])
        i += 1
    return "".join(out)


def strip_strings(text: str) -> str:
    return STRING_RE.sub('""', text)


def lean_code(text: str) -> str:
    return strip_strings(strip_lean_comments(text))


def require_file(path: Path) -> str:
    if not path.exists():
        raise AssertionError(f"missing required file: {path}")
    return path.read_text(encoding="utf-8")


def require_all(label: str, text: str, anchors: tuple[str, ...]) -> None:
    missing = [anchor for anchor in anchors if anchor not in text]
    if missing:
        raise AssertionError(f"{label} missing anchors: {', '.join(missing)}")


def main() -> int:
    lean_text = require_file(LEAN_PATH)
    lean_without_comments = strip_lean_comments(lean_text)
    lean_src = lean_code(lean_text)

    forbidden = sorted(set(FORBIDDEN_TOKENS_RE.findall(lean_src)))
    if forbidden:
        raise AssertionError(f"forbidden Lean tokens found in {LEAN_PATH}: {', '.join(forbidden)}")

    require_all("Lean imports", lean_without_comments, REQUIRED_IMPORTS)
    require_all("Lean anchors", lean_without_comments, REQUIRED_LEAN_ANCHORS)
    require_all("Lean equation anchors", lean_without_comments, REQUIRED_EQUATION_ANCHORS)

    root_text = require_file(ROOT_IMPORT_PATH)
    require_all("root import", root_text, REQUIRED_ROOT_IMPORTS)

    doc_text = require_file(DOC_PATH)
    require_all("documentation", doc_text, REQUIRED_DOC_ANCHORS)

    check_text = require_file(CHECK_PATH)
    require_all("check.sh", check_text, REQUIRED_CHECK_ANCHORS)

    print("Physical Hamiltonian operator normalization audit")
    print(f"Lean anchors audited: {len(REQUIRED_LEAN_ANCHORS)}")
    print(f"Equation anchors audited: {len(REQUIRED_EQUATION_ANCHORS)}")
    print(f"Root import audited: {ROOT_IMPORT_PATH}")
    print(f"Documentation audited: {DOC_PATH}")
    print("Forbidden Lean tokens audited: sorry/admit/axiom/constant")
    print("Physical Hamiltonian operator normalization audit passed")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except AssertionError as exc:
        print(f"audit_physical_hamiltonian_operator_normalization.py: {exc}", file=sys.stderr)
        raise SystemExit(1)
