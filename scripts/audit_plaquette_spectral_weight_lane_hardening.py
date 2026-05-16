#!/usr/bin/env python3
"""Audit the plaquette spectral-weight lane hardening layer."""

from __future__ import annotations

from pathlib import Path
import re
import sys

STRING_RE = re.compile(r'"(?:[^"\\]|\\.)*"')
FORBIDDEN_TOKENS_RE = re.compile(r"\b(sorry|admit|axiom|constant)\b")
TARGET_PATH = Path("MGAP4D/MathlibAnalytic/PlaquetteSpectralWeightLaneHardening.lean")
ROOT_PATH = Path("MGAP4D/MathlibAnalytic.lean")
DOC_PATH = Path("docs/plaquette_spectral_weight_lane_hardening.md")

REQUIRED_TARGET_ANCHORS = (
    "PlaquetteSpectralWeightLaneHardeningData",
    "PlaquetteSpectralWeightLaneHardeningData.ready",
    "plaquetteSpectralWeightLaneHardeningData",
    "plaquette_spectral_weight_lane_hardening_ready",
    "continuumYMLaneReady",
    "observableAtomReady",
    "compactPlaquetteReady",
    "operatorMeasureReady",
    "exactBodyClosureReady",
    "compactSupportHardened",
    "centeredHardened",
    "smearedHardened",
    "plaquetteConstructionHardened",
    "observableAtomHardened",
    "positiveWeightHardened",
    "nonzeroWeightHardened",
    "weightEqualsPVMMassHardened",
    "operatorMeasureCompatibilityHardened",
    "exactBodyWeightClosureHardened",
    "concretePlaquetteBoundaryVisible",
    "concreteOperatorMeasureBoundaryVisible",
    "hardPhysicalBoundaryVisible",
    "exactValuePreserved",
    "reviewLevelOnly",
    "publicBoundaryHeld",
    "finalReleaseHeld",
)

REQUIRED_THEOREM_ANCHORS = (
    "plaquette_weight_compact_support_hardened",
    "plaquette_weight_centered_hardened",
    "plaquette_weight_smeared_hardened",
    "plaquette_weight_construction_hardened",
    "plaquette_weight_observable_atom_hardened",
    "plaquette_weight_positive_weight_hardened",
    "plaquette_weight_nonzero_weight_hardened",
    "plaquette_weight_equals_pvm_mass_hardened",
    "plaquette_weight_operator_measure_compatibility_hardened",
    "plaquette_weight_exact_body_weight_closure_hardened",
    "plaquette_weight_concrete_plaquette_boundary_visible",
    "plaquette_weight_operator_measure_boundary_visible",
    "plaquette_weight_exact_value_preserved",
)

REQUIRED_ROOT_ANCHORS = (
    "import MGAP4D.MathlibAnalytic.PlaquetteSpectralWeightLaneHardening",
)

REQUIRED_DOC_ANCHORS = (
    "Plaquette Spectral Weight Lane Hardening",
    "compactSupportHardened",
    "centeredHardened",
    "smearedHardened",
    "positiveWeightHardened",
    "nonzeroWeightHardened",
    "weightEqualsPVMMassHardened",
    "operatorMeasureCompatibilityHardened",
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
        elif text[i] == "\n":
            out.append("\n")
        i += 1
    return "".join(out)


def cleaned_lean_source(path: Path) -> str:
    return STRING_RE.sub('""', strip_lean_comments(path.read_text(encoding="utf-8")))


def require(path: Path, anchors: tuple[str, ...], label: str, *, clean_lean: bool) -> list[str]:
    if not path.exists():
        return [f"missing {label} file: {path}"]
    source = cleaned_lean_source(path) if clean_lean else path.read_text(encoding="utf-8")
    return [f"missing {label} anchor {anchor!r} in {path}" for anchor in anchors if anchor not in source]


def audit_forbidden_tokens(path: Path) -> list[str]:
    if not path.exists():
        return [f"missing plaquette spectral-weight hardening file for forbidden-token audit: {path}"]
    source = cleaned_lean_source(path)
    hits: list[str] = []
    for lineno, line in enumerate(source.splitlines(), start=1):
        if FORBIDDEN_TOKENS_RE.search(line):
            hits.append(f"{path}:{lineno}: forbidden token in plaquette spectral-weight audit")
    return hits


def main() -> None:
    failures: list[str] = []
    failures.extend(audit_forbidden_tokens(TARGET_PATH))
    failures.extend(require(TARGET_PATH, REQUIRED_TARGET_ANCHORS, "plaquette spectral-weight target", clean_lean=True))
    failures.extend(require(TARGET_PATH, REQUIRED_THEOREM_ANCHORS, "plaquette spectral-weight theorem", clean_lean=True))
    failures.extend(require(ROOT_PATH, REQUIRED_ROOT_ANCHORS, "root import", clean_lean=True))
    failures.extend(require(DOC_PATH, REQUIRED_DOC_ANCHORS, "plaquette spectral-weight documentation", clean_lean=False))

    print("Plaquette spectral weight lane hardening audit")
    print(f"Plaquette spectral-weight anchors audited: {len(REQUIRED_TARGET_ANCHORS)}")
    print(f"Plaquette spectral-weight theorem anchors audited: {len(REQUIRED_THEOREM_ANCHORS)}")
    print("Root import audited: MGAP4D/MathlibAnalytic.lean")
    print("Documentation audited: docs/plaquette_spectral_weight_lane_hardening.md")
    print("Forbidden Lean tokens audited: sorry/admit/axiom/constant")

    if failures:
        print("Plaquette spectral weight lane hardening audit failed:", file=sys.stderr)
        for failure in failures:
            print(f"  {failure}", file=sys.stderr)
        raise SystemExit(1)

    print("Plaquette spectral weight lane hardening audit passed")


if __name__ == "__main__":
    main()
