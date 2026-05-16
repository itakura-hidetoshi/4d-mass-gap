#!/usr/bin/env python3
"""Audit the hard physical residual hardening map.

This guard checks that the remaining hard physical residual is split into visible
hardening lanes rather than hidden behind review-level residual filling.

It is a syntactic/contract audit. Lean kernel checking remains `lake build`.
"""

from __future__ import annotations

from pathlib import Path
import re
import sys

STRING_RE = re.compile(r'"(?:[^"\\]|\\.)*"')
FORBIDDEN_TOKENS_RE = re.compile(r"\b(sorry|admit|axiom|constant)\b")
TARGET_PATH = Path("MGAP4D/MathlibAnalytic/HardPhysicalResidualHardeningMap.lean")
ROOT_PATH = Path("MGAP4D/MathlibAnalytic.lean")
DOC_PATH = Path("docs/hard_physical_residual_hardening_map.md")

REQUIRED_TARGET_ANCHORS = (
    "HardPhysicalResidualHardeningMapData",
    "HardPhysicalResidualHardeningMapData.ready",
    "hardPhysicalResidualHardeningMapData",
    "hard_physical_residual_hardening_map_ready",
    "residualFillingReady",
    "hilbertConstructionLane",
    "selfAdjointHPhysLane",
    "continuumYangMillsLane",
    "plaquetteSpectralWeightLane",
    "noLaneHidden",
    "exactValuePreserved",
    "reviewLevelOnly",
    "publicBoundaryHeld",
    "finalReleaseHeld",
)

REQUIRED_THEOREM_ANCHORS = (
    "hard_residual_hilbert_construction_lane_visible",
    "hard_residual_self_adjoint_hphys_lane_visible",
    "hard_residual_continuum_yang_mills_lane_visible",
    "hard_residual_plaquette_spectral_weight_lane_visible",
    "hard_residual_no_lane_hidden",
    "hard_residual_exact_value_preserved",
    "hard_residual_review_level_only",
    "hard_residual_public_boundary_held",
    "hard_residual_final_release_held",
)

REQUIRED_ROOT_ANCHORS = (
    "import MGAP4D.MathlibAnalytic.HardPhysicalResidualHardeningMap",
)

REQUIRED_DOC_ANCHORS = (
    "Hard Physical Residual Hardening Map",
    "hilbertConstructionLane",
    "selfAdjointHPhysLane",
    "continuumYangMillsLane",
    "plaquetteSpectralWeightLane",
    "noLaneHidden",
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
        return [f"missing hardening-map file for forbidden-token audit: {path}"]
    source = cleaned_lean_source(path)
    hits: list[str] = []
    for lineno, line in enumerate(source.splitlines(), start=1):
        if FORBIDDEN_TOKENS_RE.search(line):
            hits.append(f"{path}:{lineno}: forbidden token in hardening-map audit")
    return hits


def main() -> None:
    failures: list[str] = []
    failures.extend(audit_forbidden_tokens(TARGET_PATH))
    failures.extend(require(TARGET_PATH, REQUIRED_TARGET_ANCHORS, "hardening-map target", clean_lean=True))
    failures.extend(require(TARGET_PATH, REQUIRED_THEOREM_ANCHORS, "hardening-map theorem", clean_lean=True))
    failures.extend(require(ROOT_PATH, REQUIRED_ROOT_ANCHORS, "root import", clean_lean=True))
    failures.extend(require(DOC_PATH, REQUIRED_DOC_ANCHORS, "hardening-map documentation", clean_lean=False))

    print("Hard physical residual hardening map audit")
    print(f"Hardening-map anchors audited: {len(REQUIRED_TARGET_ANCHORS)}")
    print(f"Hardening-map theorem anchors audited: {len(REQUIRED_THEOREM_ANCHORS)}")
    print("Root import audited: MGAP4D/MathlibAnalytic.lean")
    print("Documentation audited: docs/hard_physical_residual_hardening_map.md")
    print("Forbidden Lean tokens audited: sorry/admit/axiom/constant")

    if failures:
        print("Hard physical residual hardening map audit failed:", file=sys.stderr)
        for failure in failures:
            print(f"  {failure}", file=sys.stderr)
        raise SystemExit(1)

    print("Hard physical residual hardening map audit passed")


if __name__ == "__main__":
    main()
