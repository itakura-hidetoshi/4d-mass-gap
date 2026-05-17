#!/usr/bin/env python3
"""Audit the four-lane residual closure layer."""

from __future__ import annotations

from pathlib import Path
import re
import sys

STRING_RE = re.compile(r'"(?:[^"\\]|\\.)*"')
FORBIDDEN_TOKENS_RE = re.compile(r"\b(sorry|admit|axiom|constant)\b")
TARGET_PATH = Path("MGAP4D/MathlibAnalytic/FourLaneResidualClosure.lean")
ROOT_PATH = Path("MGAP4D/MathlibAnalytic.lean")
DOC_PATH = Path("docs/four_lane_residual_closure.md")

REQUIRED_TARGET_ANCHORS = (
    "FourLaneResidualClosureData",
    "FourLaneResidualClosureData.ready",
    "fourLaneResidualClosureData",
    "four_lane_residual_closure_ready",
    "completeHilbertLaneReady",
    "completeInfiniteDimensionalHilbertConstructionLaneData.ready",
    "selfAdjointLaneReady",
    "continuumYMLaneReady",
    "plaquetteWeightLaneReady",
    "completeHilbertLaneClosed",
    "selfAdjointLaneClosed",
    "continuumYMLaneClosed",
    "plaquetteWeightLaneClosed",
    "allFourLanesClosed",
    "noReviewLevelResidualLeft",
    "externalReviewBoundaryVisible",
    "publicBoundaryHeld",
    "finalReleaseHeld",
)

REQUIRED_THEOREM_ANCHORS = (
    "four_lane_closure_complete_hilbert_lane_closed",
    "four_lane_closure_self_adjoint_lane_closed",
    "four_lane_closure_continuum_ym_lane_closed",
    "four_lane_closure_plaquette_weight_lane_closed",
    "four_lane_closure_all_four_lanes_closed",
    "four_lane_closure_no_review_level_residual_left",
    "four_lane_closure_exact_value_preserved",
    "four_lane_closure_external_review_boundary_visible",
    "four_lane_closure_public_boundary_held",
    "four_lane_closure_final_release_held",
)

REQUIRED_ROOT_ANCHORS = (
    "import MGAP4D.MathlibAnalytic.FourLaneResidualClosure",
)

REQUIRED_DOC_ANCHORS = (
    "Four-Lane Residual Closure",
    "completeHilbertLaneReady",
    "completeHilbertLaneClosed",
    "completeInfiniteDimensionalHilbertConstructionLaneData.ready",
    "allFourLanesClosed",
    "noReviewLevelResidualLeft",
    "externalReviewBoundaryVisible",
    "publicBoundaryHeld",
    "finalReleaseHeld",
)

FORBIDDEN_STALE_ANCHORS = (
    "HilbertConstructionLaneHardening",
    "hilbertConstructionLaneHardeningData",
    "hilbert_construction_lane_hardening_ready",
    "hilbertLaneReady",
    "hilbertLaneClosed",
    "four_lane_closure_hilbert_lane_closed",
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


def source_for(path: Path, *, clean_lean: bool) -> str:
    return cleaned_lean_source(path) if clean_lean else path.read_text(encoding="utf-8")


def require(path: Path, anchors: tuple[str, ...], label: str, *, clean_lean: bool) -> list[str]:
    if not path.exists():
        return [f"missing {label} file: {path}"]
    source = source_for(path, clean_lean=clean_lean)
    return [f"missing {label} anchor {anchor!r} in {path}" for anchor in anchors if anchor not in source]


def forbid(path: Path, anchors: tuple[str, ...], label: str, *, clean_lean: bool) -> list[str]:
    if not path.exists():
        return []
    source = source_for(path, clean_lean=clean_lean)
    return [f"forbidden stale {label} anchor {anchor!r} in {path}" for anchor in anchors if anchor in source]


def audit_forbidden_tokens(path: Path) -> list[str]:
    if not path.exists():
        return [f"missing four-lane closure file for forbidden-token audit: {path}"]
    source = cleaned_lean_source(path)
    hits: list[str] = []
    for lineno, line in enumerate(source.splitlines(), start=1):
        if FORBIDDEN_TOKENS_RE.search(line):
            hits.append(f"{path}:{lineno}: forbidden token in four-lane closure audit")
    return hits


def main() -> None:
    failures: list[str] = []
    failures.extend(audit_forbidden_tokens(TARGET_PATH))
    failures.extend(require(TARGET_PATH, REQUIRED_TARGET_ANCHORS, "four-lane closure target", clean_lean=True))
    failures.extend(require(TARGET_PATH, REQUIRED_THEOREM_ANCHORS, "four-lane closure theorem", clean_lean=True))
    failures.extend(require(ROOT_PATH, REQUIRED_ROOT_ANCHORS, "root import", clean_lean=True))
    failures.extend(require(DOC_PATH, REQUIRED_DOC_ANCHORS, "four-lane closure documentation", clean_lean=False))
    failures.extend(forbid(TARGET_PATH, FORBIDDEN_STALE_ANCHORS, "old Hilbert lane", clean_lean=True))

    print("Four-lane residual closure audit")
    print(f"Four-lane closure anchors audited: {len(REQUIRED_TARGET_ANCHORS)}")
    print(f"Four-lane closure theorem anchors audited: {len(REQUIRED_THEOREM_ANCHORS)}")
    print("Root import audited: MGAP4D/MathlibAnalytic.lean")
    print("Documentation audited: docs/four_lane_residual_closure.md")
    print("Forbidden stale Hilbert lane anchors audited")
    print("Forbidden Lean tokens audited: sorry/admit/axiom/constant")

    if failures:
        print("Four-lane residual closure audit failed:", file=sys.stderr)
        for failure in failures:
            print(f"  {failure}", file=sys.stderr)
        raise SystemExit(1)

    print("Four-lane residual closure audit passed")


if __name__ == "__main__":
    main()
