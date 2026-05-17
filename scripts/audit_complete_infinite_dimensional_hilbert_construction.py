#!/usr/bin/env python3
"""Audit the complete infinite-dimensional Hilbert construction layer."""

from __future__ import annotations

from pathlib import Path
import re
import sys

STRING_RE = re.compile(r'"(?:[^"\\]|\\.)*"')
FORBIDDEN_TOKENS_RE = re.compile(r"\b(sorry|admit|axiom|constant)\b")
TARGET_PATH = Path("MGAP4D/MathlibAnalytic/CompleteInfiniteDimensionalHilbertConstruction.lean")
ROOT_PATH = Path("MGAP4D/MathlibAnalytic.lean")
BRIDGE_PATH = Path("MGAP4D/MathlibAnalytic/HilbertToPhysicalUnboundedOperatorBridge.lean")
DOC_PATH = Path("docs/complete_infinite_dimensional_hilbert_construction.md")

REQUIRED_TARGET_ANCHORS = (
    "CompleteInfiniteDimensionalHilbertConstructionLaneData",
    "CompleteInfiniteDimensionalHilbertConstructionLaneData.ready",
    "completeInfiniteDimensionalHilbertConstructionLaneData",
    "complete_infinite_dimensional_hilbert_construction_lane_ready",
    "CompleteInfiniteDimensionalHilbertConstructionData",
    "CompleteInfiniteDimensionalHilbertConstructionData.ready",
    "completeInfiniteDimensionalHilbertConstructionData",
    "complete_infinite_dimensional_hilbert_construction_ready",
    "carrier",
    "basisVector",
    "finiteBasisFamily",
    "finiteBasisFamily_def",
    "finiteRestrictionLinearlyIndependent",
    "arbitraryFiniteRankWitness",
    "noFiniteRankCollapse",
    "countableBasisRealized",
    "finiteSpanDenseInCompletion",
    "normTopologyRealized",
    "cauchyCompletionRealized",
    "completeNormedSpaceRealized",
    "innerProductRealized",
    "hilbertInstanceRealized",
    "countableBasisHardened",
    "finiteSpanDensityHardened",
    "normTopologyHardened",
    "cauchyCompletionHardened",
    "completeNormedSpaceHardened",
    "innerProductHardened",
    "hilbertInstanceHardened",
    "hardPhysicalBoundaryVisible",
    "exactValuePreserved",
    "reviewLevelOnly",
    "publicBoundaryHeld",
    "finalReleaseHeld",
)

REQUIRED_THEOREM_ANCHORS = (
    "complete_hilbert_construction_countable_basis_hardened",
    "complete_hilbert_construction_finite_span_density_hardened",
    "complete_hilbert_construction_norm_topology_hardened",
    "complete_hilbert_construction_cauchy_completion_hardened",
    "complete_hilbert_construction_complete_normed_space_hardened",
    "complete_hilbert_construction_inner_product_hardened",
    "complete_hilbert_construction_hilbert_instance_hardened",
    "complete_hilbert_construction_hard_boundary_visible",
    "complete_hilbert_construction_exact_value_preserved",
    "complete_hilbert_construction_review_level_only",
    "complete_hilbert_construction_arbitrary_finite_rank_witness",
    "complete_hilbert_construction_no_finite_rank_collapse",
    "complete_hilbert_construction_hilbert_instance_realized",
)

REQUIRED_ROOT_ANCHORS = (
    "import MGAP4D.MathlibAnalytic.CompleteInfiniteDimensionalHilbertConstruction",
)

REQUIRED_BRIDGE_ANCHORS = (
    "import MGAP4D.MathlibAnalytic.CompleteInfiniteDimensionalHilbertConstruction",
    "completeInfiniteDimensionalHilbertConstructionLaneData.ready",
    "complete_infinite_dimensional_hilbert_construction_lane_ready",
)

REQUIRED_DOC_ANCHORS = (
    "Complete Infinite-Dimensional Hilbert Construction",
    "CompleteInfiniteDimensionalHilbertConstructionLaneData",
    "completeInfiniteDimensionalHilbertConstructionLaneData",
    "CompleteInfiniteDimensionalHilbertConstructionData",
    "completeInfiniteDimensionalHilbertConstructionData",
    "arbitraryFiniteRankWitness",
    "noFiniteRankCollapse",
    "hilbertInstanceHardened",
)

FORBIDDEN_RENAME_ANCHORS = (
    "HilbertConstructionLaneHardening",
    "hilbertConstructionLaneHardeningData",
    "hilbert_construction_lane_hardening_ready",
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
        return [f"missing complete Hilbert construction file for forbidden-token audit: {path}"]
    source = cleaned_lean_source(path)
    hits: list[str] = []
    for lineno, line in enumerate(source.splitlines(), start=1):
        if FORBIDDEN_TOKENS_RE.search(line):
            hits.append(f"{path}:{lineno}: forbidden token in complete Hilbert construction audit")
    return hits


def main() -> None:
    failures: list[str] = []
    failures.extend(audit_forbidden_tokens(TARGET_PATH))
    failures.extend(require(TARGET_PATH, REQUIRED_TARGET_ANCHORS, "complete Hilbert construction target", clean_lean=True))
    failures.extend(require(TARGET_PATH, REQUIRED_THEOREM_ANCHORS, "complete Hilbert construction theorem", clean_lean=True))
    failures.extend(require(ROOT_PATH, REQUIRED_ROOT_ANCHORS, "root import", clean_lean=True))
    failures.extend(require(BRIDGE_PATH, REQUIRED_BRIDGE_ANCHORS, "Hilbert-to-physical bridge", clean_lean=True))
    failures.extend(require(DOC_PATH, REQUIRED_DOC_ANCHORS, "complete Hilbert construction documentation", clean_lean=False))
    failures.extend(forbid(TARGET_PATH, FORBIDDEN_RENAME_ANCHORS, "old Hilbert construction hardening", clean_lean=True))
    failures.extend(forbid(ROOT_PATH, FORBIDDEN_RENAME_ANCHORS, "old Hilbert construction hardening", clean_lean=True))
    failures.extend(forbid(BRIDGE_PATH, FORBIDDEN_RENAME_ANCHORS, "old Hilbert construction hardening", clean_lean=True))

    print("Complete infinite-dimensional Hilbert construction audit")
    print(f"Complete Hilbert construction anchors audited: {len(REQUIRED_TARGET_ANCHORS)}")
    print(f"Complete Hilbert construction theorem anchors audited: {len(REQUIRED_THEOREM_ANCHORS)}")
    print("Root import audited: MGAP4D/MathlibAnalytic.lean")
    print("Bridge import audited: MGAP4D/MathlibAnalytic/HilbertToPhysicalUnboundedOperatorBridge.lean")
    print("Documentation audited: docs/complete_infinite_dimensional_hilbert_construction.md")
    print("Forbidden stale-name anchors audited: HilbertConstructionLaneHardening")
    print("Forbidden Lean tokens audited: sorry/admit/axiom/constant")

    if failures:
        print("Complete infinite-dimensional Hilbert construction audit failed:", file=sys.stderr)
        for failure in failures:
            print(f"  {failure}", file=sys.stderr)
        raise SystemExit(1)

    print("Complete infinite-dimensional Hilbert construction audit passed")


if __name__ == "__main__":
    main()
