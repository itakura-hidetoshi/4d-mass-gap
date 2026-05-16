#!/usr/bin/env python3
"""Audit the Hilbert-construction lane hardening layer."""

from __future__ import annotations

from pathlib import Path
import re
import sys

STRING_RE = re.compile(r'"(?:[^"\\]|\\.)*"')
FORBIDDEN_TOKENS_RE = re.compile(r"\b(sorry|admit|axiom|constant)\b")
TARGET_PATH = Path("MGAP4D/MathlibAnalytic/HilbertConstructionLaneHardening.lean")
ROOT_PATH = Path("MGAP4D/MathlibAnalytic.lean")
DOC_PATH = Path("docs/hilbert_construction_lane_hardening.md")

REQUIRED_TARGET_ANCHORS = (
    "HilbertConstructionLaneHardeningData",
    "HilbertConstructionLaneHardeningData.ready",
    "hilbertConstructionLaneHardeningData",
    "hilbert_construction_lane_hardening_ready",
    "hardResidualMapReady",
    "countableBasisReady",
    "finiteSpanDensityReady",
    "normTopologyReady",
    "cauchyCompletionReady",
    "completeNormedSpaceReady",
    "innerProductReady",
    "hilbertInstanceReady",
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
    "hilbert_construction_countable_basis_hardened",
    "hilbert_construction_finite_span_density_hardened",
    "hilbert_construction_norm_topology_hardened",
    "hilbert_construction_cauchy_completion_hardened",
    "hilbert_construction_complete_normed_space_hardened",
    "hilbert_construction_inner_product_hardened",
    "hilbert_construction_hilbert_instance_hardened",
    "hilbert_construction_hard_boundary_visible",
    "hilbert_construction_exact_value_preserved",
    "hilbert_construction_review_level_only",
)

REQUIRED_ROOT_ANCHORS = (
    "import MGAP4D.MathlibAnalytic.HilbertConstructionLaneHardening",
)

REQUIRED_DOC_ANCHORS = (
    "Hilbert Construction Lane Hardening",
    "countableBasisHardened",
    "finiteSpanDensityHardened",
    "normTopologyHardened",
    "cauchyCompletionHardened",
    "completeNormedSpaceHardened",
    "innerProductHardened",
    "hilbertInstanceHardened",
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
        return [f"missing Hilbert-construction hardening file for forbidden-token audit: {path}"]
    source = cleaned_lean_source(path)
    hits: list[str] = []
    for lineno, line in enumerate(source.splitlines(), start=1):
        if FORBIDDEN_TOKENS_RE.search(line):
            hits.append(f"{path}:{lineno}: forbidden token in Hilbert-construction audit")
    return hits


def main() -> None:
    failures: list[str] = []
    failures.extend(audit_forbidden_tokens(TARGET_PATH))
    failures.extend(require(TARGET_PATH, REQUIRED_TARGET_ANCHORS, "Hilbert-construction target", clean_lean=True))
    failures.extend(require(TARGET_PATH, REQUIRED_THEOREM_ANCHORS, "Hilbert-construction theorem", clean_lean=True))
    failures.extend(require(ROOT_PATH, REQUIRED_ROOT_ANCHORS, "root import", clean_lean=True))
    failures.extend(require(DOC_PATH, REQUIRED_DOC_ANCHORS, "Hilbert-construction documentation", clean_lean=False))

    print("Hilbert construction lane hardening audit")
    print(f"Hilbert-construction anchors audited: {len(REQUIRED_TARGET_ANCHORS)}")
    print(f"Hilbert-construction theorem anchors audited: {len(REQUIRED_THEOREM_ANCHORS)}")
    print("Root import audited: MGAP4D/MathlibAnalytic.lean")
    print("Documentation audited: docs/hilbert_construction_lane_hardening.md")
    print("Forbidden Lean tokens audited: sorry/admit/axiom/constant")

    if failures:
        print("Hilbert construction lane hardening audit failed:", file=sys.stderr)
        for failure in failures:
            print(f"  {failure}", file=sys.stderr)
        raise SystemExit(1)

    print("Hilbert construction lane hardening audit passed")


if __name__ == "__main__":
    main()
