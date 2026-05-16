#!/usr/bin/env python3
"""Audit the infinite-dimensional residual-filling bridge.

This guard checks that bridgeable analytic residuals are represented as an
imported Lean review surface and that the hard physical continuum boundary
remains visible.

It is a syntactic/contract audit. Lean kernel checking remains `lake build`.
"""

from __future__ import annotations

from pathlib import Path
import re
import sys

STRING_RE = re.compile(r'"(?:[^"\\]|\\.)*"')
FORBIDDEN_TOKENS_RE = re.compile(r"\b(sorry|admit|axiom|constant)\b")
TARGET_PATH = Path("MGAP4D/MathlibAnalytic/InfiniteDimensionalResidualFillingBridge.lean")
ROOT_PATH = Path("MGAP4D/MathlibAnalytic.lean")
DOC_PATH = Path("docs/infinite_dimensional_residual_filling_bridge.md")

REQUIRED_TARGET_ANCHORS = (
    "InfiniteDimensionalResidualFillingBridgeData",
    "InfiniteDimensionalResidualFillingBridgeData.ready",
    "infiniteDimensionalResidualFillingBridgeData",
    "infinite_dimensional_residual_filling_bridge_ready",
    "targetLayerReady",
    "hilbertNecessityReady",
    "finiteSpanDensityReady",
    "hilbertInstanceReady",
    "physicalOperatorSkeletonReady",
    "continuumSpectralSkeletonReady",
    "normalizationBridgeReady",
    "filledInfiniteDimensionalNecessity",
    "filledFiniteSpanDensity",
    "filledHilbertInstanceSkeleton",
    "filledSelfAdjointHPhysSkeleton",
    "filledContinuumSpectralSkeleton",
    "filledNormalizationBridge",
    "exactValuePreserved",
    "remainingHardPhysicalResidualsVisible",
    "publicBoundaryHeld",
    "finalReleaseHeld",
)

REQUIRED_THEOREM_ANCHORS = (
    "residual_filling_infinite_dimensional_necessity",
    "residual_filling_finite_span_density",
    "residual_filling_hilbert_instance_skeleton",
    "residual_filling_self_adjoint_hphys_skeleton",
    "residual_filling_continuum_spectral_skeleton",
    "residual_filling_exact_value_preserved",
    "residual_filling_hard_physical_residuals_visible",
    "residual_filling_public_boundary_held",
    "residual_filling_final_release_held",
)

REQUIRED_IMPORT_ANCHORS = (
    "import MGAP4D.MathlibAnalytic.InfiniteDimensionalYangMillsRealizationTargets",
    "import MGAP4D.MathlibAnalytic.InfiniteDimensionalHilbertNecessityFromPNP",
    "import MGAP4D.MathlibAnalytic.HilbertFiniteSpanDensitySkeleton",
    "import MGAP4D.MathlibAnalytic.HilbertSpaceInstanceSkeleton",
    "import MGAP4D.MathlibAnalytic.PhysicalUnboundedOperatorSkeleton",
    "import MGAP4D.MathlibAnalytic.ContinuumSpectralTheoremSkeleton",
)

REQUIRED_ROOT_ANCHORS = (
    "import MGAP4D.MathlibAnalytic.InfiniteDimensionalResidualFillingBridge",
)

REQUIRED_DOC_ANCHORS = (
    "Infinite-dimensional Residual Filling Bridge",
    "review-level residual filling",
    "filledInfiniteDimensionalNecessity",
    "filledFiniteSpanDensity",
    "filledHilbertInstanceSkeleton",
    "filledSelfAdjointHPhysSkeleton",
    "filledContinuumSpectralSkeleton",
    "remainingHardPhysicalResidualsVisible",
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
        return [f"missing residual-filling file for forbidden-token audit: {path}"]
    source = cleaned_lean_source(path)
    hits: list[str] = []
    for lineno, line in enumerate(source.splitlines(), start=1):
        if FORBIDDEN_TOKENS_RE.search(line):
            hits.append(f"{path}:{lineno}: forbidden token in residual-filling audit")
    return hits


def main() -> None:
    failures: list[str] = []
    failures.extend(audit_forbidden_tokens(TARGET_PATH))
    failures.extend(require(TARGET_PATH, REQUIRED_IMPORT_ANCHORS, "residual-filling import", clean_lean=True))
    failures.extend(require(TARGET_PATH, REQUIRED_TARGET_ANCHORS, "residual-filling target", clean_lean=True))
    failures.extend(require(TARGET_PATH, REQUIRED_THEOREM_ANCHORS, "residual-filling theorem", clean_lean=True))
    failures.extend(require(ROOT_PATH, REQUIRED_ROOT_ANCHORS, "root import", clean_lean=True))
    failures.extend(require(DOC_PATH, REQUIRED_DOC_ANCHORS, "residual-filling documentation", clean_lean=False))

    print("Infinite-dimensional residual filling audit")
    print(f"Import anchors audited: {len(REQUIRED_IMPORT_ANCHORS)}")
    print(f"Residual-filling anchors audited: {len(REQUIRED_TARGET_ANCHORS)}")
    print(f"Residual-filling theorem anchors audited: {len(REQUIRED_THEOREM_ANCHORS)}")
    print("Root import audited: MGAP4D/MathlibAnalytic.lean")
    print("Documentation audited: docs/infinite_dimensional_residual_filling_bridge.md")
    print("Forbidden Lean tokens audited: sorry/admit/axiom/constant")

    if failures:
        print("Infinite-dimensional residual filling audit failed:", file=sys.stderr)
        for failure in failures:
            print(f"  {failure}", file=sys.stderr)
        raise SystemExit(1)

    print("Infinite-dimensional residual filling audit passed")


if __name__ == "__main__":
    main()
