#!/usr/bin/env python3
"""Audit the concrete analytic spine graph-sequence law addendum."""

from __future__ import annotations

from pathlib import Path
import re
import sys

STRING_RE = re.compile(r'"(?:[^"\\]|\\.)*"')
FORBIDDEN_TOKENS_RE = re.compile(r"\b(sorry|admit|axiom|constant)\b")
TARGET_PATH = Path("MGAP4D/MathlibAnalytic/ConcreteAnalyticSpineGraphSequenceLaw.lean")
ROOT_PATH = Path("MGAP4D/MathlibAnalytic.lean")

REQUIRED_TARGET_ANCHORS = (
    "import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineRealHilbertDomain",
    "ConcreteGraphSequenceLawSurface",
    "graphSequence : ConcreteGraphSequence T",
    "sequenceLawCarrier : Set (ConcreteRealHilbertSpace × ConcreteRealHilbertSpace)",
    "sequenceGraphPointMemLawCarrier :",
    "∀ n : ℕ, graphSequence.graphPoint n ∈ sequenceLawCarrier",
    "sequenceLawBoundaryNotClosedOperatorTheorem : Prop",
    "concrete_identity_graph_sequence_point_mem_diagonal_carrier",
    "concreteIdentityGraphSequence.graphPoint n ∈",
    "concreteIdentityGraphDiagonalCarrier",
    "concreteIdentityGraphSequenceLawSurface",
    "concrete_identity_graph_sequence_law_boundary",
    "concreteAnalyticSpineR2GraphSequenceLawSurfaceReady",
    "concrete_analytic_spine_r2_graph_sequence_law_surface_ready",
    "concreteAnalyticSpineR2GraphSequenceLawHardResidualBoundaryHeld",
    "concrete_analytic_spine_r2_graph_sequence_law_hard_residual_boundary_held",
)

REQUIRED_BOUNDARY_ANCHORS = (
    "not a closed-operator theorem",
    "not a convergence theorem",
    "not an R3 promotion",
    "does not assert",
    "closedness",
    "self-adjointness",
    "spectral theorem",
    "PVM",
    "33/20",
    "positive spectral-weight",
)

REQUIRED_ROOT_IMPORTS = (
    "import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineGraphSequenceLaw",
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
        return [f"missing graph sequence law file for forbidden-token audit: {path}"]
    source = cleaned_lean_source(path)
    hits: list[str] = []
    for lineno, line in enumerate(source.splitlines(), start=1):
        if FORBIDDEN_TOKENS_RE.search(line):
            hits.append(f"{path}:{lineno}: forbidden Lean token in graph sequence law addendum")
    return hits


def main() -> None:
    failures: list[str] = []
    failures.extend(audit_forbidden_tokens(TARGET_PATH))
    failures.extend(require(TARGET_PATH, REQUIRED_TARGET_ANCHORS, "graph sequence law target", clean_lean=True))
    failures.extend(require(TARGET_PATH, REQUIRED_BOUNDARY_ANCHORS, "boundary", clean_lean=False))
    failures.extend(require(ROOT_PATH, REQUIRED_ROOT_IMPORTS, "root import", clean_lean=False))

    print("Concrete analytic spine graph sequence law audit")
    print(f"Target anchors audited: {len(REQUIRED_TARGET_ANCHORS)}")
    print(f"Boundary anchors audited: {len(REQUIRED_BOUNDARY_ANCHORS)}")
    print(f"Root imports audited: {len(REQUIRED_ROOT_IMPORTS)}")
    print("Forbidden Lean tokens audited: sorry/admit/axiom/constant")

    if failures:
        print("Concrete analytic spine graph sequence law audit failed:", file=sys.stderr)
        for failure in failures:
            print(f"  {failure}", file=sys.stderr)
        raise SystemExit(1)

    print("Concrete analytic spine graph sequence law audit passed")


if __name__ == "__main__":
    main()
