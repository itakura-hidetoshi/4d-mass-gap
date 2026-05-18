#!/usr/bin/env python3
from __future__ import annotations

from pathlib import Path
import re
import sys

STRING_RE = re.compile(r'"(?:[^"\\]|\\.)*"')
TOKEN_RE = re.compile(r"\b(sorry|admit|axiom|constant)\b")
TARGET = Path("MGAP4D/MathlibAnalytic/ConcreteAnalyticSpineR2BatchNormClosureConsistency.lean")
ROOT = Path("MGAP4D/MathlibAnalytic.lean")

TARGET_ANCHORS = (
    "ConcreteGraphNormZeroCauchyConvergentBundle",
    "concreteIdentityGraphNormZeroCauchyConvergentBundle",
    "ConcreteGraphPointNormLimitConsistencySurface",
    "concreteIdentityGraphPointNormLimitConsistencySurface",
    "ConcreteDiagonalCandidateNormConsistencyBundle",
    "concreteIdentityDiagonalCandidateNormConsistencyBundle",
    "concreteAnalyticSpineR2BatchNormClosureConsistencySurfaceReady",
    "concrete_analytic_spine_r2_batch_norm_closure_consistency_surface_ready",
    "concreteAnalyticSpineR2BatchNormClosureConsistencyHardResidualBoundaryHeld",
    "concrete_analytic_spine_r2_batch_norm_closure_consistency_hard_residual_boundary_held",
)

BOUNDARY_ANCHORS = (
    "not graph-norm completion",
    "not Cauchy completion",
    "not a closed-operator theorem",
    "not self-adjointness",
    "spectral theorem",
    "PVM",
    "33/20",
)

ROOT_ANCHORS = (
    "import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineR2BatchNormClosureConsistency",
)


def strip_comments(text: str) -> str:
    out = []
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


def cleaned(path: Path) -> str:
    return STRING_RE.sub('""', strip_comments(path.read_text(encoding="utf-8")))


def require(path: Path, anchors: tuple[str, ...], label: str, clean: bool) -> list[str]:
    if not path.exists():
        return [f"missing {label} file: {path}"]
    text = cleaned(path) if clean else path.read_text(encoding="utf-8")
    return [f"missing {label} anchor {a!r} in {path}" for a in anchors if a not in text]


def main() -> None:
    failures = []
    if TARGET.exists():
        for lineno, line in enumerate(cleaned(TARGET).splitlines(), start=1):
            if TOKEN_RE.search(line):
                failures.append(f"{TARGET}:{lineno}: forbidden Lean token")
    failures.extend(require(TARGET, TARGET_ANCHORS, "target", True))
    failures.extend(require(TARGET, BOUNDARY_ANCHORS, "boundary", False))
    failures.extend(require(ROOT, ROOT_ANCHORS, "root import", False))
    print("Concrete analytic spine R2 batch norm closure consistency audit")
    print(f"Target anchors audited: {len(TARGET_ANCHORS)}")
    print(f"Boundary anchors audited: {len(BOUNDARY_ANCHORS)}")
    print(f"Root imports audited: {len(ROOT_ANCHORS)}")
    if failures:
        print("Concrete analytic spine R2 batch norm closure consistency audit failed:", file=sys.stderr)
        for f in failures:
            print(f"  {f}", file=sys.stderr)
        raise SystemExit(1)
    print("Concrete analytic spine R2 batch norm closure consistency audit passed")


if __name__ == "__main__":
    main()
