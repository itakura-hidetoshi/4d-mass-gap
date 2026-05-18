#!/usr/bin/env python3
from __future__ import annotations

from pathlib import Path
import re
import sys

TOKEN_RE = re.compile(r"\b(sorry|admit|axiom|constant)\b")
TARGET = Path("MGAP4D/MathlibAnalytic/ConcreteAnalyticSpineR2BatchReadinessIndex.lean")
ROOT = Path("MGAP4D/MathlibAnalytic.lean")

TARGET_ANCHORS = (
    "ConcreteAnalyticSpineR2ReadinessIndexSurface",
    "concreteAnalyticSpineR2ReadinessIndexSurface",
    "ConcreteAnalyticSpineR2BoundaryIndexSurface",
    "concreteAnalyticSpineR2BoundaryIndexSurface",
    "concrete_analytic_spine_r2_boundary_index_surface_ready",
    "concreteAnalyticSpineR2BatchReadinessIndexSurfaceReady",
    "concrete_analytic_spine_r2_batch_readiness_index_surface_ready",
    "concreteAnalyticSpineR2BatchReadinessIndexHardResidualBoundaryHeld",
    "concrete_analytic_spine_r2_batch_readiness_index_hard_residual_boundary_held",
)

BOUNDARY_FIELD_ANCHORS = (
    "notPhysicalYangMillsHamiltonian",
    "notGenuineUnboundedHamiltonian",
    "notGraphClosureTheorem",
    "notGraphNormCompletionTheorem",
    "notCauchyCompletionTheorem",
    "notClosedOperatorTheorem",
    "notSelfAdjoint",
    "notSpectralTheorem",
    "notPVM",
    "notNonDefinitional3320Emergence",
)

ROOT_ANCHOR = "import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineR2BatchReadinessIndex"


def main() -> None:
    failures = []
    target = TARGET.read_text(encoding="utf-8") if TARGET.exists() else ""
    root = ROOT.read_text(encoding="utf-8") if ROOT.exists() else ""
    for lineno, line in enumerate(target.splitlines(), start=1):
        if TOKEN_RE.search(line):
            failures.append(f"{TARGET}:{lineno}: forbidden Lean token")
    for anchor in TARGET_ANCHORS:
        if anchor not in target:
            failures.append(f"missing target anchor {anchor!r}")
    for anchor in BOUNDARY_FIELD_ANCHORS:
        if anchor not in target:
            failures.append(f"missing boundary field anchor {anchor!r}")
    if ROOT_ANCHOR not in root:
        failures.append(f"missing root import anchor {ROOT_ANCHOR!r}")
    print("Concrete analytic spine R2 batch readiness index audit")
    print(f"Target anchors audited: {len(TARGET_ANCHORS)}")
    print(f"Boundary field anchors audited: {len(BOUNDARY_FIELD_ANCHORS)}")
    print("Root imports audited: 1")
    if failures:
        print("Concrete analytic spine R2 batch readiness index audit failed:", file=sys.stderr)
        for f in failures:
            print(f"  {f}", file=sys.stderr)
        raise SystemExit(1)
    print("Concrete analytic spine R2 batch readiness index audit passed")


if __name__ == "__main__":
    main()
