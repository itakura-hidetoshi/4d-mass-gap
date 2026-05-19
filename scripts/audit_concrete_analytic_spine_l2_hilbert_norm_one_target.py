#!/usr/bin/env python3
from pathlib import Path
import re
import sys

TOKEN_RE = re.compile(r"\b(sorry|admit|axiom|constant)\b")
TARGET = Path("MGAP4D/MathlibAnalytic/ConcreteAnalyticSpineL2HilbertNormOneTarget.lean")
ANCHORS = [
    "concreteL2UnitHilbertNormOneTarget",
    "concrete_l2_unit_hilbert_norm_one_target_from_norm_sq",
    "ConcreteL2HilbertNormOneTargetSurface",
    "concreteL2HilbertNormOneTargetSurface",
    "concreteAnalyticSpineL2HilbertNormOneTargetSurfaceReady",
    "concrete_analytic_spine_l2_hilbert_norm_one_target_surface_ready",
    "concreteAnalyticSpineL2HilbertNormOneTargetHardResidualBoundaryHeld",
    "concrete_analytic_spine_l2_hilbert_norm_one_target_hard_residual_boundary_held",
    "concreteL2UnitFiniteSupportNormSq",
    "concrete_l2_unit_finite_support_norm_sq_eq_one",
    "not yet a completed `l2` Hilbert space construction",
    "not yet a Mathlib completed-Hilbert norm theorem",
    "boundaryNotCompletedL2HilbertSpaceConstruction",
    "boundaryNotMathlibNormTheorem",
    "boundaryNotGraphNormCompletion",
    "boundaryNotOperatorNormUnboundednessTheorem",
    "boundaryNotGraphClosure",
    "boundaryNotClosedOperatorTheorem",
    "boundaryNotSelfAdjointness",
]


def main():
    failures = []
    target = TARGET.read_text(encoding="utf-8") if TARGET.exists() else ""
    for i, line in enumerate(target.splitlines(), start=1):
        if TOKEN_RE.search(line):
            failures.append(f"{TARGET}:{i}: forbidden Lean token")
    for anchor in ANCHORS:
        if anchor not in target:
            failures.append(f"missing anchor {anchor!r}")
    print("Concrete analytic spine l2 Hilbert norm-one target audit")
    print(f"Anchors audited: {len(ANCHORS)}")
    print("Boundary anchors audited: completed Hilbert, Mathlib norm theorem, graph norm, unboundedness, closure, self-adjointness")
    if failures:
        print("Concrete analytic spine l2 Hilbert norm-one target audit failed:", file=sys.stderr)
        for f in failures:
            print(f"  {f}", file=sys.stderr)
        raise SystemExit(1)
    print("Concrete analytic spine l2 Hilbert norm-one target audit passed")


if __name__ == "__main__":
    main()
