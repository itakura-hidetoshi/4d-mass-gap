#!/usr/bin/env python3
from pathlib import Path
import re
import sys

TOKEN_RE = re.compile(r"\b(sorry|admit|axiom|constant)\b")
TARGET = Path("MGAP4D/MathlibAnalytic/ConcreteAnalyticSpineL2UnitObstructionBridge.lean")
ROOT = Path("MGAP4D/MathlibAnalytic.lean")
ANCHORS = [
    "concreteL2ObstructionUnitProbe",
    "concreteL2ObstructionUnitDomain",
    "concrete_l2_obstruction_unit_action_threshold_law",
    "ConcreteL2UnitObstructionBridgeSurface",
    "concreteL2UnitObstructionBridgeSurface",
    "concreteAnalyticSpineL2UnitObstructionBridgeSurfaceReady",
    "concrete_analytic_spine_l2_unit_obstruction_bridge_surface_ready",
    "concreteAnalyticSpineL2UnitObstructionBridgeHardResidualBoundaryHeld",
    "concrete_analytic_spine_l2_unit_obstruction_bridge_hard_residual_boundary_held",
    "boundaryNotOperatorNormUnboundednessTheorem",
    "boundaryNotClosedOperatorTheorem",
    "boundaryNotGraphClosureTheorem",
    "boundaryNotDensityTheorem",
    "boundaryNotSelfAdjointness",
]
ROOT_ANCHOR = "import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2UnitObstructionBridge"


def main():
    failures = []
    target = TARGET.read_text(encoding="utf-8") if TARGET.exists() else ""
    root = ROOT.read_text(encoding="utf-8") if ROOT.exists() else ""
    for i, line in enumerate(target.splitlines(), start=1):
        if TOKEN_RE.search(line):
            failures.append(f"{TARGET}:{i}: forbidden Lean token")
    for anchor in ANCHORS:
        if anchor not in target:
            failures.append(f"missing anchor {anchor!r}")
    if ROOT_ANCHOR not in root:
        failures.append("missing root import anchor")
    print("Concrete analytic spine l2 unit obstruction bridge audit")
    print(f"Anchors audited: {len(ANCHORS)}")
    print("Root imports audited: 1")
    if failures:
        print("Concrete analytic spine l2 unit obstruction bridge audit failed:", file=sys.stderr)
        for f in failures:
            print(f"  {f}", file=sys.stderr)
        raise SystemExit(1)
    print("Concrete analytic spine l2 unit obstruction bridge audit passed")


if __name__ == "__main__":
    main()
