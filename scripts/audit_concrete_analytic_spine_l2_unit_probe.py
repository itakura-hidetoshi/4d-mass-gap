#!/usr/bin/env python3
from pathlib import Path
import re
import sys

TOKEN_RE = re.compile(r"\b(sorry|admit|axiom|constant)\b")
TARGET = Path("MGAP4D/MathlibAnalytic/ConcreteAnalyticSpineL2UnitProbe.lean")
ROOT = Path("MGAP4D/MathlibAnalytic.lean")
ANCHORS = [
    "concreteL2UnitRaw",
    "concreteL2UnitFiniteSupport",
    "concreteL2Unit",
    "concreteL2UnitFiniteSupportWitness",
    "concreteL2UnitDiagonalDomain",
    "concreteL2UnitFiniteSupportCore",
    "concrete_l2_diagonal_raw_action_unit_self",
    "concrete_l2_diagonal_raw_action_unit_off",
    "ConcreteL2UnitProbeSurface",
    "concreteL2UnitProbeSurface",
    "concreteAnalyticSpineL2UnitProbeSurfaceReady",
    "concrete_analytic_spine_l2_unit_probe_surface_ready",
    "concreteAnalyticSpineL2UnitProbeHardResidualBoundaryHeld",
    "concrete_analytic_spine_l2_unit_probe_hard_residual_boundary_held",
    "boundaryNotOperatorNormUnboundednessTheorem",
    "boundaryNotDensityTheorem",
    "boundaryNotClosedOperatorTheorem",
    "boundaryNotSelfAdjointness",
]
ROOT_ANCHOR = "import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2UnitProbe"


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
    print("Concrete analytic spine l2 unit probe audit")
    print(f"Anchors audited: {len(ANCHORS)}")
    print("Root imports audited: 1")
    if failures:
        print("Concrete analytic spine l2 unit probe audit failed:", file=sys.stderr)
        for f in failures:
            print(f"  {f}", file=sys.stderr)
        raise SystemExit(1)
    print("Concrete analytic spine l2 unit probe audit passed")


if __name__ == "__main__":
    main()
