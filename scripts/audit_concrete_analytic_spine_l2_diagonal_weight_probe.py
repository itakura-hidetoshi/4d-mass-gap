#!/usr/bin/env python3
from pathlib import Path
import re
import sys

TOKEN_RE = re.compile(r"\b(sorry|admit|axiom|constant)\b")
TARGET = Path("MGAP4D/MathlibAnalytic/ConcreteAnalyticSpineL2DiagonalWeightProbe.lean")
ROOT = Path("MGAP4D/MathlibAnalytic.lean")
ANCHORS = [
    "ConcreteL2DiagonalWeightProbe",
    "concreteL2DiagonalWeightProbe",
    "concrete_l2_diagonal_weight_probe_zero",
    "concrete_l2_diagonal_weight_pos",
    "concrete_l2_diagonal_weight_eq_nat_add_one",
    "concrete_l2_diagonal_weight_succ",
    "ConcreteL2DiagonalWeightProbeSurface",
    "concreteL2DiagonalWeightProbeSurface",
    "concrete_analytic_spine_l2_diagonal_weight_probe_surface_ready",
    "concrete_analytic_spine_l2_diagonal_weight_probe_hard_residual_boundary_held",
    "boundaryNotOperatorNormUnboundednessTheorem",
    "boundaryNotClosedOperatorTheorem",
    "boundaryNotSelfAdjointness",
]
ROOT_ANCHOR = "import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2DiagonalWeightProbe"


def main() -> None:
    failures = []
    target = TARGET.read_text(encoding="utf-8") if TARGET.exists() else ""
    root = ROOT.read_text(encoding="utf-8") if ROOT.exists() else ""
    for lineno, line in enumerate(target.splitlines(), start=1):
        if TOKEN_RE.search(line):
            failures.append(f"{TARGET}:{lineno}: forbidden Lean token")
    for anchor in ANCHORS:
        if anchor not in target:
            failures.append(f"missing anchor {anchor!r}")
    if ROOT_ANCHOR not in root:
        failures.append("missing root import anchor")
    print("Concrete analytic spine l2 diagonal weight probe audit")
    print(f"Anchors audited: {len(ANCHORS)}")
    print("Root imports audited: 1")
    if failures:
        print("Concrete analytic spine l2 diagonal weight probe audit failed:", file=sys.stderr)
        for f in failures:
            print(f"  {f}", file=sys.stderr)
        raise SystemExit(1)
    print("Concrete analytic spine l2 diagonal weight probe audit passed")


if __name__ == "__main__":
    main()
