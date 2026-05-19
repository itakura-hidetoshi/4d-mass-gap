#!/usr/bin/env python3
from pathlib import Path
import re
import sys

TOKEN_RE = re.compile(r"\b(sorry|admit|axiom|constant)\b")
TARGET = Path("MGAP4D/MathlibAnalytic/ConcreteAnalyticSpineL2FiniteSupportCore.lean")
ROOT = Path("MGAP4D/MathlibAnalytic.lean")
ANCHORS = [
    "ConcreteL2DiagonalFiniteSupportDomainCarrier",
    "concreteL2DiagonalFiniteSupportDomainZero",
    "concrete_l2_diagonal_finite_support_domain_nonempty",
    "concreteL2FiniteSupportCoreToDomain",
    "concreteL2FiniteSupportCoreActionL2",
    "concrete_l2_finite_support_core_action_zero_ext",
    "ConcreteL2FiniteSupportCoreGraphCarrier",
    "concrete_l2_finite_support_core_zero_graph_pair_eq",
    "concrete_l2_finite_support_core_graph_nonempty",
    "concrete_l2_finite_support_core_zero_graph_mem",
    "ConcreteL2FiniteSupportCoreSurface",
    "concreteL2FiniteSupportCoreSurface",
    "concrete_analytic_spine_l2_finite_support_core_surface_ready",
    "concrete_analytic_spine_l2_finite_support_core_hard_residual_boundary_held",
    "boundaryNotDensityTheorem",
    "boundaryNotEssentialSelfAdjointness",
    "boundaryNotClosedOperatorTheorem",
]
ROOT_ANCHOR = "import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2FiniteSupportCore"


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
    print("Concrete analytic spine l2 finite support core audit")
    print(f"Anchors audited: {len(ANCHORS)}")
    print("Root imports audited: 1")
    if failures:
        print("Concrete analytic spine l2 finite support core audit failed:", file=sys.stderr)
        for f in failures:
            print(f"  {f}", file=sys.stderr)
        raise SystemExit(1)
    print("Concrete analytic spine l2 finite support core audit passed")


if __name__ == "__main__":
    main()
