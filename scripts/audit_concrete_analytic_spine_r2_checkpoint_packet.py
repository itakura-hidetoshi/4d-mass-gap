#!/usr/bin/env python3
from __future__ import annotations

from pathlib import Path
import re
import sys

TOKEN_RE = re.compile(r"\b(sorry|admit|axiom|constant)\b")
TARGET = Path("MGAP4D/MathlibAnalytic/ConcreteAnalyticSpineR2CheckpointPacket.lean")
ROOT = Path("MGAP4D/MathlibAnalytic.lean")

TARGET_ANCHORS = (
    "ConcreteAnalyticSpineR2CheckpointPacketSurface",
    "concreteAnalyticSpineR2CheckpointPacketSurface",
    "concreteAnalyticSpineR2CheckpointPacketSurfaceReady",
    "concrete_analytic_spine_r2_checkpoint_packet_surface_ready",
    "concreteAnalyticSpineR2CheckpointPacketHardResidualBoundaryHeld",
    "concrete_analytic_spine_r2_checkpoint_packet_hard_residual_boundary_held",
)

FIELD_ANCHORS = (
    "localClosureSummaryReady",
    "finalLocalIndexReady",
    "reviewPacketReady",
    "nonPromotionGateReady",
    "checkpointBoundaryHeld",
)

ROOT_ANCHOR = "import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineR2CheckpointPacket"


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
    for anchor in FIELD_ANCHORS:
        if anchor not in target:
            failures.append(f"missing field anchor {anchor!r}")
    if ROOT_ANCHOR not in root:
        failures.append(f"missing root import anchor {ROOT_ANCHOR!r}")
    print("Concrete analytic spine R2 checkpoint packet audit")
    print(f"Target anchors audited: {len(TARGET_ANCHORS)}")
    print(f"Field anchors audited: {len(FIELD_ANCHORS)}")
    print("Root imports audited: 1")
    if failures:
        print("Concrete analytic spine R2 checkpoint packet audit failed:", file=sys.stderr)
        for f in failures:
            print(f"  {f}", file=sys.stderr)
        raise SystemExit(1)
    print("Concrete analytic spine R2 checkpoint packet audit passed")


if __name__ == "__main__":
    main()
