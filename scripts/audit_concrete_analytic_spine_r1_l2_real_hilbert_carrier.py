#!/usr/bin/env python3
"""Audit the R1 concrete l2 real Hilbert carrier PR unit."""

from __future__ import annotations

from pathlib import Path
import re
import sys

TARGET_PATH = Path("MGAP4D/MathlibAnalytic/ConcreteAnalyticSpineR1L2RealHilbertCarrier.lean")
ROOT_PATH = Path("MGAP4D/MathlibAnalytic.lean")
STRING_RE = re.compile(r'"(?:[^"\\]|\\.)*"')
FORBIDDEN_TOKENS_RE = re.compile(r"\b(sorry|admit|axiom|constant)\b")

REQUIRED_TARGET_ANCHORS = (
    "ConcreteR1L2RealHilbertCarrier",
    "lp (fun _ : ℕ => ℝ) 2",
    "concreteR1L2RealHilbertZero",
    "concreteR1L2RealHilbertUnit",
    "NormedAddCommGroup ConcreteR1L2RealHilbertCarrier",
    "InnerProductSpace ℝ ConcreteR1L2RealHilbertCarrier",
    "CompleteSpace ConcreteR1L2RealHilbertCarrier",
    "concrete_r1_l2_real_hilbert_normed_add_comm_group",
    "concrete_r1_l2_real_hilbert_inner_product_space",
    "concrete_r1_l2_real_hilbert_complete_space",
    "concrete_r1_l2_real_hilbert_zero_norm",
    "concrete_r1_l2_real_hilbert_unit_apply_self",
    "concrete_r1_l2_real_hilbert_unit_apply_ne",
    "concrete_r1_l2_real_hilbert_unit_norm_eq_one",
    "ConcreteR1L2RealHilbertCarrierSurface",
    "normedAddCommGroupWitness",
    "innerProductSpaceWitness",
    "completeSpaceWitness",
    "unitNormOneLaw",
    "concreteAnalyticSpineR1L2RealHilbertCarrierSurfaceReady",
    "concrete_analytic_spine_r1_l2_real_hilbert_carrier_surface_ready",
    "concreteAnalyticSpineR1L2RealHilbertCarrierHardBoundaryHeld",
    "concrete_analytic_spine_r1_l2_real_hilbert_carrier_hard_boundary_held",
)

REQUIRED_BOUNDARY_ANCHORS = (
    "boundaryNotDenseDomain",
    "boundaryNotUnboundedOperator",
    "boundaryNotGraphClosure",
    "boundaryNotSelfAdjointness",
    "boundaryNotSpectralMeasure",
    "boundaryNotPVM",
    "boundaryNotPlaquetteObservable",
    "boundaryNotExactAtom3320",
    "boundaryNotPositiveSpectralWeight",
)

REQUIRED_ROOT_IMPORTS = (
    "import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineR1L2RealHilbertCarrier",
)

FORBIDDEN_PREMATURE_CLAIMS = (
    "ConcreteL2DiagonalDomain",
    "concreteL2DiagonalRawAction",
    "ConcreteDenseDomainOperator",
    "SelfAdjointPhysicalHamiltonianReady",
    "ConcretePVMSpectralMeasureReady",
    "NondefinitionalSpectralAtom3320Ready",
    "PositiveSpectralWeightDerivation3320Ready",
    "selfAdjointReady",
    "pvmReady",
    "spectralMeasureReady",
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
        i += 1
    return "".join(out)


def strip_strings(text: str) -> str:
    return STRING_RE.sub('""', text)


def require_anchors(label: str, text: str, anchors: tuple[str, ...]) -> list[str]:
    return [f"missing {label} anchor: {anchor}" for anchor in anchors if anchor not in text]


def main() -> int:
    if not TARGET_PATH.exists():
        print(f"R1 l2 real Hilbert carrier audit failed: missing {TARGET_PATH}")
        return 1
    if not ROOT_PATH.exists():
        print(f"R1 l2 real Hilbert carrier audit failed: missing {ROOT_PATH}")
        return 1

    target = TARGET_PATH.read_text(encoding="utf-8")
    root = ROOT_PATH.read_text(encoding="utf-8")
    code = strip_strings(strip_lean_comments(target))

    problems: list[str] = []
    problems.extend(require_anchors("target", target, REQUIRED_TARGET_ANCHORS))
    problems.extend(require_anchors("boundary", target, REQUIRED_BOUNDARY_ANCHORS))
    problems.extend(require_anchors("root import", root, REQUIRED_ROOT_IMPORTS))

    token_hits = sorted(set(FORBIDDEN_TOKENS_RE.findall(code)))
    if token_hits:
        problems.append("forbidden Lean tokens in code: " + ", ".join(token_hits))

    premature = [claim for claim in FORBIDDEN_PREMATURE_CLAIMS if claim in code]
    if premature:
        problems.append("premature post-R1 claims in code: " + ", ".join(premature))

    if problems:
        print("R1 l2 real Hilbert carrier audit failed:")
        for problem in problems:
            print("  " + problem)
        return 1

    print("R1 l2 real Hilbert carrier audit")
    print(f"Target anchors audited: {len(REQUIRED_TARGET_ANCHORS)}")
    print(f"Boundary anchors audited: {len(REQUIRED_BOUNDARY_ANCHORS)}")
    print(f"Root imports audited: {len(REQUIRED_ROOT_IMPORTS)}")
    print("Forbidden Lean tokens audited: sorry/admit/axiom/constant")
    print("R1 l2 real Hilbert carrier audit passed")
    return 0


if __name__ == "__main__":
    sys.exit(main())
