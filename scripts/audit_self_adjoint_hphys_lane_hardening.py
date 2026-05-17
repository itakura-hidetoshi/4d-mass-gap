#!/usr/bin/env python3
"""Audit the self-adjoint H_phys lane hardening layer."""

from __future__ import annotations

from pathlib import Path
import re
import sys

STRING_RE = re.compile(r'"(?:[^"\\]|\\.)*"')
FORBIDDEN_TOKENS_RE = re.compile(r"\b(sorry|admit|axiom|constant)\b")
TARGET_PATH = Path("MGAP4D/MathlibAnalytic/SelfAdjointHPhysLaneHardening.lean")
ROOT_PATH = Path("MGAP4D/MathlibAnalytic.lean")
DOC_PATH = Path("docs/self_adjoint_hphys_lane_hardening.md")

REQUIRED_TARGET_ANCHORS = (
    "SelfAdjointHPhysLaneHardeningData",
    "SelfAdjointHPhysLaneHardeningData.ready",
    "selfAdjointHPhysLaneHardeningData",
    "self_adjoint_hphys_lane_hardening_ready",
    "completeHilbertConstructionLaneReady",
    "completeInfiniteDimensionalHilbertConstructionLaneData.ready",
    "hphysInterfaceReady",
    "hphysTheoremBodyReady",
    "physicalOperatorSkeletonReady",
    "concreteHPhysBridgeReady",
    "interfaceHardened",
    "theoremBodyHardened",
    "domainClosureHardened",
    "symmetryOnDomainHardened",
    "selfAdjointCertificateHardened",
    "rayleighCompatibilityHardened",
    "physicalOperatorSkeletonHardened",
    "concreteHPhysBridgeHardened",
    "hardPhysicalBoundaryVisible",
    "exactValuePreserved",
    "reviewLevelOnly",
    "publicBoundaryHeld",
    "finalReleaseHeld",
)

REQUIRED_THEOREM_ANCHORS = (
    "self_adjoint_hphys_interface_hardened",
    "self_adjoint_hphys_theorem_body_hardened",
    "self_adjoint_hphys_domain_closure_hardened",
    "self_adjoint_hphys_symmetry_on_domain_hardened",
    "self_adjoint_hphys_certificate_hardened",
    "self_adjoint_hphys_rayleigh_compatibility_hardened",
    "self_adjoint_hphys_physical_operator_skeleton_hardened",
    "self_adjoint_hphys_concrete_bridge_hardened",
    "self_adjoint_hphys_hard_boundary_visible",
    "self_adjoint_hphys_exact_value_preserved",
)

REQUIRED_ROOT_ANCHORS = (
    "import MGAP4D.MathlibAnalytic.SelfAdjointHPhysLaneHardening",
)

REQUIRED_DOC_ANCHORS = (
    "Self-adjoint HPhys Lane Hardening",
    "completeHilbertConstructionLaneReady",
    "completeInfiniteDimensionalHilbertConstructionLaneData.ready",
    "interfaceHardened",
    "theoremBodyHardened",
    "domainClosureHardened",
    "symmetryOnDomainHardened",
    "selfAdjointCertificateHardened",
    "rayleighCompatibilityHardened",
    "physicalOperatorSkeletonHardened",
    "concreteHPhysBridgeHardened",
)

FORBIDDEN_STALE_ANCHORS = (
    "hilbertConstructionLaneReady",
    "hilbertConstructionLaneHardeningData",
    "hilbert_construction_lane_hardening_ready",
    "HilbertConstructionLaneHardening",
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


def source_for(path: Path, *, clean_lean: bool) -> str:
    return cleaned_lean_source(path) if clean_lean else path.read_text(encoding="utf-8")


def require(path: Path, anchors: tuple[str, ...], label: str, *, clean_lean: bool) -> list[str]:
    if not path.exists():
        return [f"missing {label} file: {path}"]
    source = source_for(path, clean_lean=clean_lean)
    return [f"missing {label} anchor {anchor!r} in {path}" for anchor in anchors if anchor not in source]


def forbid(path: Path, anchors: tuple[str, ...], label: str, *, clean_lean: bool) -> list[str]:
    if not path.exists():
        return []
    source = source_for(path, clean_lean=clean_lean)
    return [f"forbidden stale {label} anchor {anchor!r} in {path}" for anchor in anchors if anchor in source]


def audit_forbidden_tokens(path: Path) -> list[str]:
    if not path.exists():
        return [f"missing self-adjoint HPhys hardening file for forbidden-token audit: {path}"]
    source = cleaned_lean_source(path)
    hits: list[str] = []
    for lineno, line in enumerate(source.splitlines(), start=1):
        if FORBIDDEN_TOKENS_RE.search(line):
            hits.append(f"{path}:{lineno}: forbidden token in self-adjoint HPhys audit")
    return hits


def main() -> None:
    failures: list[str] = []
    failures.extend(audit_forbidden_tokens(TARGET_PATH))
    failures.extend(require(TARGET_PATH, REQUIRED_TARGET_ANCHORS, "self-adjoint HPhys target", clean_lean=True))
    failures.extend(require(TARGET_PATH, REQUIRED_THEOREM_ANCHORS, "self-adjoint HPhys theorem", clean_lean=True))
    failures.extend(require(ROOT_PATH, REQUIRED_ROOT_ANCHORS, "root import", clean_lean=True))
    failures.extend(require(DOC_PATH, REQUIRED_DOC_ANCHORS, "self-adjoint HPhys documentation", clean_lean=False))
    failures.extend(forbid(TARGET_PATH, FORBIDDEN_STALE_ANCHORS, "old Hilbert construction lane", clean_lean=True))

    print("Self-adjoint HPhys lane hardening audit")
    print(f"Self-adjoint HPhys anchors audited: {len(REQUIRED_TARGET_ANCHORS)}")
    print(f"Self-adjoint HPhys theorem anchors audited: {len(REQUIRED_THEOREM_ANCHORS)}")
    print("Root import audited: MGAP4D/MathlibAnalytic.lean")
    print("Documentation audited: docs/self_adjoint_hphys_lane_hardening.md")
    print("Forbidden stale Hilbert lane anchors audited")
    print("Forbidden Lean tokens audited: sorry/admit/axiom/constant")

    if failures:
        print("Self-adjoint HPhys lane hardening audit failed:", file=sys.stderr)
        for failure in failures:
            print(f"  {failure}", file=sys.stderr)
        raise SystemExit(1)

    print("Self-adjoint HPhys lane hardening audit passed")


if __name__ == "__main__":
    main()
