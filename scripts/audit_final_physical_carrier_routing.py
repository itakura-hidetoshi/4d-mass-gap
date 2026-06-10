#!/usr/bin/env python3
"""Audit final-physical-carrier routing for physical operator skeletons.

This is a syntactic/contract audit. Lean kernel checking remains `lake build`.
The audit prevents regression from the final countable-coordinate physical
Hilbert carrier back to one-point/PUnit prototype carriers in the physical
unbounded-operator and concrete Yang--Mills Hamiltonian skeletons.
"""

from __future__ import annotations

from pathlib import Path
import re
import sys

STRING_RE = re.compile(r'"(?:[^"\\]|\\.)*"')
FORBIDDEN_TOKENS_RE = re.compile(r"\b(sorry|admit|axiom|constant)\b")

PHYSICAL_LEAN_PATH = Path("MGAP4D/MathlibAnalytic/PhysicalUnboundedOperatorSkeleton.lean")
CONCRETE_YM_LEAN_PATH = Path("MGAP4D/MathlibAnalytic/ConcreteYangMillsHamiltonianSkeleton.lean")
PHYSICAL_DOC_PATH = Path("docs/mathlib_physical_unbounded_operator_skeleton.md")
CONCRETE_YM_DOC_PATH = Path("docs/mathlib_concrete_yang_mills_hamiltonian_skeleton.md")
CHECKLIST_PATH = Path("EXTERNAL_REVIEW_CHECKLIST.md")
CHECK_PATH = Path("scripts/check.sh")
FAST_CHECK_PATH = Path("scripts/check_changed_lean.sh")

REQUIRED_PHYSICAL_LEAN_ANCHORS = (
    "FinalPhysicalHilbertCarrier",
    "finalPhysicalHilbertZero",
    "finalPhysicalHilbertInner",
    "finalPhysicalHilbertNorm",
    "finalPhysicalHilbertDomain",
    "finalPhysicalHamiltonianWeight",
    "finalPhysicalHamiltonian",
    "finalPhysicalRayleigh",
    "finalPhysicalUnboundedOperatorSkeletonData",
    "carrier := FinalPhysicalHilbertCarrier",
    "zero := finalPhysicalHilbertZero",
    "inner := finalPhysicalHilbertInner",
    "norm := finalPhysicalHilbertNorm",
    "domain := finalPhysicalHilbertDomain",
    "H_phys := finalPhysicalHamiltonian",
    "rayleigh := finalPhysicalRayleigh",
    "abbrev prototypePhysicalUnboundedOperatorSkeletonData",
    "finalPhysicalUnboundedOperatorSkeletonData",
    "final_physical_unbounded_operator_skeleton_ready",
    "prototype_physical_unbounded_operator_skeleton_ready",
)

REQUIRED_CONCRETE_YM_LEAN_ANCHORS = (
    "import MGAP4D.MathlibAnalytic.PhysicalUnboundedOperatorSkeleton",
    "finalConcreteYangMillsHamiltonianSkeletonData",
    "state := FinalPhysicalHilbertCarrier",
    "ymData := FinalPhysicalHilbertCarrier",
    "domain := finalPhysicalHilbertDomain",
    "H_phys := finalPhysicalHamiltonian",
    "rayleigh := finalPhysicalRayleigh",
    "distinguished := finalPhysicalHilbertZero",
    "ymWitness := finalPhysicalHilbertZero",
    "finalPhysicalUnboundedOperatorSkeletonData.H_phys = finalPhysicalHamiltonian",
    "finalPhysicalUnboundedOperatorSkeletonData.domain = finalPhysicalHilbertDomain",
    "noncomputable abbrev prototypeConcreteYangMillsHamiltonianSkeletonData",
    "finalConcreteYangMillsHamiltonianSkeletonData",
    "final_concrete_ym_hamiltonian_skeleton_ready",
    "prototype_concrete_ym_hamiltonian_skeleton_ready",
)

FORBIDDEN_PHYSICAL_CODE_SNIPPETS = (
    "PUnit",
    "carrier := PUnit",
    "inner := fun _ _ => 0",
    "norm := fun _ => 0",
    "H_phys := fun ψ => ψ",
    "rayleigh := fun _ => exactGapValueReal",
)

FORBIDDEN_CONCRETE_YM_CODE_SNIPPETS = (
    "PUnit",
    "state := PUnit",
    "ymData := PUnit",
    "H_phys := fun ψ => ψ",
    "rayleigh := fun _ => exactGapValueReal",
)

REQUIRED_PHYSICAL_DOC_ANCHORS = (
    "FinalPhysicalHilbertCarrier",
    "finalPhysicalHamiltonian",
    "finalPhysicalRayleigh",
    "finalPhysicalUnboundedOperatorSkeletonData",
    "physical carrier is the final countable-coordinate Hilbert carrier, not PUnit",
    "H_phys is a diagonal coordinate Hamiltonian, not the identity on a singleton",
)

REQUIRED_CONCRETE_YM_DOC_ANCHORS = (
    "finalConcreteYangMillsHamiltonianSkeletonData",
    "prototypeConcreteYangMillsHamiltonianSkeletonData",
    "state := FinalPhysicalHilbertCarrier",
    "ymData := FinalPhysicalHilbertCarrier",
    "H_phys := finalPhysicalHamiltonian",
    "rayleigh := finalPhysicalRayleigh",
    "final-physical-carrier routed skeleton",
    "not as a one-point carrier prototype",
)

REQUIRED_CHECKLIST_ANCHORS = (
    "final-physical-carrier routing for the physical unbounded-operator and concrete Yang-Mills Hamiltonian skeletons",
    "FinalPhysicalHilbertCarrier",
    "finalPhysicalHamiltonian",
    "finalPhysicalRayleigh",
    "finalPhysicalUnboundedOperatorSkeletonData",
    "finalConcreteYangMillsHamiltonianSkeletonData",
    "prototypePhysicalUnboundedOperatorSkeletonData` aliases the final physical data",
    "prototypeConcreteYangMillsHamiltonianSkeletonData` aliases the final physical carrier route",
)

REQUIRED_CHECK_ANCHORS = (
    "audit final physical carrier routing",
    "scripts/audit_final_physical_carrier_routing.py",
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


def lean_code(text: str) -> str:
    return strip_strings(strip_lean_comments(text))


def require_file(path: Path) -> str:
    if not path.exists():
        raise AssertionError(f"missing required file: {path}")
    return path.read_text(encoding="utf-8")


def require_all(label: str, text: str, anchors: tuple[str, ...]) -> None:
    missing = [anchor for anchor in anchors if anchor not in text]
    if missing:
        raise AssertionError(f"{label} missing anchors: {', '.join(missing)}")


def forbid_all(label: str, text: str, snippets: tuple[str, ...]) -> None:
    present = [snippet for snippet in snippets if snippet in text]
    if present:
        raise AssertionError(f"{label} contains forbidden prototype/singleton snippets: {', '.join(present)}")


def audit_lean_file(path: Path, anchors: tuple[str, ...], forbidden: tuple[str, ...]) -> None:
    text = require_file(path)
    without_comments = strip_lean_comments(text)
    code = lean_code(text)

    forbidden_tokens = sorted(set(FORBIDDEN_TOKENS_RE.findall(code)))
    if forbidden_tokens:
        raise AssertionError(f"forbidden Lean tokens found in {path}: {', '.join(forbidden_tokens)}")

    require_all(str(path), without_comments, anchors)
    forbid_all(str(path), code, forbidden)


def main() -> int:
    audit_lean_file(PHYSICAL_LEAN_PATH, REQUIRED_PHYSICAL_LEAN_ANCHORS, FORBIDDEN_PHYSICAL_CODE_SNIPPETS)
    audit_lean_file(CONCRETE_YM_LEAN_PATH, REQUIRED_CONCRETE_YM_LEAN_ANCHORS, FORBIDDEN_CONCRETE_YM_CODE_SNIPPETS)

    require_all("physical unbounded-operator documentation", require_file(PHYSICAL_DOC_PATH), REQUIRED_PHYSICAL_DOC_ANCHORS)
    require_all("concrete Yang-Mills Hamiltonian documentation", require_file(CONCRETE_YM_DOC_PATH), REQUIRED_CONCRETE_YM_DOC_ANCHORS)
    require_all("external review checklist", require_file(CHECKLIST_PATH), REQUIRED_CHECKLIST_ANCHORS)
    require_all("check.sh", require_file(CHECK_PATH), REQUIRED_CHECK_ANCHORS)
    require_all("check_changed_lean.sh", require_file(FAST_CHECK_PATH), REQUIRED_CHECK_ANCHORS)

    print("Final physical carrier routing audit")
    print(f"Physical Lean anchors audited: {len(REQUIRED_PHYSICAL_LEAN_ANCHORS)}")
    print(f"Concrete Yang-Mills Lean anchors audited: {len(REQUIRED_CONCRETE_YM_LEAN_ANCHORS)}")
    print("Forbidden singleton/PUnit snippets audited in final routed skeleton files")
    print(f"Documentation audited: {PHYSICAL_DOC_PATH}, {CONCRETE_YM_DOC_PATH}")
    print(f"Checklist audited: {CHECKLIST_PATH}")
    print("Forbidden Lean tokens audited: sorry/admit/axiom/constant")
    print("Final physical carrier routing audit passed")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except AssertionError as exc:
        print(f"audit_final_physical_carrier_routing.py: {exc}", file=sys.stderr)
        raise SystemExit(1)
