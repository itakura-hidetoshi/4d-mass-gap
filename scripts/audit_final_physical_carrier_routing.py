#!/usr/bin/env python3
"""Audit final-physical-carrier routing for physical operator skeletons.

This is a syntactic/contract audit. Lean kernel checking remains `lake build`.
The audit prevents regression from the final countable-coordinate physical
Hilbert carrier back to one-point/PUnit prototype carriers in the observable,
compact plaquette, concrete Hilbert, concrete H_phys, physical unbounded-
operator, concrete Yang--Mills Hamiltonian, and operator-measure surfaces.
"""

from __future__ import annotations

from pathlib import Path
import re
import sys

STRING_RE = re.compile(r'"(?:[^"\\]|\\.)*"')
FORBIDDEN_TOKENS_RE = re.compile(r"\b(sorry|admit|axiom|constant)\b")

CORE_LEAN_PATH = Path("MGAP4D/MathlibAnalytic/FinalPhysicalHilbertCarrierCore.lean")
OBSERVABLE_INTERFACE_LEAN_PATH = Path("MGAP4D/MathlibAnalytic/ObservableAtomInterface.lean")
OBSERVABLE_THEOREM_LEAN_PATH = Path("MGAP4D/MathlibAnalytic/ObservableAtomTheoremTheorem.lean")
COMPACT_PLAQUETTE_LEAN_PATH = Path("MGAP4D/MathlibAnalytic/CompactPlaquetteConstructionTheorem.lean")
OPERATOR_MEASURE_LEAN_PATH = Path("MGAP4D/MathlibAnalytic/OperatorMeasureCompatibilityTheorem.lean")
CONCRETE_HILBERT_LEAN_PATH = Path("MGAP4D/MathlibAnalytic/ConcreteHilbertRealizationTheorem.lean")
CONCRETE_HPHYS_LEAN_PATH = Path("MGAP4D/MathlibAnalytic/ConcreteHPhysRealizationTheorem.lean")
PHYSICAL_LEAN_PATH = Path("MGAP4D/MathlibAnalytic/PhysicalUnboundedOperatorSkeleton.lean")
CONCRETE_YM_LEAN_PATH = Path("MGAP4D/MathlibAnalytic/ConcreteYangMillsHamiltonianSkeleton.lean")
PHYSICAL_DOC_PATH = Path("docs/mathlib_physical_unbounded_operator_skeleton.md")
CONCRETE_YM_DOC_PATH = Path("docs/mathlib_concrete_yang_mills_hamiltonian_skeleton.md")
CHECKLIST_PATH = Path("EXTERNAL_REVIEW_CHECKLIST.md")
CHECK_PATH = Path("scripts/check.sh")
FAST_CHECK_PATH = Path("scripts/check_changed_lean.sh")

REQUIRED_CORE_LEAN_ANCHORS = (
    "import MGAP4D.MathlibAnalytic.Basic",
    "def FinalPhysicalHilbertCarrier : Type := ℕ → ℝ",
    "def finalPhysicalHilbertZero : FinalPhysicalHilbertCarrier",
    "def finalPhysicalHilbertInner",
    "def finalPhysicalHilbertNorm",
    "def finalPhysicalHilbertDomain",
    "def finalPhysicalHamiltonianWeight",
    "def finalPhysicalHamiltonian",
    "def finalPhysicalRayleigh",
    "final_physical_hamiltonian_domain_preserved",
    "final_physical_hamiltonian_symmetric_on_domain",
    "final_physical_rayleigh_lower_bound",
    "final_physical_distinguished_attains_exact",
)

REQUIRED_OBSERVABLE_INTERFACE_LEAN_ANCHORS = (
    "import MGAP4D.MathlibAnalytic.FinalPhysicalHilbertCarrierCore",
    "abbrev PrototypeObservable := FinalPhysicalHilbertCarrier",
    "def prototypeObservable : PrototypeObservable :=",
    "finalPhysicalHilbertZero",
    "observable := FinalPhysicalHilbertCarrier",
    "chosenObservable := finalPhysicalHilbertZero",
    "spectralWeight := prototypeObservableSpectralWeight",
)

REQUIRED_OBSERVABLE_THEOREM_LEAN_ANCHORS = (
    "import MGAP4D.MathlibAnalytic.FinalPhysicalHilbertCarrierCore",
    "finalPhysicalObservableAtomTheoremTheoremData",
    "observable := FinalPhysicalHilbertCarrier",
    "chosenObservable := finalPhysicalHilbertZero",
    "spectralWeight := fun _ _ => exactGapSpectralMassReal",
    "final_physical_observable_atom_theorem_theorem_data_ready",
    "abbrev singletonObservableAtomTheoremTheoremData",
    "finalPhysicalObservableAtomTheoremTheoremData",
)

REQUIRED_COMPACT_PLAQUETTE_LEAN_ANCHORS = (
    "import MGAP4D.MathlibAnalytic.FinalPhysicalHilbertCarrierCore",
    "finalPhysicalCompactPlaquetteConstructionTheoremData",
    "plaquette := FinalPhysicalHilbertCarrier",
    "observable := FinalPhysicalHilbertCarrier",
    "constructObservable := finalPhysicalHamiltonian",
    "chosenPlaquette := finalPhysicalHilbertZero",
    "chosenObservable := finalPhysicalHamiltonian finalPhysicalHilbertZero",
    "final_physical_compact_plaquette_construction_theorem_data_ready",
    "final_physical_compact_plaquette_constructed_compact_support",
    "final_physical_compact_plaquette_chosen_observable_def",
    "abbrev singletonCompactPlaquetteConstructionTheoremData",
    "finalPhysicalCompactPlaquetteConstructionTheoremData",
)

REQUIRED_OPERATOR_MEASURE_LEAN_ANCHORS = (
    "constructedObservable := finalPhysicalHilbertZero",
    "constructionData := singletonCompactPlaquetteConstructionTheoremData",
    "observableAtomData := singletonObservableAtomTheoremTheoremData",
    "constructedObservable_def := rfl",
)

REQUIRED_CONCRETE_HILBERT_LEAN_ANCHORS = (
    "FinalConcreteHilbertCarrier",
    "finalConcreteHilbertZero",
    "finalConcreteHilbertInner",
    "finalConcreteHilbertNormSq",
    "finalConcreteHilbertRealizationTheoremData",
    "carrier := FinalConcreteHilbertCarrier",
    "zero := finalConcreteHilbertZero",
    "distinguished := finalConcreteHilbertZero",
    "inner := finalConcreteHilbertInner",
    "normSq := finalConcreteHilbertNormSq",
    "noncomputable abbrev singletonConcreteHilbertRealizationTheoremData",
    "finalConcreteHilbertRealizationTheoremData",
    "singleton_concrete_hilbert_realization_theorem_data_ready",
)

REQUIRED_CONCRETE_HPHYS_LEAN_ANCHORS = (
    "FinalConcreteHilbertCarrier",
    "finalConcreteHPhysDomain",
    "finalConcreteHPhysWeight",
    "finalConcreteHPhysHamiltonian",
    "finalConcreteHPhysRealizationTheoremData",
    "carrier := FinalConcreteHilbertCarrier",
    "domain := finalConcreteHPhysDomain",
    "H_phys := finalConcreteHPhysHamiltonian",
    "inner := finalConcreteHilbertInner",
    "distinguished := finalConcreteHilbertZero",
    "noncomputable abbrev singletonConcreteHPhysRealizationTheoremData",
    "finalConcreteHPhysRealizationTheoremData",
    "singleton_concrete_hphys_realization_theorem_data_ready",
)

REQUIRED_PHYSICAL_LEAN_ANCHORS = (
    "import MGAP4D.MathlibAnalytic.FinalPhysicalHilbertCarrierCore",
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

FORBIDDEN_CORE_CODE_SNIPPETS = (
    "PUnit",
    "carrier := PUnit",
    "H_phys := fun ψ => ψ",
    "rayleigh := fun _ => exactGapValueReal",
)

FORBIDDEN_OBSERVABLE_INTERFACE_CODE_SNIPPETS = (
    "observable := PrototypeObservable",
    "chosenObservable := prototypeObservable",
)

FORBIDDEN_OBSERVABLE_THEOREM_CODE_SNIPPETS = (
    "observable := PrototypeObservable",
    "chosenObservable := prototypeObservable",
    "spectralWeight := prototypeObservableSpectralWeight",
)

FORBIDDEN_COMPACT_PLAQUETTE_CODE_SNIPPETS = (
    "PrototypePlaquette",
    "plaquette := PrototypePlaquette",
    "observable := PrototypeObservable",
    "constructObservable := fun _ => prototypeObservable",
    "chosenObservable := prototypeObservable",
)

FORBIDDEN_OPERATOR_MEASURE_CODE_SNIPPETS = (
    "constructedObservable := prototypeObservable",
)

FORBIDDEN_CONCRETE_HILBERT_CODE_SNIPPETS = (
    "PUnit",
    "carrier := PUnit",
    "zero := PUnit.unit",
    "distinguished := PUnit.unit",
    "toRayleighState := fun _ => PUnit.unit",
)

FORBIDDEN_CONCRETE_HPHYS_CODE_SNIPPETS = (
    "PUnit",
    "carrier := PUnit",
    "distinguished := PUnit.unit",
    "H_phys := fun ψ => ψ",
    "toHPhysState := fun _ => PUnit.unit",
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
    audit_lean_file(CORE_LEAN_PATH, REQUIRED_CORE_LEAN_ANCHORS, FORBIDDEN_CORE_CODE_SNIPPETS)
    audit_lean_file(OBSERVABLE_INTERFACE_LEAN_PATH, REQUIRED_OBSERVABLE_INTERFACE_LEAN_ANCHORS, FORBIDDEN_OBSERVABLE_INTERFACE_CODE_SNIPPETS)
    audit_lean_file(OBSERVABLE_THEOREM_LEAN_PATH, REQUIRED_OBSERVABLE_THEOREM_LEAN_ANCHORS, FORBIDDEN_OBSERVABLE_THEOREM_CODE_SNIPPETS)
    audit_lean_file(COMPACT_PLAQUETTE_LEAN_PATH, REQUIRED_COMPACT_PLAQUETTE_LEAN_ANCHORS, FORBIDDEN_COMPACT_PLAQUETTE_CODE_SNIPPETS)
    audit_lean_file(OPERATOR_MEASURE_LEAN_PATH, REQUIRED_OPERATOR_MEASURE_LEAN_ANCHORS, FORBIDDEN_OPERATOR_MEASURE_CODE_SNIPPETS)
    audit_lean_file(CONCRETE_HILBERT_LEAN_PATH, REQUIRED_CONCRETE_HILBERT_LEAN_ANCHORS, FORBIDDEN_CONCRETE_HILBERT_CODE_SNIPPETS)
    audit_lean_file(CONCRETE_HPHYS_LEAN_PATH, REQUIRED_CONCRETE_HPHYS_LEAN_ANCHORS, FORBIDDEN_CONCRETE_HPHYS_CODE_SNIPPETS)
    audit_lean_file(PHYSICAL_LEAN_PATH, REQUIRED_PHYSICAL_LEAN_ANCHORS, FORBIDDEN_PHYSICAL_CODE_SNIPPETS)
    audit_lean_file(CONCRETE_YM_LEAN_PATH, REQUIRED_CONCRETE_YM_LEAN_ANCHORS, FORBIDDEN_CONCRETE_YM_CODE_SNIPPETS)

    require_all("physical unbounded-operator documentation", require_file(PHYSICAL_DOC_PATH), REQUIRED_PHYSICAL_DOC_ANCHORS)
    require_all("concrete Yang-Mills Hamiltonian documentation", require_file(CONCRETE_YM_DOC_PATH), REQUIRED_CONCRETE_YM_DOC_ANCHORS)
    require_all("external review checklist", require_file(CHECKLIST_PATH), REQUIRED_CHECKLIST_ANCHORS)
    require_all("check.sh", require_file(CHECK_PATH), REQUIRED_CHECK_ANCHORS)
    require_all("check_changed_lean.sh", require_file(FAST_CHECK_PATH), REQUIRED_CHECK_ANCHORS)

    print("Final physical carrier routing audit")
    print(f"Final physical carrier core Lean anchors audited: {len(REQUIRED_CORE_LEAN_ANCHORS)}")
    print(f"Observable interface Lean anchors audited: {len(REQUIRED_OBSERVABLE_INTERFACE_LEAN_ANCHORS)}")
    print(f"Observable theorem Lean anchors audited: {len(REQUIRED_OBSERVABLE_THEOREM_LEAN_ANCHORS)}")
    print(f"Compact plaquette Lean anchors audited: {len(REQUIRED_COMPACT_PLAQUETTE_LEAN_ANCHORS)}")
    print(f"Operator-measure Lean anchors audited: {len(REQUIRED_OPERATOR_MEASURE_LEAN_ANCHORS)}")
    print(f"Concrete Hilbert Lean anchors audited: {len(REQUIRED_CONCRETE_HILBERT_LEAN_ANCHORS)}")
    print(f"Concrete HPhys Lean anchors audited: {len(REQUIRED_CONCRETE_HPHYS_LEAN_ANCHORS)}")
    print(f"Physical Lean anchors audited: {len(REQUIRED_PHYSICAL_LEAN_ANCHORS)}")
    print(f"Concrete Yang-Mills Lean anchors audited: {len(REQUIRED_CONCRETE_YM_LEAN_ANCHORS)}")
    print("Forbidden singleton/PUnit/prototype snippets audited in final routed skeleton files")
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
