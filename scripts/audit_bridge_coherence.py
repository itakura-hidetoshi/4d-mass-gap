#!/usr/bin/env python3
"""Audit bridge coherence for the analytic/physical theorem chain.

This guard checks the declared bridge from concrete Hilbert realization through
physical/Yang--Mills Hamiltonian, spectral/PVM realization, continuum spectral
theorem surfaces, normalization, and the infinite-dimensional Yang--Mills target
obligation layer.

It is a syntactic/contract audit: Lean's kernel remains `lake build`. This
script ensures the named bridge files expose the expected import edges, ready
surfaces, value-carrier anchors, positivity anchors, physical target
obligations, and public-boundary anchors.
"""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
import re
import sys

SKIP_DIRS = {".git", ".lake"}
STRING_RE = re.compile(r'"(?:[^"\\]|\\.)*"')
FORBIDDEN_TOKENS_RE = re.compile(r"\b(sorry|admit|axiom|constant)\b")


@dataclass(frozen=True)
class BridgeFileSpec:
    path: str
    required_imports: tuple[str, ...]
    required_anchors: tuple[str, ...]
    required_ready: tuple[str, ...]
    required_boundary: tuple[str, ...] = ()


BRIDGE_FILES: tuple[BridgeFileSpec, ...] = (
    BridgeFileSpec(
        path="MGAP4D/MathlibAnalytic/ConcreteHilbertRealizationTheorem.lean",
        required_imports=("import MGAP4D.MathlibAnalytic.ExactGapPostTheoremBodyConcreteResidualMap",),
        required_anchors=(
            "ConcreteHilbertRealizationTheoremData",
            "distinguished_nonzero_norm",
            "distinguished_attains_exact",
            "all_states_lower_bound",
            "exact_value_eq_3320",
            "exact_value_positive",
        ),
        required_ready=(
            "ConcreteHilbertRealizationTheoremData.ready",
            "concrete_hilbert_realization_theorem_review_surface_ready",
        ),
        required_boundary=("infiniteDimensionalPhysicalHilbertStillOpen", "publicBoundaryHeld"),
    ),
    BridgeFileSpec(
        path="MGAP4D/MathlibAnalytic/ConcreteHPhysRealizationTheorem.lean",
        required_imports=("import MGAP4D.MathlibAnalytic.ConcreteHilbertRealizationTheorem",),
        required_anchors=(
            "ConcreteHPhysRealizationTheoremData",
            "hilbertDataReady",
            "hphysDataReady",
            "domain_closed_under_H",
            "symmetric_on_domain",
            "mapped_rayleigh_lower_bound",
            "distinguished_attains_exact",
            "exact_value_eq_3320",
        ),
        required_ready=(
            "ConcreteHPhysRealizationTheoremData.ready",
            "concrete_hphys_realization_theorem_review_surface_ready",
        ),
        required_boundary=("fullUnboundedPhysicalOperatorStillOpen", "publicBoundaryHeld"),
    ),
    BridgeFileSpec(
        path="MGAP4D/MathlibAnalytic/PhysicalUnboundedOperatorSkeleton.lean",
        required_imports=("import MGAP4D.MathlibAnalytic.HilbertSpaceInstanceSkeleton",),
        required_anchors=(
            "PhysicalUnboundedOperatorSkeletonData",
            "hilbertInstanceReady",
            "domain_preserved",
            "symmetric_on_domain",
            "selfAdjointCertificate",
            "rayleigh_lower_bound",
            "distinguished_attains_exact",
        ),
        required_ready=(
            "PhysicalUnboundedOperatorSkeletonData.ready",
            "physical_unbounded_operator_skeleton_review_surface_ready",
        ),
        required_boundary=("concreteYangMillsHamiltonianStillOpen", "publicBoundaryHeld"),
    ),
    BridgeFileSpec(
        path="MGAP4D/MathlibAnalytic/ConcreteYangMillsHamiltonianSkeleton.lean",
        required_imports=("import MGAP4D.MathlibAnalytic.PhysicalUnboundedOperatorSkeleton",),
        required_anchors=(
            "ConcreteYangMillsHamiltonianSkeletonData",
            "physicalOperatorReady",
            "ymWitness",
            "coupling_positive",
            "normalization_positive",
            "hphysBuiltFromYM",
            "plaquetteCentered",
            "normalizationBridge",
            "rayleigh_lower_bound",
            "distinguished_attains_exact",
            "exact_value_eq_3320",
        ),
        required_ready=(
            "ConcreteYangMillsHamiltonianSkeletonData.ready",
            "concrete_ym_hamiltonian_skeleton_review_surface_ready",
        ),
        required_boundary=("continuumLimitStillOpen", "spectralRealizationStillOpen", "publicBoundaryHeld"),
    ),
    BridgeFileSpec(
        path="MGAP4D/MathlibAnalytic/SpectralRealizationSkeleton.lean",
        required_imports=("import MGAP4D.MathlibAnalytic.ConcreteYangMillsHamiltonianSkeleton",),
        required_anchors=(
            "SpectralRealizationSkeletonData",
            "concreteYMReady",
            "spectralProjection",
            "spectralMass",
            "exactAtomPresent",
            "observableAtomWitness",
            "positiveMassAtExact",
            "rayleighExactWitness",
            "exact_value_eq_3320",
        ),
        required_ready=(
            "SpectralRealizationSkeletonData.ready",
            "spectral_realization_skeleton_review_surface_ready",
        ),
        required_boundary=("continuumSpectralTheoremStillOpen", "publicBoundaryHeld"),
    ),
    BridgeFileSpec(
        path="MGAP4D/MathlibAnalytic/ContinuumSpectralTheoremSkeleton.lean",
        required_imports=("import MGAP4D.MathlibAnalytic.SpectralRealizationSkeleton",),
        required_anchors=(
            "ContinuumSpectralTheoremSkeletonData",
            "spectralReady",
            "continuumLimit",
            "continuumSpectralProjection",
            "continuumSpectralMass",
            "continuumSpectralTheoremCertificate",
            "exactAtomPreserved",
            "positiveMassPreserved",
            "observableWitnessPreserved",
            "exact_value_eq_3320",
        ),
        required_ready=(
            "ContinuumSpectralTheoremSkeletonData.ready",
            "continuum_spectral_theorem_skeleton_review_surface_ready",
        ),
        required_boundary=("finalTheoremReleaseStillHeld", "publicBoundaryHeld"),
    ),
    BridgeFileSpec(
        path="MGAP4D/MathlibAnalytic/PhysicalHamiltonianNormalizationBridge.lean",
        required_imports=("import MGAP4D.MathlibAnalytic.ConcreteResidualClosure",),
        required_anchors=(
            "PhysicalHamiltonianNormalizationBridgeData",
            "referenceEnergyScale",
            "physicalGap",
            "normalizedGap",
            "scale_positive",
            "normalized_gap_def",
            "physical_gap_reconstruction",
            "internal_reference_scale_eq_one",
            "normalized_gap_eq_exact",
            "physical_gap_eq_exact_in_internal_units",
        ),
        required_ready=(
            "PhysicalHamiltonianNormalizationBridgeData.ready",
            "physical_hamiltonian_normalization_bridge_review_surface_ready",
        ),
        required_boundary=("theoremBodyUnchanged", "publicBoundaryHeld"),
    ),
    BridgeFileSpec(
        path="MGAP4D/MathlibAnalytic/InfiniteDimensionalYangMillsRealizationTargets.lean",
        required_imports=("import MGAP4D.MathlibAnalytic.PhysicalHamiltonianNormalizationBridge",),
        required_anchors=(
            "InfiniteDimensionalYangMillsRealizationTarget",
            "infinite_dimensional_witness",
            "separable_hilbert_witness",
            "dense_core_witness",
            "domain_density_witness",
            "hphys_self_adjoint_witness",
            "gauge_invariance_witness",
            "yang_mills_energy_witness",
            "continuum_limit_witness",
            "spectral_theorem_witness",
            "plaquette_nonzero_weight_witness",
            "vacuum_orthogonal_nonempty_witness",
            "normalized_gap_eq_exact",
            "exact_value_eq_3320",
        ),
        required_ready=(
            "InfiniteDimensionalYangMillsRealizationTarget.ready",
            "infinite_dimensional_yang_mills_target_review_surface_ready",
        ),
        required_boundary=("publicBoundaryHeld", "finalReleaseHeld"),
    ),
)

ORDERED_IMPORT_EDGES: tuple[tuple[str, str], ...] = (
    (
        "MGAP4D/MathlibAnalytic/ConcreteHPhysRealizationTheorem.lean",
        "import MGAP4D.MathlibAnalytic.ConcreteHilbertRealizationTheorem",
    ),
    (
        "MGAP4D/MathlibAnalytic/ConcreteYangMillsHamiltonianSkeleton.lean",
        "import MGAP4D.MathlibAnalytic.PhysicalUnboundedOperatorSkeleton",
    ),
    (
        "MGAP4D/MathlibAnalytic/SpectralRealizationSkeleton.lean",
        "import MGAP4D.MathlibAnalytic.ConcreteYangMillsHamiltonianSkeleton",
    ),
    (
        "MGAP4D/MathlibAnalytic/ContinuumSpectralTheoremSkeleton.lean",
        "import MGAP4D.MathlibAnalytic.SpectralRealizationSkeleton",
    ),
    (
        "MGAP4D/MathlibAnalytic/InfiniteDimensionalYangMillsRealizationTargets.lean",
        "import MGAP4D.MathlibAnalytic.PhysicalHamiltonianNormalizationBridge",
    ),
)

TOP_LEVEL_ANCHORS: tuple[tuple[str, tuple[str, ...]], ...] = (
    (
        "MGAP4D.lean",
        (
            "import MGAP4D.MathlibAnalytic.ExactValueTheoremBodyOrigin",
        ),
    ),
    (
        "MGAP4D/MathlibAnalytic.lean",
        (
            "import MGAP4D.MathlibAnalytic.PhysicalHamiltonianNormalizationBridge",
            "import MGAP4D.MathlibAnalytic.ConcreteResidualClosure",
            "import MGAP4D.MathlibAnalytic.InfiniteDimensionalYangMillsRealizationTargets",
        ),
    ),
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


def cleaned_source(text: str) -> str:
    return STRING_RE.sub('""', strip_lean_comments(text))


def iter_lean_files(root: Path):
    for path in root.rglob("*.lean"):
        if any(part in SKIP_DIRS for part in path.parts):
            continue
        yield path


def audit_forbidden_tokens(root: Path) -> list[str]:
    hits: list[str] = []
    for path in iter_lean_files(root):
        source = cleaned_source(path.read_text(encoding="utf-8"))
        for lineno, line in enumerate(source.splitlines(), start=1):
            if FORBIDDEN_TOKENS_RE.search(line):
                hits.append(f"{path}:{lineno}: forbidden token in bridge coherence audit")
    return hits


def require_anchors(root: Path, path: str, anchors: tuple[str, ...], label: str) -> list[str]:
    failures: list[str] = []
    full_path = root / path
    if not full_path.exists():
        return [f"missing {label} file: {path}"]
    source = cleaned_source(full_path.read_text(encoding="utf-8"))
    for anchor in anchors:
        if anchor not in source:
            failures.append(f"missing {label} anchor {anchor!r} in {path}")
    return failures


def audit_bridge_files(root: Path) -> list[str]:
    failures: list[str] = []
    for spec in BRIDGE_FILES:
        failures.extend(require_anchors(root, spec.path, spec.required_imports, "import"))
        failures.extend(require_anchors(root, spec.path, spec.required_anchors, "bridge"))
        failures.extend(require_anchors(root, spec.path, spec.required_ready, "ready"))
        failures.extend(require_anchors(root, spec.path, spec.required_boundary, "boundary"))
    return failures


def audit_ordered_import_edges(root: Path) -> list[str]:
    failures: list[str] = []
    for path, import_line in ORDERED_IMPORT_EDGES:
        failures.extend(require_anchors(root, path, (import_line,), "ordered import edge"))
    return failures


def audit_top_level_anchors(root: Path) -> list[str]:
    failures: list[str] = []
    for path, anchors in TOP_LEVEL_ANCHORS:
        failures.extend(require_anchors(root, path, anchors, "top-level"))
    return failures


def main() -> None:
    root = Path(".")
    failures: list[str] = []
    failures.extend(audit_forbidden_tokens(root))
    failures.extend(audit_bridge_files(root))
    failures.extend(audit_ordered_import_edges(root))
    failures.extend(audit_top_level_anchors(root))

    print(f"Bridge files audited: {len(BRIDGE_FILES)}")
    print(f"Ordered import edges audited: {len(ORDERED_IMPORT_EDGES)}")
    print("Forbidden Lean tokens audited: sorry/admit/axiom/constant")
    print("Bridge anchors audited: Hilbert, H_phys, Yang-Mills, spectral/PVM, continuum, normalization, infinite-dimensional target")
    print("Value anchors audited: exact value route / exactGapValueReal carrier")
    print("Boundary anchors audited: publicBoundaryHeld, finalReleaseHeld, and open-boundary markers")

    if failures:
        print("Bridge coherence audit failed:", file=sys.stderr)
        for failure in failures:
            print(f"  {failure}", file=sys.stderr)
        raise SystemExit(1)

    print("Bridge coherence audit passed")


if __name__ == "__main__":
    main()
