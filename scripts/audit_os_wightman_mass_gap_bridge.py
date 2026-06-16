#!/usr/bin/env python3
"""Structural audit for the OS/Wightman--Euclidean proof route.

This audit must remain proof-progressive: it checks that the Lean construction
route stays connected and free of structural placeholders, but it does not
freeze any mathematical obligation in an "open" state and does not require a
particular public-status sentence.  When the physical continuum construction is
proved, the theorem surface may advance without weakening this audit.
"""

from __future__ import annotations

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]

FILES = {
    "axiomatic": ROOT / "MGAP4D/MathlibAnalytic/AxiomaticYangMillsMassGapClosure.lean",
    "spine": ROOT / "MGAP4D/MathlibAnalytic/OSWightmanHamiltonianReconstructionSpine.lean",
    "definition_bridge": ROOT / "MGAP4D/MathlibAnalytic/OSWightmanMassGapDefinitionBridge.lean",
    "external_bridge": ROOT / "MGAP4D/MathlibAnalytic/OSWightmanMassGapExternalAuditBridge.lean",
    "measure_pipeline": ROOT / "MGAP4D/MathlibAnalytic/EuclideanYangMillsMeasureToMassGapPipeline.lean",
    "unconditional_target": ROOT / "MGAP4D/MathlibAnalytic/EuclideanYangMillsMeasureUnconditionalTarget.lean",
    "construction_spine": ROOT / "MGAP4D/MathlibAnalytic/EuclideanYangMillsMeasureConstructionSpine.lean",
    "construction_external_bridge": ROOT / "MGAP4D/MathlibAnalytic/EuclideanYangMillsMeasureConstructionExternalAuditBridge.lean",
    "root_import": ROOT / "MGAP4D/MathlibAnalytic.lean",
    "check_sh": ROOT / "scripts/check.sh",
}

ANCHORS = {
    "axiomatic": [
        "structure OSWightmanYangMillsAxioms where",
        "structure FourDimensionalYangMillsAxiomaticModel where",
        "def FourDimensionalYangMillsAxiomaticModel.hasMassGap",
        "theorem wightman_os_hamiltonian_spectral_pvm_closes_4d_mass_gap",
    ],
    "spine": [
        "structure OSWightmanHamiltonianReconstructionSpine where",
        "theorem os_wightman_reconstruction_spine_has_mass_gap",
        "theorem os_wightman_reconstruction_spine_exact_gap_positive",
        "structure OSWightmanHamiltonianReconstructionSpineCertificate",
    ],
    "definition_bridge": [
        "structure OSWightmanMassGapDefinitionBridge where",
        "theorem os_wightman_bridge_positive_energy",
        "theorem os_wightman_bridge_vacuum_isolated",
        "theorem os_wightman_bridge_mass_gap_definition",
        "structure OSWightmanMassGapDefinitionBridgeCertificate",
    ],
    "external_bridge": [
        "import MGAP4D.MathlibAnalytic.ExternalAuditReadinessGate",
        "import MGAP4D.MathlibAnalytic.OSWightmanMassGapDefinitionBridge",
        "def ExternalAuditReadinessOSWightmanMassGapDefinitionBridgeProjection",
        "theorem external_audit_readiness_os_wightman_mass_gap_definition_bridge_projection",
    ],
    "measure_pipeline": [
        "structure EuclideanYangMillsMeasurePackage where",
        "structure EuclideanYangMillsMeasureToOSWightmanBridge where",
        "structure EuclideanYangMillsMeasureMassGapPipeline where",
        "theorem euclidean_yang_mills_measure_os_reconstruction_wightman_hamiltonian_mass_gap",
    ],
    "unconditional_target": [
        "structure EuclideanYangMillsMeasureUnconditionalConstructionTarget where",
        "continuumFourDimensionalYangMillsMeasureConstructed_proof",
        "theorem euclidean_yang_mills_unconditional_target_ready",
        "theorem euclidean_yang_mills_unconditional_measure_construction_mass_gap",
    ],
    "construction_spine": [
        "structure EuclideanYangMillsFiniteVolumeApproximation where",
        "structure EuclideanYangMillsContinuumMeasureConstructionSpine where",
        "projectiveConsistency_proof",
        "tightness_proof",
        "weakLimitExists_proof",
        "def EuclideanYangMillsContinuumMeasureConstructionSpine.toPipeline",
        "theorem euclidean_yang_mills_finite_volume_continuum_construction_mass_gap",
    ],
    "construction_external_bridge": [
        "import MGAP4D.MathlibAnalytic.OSWightmanMassGapExternalAuditBridge",
        "import MGAP4D.MathlibAnalytic.EuclideanYangMillsMeasureConstructionSpine",
        "def ExternalAuditReadinessEuclideanYangMillsConstructionSpineProjection",
        "theorem external_audit_readiness_euclidean_yang_mills_construction_spine_projection",
        "structure ExternalAuditReadinessEuclideanYangMillsConstructionSpineCertificate",
    ],
    "root_import": [
        "import MGAP4D.MathlibAnalytic.ExternalAuditReadinessGate",
        "import MGAP4D.MathlibAnalytic.OSWightmanMassGapExternalAuditBridge",
        "import MGAP4D.MathlibAnalytic.EuclideanYangMillsMeasureToMassGapPipeline",
        "import MGAP4D.MathlibAnalytic.EuclideanYangMillsMeasureUnconditionalTarget",
        "import MGAP4D.MathlibAnalytic.EuclideanYangMillsMeasureConstructionSpine",
        "import MGAP4D.MathlibAnalytic.EuclideanYangMillsMeasureConstructionExternalAuditBridge",
    ],
    "check_sh": [
        "audit OS/Wightman mass-gap bridge|python3 scripts/audit_os_wightman_mass_gap_bridge.py",
        "MGAP4D.MathlibAnalytic.OSWightmanMassGapExternalAuditBridge",
        "MGAP4D.MathlibAnalytic.EuclideanYangMillsMeasureToMassGapPipeline",
        "MGAP4D.MathlibAnalytic.EuclideanYangMillsMeasureUnconditionalTarget",
        "MGAP4D.MathlibAnalytic.EuclideanYangMillsMeasureConstructionSpine",
        "MGAP4D.MathlibAnalytic.EuclideanYangMillsMeasureConstructionExternalAuditBridge",
    ],
}

LEAN_FILES = [name for name in ANCHORS if name not in {"root_import", "check_sh"}]

# The repository-wide forbidden-token audit handles declarations such as axioms.
# Here we only reject route-specific structural placeholders, avoiding false
# positives from identifiers and explanatory comments.
FORBIDDEN_ROUTE_SNIPPETS = [
    " : Prop :=\n  True",
    "sorry",
    "admit",
    "receipt : True",
    "readyReceipt",
    "terminalReceipt",
]


def read(path: Path) -> str:
    try:
        return path.read_text(encoding="utf-8")
    except FileNotFoundError:
        print(f"missing required file: {path.relative_to(ROOT)}", file=sys.stderr)
        raise


def require_order(
    failures: list[str], *, text: str, rel: Path, before: str, after: str
) -> None:
    if before not in text or after not in text:
        return
    if text.index(after) < text.index(before):
        failures.append(f"{rel} has invalid route order: {after!r} precedes {before!r}")


def main() -> int:
    failures: list[str] = []
    contents = {name: read(path) for name, path in FILES.items()}

    for name, anchors in ANCHORS.items():
        rel = FILES[name].relative_to(ROOT)
        for anchor in anchors:
            if anchor not in contents[name]:
                failures.append(f"{rel} missing proof-route anchor: {anchor!r}")

    for name in LEAN_FILES:
        rel = FILES[name].relative_to(ROOT)
        for forbidden in FORBIDDEN_ROUTE_SNIPPETS:
            if forbidden in contents[name]:
                failures.append(f"{rel} contains structural placeholder: {forbidden!r}")

    ordered_imports = ANCHORS["root_import"]
    root_text = contents["root_import"]
    root_rel = FILES["root_import"].relative_to(ROOT)
    for before, after in zip(ordered_imports, ordered_imports[1:]):
        require_order(failures, text=root_text, rel=root_rel, before=before, after=after)

    require_order(
        failures,
        text=contents["external_bridge"],
        rel=FILES["external_bridge"].relative_to(ROOT),
        before="import MGAP4D.MathlibAnalytic.ExternalAuditReadinessGate",
        after="import MGAP4D.MathlibAnalytic.OSWightmanMassGapDefinitionBridge",
    )

    if failures:
        print("OS/Wightman mass-gap proof-route audit failed:")
        for failure in failures:
            print(f"  {failure}")
        return 1

    print("OS/Wightman mass-gap proof-route audit passed")
    print("Theorem declarations, import order, and structural placeholders audited")
    print("No unresolved physical obligation is frozen by this audit")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
