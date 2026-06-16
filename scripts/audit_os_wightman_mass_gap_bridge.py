#!/usr/bin/env python3
"""Audit the OS/Wightman--Euclidean mass-gap route and its public boundary.

The audit has two independent duties:

1. keep the theorem-facing Lean route structurally connected and free of
   placeholder declarations;
2. keep the public status documents explicit that the physical continuum
   construction, scale-uniform Wilson estimate, normalization bridge, and
   external mathematical validation remain open.

It is intentionally textual and complements, rather than replaces, Lean kernel
checking and independent mathematical review.
"""

from __future__ import annotations

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]

FILES = {
    "readme": ROOT / "README.md",
    "roadmap": ROOT / "ROADMAP.md",
    "current_status": ROOT / "docs/current_proof_status.md",
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
    "readme": [
        "## Current status — 2026-06-17",
        "It is not a completed public solution",
        "finite_lattice_singleLinkHeatBath_reversible_product_sum",
        "uniform non-Abelian estimate",
        "Physical derivation of `33/20` | Not established",
        "External mathematical consensus | Not claimed",
        "## Public claim boundary",
    ],
    "roadmap": [
        "## Status snapshot — 2026-06-17",
        "does **not** yet contain an unconditional construction",
        "Gibbs-pairing symmetry",
        "## Immediate milestone 1 — close the local Hilbert projection package",
        "## Immediate milestone 2 — repair the gap normalization",
        "No theorem requires a normalized Markov contraction coefficient bounded by one",
    ],
    "current_status": [
        "**Updated:** 2026-06-17",
        "finite_lattice_singleLinkHeatBath_reversible_product_sum",
        "Gibbs-pairing symmetry",
        "Physical mass gap | open",
        "External consensus | not claimed",
        "Lean theorem bodies are authoritative",
    ],
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

LEAN_FILES = [
    "axiomatic",
    "spine",
    "definition_bridge",
    "external_bridge",
    "measure_pipeline",
    "unconditional_target",
    "construction_spine",
    "construction_external_bridge",
]

FORBIDDEN_LEAN_SNIPPETS = [
    " : Prop :=\n  True",
    "sorry",
    "admit",
    "axiom ",
    "constant ",
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
    failures: list[str], *, text: str, rel: Path, before: str, after: str, label: str
) -> None:
    if before not in text:
        failures.append(f"{rel} missing order anchor before-side for {label}: {before!r}")
        return
    if after not in text:
        failures.append(f"{rel} missing order anchor after-side for {label}: {after!r}")
        return
    if text.index(after) < text.index(before):
        failures.append(f"{rel} has invalid order for {label}: {after!r} precedes {before!r}")


def audit_anchors(failures: list[str], contents: dict[str, str]) -> None:
    for name, anchors in ANCHORS.items():
        rel = FILES[name].relative_to(ROOT)
        text = contents[name]
        for anchor in anchors:
            if anchor not in text:
                failures.append(f"{rel} missing OS/Wightman route anchor: {anchor!r}")


def audit_forbidden(failures: list[str], contents: dict[str, str]) -> None:
    for name in LEAN_FILES:
        rel = FILES[name].relative_to(ROOT)
        text = contents[name]
        for forbidden in FORBIDDEN_LEAN_SNIPPETS:
            if forbidden in text:
                failures.append(f"{rel} contains forbidden placeholder snippet: {forbidden!r}")


def audit_order(failures: list[str], contents: dict[str, str]) -> None:
    root_text = contents["root_import"]
    root_rel = FILES["root_import"].relative_to(ROOT)
    ordered_imports = [
        "import MGAP4D.MathlibAnalytic.ExternalAuditReadinessGate",
        "import MGAP4D.MathlibAnalytic.OSWightmanMassGapExternalAuditBridge",
        "import MGAP4D.MathlibAnalytic.EuclideanYangMillsMeasureToMassGapPipeline",
        "import MGAP4D.MathlibAnalytic.EuclideanYangMillsMeasureUnconditionalTarget",
        "import MGAP4D.MathlibAnalytic.EuclideanYangMillsMeasureConstructionSpine",
        "import MGAP4D.MathlibAnalytic.EuclideanYangMillsMeasureConstructionExternalAuditBridge",
    ]
    for before, after in zip(ordered_imports, ordered_imports[1:]):
        require_order(
            failures,
            text=root_text,
            rel=root_rel,
            before=before,
            after=after,
            label="theorem-facing root route",
        )

    external_text = contents["external_bridge"]
    require_order(
        failures,
        text=external_text,
        rel=FILES["external_bridge"].relative_to(ROOT),
        before="import MGAP4D.MathlibAnalytic.ExternalAuditReadinessGate",
        after="import MGAP4D.MathlibAnalytic.OSWightmanMassGapDefinitionBridge",
        label="external readiness gate before definition bridge",
    )


def main() -> int:
    failures: list[str] = []
    contents = {name: read(path) for name, path in FILES.items()}

    audit_anchors(failures, contents)
    audit_forbidden(failures, contents)
    audit_order(failures, contents)

    if failures:
        print("OS/Wightman mass-gap route audit failed:")
        for failure in failures:
            print(f"  {failure}")
        return 1

    print("OS/Wightman mass-gap route audit")
    for name in sorted(ANCHORS):
        print(f"{name} anchors audited: {len(ANCHORS[name])}")
    print("Root theorem-facing import order audited")
    print("Public incomplete/conditional claim boundary audited")
    print("Forbidden Lean placeholder snippets audited")
    print("OS/Wightman mass-gap route audit passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
