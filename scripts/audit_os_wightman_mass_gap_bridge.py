#!/usr/bin/env python3
"""Static audit for the OS/Wightman -> Hamiltonian/PVM mass-gap bridge.

The goal of this audit is narrow and textual: keep the conditional axiom-to-
Hamiltonian route from regressing into terminal True/receipt placeholders, and
make sure the root aggregator, Euclidean-measure pipeline, full replay script,
workflow, and documentation expose the final theorem surfaces.
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
    "root_import": ROOT / "MGAP4D/MathlibAnalytic.lean",
    "check_sh": ROOT / "scripts/check.sh",
    "full_local_workflow": ROOT / ".github/workflows/full-local-check.yml",
    "docs": ROOT / "docs/axiomatic_yang_mills_mass_gap_closure.md",
}

ANCHORS = {
    "axiomatic": [
        "structure OSWightmanYangMillsAxioms where",
        "structure FourDimensionalYangMillsAxiomaticModel where",
        "def FourDimensionalYangMillsAxiomaticModel.hasMassGap",
        "theorem wightman_os_hamiltonian_spectral_pvm_closes_4d_mass_gap",
        "theorem axiomatic_yang_mills_mass_gap_value_eq_sInf_nonvacuum",
    ],
    "spine": [
        "structure OSWightmanHamiltonianReconstructionSpine where",
        "theorem os_wightman_reconstruction_spine_has_mass_gap",
        "theorem os_wightman_reconstruction_spine_exact_gap_positive",
        "theorem os_wightman_reconstruction_spine_exact_gap_is_sInf_nonvacuum",
        "structure OSWightmanHamiltonianReconstructionSpineCertificate",
    ],
    "definition_bridge": [
        "structure OSWightmanMassGapDefinitionBridge where",
        "theorem os_wightman_bridge_positive_energy",
        "theorem os_wightman_bridge_vacuum_isolated",
        "theorem os_wightman_bridge_first_excitation_has_pvm_support",
        "theorem os_wightman_bridge_mass_gap_definition",
        "theorem os_wightman_bridge_exact_gap_positive",
        "theorem os_wightman_bridge_exact_gap_spectral_threshold",
        "structure OSWightmanMassGapDefinitionBridgeCertificate",
        "def osWightmanMassGapDefinitionBridgeCertificate",
    ],
    "external_bridge": [
        "import MGAP4D.MathlibAnalytic.ExternalAuditReadinessGate",
        "import MGAP4D.MathlibAnalytic.OSWightmanMassGapDefinitionBridge",
        "def ExternalAuditReadinessOSWightmanMassGapDefinitionBridgeProjection",
        "theorem external_audit_readiness_os_wightman_mass_gap_definition_bridge_projection",
        "theorem external_audit_readiness_os_wightman_definition_bridge_exact_gap_positive",
        "theorem external_audit_readiness_os_wightman_definition_bridge_exact_gap_threshold",
        "theorem external_audit_readiness_os_wightman_definition_bridge_pvm_detects_first_excitation",
    ],
    "measure_pipeline": [
        "import MGAP4D.MathlibAnalytic.OSWightmanMassGapDefinitionBridge",
        "structure EuclideanYangMillsMeasurePackage where",
        "euclideanMeasure : MeasureTheory.Measure configurationSpace",
        "structure EuclideanYangMillsMeasureToOSWightmanBridge where",
        "theorem euclidean_yang_mills_measure_to_os_wightman_ready",
        "structure EuclideanYangMillsMeasureMassGapPipeline where",
        "def EuclideanYangMillsMeasureMassGapPipeline.nonVacuumHamiltonianSpectrum",
        "def EuclideanYangMillsMeasureMassGapPipeline.vacuumOmega",
        "theorem euclidean_yang_mills_measure_pipeline_os_axioms_ready",
        "theorem euclidean_yang_mills_measure_pipeline_wightman_theory",
        "theorem euclidean_yang_mills_measure_pipeline_hamiltonian_time_translation_generator",
        "theorem euclidean_yang_mills_measure_pipeline_vacuum_omega_spectral_point",
        "theorem euclidean_yang_mills_measure_pipeline_nonvacuum_spectrum_threshold",
        "theorem euclidean_yang_mills_measure_pipeline_delta_positive",
        "theorem euclidean_yang_mills_measure_os_reconstruction_wightman_hamiltonian_mass_gap",
        "structure EuclideanYangMillsMeasureToMassGapPipelineCertificate",
        "def euclideanYangMillsMeasureToMassGapPipelineCertificate",
    ],
    "root_import": [
        "import MGAP4D.MathlibAnalytic.ExternalAuditReadinessGate",
        "import MGAP4D.MathlibAnalytic.OSWightmanMassGapExternalAuditBridge",
        "import MGAP4D.MathlibAnalytic.EuclideanYangMillsMeasureToMassGapPipeline",
    ],
    "check_sh": [
        "audit OS/Wightman mass-gap bridge|python3 scripts/audit_os_wightman_mass_gap_bridge.py",
        "MGAP4D.MathlibAnalytic.OSWightmanMassGapExternalAuditBridge",
        "MGAP4D.MathlibAnalytic.EuclideanYangMillsMeasureToMassGapPipeline",
    ],
    "full_local_workflow": [
        "name: Full Local Check CI",
        "bash scripts/check.sh",
    ],
    "docs": [
        "OSWightmanMassGapExternalAuditBridge.lean",
        "EuclideanYangMillsMeasureToMassGapPipeline.lean",
        "EuclideanYangMillsMeasurePackage",
        "EuclideanYangMillsMeasureMassGapPipeline",
        "euclidean_yang_mills_measure_os_reconstruction_wightman_hamiltonian_mass_gap",
        "external_audit_readiness_os_wightman_mass_gap_definition_bridge_projection",
        "external_audit_readiness_os_wightman_definition_bridge_exact_gap_positive",
        "external_audit_readiness_os_wightman_definition_bridge_exact_gap_threshold",
        "external_audit_readiness_os_wightman_definition_bridge_pvm_detects_first_excitation",
    ],
}

LEAN_FORBIDDEN_IN_BRIDGE = [
    "def ExternalAuditReadinessOSWightmanMassGapDefinitionBridgeProjection\n    (B : OSWightmanMassGapDefinitionBridge) : Prop :=\n  True",
    "theorem external_audit_readiness_os_wightman_mass_gap_definition_bridge_projection\n    (B : OSWightmanMassGapDefinitionBridge) :\n    True",
    "sorry",
    "admit",
    "axiom ",
    "constant ",
]

LEAN_FORBIDDEN_IN_MEASURE_PIPELINE = [
    " : Prop :=\n  True",
    "sorry",
    "admit",
    "axiom ",
    "constant ",
    "receipt : True",
    "readyReceipt",
    "terminalReceipt",
]

# Receipt language is allowed in explanatory prose comments, but not as a named
# Lean carrier for this bridge.  These strings catch accidental reintroduction of
# terminal placeholder declarations.
LEAN_PLACEHOLDER_DECLS = [
    "Receipt",
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
    failures: list[str],
    *,
    text: str,
    rel: Path,
    before: str,
    after: str,
    label: str,
) -> None:
    if before not in text:
        failures.append(f"{rel} missing order anchor before-side for {label}: {before!r}")
        return
    if after not in text:
        failures.append(f"{rel} missing order anchor after-side for {label}: {after!r}")
        return
    if text.index(after) < text.index(before):
        failures.append(f"{rel} has invalid order for {label}: {after!r} precedes {before!r}")


def main() -> int:
    failures: list[str] = []
    contents = {name: read(path) for name, path in FILES.items()}

    for name, anchors in ANCHORS.items():
        text = contents[name]
        rel = FILES[name].relative_to(ROOT)
        for anchor in anchors:
            if anchor not in text:
                failures.append(f"{rel} missing OS/Wightman bridge anchor: {anchor!r}")

    root_text = contents["root_import"]
    root_rel = FILES["root_import"].relative_to(ROOT)
    gate_import = "import MGAP4D.MathlibAnalytic.ExternalAuditReadinessGate"
    bridge_import = "import MGAP4D.MathlibAnalytic.OSWightmanMassGapExternalAuditBridge"
    pipeline_import = "import MGAP4D.MathlibAnalytic.EuclideanYangMillsMeasureToMassGapPipeline"
    require_order(
        failures,
        text=root_text,
        rel=root_rel,
        before=gate_import,
        after=bridge_import,
        label="root external audit gate before OS/Wightman bridge",
    )
    require_order(
        failures,
        text=root_text,
        rel=root_rel,
        before=bridge_import,
        after=pipeline_import,
        label="root OS/Wightman bridge before Euclidean measure pipeline",
    )

    external_text = contents["external_bridge"]
    external_rel = FILES["external_bridge"].relative_to(ROOT)
    definition_bridge_import = "import MGAP4D.MathlibAnalytic.OSWightmanMassGapDefinitionBridge"
    require_order(
        failures,
        text=external_text,
        rel=external_rel,
        before=gate_import,
        after=definition_bridge_import,
        label="direct ExternalAuditReadinessGate import before definition bridge import",
    )
    for forbidden in LEAN_FORBIDDEN_IN_BRIDGE + LEAN_PLACEHOLDER_DECLS:
        if forbidden in external_text:
            failures.append(f"{external_rel} contains forbidden placeholder snippet: {forbidden!r}")

    measure_text = contents["measure_pipeline"]
    measure_rel = FILES["measure_pipeline"].relative_to(ROOT)
    for forbidden in LEAN_FORBIDDEN_IN_MEASURE_PIPELINE:
        if forbidden in measure_text:
            failures.append(f"{measure_rel} contains forbidden placeholder snippet: {forbidden!r}")

    definition_text = contents["definition_bridge"]
    definition_rel = FILES["definition_bridge"].relative_to(ROOT)
    for forbidden in ["receipt : True", "terminalReceipt", "readyReceipt"]:
        if forbidden in definition_text:
            failures.append(f"{definition_rel} contains forbidden bridge placeholder snippet: {forbidden!r}")

    check_text = contents["check_sh"]
    check_rel = FILES["check_sh"].relative_to(ROOT)
    require_order(
        failures,
        text=check_text,
        rel=check_rel,
        before="audit OS/Wightman mass-gap bridge|python3 scripts/audit_os_wightman_mass_gap_bridge.py",
        after="replay summary|python3 scripts/replay_summary.py",
        label="OS/Wightman audit before replay summary",
    )
    require_order(
        failures,
        text=check_text,
        rel=check_rel,
        before="MGAP4D.MathlibAnalytic.ExternalAuditReadinessGate",
        after="MGAP4D.MathlibAnalytic.OSWightmanMassGapExternalAuditBridge",
        label="full replay external audit gate build before OS/Wightman bridge build",
    )
    require_order(
        failures,
        text=check_text,
        rel=check_rel,
        before="MGAP4D.MathlibAnalytic.OSWightmanMassGapExternalAuditBridge",
        after="MGAP4D.MathlibAnalytic.EuclideanYangMillsMeasureToMassGapPipeline",
        label="full replay OS/Wightman bridge build before Euclidean measure pipeline build",
    )

    if failures:
        print("OS/Wightman mass-gap bridge audit failed:")
        for failure in failures:
            print(f"  {failure}")
        return 1

    print("OS/Wightman mass-gap bridge audit")
    print(f"Axiomatic anchors audited: {len(ANCHORS['axiomatic'])}")
    print(f"Reconstruction spine anchors audited: {len(ANCHORS['spine'])}")
    print(f"Definition bridge anchors audited: {len(ANCHORS['definition_bridge'])}")
    print(f"External bridge anchors audited: {len(ANCHORS['external_bridge'])}")
    print(f"Euclidean measure pipeline anchors audited: {len(ANCHORS['measure_pipeline'])}")
    print("Root import order audited: ExternalAuditReadinessGate before OSWightmanMassGapExternalAuditBridge before EuclideanYangMillsMeasureToMassGapPipeline")
    print("Direct bridge import order audited: ExternalAuditReadinessGate before OSWightmanMassGapDefinitionBridge")
    print("Full replay script audited: audit + OS/Wightman build + Euclidean measure pipeline build connected through scripts/check.sh")
    print("Full local workflow audited: .github/workflows/full-local-check.yml runs scripts/check.sh")
    print("Documentation audited: docs/axiomatic_yang_mills_mass_gap_closure.md")
    print("Forbidden placeholder snippets audited: True/receipt/sorry/admit/axiom/constant")
    print("OS/Wightman mass-gap bridge audit passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
