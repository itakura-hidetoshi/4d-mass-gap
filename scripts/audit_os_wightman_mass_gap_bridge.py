#!/usr/bin/env python3
"""Static audit for the OS/Wightman -> Hamiltonian/PVM mass-gap bridge.

The goal of this audit is narrow and textual: keep the conditional axiom-to-
Hamiltonian route from regressing into terminal True/receipt placeholders, and
make sure the root aggregator, Euclidean-measure pipeline, unconditional
construction target, finite-volume construction spine, construction external
audit bridge, README, full replay script, workflow, documentation, theorem
index, full local check ledger, current proof status, external audit packet,
independent replay guide, and external review checklist expose the final theorem
surfaces.
"""

from __future__ import annotations

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]

FILES = {
    "readme": ROOT / "README.md",
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
    "full_local_workflow": ROOT / ".github/workflows/full-local-check.yml",
    "docs": ROOT / "docs/axiomatic_yang_mills_mass_gap_closure.md",
    "theorem_index": ROOT / "THEOREM_INDEX.md",
    "full_local_check_doc": ROOT / "docs/full_local_check_ci.md",
    "current_status_doc": ROOT / "docs/current_proof_status.md",
    "external_audit_packet": ROOT / "EXTERNAL_AUDIT_PACKET.md",
    "independent_replay": ROOT / "INDEPENDENT_REPLAY.md",
    "review_checklist": ROOT / "EXTERNAL_REVIEW_CHECKLIST.md",
}

COMMON_EUCLIDEAN_REPLAY_ANCHORS = [
    "[check] audit OS/Wightman mass-gap bridge",
    "[check] build OS/Wightman mass-gap external audit bridge",
    "[check] build Euclidean Yang-Mills measure to mass-gap pipeline",
    "[check] build unconditional Euclidean Yang-Mills measure target",
    "[check] build Euclidean Yang-Mills measure construction spine",
    "[check] build Euclidean Yang-Mills construction external audit bridge",
    "lake build MGAP4D.MathlibAnalytic.OSWightmanMassGapExternalAuditBridge",
    "lake build MGAP4D.MathlibAnalytic.EuclideanYangMillsMeasureToMassGapPipeline",
    "lake build MGAP4D.MathlibAnalytic.EuclideanYangMillsMeasureUnconditionalTarget",
    "lake build MGAP4D.MathlibAnalytic.EuclideanYangMillsMeasureConstructionSpine",
    "lake build MGAP4D.MathlibAnalytic.EuclideanYangMillsMeasureConstructionExternalAuditBridge",
]

COMMON_EUCLIDEAN_ROUTE_ANCHORS = [
    "EuclideanYangMillsFiniteVolumeApproximation",
    "EuclideanYangMillsContinuumMeasureConstructionSpine",
    "EuclideanYangMillsMeasureUnconditionalConstructionTarget",
    "EuclideanYangMillsMeasureMassGapPipeline",
    "OSWightmanMassGapDefinitionBridge",
    "ExternalAuditReadinessOSWightmanMassGapDefinitionBridgeProjection",
    "ExternalAuditReadinessEuclideanYangMillsConstructionSpineProjection",
]

COMMON_EUCLIDEAN_THEOREM_ANCHORS = [
    "euclidean_yang_mills_continuum_spine_limit_ready",
    "euclidean_yang_mills_continuum_spine_os_axioms_ready",
    "euclidean_yang_mills_continuum_spine_wightman_theory",
    "euclidean_yang_mills_continuum_spine_positive_hamiltonian_spectrum",
    "euclidean_yang_mills_continuum_spine_vacuum_isolated",
    "euclidean_yang_mills_continuum_spine_first_excitation_pvm_detected",
    "euclidean_yang_mills_continuum_spine_mass_gap_definition",
    "euclidean_yang_mills_finite_volume_continuum_construction_mass_gap",
    "external_audit_readiness_euclidean_yang_mills_construction_spine_projection",
    "external_audit_readiness_euclidean_construction_spine_exact_gap_positive",
    "external_audit_readiness_euclidean_construction_spine_exact_gap_threshold",
    "external_audit_readiness_euclidean_construction_spine_pvm_detects_first_excitation",
]

ANCHORS = {
    "readme": [
        "Current status as of 2026-06-12",
        "OS/Wightman external audit bridge",
        "Euclidean measure unconditional-construction target",
        "finite-volume / continuum construction spine",
        "Euclidean construction external audit bridge",
        "ExternalAuditReadinessEuclideanYangMillsConstructionSpineProjection",
        "externally accepted construction-spine external-audit projection",
        "construction-spine external-audit projection",
        "construction-spine external-audit projection equals external acceptance",
        "OS/Wightman--Euclidean theorem-facing route",
        *COMMON_EUCLIDEAN_ROUTE_ANCHORS,
        *COMMON_EUCLIDEAN_REPLAY_ANCHORS[:6],
        *COMMON_EUCLIDEAN_REPLAY_ANCHORS[6:],
        "EuclideanYangMillsMeasureConstructionExternalAuditBridge.lean",
        *COMMON_EUCLIDEAN_THEOREM_ANCHORS[-4:],
    ],
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
        "theorem euclidean_yang_mills_measure_pipeline_positive_hamiltonian_spectrum",
        "theorem euclidean_yang_mills_measure_pipeline_nonvacuum_spectrum_threshold",
        "theorem euclidean_yang_mills_measure_pipeline_delta_positive",
        "theorem euclidean_yang_mills_measure_os_reconstruction_wightman_hamiltonian_mass_gap",
        "structure EuclideanYangMillsMeasureToMassGapPipelineCertificate",
        "def euclideanYangMillsMeasureToMassGapPipelineCertificate",
    ],
    "unconditional_target": [
        "import MGAP4D.MathlibAnalytic.EuclideanYangMillsMeasureToMassGapPipeline",
        "structure EuclideanYangMillsMeasureUnconditionalConstructionTarget where",
        "continuumFourDimensionalYangMillsMeasureConstructed_proof",
        "nontrivialCompactGaugeGroupConstructed_proof",
        "interactingContinuumLimitConstructed_proof",
        "gaugeInvariantSchwingerFunctionsConstructed_proof",
        "theorem euclidean_yang_mills_unconditional_target_measure_ready",
        "theorem euclidean_yang_mills_unconditional_target_ready",
        "theorem euclidean_yang_mills_unconditional_target_bridge_measure_ready",
        "def EuclideanYangMillsMeasureUnconditionalConstructionTarget.toPipeline",
        "theorem euclidean_yang_mills_unconditional_target_delta_positive",
        "theorem euclidean_yang_mills_unconditional_target_nonvacuum_threshold",
        "theorem euclidean_yang_mills_unconditional_measure_construction_mass_gap",
        "structure EuclideanYangMillsMeasureUnconditionalConstructionCertificate",
        "def euclideanYangMillsMeasureUnconditionalConstructionCertificate",
    ],
    "construction_spine": [
        "import MGAP4D.MathlibAnalytic.EuclideanYangMillsMeasureUnconditionalTarget",
        "structure EuclideanYangMillsFiniteVolumeApproximation where",
        "finiteVolumeMeasure :",
        "@MeasureTheory.Measure",
        "structure EuclideanYangMillsContinuumMeasureConstructionSpine where",
        "projectiveConsistency_proof",
        "tightness_proof",
        "weakLimitExists_proof",
        "continuumMeasureIdentified_proof",
        "schwingerFunctionsAreContinuumLimits_proof",
        "def EuclideanYangMillsContinuumMeasureConstructionSpine.limitReady",
        "theorem euclidean_yang_mills_continuum_spine_limit_ready",
        "def EuclideanYangMillsContinuumMeasureConstructionSpine.toUnconditionalTarget",
        "theorem euclidean_yang_mills_continuum_spine_unconditional_target_ready",
        "def EuclideanYangMillsContinuumMeasureConstructionSpine.toPipeline",
        "theorem euclidean_yang_mills_continuum_spine_measure_ready",
        "theorem euclidean_yang_mills_continuum_spine_bridge_measure_ready",
        "theorem euclidean_yang_mills_continuum_spine_os_axioms_ready",
        "theorem euclidean_yang_mills_continuum_spine_wightman_theory",
        "theorem euclidean_yang_mills_continuum_spine_physical_hilbert_space",
        "theorem euclidean_yang_mills_continuum_spine_hamiltonian_time_translation_generator",
        "theorem euclidean_yang_mills_continuum_spine_vacuum_omega_spectral_point",
        "theorem euclidean_yang_mills_continuum_spine_positive_hamiltonian_spectrum",
        "theorem euclidean_yang_mills_continuum_spine_vacuum_isolated",
        "theorem euclidean_yang_mills_continuum_spine_first_excitation_pvm_detected",
        "theorem euclidean_yang_mills_continuum_spine_mass_gap_definition",
        "theorem euclidean_yang_mills_continuum_spine_delta_positive",
        "theorem euclidean_yang_mills_continuum_spine_nonvacuum_threshold",
        "theorem euclidean_yang_mills_finite_volume_continuum_construction_mass_gap",
        "structure EuclideanYangMillsContinuumMeasureConstructionCertificate",
        "def euclideanYangMillsContinuumMeasureConstructionCertificate",
    ],
    "construction_external_bridge": [
        "import MGAP4D.MathlibAnalytic.OSWightmanMassGapExternalAuditBridge",
        "import MGAP4D.MathlibAnalytic.EuclideanYangMillsMeasureConstructionSpine",
        "def ExternalAuditReadinessEuclideanYangMillsConstructionSpineProjection",
        "theorem external_audit_readiness_euclidean_yang_mills_construction_spine_projection",
        "theorem external_audit_readiness_euclidean_construction_spine_exact_gap_positive",
        "theorem external_audit_readiness_euclidean_construction_spine_exact_gap_threshold",
        "theorem external_audit_readiness_euclidean_construction_spine_pvm_detects_first_excitation",
        "structure ExternalAuditReadinessEuclideanYangMillsConstructionSpineCertificate",
        "def externalAuditReadinessEuclideanYangMillsConstructionSpineCertificate",
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
    "full_local_workflow": ["name: Full Local Check CI", "bash scripts/check.sh"],
    "docs": [
        "OSWightmanMassGapExternalAuditBridge.lean",
        "EuclideanYangMillsMeasureToMassGapPipeline.lean",
        "EuclideanYangMillsMeasureUnconditionalTarget.lean",
        "EuclideanYangMillsMeasureConstructionSpine.lean",
        "EuclideanYangMillsMeasureConstructionExternalAuditBridge.lean",
        "EuclideanYangMillsMeasurePackage",
        "EuclideanYangMillsMeasureMassGapPipeline",
        "EuclideanYangMillsMeasureUnconditionalConstructionTarget",
        "EuclideanYangMillsContinuumMeasureConstructionSpine",
        "ExternalAuditReadinessEuclideanYangMillsConstructionSpineProjection",
        "euclidean_yang_mills_measure_os_reconstruction_wightman_hamiltonian_mass_gap",
        "euclidean_yang_mills_unconditional_measure_construction_mass_gap",
        "euclidean_yang_mills_continuum_spine_positive_hamiltonian_spectrum",
        "euclidean_yang_mills_continuum_spine_vacuum_isolated",
        "euclidean_yang_mills_continuum_spine_first_excitation_pvm_detected",
        "external_audit_readiness_euclidean_yang_mills_construction_spine_projection",
        "external_audit_readiness_euclidean_construction_spine_exact_gap_positive",
        "euclidean_yang_mills_finite_volume_continuum_construction_mass_gap",
        "external_audit_readiness_os_wightman_mass_gap_definition_bridge_projection",
    ],
    "theorem_index": [
        "OS/Wightman--Euclidean construction audit route",
        *COMMON_EUCLIDEAN_ROUTE_ANCHORS,
        "MGAP4D/MathlibAnalytic/EuclideanYangMillsMeasureConstructionExternalAuditBridge.lean",
        "external audit bridge = review-routing projection, not community acceptance",
        "scripts/audit_os_wightman_mass_gap_bridge.py",
        "docs/axiomatic_yang_mills_mass_gap_closure.md",
        "EXTERNAL_REVIEW_CHECKLIST.md",
    ] + COMMON_EUCLIDEAN_THEOREM_ANCHORS[-4:],
    "full_local_check_doc": [
        "Full Local Check CI Ledger",
        *COMMON_EUCLIDEAN_REPLAY_ANCHORS[:6],
        "MGAP4D.MathlibAnalytic.EuclideanYangMillsMeasureConstructionExternalAuditBridge",
        "ExternalAuditReadinessGate",
        "OSWightmanMassGapExternalAuditBridge",
        "EuclideanYangMillsMeasureToMassGapPipeline",
        "EuclideanYangMillsMeasureUnconditionalTarget",
        "EuclideanYangMillsMeasureConstructionSpine",
        "EuclideanYangMillsMeasureConstructionExternalAuditBridge",
        "construction-spine external-audit projection builds",
        "that the construction-spine external-audit projection is itself external acceptance",
        "Euclidean construction external audit bridge build result",
    ],
    "current_status_doc": [
        "Current proof status anchor",
        "construction-spine external-audit projection: present",
        "external acceptance of the construction-spine external-audit projection: not claimed",
        "EuclideanYangMillsMeasureConstructionExternalAuditBridge.lean",
        *COMMON_EUCLIDEAN_ROUTE_ANCHORS,
        *COMMON_EUCLIDEAN_THEOREM_ANCHORS,
        "ExternalAuditReadinessEuclideanYangMillsConstructionSpineCertificate",
        "externalAuditReadinessEuclideanYangMillsConstructionSpineCertificate",
        "scripts/audit_os_wightman_mass_gap_bridge.py",
        "THEOREM_INDEX.md",
        "EXTERNAL_REVIEW_CHECKLIST.md",
        "docs/full_local_check_ci.md",
        "The construction external-audit bridge is a review-routing projection, not community acceptance.",
    ],
    "external_audit_packet": [
        "MGAP4D External Audit Packet",
        "construction-spine external-audit projection",
        "that the construction-spine external-audit projection is itself external acceptance",
        "OS/Wightman--Euclidean construction audit route",
        *COMMON_EUCLIDEAN_ROUTE_ANCHORS,
        *COMMON_EUCLIDEAN_REPLAY_ANCHORS[:6],
        *COMMON_EUCLIDEAN_REPLAY_ANCHORS[6:],
        *COMMON_EUCLIDEAN_THEOREM_ANCHORS[-4:],
        "scripts/audit_os_wightman_mass_gap_bridge.py",
        "construction-spine external-audit projection builds",
        "Euclidean construction external audit bridge build result",
    ],
    "independent_replay": [
        "Independent Replay Guide",
        "OS/Wightman--Euclidean construction route",
        "external acceptance of the construction-spine external-audit projection",
        *COMMON_EUCLIDEAN_ROUTE_ANCHORS,
        *COMMON_EUCLIDEAN_REPLAY_ANCHORS[:6],
        *COMMON_EUCLIDEAN_REPLAY_ANCHORS[6:],
        *COMMON_EUCLIDEAN_THEOREM_ANCHORS,
        "EuclideanYangMillsMeasureConstructionExternalAuditBridge",
    ],
    "review_checklist": [
        "Euclidean-measure unconditional-construction target",
        "proof-field socket",
        "finite-volume/continuum Euclidean-measure construction spine",
        "construction-spine external-audit projection",
        *COMMON_EUCLIDEAN_REPLAY_ANCHORS[:6],
        "Unconditional Euclidean Yang-Mills measure target build succeeds",
        "Euclidean Yang-Mills measure construction spine build succeeds",
        "Euclidean Yang-Mills construction external audit bridge build succeeds",
        *COMMON_EUCLIDEAN_REPLAY_ANCHORS[8:],
        "`EuclideanYangMillsMeasureConstructionExternalAuditBridge.lean` inspected as the construction-spine external-audit projection",
        "ExternalAuditReadinessEuclideanYangMillsConstructionSpineProjection",
        *COMMON_EUCLIDEAN_THEOREM_ANCHORS[-4:],
        "spectral projections from construction spine to positive energy, vacuum isolation, PVM detection, and mass-gap definition are present and audited",
        "construction-spine external-audit projection is present and audited",
        "Construction-spine external-audit projection interpretation recorded",
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
LEAN_FORBIDDEN_IN_MEASURE_PIPELINE = [" : Prop :=\n  True", "sorry", "admit", "axiom ", "constant ", "receipt : True", "readyReceipt", "terminalReceipt"]
LEAN_FORBIDDEN_IN_UNCONDITIONAL_TARGET = [" : Prop :=\n  True", "sorry", "admit", "axiom ", "constant ", "receipt : True", "readyReceipt", "terminalReceipt"]
LEAN_FORBIDDEN_IN_CONSTRUCTION_SPINE = [" : Prop :=\n  True", "sorry", "admit", "axiom ", "constant ", "receipt : True", "readyReceipt", "terminalReceipt"]
LEAN_FORBIDDEN_IN_CONSTRUCTION_EXTERNAL_BRIDGE = [" : Prop :=\n  True", "sorry", "admit", "axiom ", "constant ", "receipt : True", "readyReceipt", "terminalReceipt"]
LEAN_PLACEHOLDER_DECLS = ["Receipt", "receipt : True", "readyReceipt", "terminalReceipt"]


def read(path: Path) -> str:
    try:
        return path.read_text(encoding="utf-8")
    except FileNotFoundError:
        print(f"missing required file: {path.relative_to(ROOT)}", file=sys.stderr)
        raise


def require_order(failures: list[str], *, text: str, rel: Path, before: str, after: str, label: str) -> None:
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
    target_import = "import MGAP4D.MathlibAnalytic.EuclideanYangMillsMeasureUnconditionalTarget"
    construction_import = "import MGAP4D.MathlibAnalytic.EuclideanYangMillsMeasureConstructionSpine"
    construction_external_import = "import MGAP4D.MathlibAnalytic.EuclideanYangMillsMeasureConstructionExternalAuditBridge"
    require_order(failures, text=root_text, rel=root_rel, before=gate_import, after=bridge_import, label="root external audit gate before OS/Wightman bridge")
    require_order(failures, text=root_text, rel=root_rel, before=bridge_import, after=pipeline_import, label="root OS/Wightman bridge before Euclidean measure pipeline")
    require_order(failures, text=root_text, rel=root_rel, before=pipeline_import, after=target_import, label="root Euclidean measure pipeline before unconditional target")
    require_order(failures, text=root_text, rel=root_rel, before=target_import, after=construction_import, label="root unconditional target before construction spine")
    require_order(failures, text=root_text, rel=root_rel, before=construction_import, after=construction_external_import, label="root construction spine before construction external audit bridge")

    external_text = contents["external_bridge"]
    external_rel = FILES["external_bridge"].relative_to(ROOT)
    definition_bridge_import = "import MGAP4D.MathlibAnalytic.OSWightmanMassGapDefinitionBridge"
    require_order(failures, text=external_text, rel=external_rel, before=gate_import, after=definition_bridge_import, label="direct ExternalAuditReadinessGate import before definition bridge import")
    for forbidden in LEAN_FORBIDDEN_IN_BRIDGE + LEAN_PLACEHOLDER_DECLS:
        if forbidden in external_text:
            failures.append(f"{external_rel} contains forbidden placeholder snippet: {forbidden!r}")

    for name, forbidden_list in [
        ("measure_pipeline", LEAN_FORBIDDEN_IN_MEASURE_PIPELINE),
        ("unconditional_target", LEAN_FORBIDDEN_IN_UNCONDITIONAL_TARGET),
        ("construction_spine", LEAN_FORBIDDEN_IN_CONSTRUCTION_SPINE),
        ("construction_external_bridge", LEAN_FORBIDDEN_IN_CONSTRUCTION_EXTERNAL_BRIDGE),
    ]:
        text = contents[name]
        rel = FILES[name].relative_to(ROOT)
        for forbidden in forbidden_list:
            if forbidden in text:
                failures.append(f"{rel} contains forbidden placeholder snippet: {forbidden!r}")

    definition_text = contents["definition_bridge"]
    definition_rel = FILES["definition_bridge"].relative_to(ROOT)
    for forbidden in ["receipt : True", "terminalReceipt", "readyReceipt"]:
        if forbidden in definition_text:
            failures.append(f"{definition_rel} contains forbidden bridge placeholder snippet: {forbidden!r}")

    check_text = contents["check_sh"]
    check_rel = FILES["check_sh"].relative_to(ROOT)
    require_order(failures, text=check_text, rel=check_rel, before="audit OS/Wightman mass-gap bridge|python3 scripts/audit_os_wightman_mass_gap_bridge.py", after="replay summary|python3 scripts/replay_summary.py", label="OS/Wightman audit before replay summary")
    require_order(failures, text=check_text, rel=check_rel, before="MGAP4D.MathlibAnalytic.ExternalAuditReadinessGate", after="MGAP4D.MathlibAnalytic.OSWightmanMassGapExternalAuditBridge", label="full replay external audit gate build before OS/Wightman bridge build")
    require_order(failures, text=check_text, rel=check_rel, before="MGAP4D.MathlibAnalytic.OSWightmanMassGapExternalAuditBridge", after="MGAP4D.MathlibAnalytic.EuclideanYangMillsMeasureToMassGapPipeline", label="full replay OS/Wightman bridge build before Euclidean measure pipeline build")
    require_order(failures, text=check_text, rel=check_rel, before="MGAP4D.MathlibAnalytic.EuclideanYangMillsMeasureToMassGapPipeline", after="MGAP4D.MathlibAnalytic.EuclideanYangMillsMeasureUnconditionalTarget", label="full replay Euclidean measure pipeline build before unconditional target build")
    require_order(failures, text=check_text, rel=check_rel, before="MGAP4D.MathlibAnalytic.EuclideanYangMillsMeasureUnconditionalTarget", after="MGAP4D.MathlibAnalytic.EuclideanYangMillsMeasureConstructionSpine", label="full replay unconditional target before construction spine")
    require_order(failures, text=check_text, rel=check_rel, before="MGAP4D.MathlibAnalytic.EuclideanYangMillsMeasureConstructionSpine", after="MGAP4D.MathlibAnalytic.EuclideanYangMillsMeasureConstructionExternalAuditBridge", label="full replay construction spine before external audit bridge")

    if failures:
        print("OS/Wightman mass-gap bridge audit failed:")
        for failure in failures:
            print(f"  {failure}")
        return 1

    print("OS/Wightman mass-gap bridge audit")
    for name in [
        "readme", "axiomatic", "spine", "definition_bridge", "external_bridge",
        "measure_pipeline", "unconditional_target", "construction_spine",
        "construction_external_bridge", "theorem_index", "full_local_check_doc",
        "current_status_doc", "external_audit_packet", "independent_replay",
        "review_checklist",
    ]:
        print(f"{name} anchors audited: {len(ANCHORS[name])}")
    print("Root import order audited: ExternalAuditReadinessGate before OSWightmanMassGapExternalAuditBridge before EuclideanYangMillsMeasureToMassGapPipeline before EuclideanYangMillsMeasureUnconditionalTarget before EuclideanYangMillsMeasureConstructionSpine before EuclideanYangMillsMeasureConstructionExternalAuditBridge")
    print("Full replay script audited: audit + OS/Wightman build + Euclidean measure pipeline build + unconditional target build + finite-volume construction spine build + construction external audit bridge build connected through scripts/check.sh")
    print("README audited: README.md")
    print("External audit packet audited: EXTERNAL_AUDIT_PACKET.md")
    print("Independent replay guide audited: INDEPENDENT_REPLAY.md")
    print("Forbidden placeholder snippets audited: True/receipt/sorry/admit/axiom/constant")
    print("OS/Wightman mass-gap bridge audit passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
