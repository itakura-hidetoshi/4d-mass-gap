#!/usr/bin/env python3
"""Progress-compatible static audit for the OS/Wightman mass-gap route.

The audit verifies theorem-route anchors, replay entry points, placeholder
exclusion, and the presence of public status categories.  It deliberately does
not freeze status values such as ``open``, ``not proved``, or ``not claimed``:
those values must be allowed to advance when later Lean developments discharge
the corresponding obligations.
"""

from __future__ import annotations

from pathlib import Path
import re
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
    "full_local_workflow": ROOT / ".github/workflows/full-local-check.yml",
}

ANCHORS = {
    "readme": [
        "## Current status",
        "Concrete finite Wilson heat-bath lane",
        "Conditional propagation lane",
        "Normalized exact-gap audit lane",
        "Nontrivial physical continuum construction",
        "Physical derivation of `33/20`",
        "External mathematical consensus",
        "## Replay",
        "bash scripts/check.sh",
    ],
    "roadmap": [
        "## Status snapshot",
        "Gibbs-pairing symmetry of the single-link heat-bath projection",
        "OS/Wightman reconstruction",
        "Immediate milestone 1",
        "repair the gap normalization",
        "physical Hamiltonian and quadratic-form identification",
    ],
    "current_status": [
        "# Current proof status",
        "Nontrivial continuum Yang--Mills measure",
        "Physical mass gap",
        "Independent physical derivation of `33/20`",
        "External consensus",
        "Lean theorem bodies are authoritative.",
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
        "structure EuclideanYangMillsMeasurePackage where",
        "structure EuclideanYangMillsMeasureToOSWightmanBridge where",
        "structure EuclideanYangMillsMeasureMassGapPipeline where",
        "theorem euclidean_yang_mills_measure_pipeline_positive_hamiltonian_spectrum",
        "theorem euclidean_yang_mills_measure_os_reconstruction_wightman_hamiltonian_mass_gap",
    ],
    "unconditional_target": [
        "structure EuclideanYangMillsMeasureUnconditionalConstructionTarget where",
        "continuumFourDimensionalYangMillsMeasureConstructed_proof",
        "nontrivialCompactGaugeGroupConstructed_proof",
        "interactingContinuumLimitConstructed_proof",
        "gaugeInvariantSchwingerFunctionsConstructed_proof",
        "theorem euclidean_yang_mills_unconditional_measure_construction_mass_gap",
    ],
    "construction_spine": [
        "structure EuclideanYangMillsFiniteVolumeApproximation where",
        "structure EuclideanYangMillsContinuumMeasureConstructionSpine where",
        "projectiveConsistency_proof",
        "tightness_proof",
        "weakLimitExists_proof",
        "continuumMeasureIdentified_proof",
        "schwingerFunctionsAreContinuumLimits_proof",
        "def EuclideanYangMillsContinuumMeasureConstructionSpine.toUnconditionalTarget",
        "def EuclideanYangMillsContinuumMeasureConstructionSpine.toPipeline",
        "theorem euclidean_yang_mills_finite_volume_continuum_construction_mass_gap",
    ],
    "construction_external_bridge": [
        "import MGAP4D.MathlibAnalytic.OSWightmanMassGapExternalAuditBridge",
        "import MGAP4D.MathlibAnalytic.EuclideanYangMillsMeasureConstructionSpine",
        "def ExternalAuditReadinessEuclideanYangMillsConstructionSpineProjection",
        "theorem external_audit_readiness_euclidean_yang_mills_construction_spine_projection",
        "theorem external_audit_readiness_euclidean_construction_spine_exact_gap_positive",
        "theorem external_audit_readiness_euclidean_construction_spine_exact_gap_threshold",
        "theorem external_audit_readiness_euclidean_construction_spine_pvm_detects_first_excitation",
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
    "full_local_workflow": [
        "name: Full Local Check CI",
        "bash scripts/check.sh",
    ],
}

LEAN_FILES = [
    "measure_pipeline",
    "unconditional_target",
    "construction_spine",
    "construction_external_bridge",
    "external_bridge",
    "definition_bridge",
]

FORBIDDEN_PATTERNS = [
    ("sorry", re.compile(r"\bsorry\b")),
    ("admit", re.compile(r"\badmit\b")),
    ("axiom declaration", re.compile(r"(?m)^\s*axiom\s+")),
    ("constant declaration", re.compile(r"(?m)^\s*constant\s+")),
    ("receipt : True", re.compile(r"receipt\s*:\s*True")),
    ("readyReceipt", re.compile(r"\breadyReceipt\b")),
    ("terminalReceipt", re.compile(r"\bterminalReceipt\b")),
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
    elif after not in text:
        failures.append(f"{rel} missing order anchor after-side for {label}: {after!r}")
    elif text.index(after) < text.index(before):
        failures.append(f"{rel} has invalid order for {label}: {after!r} precedes {before!r}")


def main() -> int:
    failures: list[str] = []
    contents = {name: read(path) for name, path in FILES.items()}

    for name, anchors in ANCHORS.items():
        text = contents[name]
        rel = FILES[name].relative_to(ROOT)
        for anchor in anchors:
            if anchor not in text:
                failures.append(f"{rel} missing OS/Wightman route anchor: {anchor!r}")

    for name in LEAN_FILES:
        text = contents[name]
        rel = FILES[name].relative_to(ROOT)
        for label, pattern in FORBIDDEN_PATTERNS:
            if pattern.search(text):
                failures.append(f"{rel} contains forbidden placeholder pattern: {label}")

    root_text = contents["root_import"]
    root_rel = FILES["root_import"].relative_to(ROOT)
    root_chain = [
        "import MGAP4D.MathlibAnalytic.ExternalAuditReadinessGate",
        "import MGAP4D.MathlibAnalytic.OSWightmanMassGapExternalAuditBridge",
        "import MGAP4D.MathlibAnalytic.EuclideanYangMillsMeasureToMassGapPipeline",
        "import MGAP4D.MathlibAnalytic.EuclideanYangMillsMeasureUnconditionalTarget",
        "import MGAP4D.MathlibAnalytic.EuclideanYangMillsMeasureConstructionSpine",
        "import MGAP4D.MathlibAnalytic.EuclideanYangMillsMeasureConstructionExternalAuditBridge",
    ]
    for before, after in zip(root_chain, root_chain[1:]):
        require_order(
            failures,
            text=root_text,
            rel=root_rel,
            before=before,
            after=after,
            label="root OS/Wightman--Euclidean route",
        )

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

    if failures:
        print("OS/Wightman mass-gap bridge audit failed:")
        for failure in failures:
            print(f"  {failure}")
        return 1

    print("OS/Wightman mass-gap bridge audit")
    for name in sorted(ANCHORS):
        print(f"{name} anchors audited: {len(ANCHORS[name])}")
    print("Public status categories audited without freezing their current values")
    print("Lean route, replay entry points, import order, and placeholder exclusions audited")
    print("OS/Wightman mass-gap bridge audit passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
