#!/usr/bin/env python3
"""Static audit for the OS/Wightman -> Hamiltonian/PVM mass-gap bridge.

The goal of this audit is narrow and textual: keep the conditional axiom-to-
Hamiltonian route from regressing into terminal True/receipt placeholders, and
make sure the root aggregator and documentation expose the final external-audit
bridge file.
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
    "root_import": ROOT / "MGAP4D/MathlibAnalytic.lean",
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
        "import MGAP4D.MathlibAnalytic.OSWightmanMassGapDefinitionBridge",
        "def ExternalAuditReadinessOSWightmanMassGapDefinitionBridgeProjection",
        "theorem external_audit_readiness_os_wightman_mass_gap_definition_bridge_projection",
        "theorem external_audit_readiness_os_wightman_definition_bridge_exact_gap_positive",
        "theorem external_audit_readiness_os_wightman_definition_bridge_exact_gap_threshold",
        "theorem external_audit_readiness_os_wightman_definition_bridge_pvm_detects_first_excitation",
    ],
    "root_import": [
        "import MGAP4D.MathlibAnalytic.OSWightmanMassGapExternalAuditBridge",
    ],
    "docs": [
        "OSWightmanMassGapExternalAuditBridge.lean",
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


def main() -> int:
    failures: list[str] = []
    contents = {name: read(path) for name, path in FILES.items()}

    for name, anchors in ANCHORS.items():
        text = contents[name]
        rel = FILES[name].relative_to(ROOT)
        for anchor in anchors:
            if anchor not in text:
                failures.append(f"{rel} missing OS/Wightman bridge anchor: {anchor!r}")

    external_text = contents["external_bridge"]
    external_rel = FILES["external_bridge"].relative_to(ROOT)
    for forbidden in LEAN_FORBIDDEN_IN_BRIDGE + LEAN_PLACEHOLDER_DECLS:
        if forbidden in external_text:
            failures.append(f"{external_rel} contains forbidden placeholder snippet: {forbidden!r}")

    definition_text = contents["definition_bridge"]
    definition_rel = FILES["definition_bridge"].relative_to(ROOT)
    for forbidden in ["receipt : True", "terminalReceipt", "readyReceipt"]:
        if forbidden in definition_text:
            failures.append(f"{definition_rel} contains forbidden bridge placeholder snippet: {forbidden!r}")

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
    print("Root import audited: MGAP4D/MathlibAnalytic.lean")
    print("Documentation audited: docs/axiomatic_yang_mills_mass_gap_closure.md")
    print("Forbidden placeholder snippets audited: True/receipt/sorry/admit/axiom/constant")
    print("OS/Wightman mass-gap bridge audit passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
