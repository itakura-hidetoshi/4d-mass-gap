#!/usr/bin/env python3
"""Audit the hard physical residual ledger and terminal discharge index."""

from __future__ import annotations

from pathlib import Path
import sys

LEDGER_PATHS = (
    Path("docs/hard_physical_residual_ledger.md"),
    Path("docs/hard_physical_residual_ledger_terminal_discharge_index.md"),
)

ANCHOR_GROUPS: tuple[tuple[str, tuple[str, ...]], ...] = (
    ("ledger", (
        "Hard Physical Residual Ledger v0.1",
        "replay-visible audit surface",
        "fully concrete non-definitional analytic construction",
        "externalAuditReadinessPVMSpectralAtomPublicAuditProjection",
        "external_audit_readiness_pvm_spectral_atom_public_audit_projection",
        "external_audit_readiness_pvm_spectral_atom_value_eq_3320",
        "external_audit_readiness_pvm_spectral_atom_positive_nonzero_mass",
        "external_audit_readiness_pvm_spectral_atom_boundary_held",
    )),
    ("internal-discharge", (
        "Internal R1--R7 discharge spine v0.1",
        "MGAP4D/ConcreteR1R7ResidualDischarge.lean",
        "ConcreteR1R7ResidualDischarge",
        "concreteR1R7ResidualDischarge3320",
        "concrete_r1r7_residual_discharge_3320_ready",
        "concrete_r1r7_residual_discharge_exact_gap_value_3320",
        "concrete_r1r7_residual_discharge_positive_nonzero_spectral_mass",
        "concrete_r1r7_residual_discharge_final_release_held",
        "concrete_r1r7_residual_discharge_public_boundary_locked",
        "ConcreteR1R7ResidualDischarge: installed / internal discharge spine visible",
    )),
    ("ledger-bridge", (
        "MGAP4D/HardPhysicalResidualLedgerR1R7DischargeBridge.lean",
        "HardPhysicalResidualLedgerR1R7DischargeBridge",
        "hardPhysicalResidualLedgerR1R7DischargeBridge3320",
        "hard_physical_residual_ledger_r1r7_discharge_bridge_ready",
        "hard_physical_residual_ledger_r1r7_discharge_bridge_exact_gap_value_3320",
        "hard_physical_residual_ledger_r1r7_discharge_bridge_positive_nonzero_spectral_mass",
        "hard_physical_residual_ledger_r1r7_discharge_bridge_final_release_held",
        "hard_physical_residual_ledger_r1r7_discharge_bridge_public_boundary_locked",
        "hard_physical_residual_ledger_r1r7_discharge_bridge_status_preserved",
        "HardPhysicalResidualLedgerR1R7DischargeBridge: installed / ledger bridge visible",
    )),
    ("final-bundle", (
        "MGAP4D/HardPhysicalResidualLedgerFinalBundleAuditMap.lean",
        "HardPhysicalResidualLedgerFinalBundleAuditMap",
        "hardPhysicalResidualLedgerFinalBundleAuditMap3320",
        "hard_physical_residual_ledger_final_bundle_audit_map_3320_ready",
        "hard_physical_residual_ledger_final_bundle_audit_map_no_auto_release",
        "hard_physical_residual_ledger_final_bundle_audit_map_nonpromotion_boundary",
        "MGAP4D/HardPhysicalResidualLedgerFinalBundleStatusManifest.lean",
        "HardPhysicalResidualLedgerFinalBundleStatusManifest",
        "hardPhysicalResidualLedgerFinalBundleStatusManifest3320",
        "MGAP4D/HardPhysicalResidualLedgerFinalBundleStatusManifestChainIndex.lean",
        "HardPhysicalResidualLedgerFinalBundleStatusManifestChainIndex",
        "hardPhysicalResidualLedgerFinalBundleStatusManifestChainIndex3320",
        "hard_physical_residual_ledger_final_bundle_status_manifest_chain_index_r1_closure_ready",
        "hard_physical_residual_ledger_final_bundle_status_manifest_chain_index_r2_closure_ready",
    )),
    ("r1-r3-bridges", (
        "MGAP4D/HardPhysicalResidualLedgerR1ConcreteHilbertClosure.lean",
        "HardPhysicalResidualLedgerR1ConcreteHilbertClosure",
        "hard_physical_residual_ledger_r1_concrete_hilbert_closure_3320_ready",
        "hard_physical_residual_ledger_r1_concrete_hilbert_closure_mathlib_ready",
        "MGAP4D/HardPhysicalResidualLedgerR2DenseDomainOperatorClosure.lean",
        "HardPhysicalResidualLedgerR2DenseDomainOperatorClosure",
        "hard_physical_residual_ledger_r2_dense_domain_operator_closure_3320_ready",
        "hard_physical_residual_ledger_r2_dense_domain_operator_closure_unboundedness_ready",
        "MGAP4D/HardPhysicalResidualLedgerR3SelfAdjointInputBridge.lean",
        "HardPhysicalResidualLedgerR3SelfAdjointInputBridge",
        "hard_physical_residual_ledger_r3_self_adjoint_input_bridge_3320_ready",
        "R3 input bridge: installed and consumes closed R2 unbounded operator",
    )),
    ("terminal-discharge", (
        "Hard Physical Residual Ledger Terminal Discharge Chain Index v0.1",
        "MGAP4D/HardPhysicalResidualLedgerR1R7TerminalDischargeChainIndex.lean",
        "HardPhysicalResidualLedgerR1R7TerminalDischargeChainIndex",
        "hardPhysicalResidualLedgerR1R7TerminalDischargeChainIndex3320",
        "hard_physical_residual_ledger_r1_r7_terminal_discharge_chain_index_3320_ready",
        "hard_physical_residual_ledger_r1_r7_terminal_discharged",
        "hard_physical_residual_ledger_r1_r7_terminal_final_release_held",
        "hard_physical_residual_ledger_r1_r7_terminal_public_boundary_locked",
        "hard_physical_residual_ledger_r1_r7_terminal_exact_value_and_positive_weight",
        "R1--R7 terminal discharge chain index: installed / terminal discharge receipt visible",
        "Terminal exact 33/20 and positive spectral-weight projection: carried",
        "Terminal final-release boundary: held",
        "Terminal public boundary: locked",
    )),
    ("public-audit", (
        "MGAP4D/HardPhysicalResidualLedgerR1R7PublicAuditSurface.lean",
        "HardPhysicalResidualLedgerR1R7PublicAuditSurface",
        "hardPhysicalResidualLedgerR1R7PublicAuditSurface3320",
        "hard_physical_residual_ledger_r1_r7_public_audit_surface_3320_ready",
        "hard_physical_residual_ledger_public_surface_exact_3320_positive_weight",
        "hard_physical_residual_ledger_public_surface_r4_genuine_pvm_laws_visible",
        "hard_physical_residual_ledger_public_surface_boundary_locked",
        "MGAP4D/HardPhysicalResidualLedgerR1R7PublicAuditChainIndex.lean",
        "HardPhysicalResidualLedgerR1R7PublicAuditChainIndex",
        "hardPhysicalResidualLedgerR1R7PublicAuditChainIndex3320",
        "hard_physical_residual_ledger_r1_r7_public_audit_chain_index_3320_ready",
        "hard_physical_residual_ledger_public_audit_chain_exact_3320_positive_weight",
        "hard_physical_residual_ledger_public_audit_chain_r4_genuine_pvm_laws_visible",
        "hard_physical_residual_ledger_public_audit_chain_boundary_locked",
        "R1--R7 public audit surface: installed / public receipt visible",
        "R1--R7 public audit chain index: installed / indexed public receipt visible",
        "Public audit exact 33/20 and positive spectral-weight projection: carried",
        "Public audit R4 genuine-PVM law receipts: visible",
        "Public audit boundary: non-releasing and locked",
    )),
    ("residual-ids", (
        "R1. Concrete real Hilbert space on Mathlib",
        "R2. Densely defined unbounded operator",
        "R3. Self-adjointness proof",
        "R4. Concrete PVM / spectral measure construction",
        "R5. Compact centered plaquette observable",
        "R6. Non-definitional derivation of the exact atom 33/20",
        "R7. Nontrivial derivation of positive spectral weight",
    )),
    ("closure-language", (
        "Mathlib-recognized NormedAddCommGroup",
        "InnerProductSpace ℝ",
        "CompleteSpace",
        "dense subspace or dense set",
        "Mathlib LinearPMap",
        "unit probes have norm one",
        "arbitrary real thresholds",
        "domain equality with the adjoint",
        "Mathlib adjoint graph theorem",
        "concrete self-adjointness theorem",
        "projection-valued measure",
        "countable additivity",
        "compactly supported smeared centered plaquette observable",
        "33/20 is not introduced by defining exactGapValueReal to be 33/20",
        "ρ_{A_{p,g}}({33/20}) > 0",
        "nonzero overlap / nonzero spectral projection / cyclic vector / observable localization argument",
    )),
    ("terminal-status", (
        "R1: Mathlib-substrate discharged / terminal chain indexed",
        "R2: dense-domain unbounded operator discharged / terminal chain indexed",
        "R3: adjoint graph theorem and concrete self-adjointness discharged / terminal chain indexed",
        "R4: genuine PVM discharged / terminal chain indexed",
        "R5: compact centered plaquette observable discharged / terminal chain indexed",
        "R6: non-definitional exact atom discharged / terminal chain indexed",
        "R7: positive spectral weight discharged / terminal chain indexed",
    )),
)

FORBIDDEN_PHRASES = (
    "R1: closed",
    "R2: closed",
    "R3: closed",
    "R4: closed",
    "R5: closed",
    "R6: closed",
    "R7: closed",
    "R3: input bridge installed / Mathlib adjoint graph theorem pending",
    "R4: open / PVM-construction required",
    "R5: open / observable-construction required",
    "R6: open / non-definitional exact-value derivation required",
    "R7: open / nontrivial positive spectral-weight derivation required",
    "external mathematical consensus obtained",
    "fully concrete analytic construction completed",
)


def read_all() -> tuple[str, list[str]]:
    failures: list[str] = []
    chunks: list[str] = []
    for path in LEDGER_PATHS:
        if not path.exists():
            failures.append(f"missing hard physical residual ledger component: {path}")
        else:
            chunks.append(path.read_text(encoding="utf-8"))
    return "\n".join(chunks), failures


def main() -> None:
    text, failures = read_all()

    for label, anchors in ANCHOR_GROUPS:
        missing = [anchor for anchor in anchors if anchor not in text]
        failures.extend(f"missing {label} anchor {anchor!r}" for anchor in missing)

    forbidden = [phrase for phrase in FORBIDDEN_PHRASES if phrase in text]
    failures.extend(f"forbidden premature-closure phrase {phrase!r}" for phrase in forbidden)

    print("Hard physical residual ledger audit")
    for label, anchors in ANCHOR_GROUPS:
        print(f"{label} anchors audited: {len(anchors)}")
    print(f"Forbidden premature-closure phrases audited: {len(FORBIDDEN_PHRASES)}")

    if failures:
        print("Hard physical residual ledger audit failed:", file=sys.stderr)
        for failure in failures:
            print(f"  {failure}", file=sys.stderr)
        raise SystemExit(1)

    print("Hard physical residual ledger audit passed")


if __name__ == "__main__":
    main()
