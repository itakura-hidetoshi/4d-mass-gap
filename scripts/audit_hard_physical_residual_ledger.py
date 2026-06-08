#!/usr/bin/env python3
"""Audit the hard physical residual ledger.

This audit keeps the repository honest about the difference between a
CI-enforced replay-visible theorem/audit surface and a fully concrete,
non-definitional analytic construction of the 4D Yang--Mills mass-gap route.
"""

from __future__ import annotations

from pathlib import Path
import sys

LEDGER_PATH = Path("docs/hard_physical_residual_ledger.md")

REQUIRED_LEDGER_ANCHORS = (
    "Hard Physical Residual Ledger v0.1",
    "replay-visible audit surface",
    "fully concrete non-definitional analytic construction",
    "externalAuditReadinessPVMSpectralAtomPublicAuditProjection",
    "external_audit_readiness_pvm_spectral_atom_public_audit_projection",
    "external_audit_readiness_pvm_spectral_atom_value_eq_3320",
    "external_audit_readiness_pvm_spectral_atom_positive_nonzero_mass",
    "external_audit_readiness_pvm_spectral_atom_boundary_held",
)

REQUIRED_INTERNAL_DISCHARGE_ANCHORS = (
    "Internal R1--R7 discharge spine v0.1",
    "MGAP4D/ConcreteR1R7ResidualDischarge.lean",
    "ConcreteR1R7ResidualDischarge",
    "concreteR1R7ResidualDischarge3320",
    "concrete_r1r7_residual_discharge_3320_ready",
    "concrete_r1r7_residual_discharge_exact_gap_value_3320",
    "concrete_r1r7_residual_discharge_positive_nonzero_spectral_mass",
    "concrete_r1r7_residual_discharge_final_release_held",
    "concrete_r1r7_residual_discharge_public_boundary_locked",
    "internal discharge spine binding present",
    "ConcreteR1R7ResidualDischarge: installed / internal discharge spine visible",
    "Hard residual ledger statuses: preserved for stronger future Mathlib/operator-theoretic replacement",
)

REQUIRED_LEDGER_BRIDGE_ANCHORS = (
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
)

REQUIRED_RESIDUAL_IDS = (
    "R1. Concrete real Hilbert space on Mathlib",
    "R2. Densely defined unbounded operator",
    "R3. Self-adjointness proof",
    "R4. Concrete PVM / spectral measure construction",
    "R5. Compact centered plaquette observable",
    "R6. Non-definitional derivation of the exact atom 33/20",
    "R7. Nontrivial derivation of positive spectral weight",
)

REQUIRED_CLOSURE_PHRASES = (
    "Mathlib-recognized NormedAddCommGroup",
    "InnerProductSpace ℝ",
    "CompleteSpace",
    "dense subspace or dense set",
    "domain equality with the adjoint",
    "projection-valued measure",
    "countable additivity",
    "compactly supported smeared centered plaquette observable",
    "33/20 is not introduced by defining exactGapValueReal to be 33/20",
    "ρ_{A_{p,g}}({33/20}) > 0",
    "nonzero overlap / nonzero spectral projection / cyclic vector / observable localization argument",
)

REQUIRED_SPINE_ANCHORS = (
    "ConcreteRealHilbertSpace",
    "DenseDomainUnboundedHamiltonian",
    "SelfAdjointPhysicalHamiltonian",
    "ConcretePVMSpectralMeasure",
    "CompactCenteredPlaquetteObservable",
    "NondefinitionalSpectralAtom3320",
    "PositiveSpectralWeightDerivation3320",
)

REQUIRED_STATUS_ANCHORS = (
    "R1: open / construction-hardening required",
    "R2: open / domain-hardening required",
    "R3: open / self-adjointness-hardening required",
    "R4: open / PVM-construction required",
    "R5: open / observable-construction required",
    "R6: open / non-definitional exact-value derivation required",
    "R7: open / nontrivial positive spectral-weight derivation required",
)

FORBIDDEN_COLLAPSE_PHRASES = (
    "R1: closed",
    "R2: closed",
    "R3: closed",
    "R4: closed",
    "R5: closed",
    "R6: closed",
    "R7: closed",
    "external mathematical consensus obtained",
    "fully concrete analytic construction completed",
)


def require_all(text: str, anchors: tuple[str, ...], label: str) -> list[str]:
    return [f"missing {label} anchor {anchor!r} in {LEDGER_PATH}" for anchor in anchors if anchor not in text]


def forbid_all(text: str, anchors: tuple[str, ...], label: str) -> list[str]:
    return [f"forbidden {label} phrase {anchor!r} in {LEDGER_PATH}" for anchor in anchors if anchor in text]


def main() -> None:
    failures: list[str] = []
    if not LEDGER_PATH.exists():
        failures.append(f"missing hard physical residual ledger: {LEDGER_PATH}")
        text = ""
    else:
        text = LEDGER_PATH.read_text(encoding="utf-8")

    failures.extend(require_all(text, REQUIRED_LEDGER_ANCHORS, "ledger"))
    failures.extend(require_all(text, REQUIRED_INTERNAL_DISCHARGE_ANCHORS, "internal-discharge"))
    failures.extend(require_all(text, REQUIRED_LEDGER_BRIDGE_ANCHORS, "ledger-bridge"))
    failures.extend(require_all(text, REQUIRED_RESIDUAL_IDS, "residual-id"))
    failures.extend(require_all(text, REQUIRED_CLOSURE_PHRASES, "closure-condition"))
    failures.extend(require_all(text, REQUIRED_SPINE_ANCHORS, "future-spine"))
    failures.extend(require_all(text, REQUIRED_STATUS_ANCHORS, "status"))
    failures.extend(forbid_all(text, FORBIDDEN_COLLAPSE_PHRASES, "premature-closure"))

    print("Hard physical residual ledger audit")
    print(f"Ledger anchors audited: {len(REQUIRED_LEDGER_ANCHORS)}")
    print(f"Internal discharge anchors audited: {len(REQUIRED_INTERNAL_DISCHARGE_ANCHORS)}")
    print(f"Ledger bridge anchors audited: {len(REQUIRED_LEDGER_BRIDGE_ANCHORS)}")
    print(f"Residual ids audited: {len(REQUIRED_RESIDUAL_IDS)}")
    print(f"Closure-condition anchors audited: {len(REQUIRED_CLOSURE_PHRASES)}")
    print(f"Future-spine anchors audited: {len(REQUIRED_SPINE_ANCHORS)}")
    print(f"Status anchors audited: {len(REQUIRED_STATUS_ANCHORS)}")
    print(f"Forbidden premature-closure phrases audited: {len(FORBIDDEN_COLLAPSE_PHRASES)}")

    if failures:
        print("Hard physical residual ledger audit failed:", file=sys.stderr)
        for failure in failures:
            print(f"  {failure}", file=sys.stderr)
        raise SystemExit(1)

    print("Hard physical residual ledger audit passed")


if __name__ == "__main__":
    main()
