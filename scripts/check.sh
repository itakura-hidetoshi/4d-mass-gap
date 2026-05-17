#!/usr/bin/env bash
set -euo pipefail

echo "[check] verify manifest"
python3 scripts/verify_manifest.py

echo "[check] audit Lean forbidden tokens"
python3 scripts/audit_lean_forbidden_tokens.py

echo "[check] audit major theorem non-placeholder surfaces"
python3 scripts/audit_major_theorem_nonplaceholder.py

echo "[check] audit analytic bridge coherence"
python3 scripts/audit_bridge_coherence.py

echo "[check] audit infinite-dimensional Yang-Mills target layer"
python3 scripts/audit_infinite_dimensional_target_layer.py

echo "[check] audit infinite-dimensional residual filling bridge"
python3 scripts/audit_infinite_dimensional_residual_filling.py

echo "[check] audit hard physical residual hardening map"
python3 scripts/audit_hard_physical_residual_hardening_map.py

echo "[check] audit complete infinite-dimensional Hilbert construction"
python3 scripts/audit_complete_infinite_dimensional_hilbert_construction.py

echo "[check] audit self-adjoint HPhys lane hardening"
python3 scripts/audit_self_adjoint_hphys_lane_hardening.py

echo "[check] audit continuum Yang-Mills lane hardening"
python3 scripts/audit_continuum_yang_mills_lane_hardening.py

echo "[check] audit plaquette spectral weight lane hardening"
python3 scripts/audit_plaquette_spectral_weight_lane_hardening.py

echo "[check] audit continuum Hamiltonian witness hardening"
python3 scripts/audit_continuum_hamiltonian_mass_gap_witness_hardening.py

echo "[check] audit four-lane residual closure"
python3 scripts/audit_four_lane_residual_closure.py

echo "[check] audit internal review residual closure gate"
python3 scripts/audit_internal_review_residual_closure_gate.py

echo "[check] audit external audit readiness gate"
python3 scripts/audit_external_audit_readiness_gate.py

echo "[check] audit external audit readiness gate field classification"
python3 scripts/audit_external_audit_readiness_gate_field_classification.py

echo "[check] audit external audit readiness replay certificate"
python3 scripts/audit_external_audit_readiness_replay_certificate.py

echo "[check] replay summary"
python3 scripts/replay_summary.py

echo "[check] lake update"
lake update

echo "[check] build continuum Hamiltonian exact mass-gap derivation"
lake build MGAP4D.MathlibAnalytic.ContinuumHamiltonianExactMassGapDerivation

echo "[check] build continuum Hamiltonian release-chain addendum"
lake build MGAP4D.MathlibAnalytic.FinalTheoremReleaseChainIndexContinuumHamiltonianAddendum

echo "[check] build external audit readiness gate"
lake build MGAP4D.MathlibAnalytic.ExternalAuditReadinessGate

echo "[check] lake build"
lake build
