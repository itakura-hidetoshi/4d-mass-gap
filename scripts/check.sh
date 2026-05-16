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

echo "[check] audit Hilbert construction lane hardening"
python3 scripts/audit_hilbert_construction_lane_hardening.py

echo "[check] audit self-adjoint HPhys lane hardening"
python3 scripts/audit_self_adjoint_hphys_lane_hardening.py

echo "[check] audit continuum Yang-Mills lane hardening"
python3 scripts/audit_continuum_yang_mills_lane_hardening.py

echo "[check] audit plaquette spectral weight lane hardening"
python3 scripts/audit_plaquette_spectral_weight_lane_hardening.py

echo "[check] audit four-lane residual closure"
python3 scripts/audit_four_lane_residual_closure.py

echo "[check] audit internal review residual closure gate"
python3 scripts/audit_internal_review_residual_closure_gate.py

echo "[check] audit external audit readiness gate"
python3 scripts/audit_external_audit_readiness_gate.py

echo "[check] replay summary"
python3 scripts/replay_summary.py

echo "[check] lake update"
lake update

echo "[check] lean external audit readiness gate"
lake env lean MGAP4D/MathlibAnalytic/ExternalAuditReadinessGate.lean

echo "[check] lake build"
lake build
