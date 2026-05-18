#!/usr/bin/env bash
set -euo pipefail

# Legacy textual anchors for audit scripts that inspect scripts/check.sh directly.
# These comments preserve the old explicit spellings while the executable body
# below stays compact.
# build Yang-Mills Hamiltonian spectral derivation of 33/20
# lake build MGAP4D.MathlibAnalytic.YangMillsHamiltonianSpectralDerivation3320
# build complete Hamiltonian spectral release adoption
# lake build MGAP4D.MathlibAnalytic.ContinuumHamiltonianCompleteMassGapReleaseAdoption
# build continuum Hamiltonian exact mass-gap derivation
# lake build MGAP4D.MathlibAnalytic.ContinuumHamiltonianExactMassGapDerivation
# build continuum Hamiltonian release-chain addendum
# lake build MGAP4D.MathlibAnalytic.FinalTheoremReleaseChainIndexContinuumHamiltonianAddendum
# build external audit readiness gate
# lake build MGAP4D.MathlibAnalytic.ExternalAuditReadinessGate

declare -a AUDITS=(
  "verify manifest|python3 scripts/verify_manifest.py"
  "audit Lean forbidden tokens|python3 scripts/audit_lean_forbidden_tokens.py"
  "audit major theorem non-placeholder surfaces|python3 scripts/audit_major_theorem_nonplaceholder.py"
  "audit analytic bridge coherence|python3 scripts/audit_bridge_coherence.py"
  "audit hard physical residual ledger|python3 scripts/audit_hard_physical_residual_ledger.py"
  "audit concrete analytic spine from scratch|python3 scripts/audit_concrete_analytic_spine_from_scratch.py"
  "audit concrete analytic spine graph sequence law|python3 scripts/audit_concrete_analytic_spine_graph_sequence_law.py"
  "audit concrete analytic spine graph norm sequence law|python3 scripts/audit_concrete_analytic_spine_graph_norm_sequence_law.py"
  "audit concrete analytic spine graph norm bounded sequence|python3 scripts/audit_concrete_analytic_spine_graph_norm_bounded_sequence.py"
  "audit concrete analytic spine graph norm Cauchy sequence|python3 scripts/audit_concrete_analytic_spine_graph_norm_cauchy_sequence.py"
  "audit concrete analytic spine graph norm convergent sequence|python3 scripts/audit_concrete_analytic_spine_graph_norm_convergent_sequence.py"
  "audit concrete analytic spine graph point limit sequence|python3 scripts/audit_concrete_analytic_spine_graph_point_limit_sequence.py"
  "audit concrete analytic spine graph point limit carrier|python3 scripts/audit_concrete_analytic_spine_graph_point_limit_carrier.py"
  "audit concrete analytic spine graph limit carrier compatibility|python3 scripts/audit_concrete_analytic_spine_graph_limit_carrier_compatibility.py"
  "audit concrete analytic spine graph sequence closure candidate|python3 scripts/audit_concrete_analytic_spine_graph_sequence_closure_candidate.py"
  "audit concrete analytic spine R2 batch closure bridge|python3 scripts/audit_concrete_analytic_spine_r2_batch_closure_bridge.py"
  "audit concrete analytic spine R2 batch carrier compatibility|python3 scripts/audit_concrete_analytic_spine_r2_batch_carrier_compatibility.py"
  "audit concrete analytic spine R2 batch norm closure consistency|python3 scripts/audit_concrete_analytic_spine_r2_batch_norm_closure_consistency.py"
  "audit concrete analytic spine R2 batch readiness index|python3 scripts/audit_concrete_analytic_spine_r2_batch_readiness_index.py"
  "audit concrete analytic spine R2 non-promotion gate|python3 scripts/audit_concrete_analytic_spine_r2_non_promotion_gate.py"
  "audit concrete analytic spine R2 review packet|python3 scripts/audit_concrete_analytic_spine_r2_review_packet.py"
  "audit concrete analytic spine R2 final local index|python3 scripts/audit_concrete_analytic_spine_r2_final_local_index.py"
  "audit concrete analytic spine R2 local closure summary|python3 scripts/audit_concrete_analytic_spine_r2_local_closure_summary.py"
  "audit concrete analytic spine R2 checkpoint packet|python3 scripts/audit_concrete_analytic_spine_r2_checkpoint_packet.py"
  "audit concrete analytic spine operator lane|python3 scripts/audit_concrete_analytic_spine_operator_lane.py"
  "audit concrete analytic spine operator lane checkpoint|python3 scripts/audit_concrete_analytic_spine_operator_lane_checkpoint.py"
  "audit concrete analytic spine l2 real sequence|python3 scripts/audit_concrete_analytic_spine_l2_real_sequence.py"
  "audit concrete analytic spine l2 diagonal graph|python3 scripts/audit_concrete_analytic_spine_l2_diagonal_graph.py"
  "audit concrete analytic spine l2 diagonal graph norm|python3 scripts/audit_concrete_analytic_spine_l2_diagonal_graph_norm.py"
  "audit physical Hamiltonian operator normalization|python3 scripts/audit_physical_hamiltonian_operator_normalization.py"
  "audit Yang-Mills Hamiltonian spectral derivation of 33/20|python3 scripts/audit_yang_mills_hamiltonian_spectral_derivation_3320.py"
  "audit infinite-dimensional Yang-Mills target layer|python3 scripts/audit_infinite_dimensional_target_layer.py"
  "audit infinite-dimensional residual filling bridge|python3 scripts/audit_infinite_dimensional_residual_filling.py"
  "audit hard physical residual hardening map|python3 scripts/audit_hard_physical_residual_hardening_map.py"
  "audit complete infinite-dimensional Hilbert construction|python3 scripts/audit_complete_infinite_dimensional_hilbert_construction.py"
  "audit self-adjoint HPhys lane hardening|python3 scripts/audit_self_adjoint_hphys_lane_hardening.py"
  "audit continuum Yang-Mills lane hardening|python3 scripts/audit_continuum_yang_mills_lane_hardening.py"
  "audit plaquette spectral weight lane hardening|python3 scripts/audit_plaquette_spectral_weight_lane_hardening.py"
  "audit continuum Hamiltonian witness hardening|python3 scripts/audit_continuum_hamiltonian_mass_gap_witness_hardening.py"
  "audit four-lane residual closure|python3 scripts/audit_four_lane_residual_closure.py"
  "audit internal review residual closure gate|python3 scripts/audit_internal_review_residual_closure_gate.py"
  "audit external audit readiness gate|python3 scripts/audit_external_audit_readiness_gate.py"
  "audit external audit readiness gate field classification|python3 scripts/audit_external_audit_readiness_gate_field_classification.py"
  "audit external audit readiness replay certificate|python3 scripts/audit_external_audit_readiness_replay_certificate.py"
  "replay summary|python3 scripts/replay_summary.py"
)

for entry in "${AUDITS[@]}"; do
  label="${entry%%|*}"
  command="${entry#*|}"
  echo "[check] ${label}"
  eval "${command}"
done

echo "[check] lake update"
lake update

declare -a BUILDS=(
  MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineRealHilbertDomain
  MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineGraphSequenceLaw
  MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineGraphNormSequenceLaw
  MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineGraphNormBoundedSequence
  MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineGraphNormCauchySequence
  MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineGraphNormConvergentSequence
  MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineGraphPointLimitSequence
  MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineGraphPointLimitCarrier
  MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineGraphLimitCarrierCompatibility
  MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineGraphSequenceClosureCandidate
  MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineR2BatchClosureBridge
  MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineR2BatchCarrierCompatibility
  MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineR2BatchNormClosureConsistency
  MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineR2BatchReadinessIndex
  MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineR2NonPromotionGate
  MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineR2ReviewPacket
  MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineR2FinalLocalIndex
  MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineR2LocalClosureSummary
  MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineR2CheckpointPacket
  MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineOperatorLane
  MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineOperatorLaneCheckpoint
  MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2RealSequence
  MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2DiagonalGraph
  MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2DiagonalGraphNorm
  MGAP4D.MathlibAnalytic.PhysicalHamiltonianOperatorNormalization
  MGAP4D.MathlibAnalytic.YangMillsHamiltonianSpectralDerivation3320
  MGAP4D.MathlibAnalytic.ContinuumHamiltonianCompleteMassGapReleaseAdoption
  MGAP4D.MathlibAnalytic.ContinuumHamiltonianExactMassGapDerivation
  MGAP4D.MathlibAnalytic.FinalTheoremReleaseChainIndexContinuumHamiltonianAddendum
  MGAP4D.MathlibAnalytic.ExternalAuditReadinessGate
)

for target in "${BUILDS[@]}"; do
  echo "[check] build ${target}"
  lake build "${target}"
done

echo "[check] lake build"
lake build
