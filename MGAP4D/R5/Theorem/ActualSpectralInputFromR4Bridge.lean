import MGAP4D.R4.Theorem.SelfAdjointInputBridge
import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapSpectralMeasureInputHandoff
import MGAP4D.R5.Theorem.SpectrumMilestone
import MGAP4D.R5.TheoremSurface.ExportSurface

namespace MGAP4D
namespace R5
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- R5 actual spectral-input theorem packet.

R4 owns the exact lower-bound/operator-order layer.  The self-adjointness result
is treated as an R4 input bridge, not as R4 itself.  This R5 packet starts after
that bridge: it records that the spectral lane has an actual self-adjoint
`LinearPMap` input and a spectral-measure input handoff, while the full spectral
theorem/PVM construction remains downstream. -/
def ActualSpectralInputFromR4BridgePacket : Prop :=
  R4.Theorem.SelfAdjointInputBridgeReady ∧
  MathlibAnalytic.concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapSpectralMeasureInputHandoffReady ∧
  IsSelfAdjoint MathlibAnalytic.concreteL2R2DenseDiagonalDomainLinearPMap ∧
  LinearPMap.adjoint MathlibAnalytic.concreteL2R2DenseDiagonalDomainLinearPMap =
    MathlibAnalytic.concreteL2R2DenseDiagonalDomainLinearPMap ∧
  MathlibAnalytic.spectralRealizationSkeletonReviewSurface.ready ∧
  MathlibAnalytic.spectralRealizationSkeletonReviewSurface.exactAtomPresent ∧
  MathlibAnalytic.spectralRealizationSkeletonReviewSurface.observableAtomWitness ∧
  MathlibAnalytic.spectralRealizationSkeletonReviewSurface.positiveMassAtExact ∧
  MathlibAnalytic.exactGapValueReal = (33 : ℝ) / 20

/-- The R5 actual spectral-input theorem packet is ready. -/
theorem actual_spectral_input_from_r4_bridge_packet_ready :
    ActualSpectralInputFromR4BridgePacket := by
  exact ⟨
    R4.Theorem.self_adjoint_input_bridge_ready,
    MathlibAnalytic.concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_pmap_spectral_measure_input_handoff_ready,
    R4.Theorem.r4_self_adjoint_input_supplied,
    MathlibAnalytic.concrete_l2_r2_dense_diagonal_domain_linear_pmap_actual_adjoint_eq_self,
    MathlibAnalytic.spectral_realization_skeleton_review_surface_ready,
    MathlibAnalytic.spectralRealizationSkeletonReviewSurface.exactAtomPresent_proof,
    MathlibAnalytic.spectralRealizationSkeletonReviewSurface.observableAtomWitness_proof,
    MathlibAnalytic.spectralRealizationSkeletonReviewSurface.positiveMassAtExact_proof,
    MathlibAnalytic.exactGapValueReal_eq⟩

/-- R5 actual spectral-input boundary.

The actual self-adjoint input is available for R5.  The full spectral theorem,
concrete spectral measure, concrete PVM, and positive-weight construction remain
visible downstream obligations. -/
def ActualSpectralInputFromR4BridgeBoundary : Prop :=
  ActualSpectralInputFromR4BridgePacket ∧
  MathlibAnalytic.concreteL2R2DenseDiagonalDomainLinearPMapSpectralMeasureInputHandoffSurface.concreteSpectralMeasureStillOpen ∧
  MathlibAnalytic.concreteL2R2DenseDiagonalDomainLinearPMapSpectralMeasureInputHandoffSurface.concretePVMStillOpen ∧
  MathlibAnalytic.concreteL2R2DenseDiagonalDomainLinearPMapSpectralMeasureInputHandoffSurface.continuumSpectralTheoremStillOpen ∧
  MathlibAnalytic.concreteL2R2DenseDiagonalDomainLinearPMapSpectralMeasureInputHandoffSurface.finalReleaseStillHeld ∧
  MathlibAnalytic.concreteL2R2DenseDiagonalDomainLinearPMapSpectralMeasureInputHandoffSurface.publicBoundaryStillHeld

/-- The R5 actual spectral-input boundary is ready. -/
theorem actual_spectral_input_from_r4_bridge_boundary_ready :
    ActualSpectralInputFromR4BridgeBoundary := by
  exact ⟨
    actual_spectral_input_from_r4_bridge_packet_ready,
    trivial,
    trivial,
    MathlibAnalytic.spectralRealizationSkeletonReviewSurface.continuumSpectralTheoremStillOpen_proof,
    MathlibAnalytic.spectralRealizationSkeletonReviewSurface.finalReleaseHeld_proof,
    MathlibAnalytic.spectralRealizationSkeletonReviewSurface.publicBoundaryHeld_proof⟩

/-- Public R5 readiness after the R4 self-adjoint input bridge. -/
def ActualSpectralInputFromR4BridgeReady : Prop :=
  ActualSpectralInputFromR4BridgePacket ∧ ActualSpectralInputFromR4BridgeBoundary

/-- R5 actual spectral-input readiness theorem. -/
theorem actual_spectral_input_from_r4_bridge_ready :
    ActualSpectralInputFromR4BridgeReady := by
  exact ⟨
    actual_spectral_input_from_r4_bridge_packet_ready,
    actual_spectral_input_from_r4_bridge_boundary_ready⟩

/-- Short alias: R5 has acquired an actual Mathlib self-adjoint operator input. -/
theorem r5_actual_self_adjoint_operator_input_ready :
    IsSelfAdjoint MathlibAnalytic.concreteL2R2DenseDiagonalDomainLinearPMap := by
  exact R4.Theorem.r4_self_adjoint_input_supplied

end

end Theorem
end R5
end MGAP4D