import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R4ActualSelfAdjointnessTheorem
import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapSpectralMeasureInputHandoff
import MGAP4D.R5.Theorem.SpectrumMilestone
import MGAP4D.R5.TheoremSurface.ExportSurface

namespace MGAP4D
namespace R5
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- R5 actual spectral-input theorem packet.

This is the additive R5 bridge after R4 was upgraded from a precondition packet to
an actual Mathlib self-adjointness theorem.  It does not claim the full spectral
theorem/PVM construction.  It records that R5 now has an actual self-adjoint
`LinearPMap` input and a spectral-measure input handoff. -/
def R5ActualSpectralInputTheoremPacket : Prop :=
  MathlibAnalytic.concreteAnalyticSpineL2R4ActualSelfAdjointnessTheoremReady ∧
  MathlibAnalytic.concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapSpectralMeasureInputHandoffReady ∧
  MathlibAnalytic.IsSelfAdjoint MathlibAnalytic.concreteL2R2DenseDiagonalDomainLinearPMap ∧
  MathlibAnalytic.LinearPMap.adjoint MathlibAnalytic.concreteL2R2DenseDiagonalDomainLinearPMap =
    MathlibAnalytic.concreteL2R2DenseDiagonalDomainLinearPMap ∧
  MathlibAnalytic.spectralRealizationSkeletonReviewSurface.ready ∧
  MathlibAnalytic.spectralRealizationSkeletonReviewSurface.exactAtomPresent ∧
  MathlibAnalytic.spectralRealizationSkeletonReviewSurface.observableAtomWitness ∧
  MathlibAnalytic.spectralRealizationSkeletonReviewSurface.positiveMassAtExact ∧
  MathlibAnalytic.exactGapValueReal = (33 : ℝ) / 20

/-- R5 actual spectral-input theorem packet is ready. -/
theorem r5_actual_spectral_input_theorem_packet_ready :
    R5ActualSpectralInputTheoremPacket := by
  exact ⟨
    MathlibAnalytic.concrete_analytic_spine_l2_r4_actual_self_adjointness_theorem_ready,
    MathlibAnalytic.concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_pmap_spectral_measure_input_handoff_ready,
    MathlibAnalytic.concrete_l2_r4_dense_diagonal_linear_pmap_isSelfAdjoint,
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
def R5ActualSpectralInputBoundary : Prop :=
  R5ActualSpectralInputTheoremPacket ∧
  MathlibAnalytic.concreteL2R2DenseDiagonalDomainLinearPMapSpectralMeasureInputHandoffSurface.concreteSpectralMeasureStillOpen ∧
  MathlibAnalytic.concreteL2R2DenseDiagonalDomainLinearPMapSpectralMeasureInputHandoffSurface.concretePVMStillOpen ∧
  MathlibAnalytic.concreteL2R2DenseDiagonalDomainLinearPMapSpectralMeasureInputHandoffSurface.continuumSpectralTheoremStillOpen ∧
  MathlibAnalytic.concreteL2R2DenseDiagonalDomainLinearPMapSpectralMeasureInputHandoffSurface.finalReleaseStillHeld ∧
  MathlibAnalytic.concreteL2R2DenseDiagonalDomainLinearPMapSpectralMeasureInputHandoffSurface.publicBoundaryStillHeld

/-- R5 actual spectral-input boundary is ready. -/
theorem r5_actual_spectral_input_boundary_ready :
    R5ActualSpectralInputBoundary := by
  exact ⟨
    r5_actual_spectral_input_theorem_packet_ready,
    trivial,
    trivial,
    MathlibAnalytic.spectralRealizationSkeletonReviewSurface.continuumSpectralTheoremStillOpen_proof,
    MathlibAnalytic.spectralRealizationSkeletonReviewSurface.finalReleaseHeld_proof,
    MathlibAnalytic.spectralRealizationSkeletonReviewSurface.publicBoundaryHeld_proof⟩

/-- Public R5 readiness after actual R4 self-adjointness. -/
def R5ActualSpectralInputReady : Prop :=
  R5ActualSpectralInputTheoremPacket ∧ R5ActualSpectralInputBoundary

/-- R5 actual spectral-input readiness theorem. -/
theorem r5_actual_spectral_input_ready :
    R5ActualSpectralInputReady := by
  exact ⟨
    r5_actual_spectral_input_theorem_packet_ready,
    r5_actual_spectral_input_boundary_ready⟩

/-- Short alias: R5 has acquired an actual Mathlib self-adjoint operator input. -/
theorem r5_actual_self_adjoint_operator_input_ready :
    MathlibAnalytic.IsSelfAdjoint MathlibAnalytic.concreteL2R2DenseDiagonalDomainLinearPMap := by
  exact MathlibAnalytic.concrete_l2_r4_dense_diagonal_linear_pmap_isSelfAdjoint

end

end Theorem
end R5
end MGAP4D