import MGAP4D.R3.Theorem.SelfAdjointClosureBridge
import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapSpectralMeasureInputHandoff
import MGAP4D.R4.TheoremSurface.ExportSurface

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- R4 spectral-measure/PVM input packet in the seven-stage analytic roadmap.

In the seven-stage roadmap, R3 is actual self-adjointness and R4 is the
spectral-measure/PVM layer.  This packet starts from the closed R3 self-adjoint
closure bridge and records the R4 input state for spectral measure and PVM
construction.  It does not claim the concrete spectral measure or concrete PVM
construction yet. -/
def SpectralMeasurePVMInputPacket : Prop :=
  R3.Theorem.SelfAdjointClosureBridgeReady ∧
  MathlibAnalytic.concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapSpectralMeasureInputHandoffReady ∧
  IsSelfAdjoint MathlibAnalytic.concreteL2R2DenseDiagonalDomainLinearPMap ∧
  LinearPMap.adjoint MathlibAnalytic.concreteL2R2DenseDiagonalDomainLinearPMap =
    MathlibAnalytic.concreteL2R2DenseDiagonalDomainLinearPMap ∧
  MathlibAnalytic.spectralRealizationSkeletonReviewSurface.ready ∧
  MathlibAnalytic.spectralRealizationSkeletonReviewSurface.exactAtomPresent ∧
  MathlibAnalytic.spectralRealizationSkeletonReviewSurface.observableAtomWitness ∧
  MathlibAnalytic.spectralRealizationSkeletonReviewSurface.positiveMassAtExact ∧
  MathlibAnalytic.exactGapValueReal = (33 : ℝ) / 20

/-- The R4 spectral-measure/PVM input packet is ready. -/
theorem spectral_measure_pvm_input_packet_ready :
    SpectralMeasurePVMInputPacket := by
  exact ⟨
    R3.Theorem.self_adjoint_closure_bridge_ready,
    MathlibAnalytic.concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_pmap_spectral_measure_input_handoff_ready,
    R3.Theorem.r3_self_adjoint_operator_ready,
    MathlibAnalytic.concrete_l2_r2_dense_diagonal_domain_linear_pmap_actual_adjoint_eq_self,
    MathlibAnalytic.spectral_realization_skeleton_review_surface_ready,
    MathlibAnalytic.spectralRealizationSkeletonReviewSurface.exactAtomPresent_proof,
    MathlibAnalytic.spectralRealizationSkeletonReviewSurface.observableAtomWitness_proof,
    MathlibAnalytic.spectralRealizationSkeletonReviewSurface.positiveMassAtExact_proof,
    MathlibAnalytic.exactGapValueReal_eq⟩

/-- R4 spectral-measure/PVM boundary.

R4 has acquired the actual self-adjoint input and the spectral-realization input
surface.  The concrete spectral measure, concrete PVM, and continuum spectral
theorem remain visible downstream obligations inside R4. -/
def SpectralMeasurePVMBoundary : Prop :=
  SpectralMeasurePVMInputPacket ∧
  MathlibAnalytic.concreteL2R2DenseDiagonalDomainLinearPMapSpectralMeasureInputHandoffSurface.concreteSpectralMeasureStillOpen ∧
  MathlibAnalytic.concreteL2R2DenseDiagonalDomainLinearPMapSpectralMeasureInputHandoffSurface.concretePVMStillOpen ∧
  MathlibAnalytic.concreteL2R2DenseDiagonalDomainLinearPMapSpectralMeasureInputHandoffSurface.continuumSpectralTheoremStillOpen ∧
  MathlibAnalytic.concreteL2R2DenseDiagonalDomainLinearPMapSpectralMeasureInputHandoffSurface.finalReleaseStillHeld ∧
  MathlibAnalytic.concreteL2R2DenseDiagonalDomainLinearPMapSpectralMeasureInputHandoffSurface.publicBoundaryStillHeld

/-- The R4 spectral-measure/PVM boundary is ready. -/
theorem spectral_measure_pvm_boundary_ready :
    SpectralMeasurePVMBoundary := by
  exact ⟨
    spectral_measure_pvm_input_packet_ready,
    trivial,
    trivial,
    MathlibAnalytic.spectralRealizationSkeletonReviewSurface.continuumSpectralTheoremStillOpen_proof,
    MathlibAnalytic.spectralRealizationSkeletonReviewSurface.finalReleaseHeld_proof,
    MathlibAnalytic.spectralRealizationSkeletonReviewSurface.publicBoundaryHeld_proof⟩

/-- Public readiness predicate for R4 in the seven-stage analytic roadmap. -/
def SpectralMeasurePVMInputReady : Prop :=
  SpectralMeasurePVMInputPacket ∧ SpectralMeasurePVMBoundary

/-- R4 spectral-measure/PVM input is ready. -/
theorem spectral_measure_pvm_input_ready :
    SpectralMeasurePVMInputReady := by
  exact ⟨spectral_measure_pvm_input_packet_ready, spectral_measure_pvm_boundary_ready⟩

/-- Short alias: R4 has the actual self-adjoint operator input required for
spectral measure/PVM construction. -/
theorem r4_self_adjoint_operator_input_ready :
    IsSelfAdjoint MathlibAnalytic.concreteL2R2DenseDiagonalDomainLinearPMap := by
  exact R3.Theorem.r3_self_adjoint_operator_ready

end

end Theorem
end R4
end MGAP4D