import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceC5ExceptionalProbabilityCovariance
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceFixedRightTargetRatioResponse
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

local instance physicalContinuousVacuumC5ExceptionalFixedRightResponseSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

/-- Outside the volume-independent C5 exceptional set, the complete physical
continuous-vacuum four-point defect is exactly the source spatial factor times
the squared fixed-right kernel-section mass, times the positive source-crossing
mean, times the fixed-right response of the literal target-local ratio.

This transports the geometric exceptional-set decomposition directly into the
fixed-right response lane.  No covariance-decay, summability, Gibbs/RCD
identification, or coefficient cancellation is introduced. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_remote_crossRatio_defect_eq_sourceSpatialRatio_mul_mass_sq_mul_crossingExpectation_mul_fixedRight_response_of_not_mem_C5Exceptional
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (fiber distinguishedTarget backgroundFiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (hRemote : backgroundFiber ∉
      periodicHypercubicEvenSpatialSliceC5ExceptionalBackgroundFibers
        H fiber distinguishedTarget)
    (h k g₁ g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta‖ *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H N hN beta hbeta
          (Function.update (Function.update B fiber h) backgroundFiber g₁)) *
      (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta‖ *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H N hN beta hbeta
          (Function.update (Function.update B fiber k) backgroundFiber g₂)) -
      (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta‖ *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H N hN beta hbeta
          (Function.update (Function.update B fiber k) backgroundFiber g₁)) *
      (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta‖ *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H N hN beta hbeta
          (Function.update (Function.update B fiber h) backgroundFiber g₂)) =
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetSpatialHalfUpdateFactor
          H N beta B fiber h /
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetSpatialHalfUpdateFactor
          H N beta B fiber k) *
      ((‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
            H N hN beta hbeta‖ *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
            H N hN beta hbeta
            (Function.update (Function.update B fiber k) backgroundFiber g₂)) ^ 2 *
        ((∫ A,
          specialUnitaryWilsonRelativeKernel N beta (A fiber) h /
            specialUnitaryWilsonRelativeKernel N beta (A fiber) k
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
            H N hN beta hbeta
            (Function.update (Function.update B fiber k) backgroundFiber g₂)) *
        ((∫ A,
            periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
                  H N beta A B backgroundFiber g₁ /
              periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
                  H N beta A B backgroundFiber g₂
            ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
              H N hN beta hbeta
              (Function.update (Function.update B fiber h) backgroundFiber g₂)) -
          (∫ A,
            periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
                  H N beta A B backgroundFiber g₁ /
              periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
                  H N beta A B backgroundFiber g₂
            ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
              H N hN beta hbeta
              (Function.update (Function.update B fiber k) backgroundFiber g₂))))) := by
  rcases
    periodicHypercubicEvenSpatialSlice_not_mem_C5ExceptionalBackgroundFibers
      H fiber distinguishedTarget backgroundFiber hRemote with
    ⟨hFiberBackground, _hBackgroundTarget, hNoShare⟩
  have hne : backgroundFiber ≠ fiber := Ne.symm hFiberBackground
  have hReference :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure_eq_kernelSection_source_then_target_of_remote
      H N hN beta hbeta B (target := backgroundFiber) (source := fiber)
      hne hNoShare k g₂
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_remote_crossRatio_defect_eq_sourceSpatialRatio_mul_mass_sq_mul_probabilityCovariance_of_not_mem_C5Exceptional
      H N hN beta hbeta B fiber distinguishedTarget backgroundFiber hRemote h k g₁ g₂]
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionProbabilityMeasure_eq_continuous
      H N hN beta hbeta
      (Function.update (Function.update B fiber k) backgroundFiber g₂)]
  conv_lhs =>
    rw [← hReference]
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure_targetRatio_crossingRatio_covariance_eq_crossingRatioExpectation_mul_fixedRight_response_of_remote
      H N hN beta hbeta B (target := backgroundFiber) (source := fiber)
      hne hNoShare h k g₁ g₂]

end

end MathlibAnalytic
end MGAP4D