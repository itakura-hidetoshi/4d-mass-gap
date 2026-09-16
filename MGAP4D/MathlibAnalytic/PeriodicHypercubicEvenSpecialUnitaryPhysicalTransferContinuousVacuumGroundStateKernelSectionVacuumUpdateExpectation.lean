import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumGroundStateKernelSectionContinuousDensity
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryOneSlabRightTargetLocalFactorBounds
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

local instance kernelSectionVacuumUpdateExpectationSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

/-- A one-link response of the canonical continuous vacuum is exactly the
expectation of the corresponding one-slab right-target local Boltzmann factor
under the fixed-right ground-state kernel-section probability law.

This is the pointwise eigenfunction equation rewritten as a normalized
probability identity.  It converts a global vacuum ratio into an expectation
of a literal one-link Wilson observable.  No regular-conditional,
independence, decay, or contraction statement is asserted. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure_integral_rightTargetLocalFactor_eq_vacuum_update_ratio
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    (∫ A,
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
        H N beta A C target g
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
        H N hN beta hbeta C) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H N hN beta hbeta (Function.update C target g) /
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H N hN beta hbeta C := by
  rw [←
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionProbabilityMeasure_eq_continuous
      H N hN beta hbeta C]
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionProbabilityMeasure
  rw [
    realIntegralWeightedProbabilityMeasure_integral
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionWeight
        H N hN beta hbeta C)
      (fun A =>
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
          H N beta A C target g)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionWeight_integrable
        H N hN beta hbeta C)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionWeight_ae_nonnegative
        H N hN beta hbeta C)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionWeight_integral_pos
        H N hN beta hbeta C)]
  have hNumerator :
      (∫ A,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionWeight
            H N hN beta hbeta C A *
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
            H N beta A C target g
        ∂periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) =
      ∫ A,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionWeight
          H N hN beta hbeta (Function.update C target g) A
        ∂periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N := by
    apply integral_congr_ae
    filter_upwards with A
    unfold
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionWeight
    rw [
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_update_right_eq_localFactor_mul]
    ring
  rw [hNumerator]
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionWeight_integral
      H N hN beta hbeta C,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionWeight_integral
      H N hN beta hbeta (Function.update C target g)]
  have hNorm :
      0 < ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H N hN beta hbeta‖ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos_from_uniform_kernel_floor
      H N hN beta hbeta
  have hVacuum :
      0 < periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
        H N hN beta hbeta C :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
      H N hN beta hbeta C
  field_simp [ne_of_gt hNorm, ne_of_gt hVacuum]

end

end MathlibAnalytic
end MGAP4D
