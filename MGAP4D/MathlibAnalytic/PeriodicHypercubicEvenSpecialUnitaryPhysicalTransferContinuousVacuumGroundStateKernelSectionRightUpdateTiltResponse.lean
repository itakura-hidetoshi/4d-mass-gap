import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumGroundStateKernelSectionVacuumUpdateExpectation
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

local instance kernelSectionRightUpdateTiltResponseSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

/-- Updating one right-boundary link in the fixed-right ground-state
kernel-section law is exactly a normalized tilt by the corresponding one-slab
local Boltzmann factor, at the level of expectations.

The formula is stated directly for arbitrary real observables.  It is an exact
normalization identity and does not assert a regular-conditional or Gibbs
interpretation. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure_integral_update_right_eq_localFactor_tilt
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (F : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ) :
    (∫ A, F A
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
        H N hN beta hbeta (Function.update C target g)) =
      (∫ A,
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
              H N beta A C target g * F A
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
          H N hN beta hbeta C) /
        (∫ A,
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
            H N beta A C target g
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
            H N hN beta hbeta C) := by
  rw [←
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionProbabilityMeasure_eq_continuous
      H N hN beta hbeta (Function.update C target g)]
  rw [←
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionProbabilityMeasure_eq_continuous
      H N hN beta hbeta C]
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionProbabilityMeasure
  rw [
    realIntegralWeightedProbabilityMeasure_integral
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionWeight
        H N hN beta hbeta (Function.update C target g))
      F
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionWeight_integrable
        H N hN beta hbeta (Function.update C target g))
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionWeight_ae_nonnegative
        H N hN beta hbeta (Function.update C target g))
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionWeight_integral_pos
        H N hN beta hbeta (Function.update C target g)),
    realIntegralWeightedProbabilityMeasure_integral
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionWeight
        H N hN beta hbeta C)
      (fun A =>
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
            H N beta A C target g * F A)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionWeight_integrable
        H N hN beta hbeta C)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionWeight_ae_nonnegative
        H N hN beta hbeta C)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionWeight_integral_pos
        H N hN beta hbeta C),
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
  have hWeight :
      ∀ A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionWeight
            H N hN beta hbeta (Function.update C target g) A =
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionWeight
              H N hN beta hbeta C A *
            periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
              H N beta A C target g := by
    intro A
    unfold
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionWeight
    rw [
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_update_right_eq_localFactor_mul]
    ring
  have hMass :
      (∫ A,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionWeight
          H N hN beta hbeta (Function.update C target g) A
        ∂periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) =
      ∫ A,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionWeight
            H N hN beta hbeta C A *
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
            H N beta A C target g
        ∂periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N := by
    apply integral_congr_ae
    filter_upwards with A
    exact hWeight A
  have hJoint :
      (∫ A,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionWeight
            H N hN beta hbeta (Function.update C target g) A * F A
        ∂periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) =
      ∫ A,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionWeight
            H N hN beta hbeta C A *
          (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
              H N beta A C target g * F A)
        ∂periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N := by
    apply integral_congr_ae
    filter_upwards with A
    rw [hWeight A]
    ring
  rw [hMass, hJoint]
  have hBaseMassPos :
      0 <
        ∫ A,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionWeight
            H N hN beta hbeta C A
          ∂periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionWeight_integral_pos
      H N hN beta hbeta C
  have hTiltMassPos :
      0 <
        ∫ A,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionWeight
              H N hN beta hbeta C A *
            periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
              H N beta A C target g
          ∂periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N := by
    rw [← hMass]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionWeight_integral_pos
        H N hN beta hbeta (Function.update C target g)
  field_simp [ne_of_gt hBaseMassPos, ne_of_gt hTiltMassPos]

/-- Consequently the response of an arbitrary observable to a one-link change
of the fixed right boundary is exactly a covariance with the local Boltzmann
factor, divided by its positive expectation.

This is the desired local response normal form.  Any decay or summability bound
must still be proved separately. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure_integral_update_right_sub_eq_covariance_div_localFactor_expectation
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (F : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ) :
    (∫ A, F A
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
          H N hN beta hbeta (Function.update C target g)) -
      (∫ A, F A
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
          H N hN beta hbeta C) =
      realIntegralCovariance
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
            H N hN beta hbeta C)
          (fun A =>
            periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
              H N beta A C target g)
          F /
        (∫ A,
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
            H N beta A C target g
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
            H N hN beta hbeta C) := by
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure_integral_update_right_eq_localFactor_tilt
      H N hN beta hbeta C target g F]
  unfold realIntegralCovariance
  have hDenomPos :
      0 <
        ∫ A,
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
            H N beta A C target g
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
            H N hN beta hbeta C := by
    rw [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure_integral_rightTargetLocalFactor_eq_vacuum_update_ratio
        H N hN beta hbeta C target g]
    exact div_pos
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
        H N hN beta hbeta (Function.update C target g))
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
        H N hN beta hbeta C)
  field_simp [ne_of_gt hDenomPos]

end

end MathlibAnalytic
end MGAP4D
