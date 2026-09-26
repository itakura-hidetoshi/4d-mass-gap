import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourcePairFixedBackgroundRMSFubini
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourcePairSecondMeanRMSTargetResidualMajorant
import Mathlib.Tactic

/-!
# Fixed-background RMS energy bounded by the target residual

PR #4831 identifies the outer kernel-section integral of the squared
fixed-background second-mean RMS norm with the squared norm of the
corresponding full source-pair RMS L2 vector.

PR #4813 bounds that full source-pair RMS energy by a source-independent
target kernel-section residual energy after multiplication by the exact
half-barrier feedback gap.

This file composes those two statements.  For every off-diagonal
source/target pair,

  (1 - ofReal(q_half^2))
    * integral_A ofReal(||RMS_fiber(A;source,target)||^2)
  <=
    (K_H(beta) + 1) * E_target(C).

The right-hand side depends on the target but not on the source.

A second wrapper states the same result for a link-indexed family of bounded
concrete representatives F_target, matching the PR #4829/#4830 sweep-stage
orientation.

No new estimate, source summation, finite-cardinality factor, factor two,
response coefficient, pin-free replacement, or probability law is introduced.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory BigOperators

noncomputable section

local instance fixedBackgroundRMSTargetResidualSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance fixedBackgroundRMSTargetResidualSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The source-independent PR #4813 target residual majorant rewritten through
the PR #4831 fixed-background Fubini identity. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLaw_diagonal_one_sub_halfBarrierPinFreeCoefficient_sq_mul_fixedBackgroundSecondMeanRMS_norm_sq_lintegral_le_harnackFactor_add_one_mul_targetKernelSectionResidualEnergy
    (N : ℕ) (hN : 0 < N)
    (s : ℝ) (hs : 1 < s)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff
          s)
    (H : ℕ)
    (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource source target :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (hne : target ≠ source)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound) :
    (1 -
        ENNReal.ofReal
          ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient
            s beta) ^ 2)) *
      (∫⁻ A,
        ENNReal.ofReal
          (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeCurrentValueFixedBackgroundL2
              H N hN beta hbeta C A distinguishedSource source target
              F hF bound hbound C‖ ^ 2)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
          H N hN beta hbeta C) ≤
      (ENNReal.ofReal ((Real.exp (32 * beta)) ^ 2) + 1) *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointTargetKernelSectionResidualEnergy
          H N hN beta hbeta C target F := by
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeCurrentValueFixedBackgroundL2_norm_sq_lintegral_eq_fullL2_norm_sq_ofReal
      H N hN beta hbeta C distinguishedSource source target
      F hF bound hbound]
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLaw_diagonal_one_sub_halfBarrierPinFreeCoefficient_sq_ofReal_mul_secondMeanRMSAmplitudeL2_norm_sq_ofReal_le_harnackFactor_add_one_mul_targetKernelSectionResidualEnergy
      N hN s hs beta hbeta hcut H C distinguishedSource source target hne
      F hF bound hbound

/-- Link-indexed wrapper: the response target uses its own bounded concrete
representative F_target, while the majorant remains target-indexed and
source-independent. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairLinkIndexed_diagonal_one_sub_halfBarrierPinFreeCoefficient_sq_mul_fixedBackgroundSecondMeanRMS_norm_sq_lintegral_le_targetResidualEnergy
    (N : ℕ) (hN : 0 < N)
    (s : ℝ) (hs : 1 < s)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff
          s)
    (H : ℕ)
    (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource source target :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (hne : target ≠ source)
    (F :
      PeriodicHypercubicEvenSpatialSliceLink H →
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : ∀ e, StronglyMeasurable (F e))
    (bound : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hbound : ∀ e z, ‖F e z‖ ≤ bound e) :
    (1 -
        ENNReal.ofReal
          ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient
            s beta) ^ 2)) *
      (∫⁻ A,
        ENNReal.ofReal
          (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeCurrentValueFixedBackgroundL2
              H N hN beta hbeta C A distinguishedSource source target
              (F target) (hF target) (bound target) (hbound target) C‖ ^ 2)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
          H N hN beta hbeta C) ≤
      (ENNReal.ofReal ((Real.exp (32 * beta)) ^ 2) + 1) *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointTargetKernelSectionResidualEnergy
          H N hN beta hbeta C target (F target) := by
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLaw_diagonal_one_sub_halfBarrierPinFreeCoefficient_sq_mul_fixedBackgroundSecondMeanRMS_norm_sq_lintegral_le_harnackFactor_add_one_mul_targetKernelSectionResidualEnergy
      N hN s hs beta hbeta hcut H C distinguishedSource source target hne
      (F target) (hF target) (bound target) (hbound target)

end

end MGAP4D.MathlibAnalytic
