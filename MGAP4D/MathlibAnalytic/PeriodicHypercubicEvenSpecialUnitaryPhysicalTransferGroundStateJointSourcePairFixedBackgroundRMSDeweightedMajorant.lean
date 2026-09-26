import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourcePairFixedBackgroundRMSTargetResidual
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourcePairSecondMeanRMSUniformFeedback
import Mathlib.Tactic

/-!
# Deweighted fixed-background RMS target majorant

PR #4832 proves, at one fixed outer boundary C,

  gap * integral_A ofReal(||RMS_fiber(A;source,target)||^2)
    <= (K_H(beta) + 1) * E_target(C),

where

  gap = 1 - ofReal(q_half(s,beta)^2) > 0.

This file removes that common feedback gap exactly, using the same ENNReal
inverse cancellation already validated globally in PR #4815.

It also names the resulting source-independent target majorant

  M_target(C)
    = gap^{-1} * (K_H(beta) + 1) * E_target(C).

Every off-diagonal source has its current-value fixed-background RMS outer
energy bounded by this same target quantity.

No source summation, finite-cardinality factor, factor two, response
coefficient, pin-free replacement, or new probability law is introduced.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory BigOperators

noncomputable section

local instance fixedBackgroundRMSDeweightedMajorantSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance fixedBackgroundRMSDeweightedMajorantSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Current-value fixed-background RMS energy after integrating only the outer
kernel-section background A. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundSecondMeanRMSAmplitudeEnergy
    (H N : ℕ) (hN : 0 < N)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource source target :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound) : ℝ≥0∞ :=
  ∫⁻ A,
    ENNReal.ofReal
      (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeCurrentValueFixedBackgroundL2
          H N hN beta hbeta C A distinguishedSource source target
          F hF bound hbound C‖ ^ 2)
    ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
      H N hN beta hbeta C

/-- Source-independent target majorant for the fixed-background RMS outer
energy. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundSecondMeanRMSTargetMajorant
    (H N : ℕ) (hN : 0 < N)
    (s : ℝ)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ) : ℝ≥0∞ :=
  (1 -
      ENNReal.ofReal
        ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient
          s beta) ^ 2))⁻¹ *
    ((ENNReal.ofReal ((Real.exp (32 * beta)) ^ 2) + 1) *
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointTargetKernelSectionResidualEnergy
        H N hN beta hbeta C target F)

/-- Exact feedback-gap weighted form of the PR #4832 fixed-background RMS
estimate, packaged through the named outer energy. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLaw_feedbackGap_mul_fixedBackgroundSecondMeanRMSAmplitudeEnergy_le_harnackFactor_add_one_mul_targetResidual
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
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundSecondMeanRMSAmplitudeEnergy
        H N hN beta hbeta C distinguishedSource source target
        F hF bound hbound ≤
      (ENNReal.ofReal ((Real.exp (32 * beta)) ^ 2) + 1) *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointTargetKernelSectionResidualEnergy
          H N hN beta hbeta C target F := by
  simpa [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundSecondMeanRMSAmplitudeEnergy] using
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLaw_diagonal_one_sub_halfBarrierPinFreeCoefficient_sq_mul_fixedBackgroundSecondMeanRMS_norm_sq_lintegral_le_harnackFactor_add_one_mul_targetKernelSectionResidualEnergy
      N hN s hs beta hbeta hcut H C distinguishedSource source target hne
      F hF bound hbound

/-- Deweighted source-independent target majorant for the fixed-background RMS
outer energy. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLaw_fixedBackgroundSecondMeanRMSAmplitudeEnergy_le_targetMajorant
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
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundSecondMeanRMSAmplitudeEnergy
        H N hN beta hbeta C distinguishedSource source target
        F hF bound hbound ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundSecondMeanRMSTargetMajorant
        H N hN s beta hbeta C target F := by
  let c : ℝ≥0∞ :=
    ENNReal.ofReal
      ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient
        s beta) ^ 2)
  let gap : ℝ≥0∞ := 1 - c
  let X : ℝ≥0∞ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundSecondMeanRMSAmplitudeEnergy
      H N hN beta hbeta C distinguishedSource source target
      F hF bound hbound
  let A : ℝ≥0∞ :=
    (ENNReal.ofReal ((Real.exp (32 * beta)) ^ 2) + 1) *
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointTargetKernelSectionResidualEnergy
        H N hN beta hbeta C target F
  have hc : c < 1 := by
    simpa [c] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient_sq_ofReal_lt_one_of_strictPhysicalSweepCutoff
        s beta hbeta hcut
  have hGapPos : 0 < gap := by
    simpa [gap] using (tsub_pos_iff_lt.mpr hc)
  have hGapZero : gap ≠ 0 := ne_of_gt hGapPos
  have hGapTop : gap ≠ ⊤ := by
    simp [gap]
  have hBase : gap * X ≤ A := by
    simpa [gap, c, X, A] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLaw_feedbackGap_mul_fixedBackgroundSecondMeanRMSAmplitudeEnergy_le_harnackFactor_add_one_mul_targetResidual
        N hN s hs beta hbeta hcut H C distinguishedSource source target hne
        F hF bound hbound
  have hSolved : X ≤ gap⁻¹ * A :=
    (ENNReal.mul_le_iff_le_inv hGapZero hGapTop).mp hBase
  simpa [
    gap, c, X, A,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundSecondMeanRMSTargetMajorant] using hSolved

/-- Link-indexed form used by the six-spatial sweep representative family. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairLinkIndexed_fixedBackgroundSecondMeanRMSAmplitudeEnergy_le_targetMajorant
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
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundSecondMeanRMSAmplitudeEnergy
        H N hN beta hbeta C distinguishedSource source target
        (F target) (hF target) (bound target) (hbound target) ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundSecondMeanRMSTargetMajorant
        H N hN s beta hbeta C target (F target) := by
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLaw_fixedBackgroundSecondMeanRMSAmplitudeEnergy_le_targetMajorant
      N hN s hs beta hbeta hcut H C distinguishedSource source target hne
      (F target) (hF target) (bound target) (hbound target)

end

end MGAP4D.MathlibAnalytic
