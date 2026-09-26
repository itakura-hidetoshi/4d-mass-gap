import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferVacuumSecondMeanRMSTargetMajorant
import Mathlib.Tactic

/-!
# Remove the common feedback gap from the vacuum RMS majorant

PR #4814 proves the source-independent target-indexed estimate

  ∫ g_fb * ofReal(||RMS2(C,source,target)||^2) d nu_vac(C)
    <=
  (K_H(beta)+1) * ofReal(||F-CondExp_target F||^2),

where

  g_fb = 1 - ofReal(q_half(s,beta)^2).

PR #4812 already proves ofReal(q_half^2) < 1 on the same strict physical-sweep
interval.  Hence g_fb is nonzero and finite.  This file factors g_fb out of
the lower integral and cancels it with the ENNReal inverse.

The result is a receiver-ready global RMS-energy majorant

  RMSGlobalEnergy(source,target)
    <=
  g_fb^{-1} * (K_H(beta)+1) *
    ofReal(||F-CondExp_target F||^2).

The right-hand side is target-indexed and source-independent.

No new cutoff, response coefficient, Harnack factor, factor two, or
cardinality loss is introduced.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory BigOperators

noncomputable section

local instance vacuumSecondMeanRMSDeweightedMajorantSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance vacuumSecondMeanRMSDeweightedMajorantSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance vacuumSecondMeanRMSDeweightedMajorantSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance vacuumSecondMeanRMSDeweightedMajorantSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance vacuumSecondMeanRMSDeweightedMajorantSpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance vacuumSecondMeanRMSDeweightedMajorantSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Vacuum integral of the squared source-pair second-mean RMS L2 amplitude. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawVacuumSecondMeanRMSAmplitudeEnergy
    (H N : ℕ) (hN : 0 < N)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (distinguishedSource source target :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound) : ℝ≥0∞ :=
  ∫⁻ C,
    ENNReal.ofReal
      (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeL2
          H N hN beta hbeta C distinguishedSource source target
          (C distinguishedSource) (C source)
          F hF bound hbound C‖ ^ 2)
    ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
      H N hN beta hbeta

/-- The PR #4814 weighted outer RMS estimate is exactly the common feedback
gap times the unweighted vacuum RMS energy. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLaw_feedbackGap_mul_vacuumSecondMeanRMSAmplitudeEnergy_le_harnackFactor_add_one_mul_condExpL2_residual_norm_sq
    (N : ℕ) (hN : 0 < N)
    (s : ℝ) (hs : 1 < s)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff
          s)
    (H : ℕ)
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
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawVacuumSecondMeanRMSAmplitudeEnergy
        H N hN beta hbeta distinguishedSource source target
        F hF bound hbound ≤
      (ENNReal.ofReal ((Real.exp (32 * beta)) ^ 2) + 1) *
        ENNReal.ofReal
          (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
                H N hN beta hbeta F hF bound hbound -
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
                H N hN beta hbeta target
                (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
                  H N hN beta hbeta F hF bound hbound)‖ ^ 2) := by
  let gap : ℝ≥0∞ :=
    1 -
      ENNReal.ofReal
        ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient
          s beta) ^ 2)
  let rms :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ≥0∞ :=
    fun C =>
      ENNReal.ofReal
        (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeL2
            H N hN beta hbeta C distinguishedSource source target
            (C distinguishedSource) (C source)
            F hF bound hbound C‖ ^ 2)
  have hBase :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLaw_vacuum_diagonal_one_sub_halfBarrierPinFreeCoefficient_sq_ofReal_mul_secondMeanRMSAmplitudeL2_norm_sq_ofReal_lintegral_le_harnackFactor_add_one_mul_condExpL2_residual_norm_sq
      N hN s hs beta hbeta hcut H distinguishedSource source target hne
      F hF bound hbound
  have hFactor :
      (∫⁻ C, gap * rms C
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
          H N hN beta hbeta) =
        gap *
          ∫⁻ C, rms C
            ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
              H N hN beta hbeta := by
    rw [lintegral_const_mul']
    simp [gap]
  rw [show
      (∫⁻ C,
        (1 -
            ENNReal.ofReal
              ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient
                s beta) ^ 2)) *
          ENNReal.ofReal
            (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeL2
                H N hN beta hbeta C distinguishedSource source target
                (C distinguishedSource) (C source)
                F hF bound hbound C‖ ^ 2)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
          H N hN beta hbeta) =
      gap *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawVacuumSecondMeanRMSAmplitudeEnergy
          H N hN beta hbeta distinguishedSource source target
          F hF bound hbound by
        simpa [
          gap, rms,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawVacuumSecondMeanRMSAmplitudeEnergy] using hFactor]
    at hBase
  simpa [gap,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawVacuumSecondMeanRMSAmplitudeEnergy] using hBase

/-- Deweighted receiver-ready global target-indexed RMS-energy majorant. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLaw_vacuumSecondMeanRMSAmplitudeEnergy_le_feedbackGap_inv_mul_harnackFactor_add_one_mul_condExpL2_residual_norm_sq
    (N : ℕ) (hN : 0 < N)
    (s : ℝ) (hs : 1 < s)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff
          s)
    (H : ℕ)
    (distinguishedSource source target :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (hne : target ≠ source)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawVacuumSecondMeanRMSAmplitudeEnergy
        H N hN beta hbeta distinguishedSource source target
        F hF bound hbound ≤
      (1 -
          ENNReal.ofReal
            ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient
              s beta) ^ 2))⁻¹ *
        ((ENNReal.ofReal ((Real.exp (32 * beta)) ^ 2) + 1) *
          ENNReal.ofReal
            (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
                  H N hN beta hbeta F hF bound hbound -
                periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
                  H N hN beta hbeta target
                  (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
                    H N hN beta hbeta F hF bound hbound)‖ ^ 2)) := by
  let c : ℝ≥0∞ :=
    ENNReal.ofReal
      ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient
        s beta) ^ 2)
  let gap : ℝ≥0∞ := 1 - c
  let X : ℝ≥0∞ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawVacuumSecondMeanRMSAmplitudeEnergy
      H N hN beta hbeta distinguishedSource source target
      F hF bound hbound
  let A : ℝ≥0∞ :=
    (ENNReal.ofReal ((Real.exp (32 * beta)) ^ 2) + 1) *
      ENNReal.ofReal
        (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
              H N hN beta hbeta F hF bound hbound -
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
              H N hN beta hbeta target
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
                H N hN beta hbeta F hF bound hbound)‖ ^ 2)
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
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLaw_feedbackGap_mul_vacuumSecondMeanRMSAmplitudeEnergy_le_harnackFactor_add_one_mul_condExpL2_residual_norm_sq
        N hN s hs beta hbeta hcut H distinguishedSource source target hne
        F hF bound hbound
  have hSolved : X ≤ gap⁻¹ * A :=
    (ENNReal.mul_le_iff_le_inv hGapZero hGapTop).mp hBase
  simpa [gap, c, X, A] using hSolved

end

end MGAP4D.MathlibAnalytic
