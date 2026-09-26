import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourcePairSecondMeanRMSL2
import Mathlib.Tactic

/-!
# Squared response bound by the second-mean RMS L2 energy

PR #4800 proves the sharp norm estimate

  ||ResponseL2||
    <= K_pin(target,source) * ||RMS2L2||.

This file records the exact squared real and ENNReal forms needed by the
self-absorption step:

  ||ResponseL2||^2
    <= K_pin(target,source)^2 * ||RMS2L2||^2,

and

  ofReal(||ResponseL2||^2)
    <= ofReal(K_pin(target,source)^2) * ofReal(||RMS2L2||^2).

No new response coefficient, Harnack factor, factor two, or cardinality loss
is introduced.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

noncomputable section

local instance secondMeanRMSResponseSquareSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance secondMeanRMSResponseSquareSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance secondMeanRMSResponseSquareSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance secondMeanRMSResponseSquareSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance secondMeanRMSResponseSquareSpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance secondMeanRMSResponseSquareSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Real squared form of the sharp second-mean RMS response estimate. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseL2_norm_sq_le_canonicalPinFree_sq_mul_secondMeanRMSAmplitudeL2_norm_sq
    (N : ℕ) (hN : 0 < N) (s : ℝ) (hs : 1 < s)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff
          s)
    (H : ℕ)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource source target :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound)
    (left : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseL2
        H N hN beta hbeta B distinguishedSource source target k g₂
        F hF bound hbound left 0‖ ^ 2 ≤
      ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledPhysicalLeftKernel
          H beta hbeta
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
            H N hN beta hbeta)
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_nonneg
            H N hN beta hbeta)).influence target source) ^ 2 *
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeL2
          H N hN beta hbeta B distinguishedSource source target k g₂
          F hF bound hbound left‖ ^ 2 := by
  let K :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledPhysicalLeftKernel
      H beta hbeta
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_nonneg
        H N hN beta hbeta)
  let response :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseL2
      H N hN beta hbeta B distinguishedSource source target k g₂
      F hF bound hbound left 0
  let amplitude :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeL2
      H N hN beta hbeta B distinguishedSource source target k g₂
      F hF bound hbound left
  have hBase :
      ‖response‖ ≤ K.influence target source * ‖amplitude‖ := by
    simpa [K, response, amplitude] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseL2_norm_le_canonicalPinFree_mul_secondMeanRMSAmplitudeL2_norm
        N hN s hs beta hbeta hcut H B distinguishedSource source target k g₂
        F hF bound hbound left
  have hK0 : 0 ≤ K.influence target source :=
    K.influence_nonneg target source
  have hRight0 : 0 ≤ K.influence target source * ‖amplitude‖ :=
    mul_nonneg hK0 (norm_nonneg _)
  have hSq :
      ‖response‖ ^ 2 ≤
        (K.influence target source * ‖amplitude‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg response) hRight0).2 hBase
  simpa [K, response, amplitude, mul_pow] using hSq

/-- ENNReal squared form, with the background-independent pin-free coefficient
factored out explicitly. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseL2_norm_sq_ofReal_le_canonicalPinFree_sq_ofReal_mul_secondMeanRMSAmplitudeL2_norm_sq_ofReal
    (N : ℕ) (hN : 0 < N) (s : ℝ) (hs : 1 < s)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff
          s)
    (H : ℕ)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource source target :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound)
    (left : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    ENNReal.ofReal
        (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseL2
            H N hN beta hbeta B distinguishedSource source target k g₂
            F hF bound hbound left 0‖ ^ 2) ≤
      ENNReal.ofReal
          (((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledPhysicalLeftKernel
              H beta hbeta
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
                H N hN beta hbeta)
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_nonneg
                H N hN beta hbeta)).influence target source) ^ 2) *
        ENNReal.ofReal
          (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeL2
              H N hN beta hbeta B distinguishedSource source target k g₂
              F hF bound hbound left‖ ^ 2) := by
  let K :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledPhysicalLeftKernel
      H beta hbeta
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_nonneg
        H N hN beta hbeta)
  let amplitude :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeL2
      H N hN beta hbeta B distinguishedSource source target k g₂
      F hF bound hbound left
  have hSq :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseL2_norm_sq_le_canonicalPinFree_sq_mul_secondMeanRMSAmplitudeL2_norm_sq
      N hN s hs beta hbeta hcut H B distinguishedSource source target k g₂
      F hF bound hbound left
  calc
    ENNReal.ofReal
        (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseL2
            H N hN beta hbeta B distinguishedSource source target k g₂
            F hF bound hbound left 0‖ ^ 2) ≤
      ENNReal.ofReal
        ((K.influence target source) ^ 2 * ‖amplitude‖ ^ 2) :=
      ENNReal.ofReal_le_ofReal hSq
    _ =
      ENNReal.ofReal ((K.influence target source) ^ 2) *
        ENNReal.ofReal (‖amplitude‖ ^ 2) := by
      rw [ENNReal.ofReal_mul (sq_nonneg (K.influence target source))]
    _ = _ := by
      rfl

end

end MGAP4D.MathlibAnalytic
