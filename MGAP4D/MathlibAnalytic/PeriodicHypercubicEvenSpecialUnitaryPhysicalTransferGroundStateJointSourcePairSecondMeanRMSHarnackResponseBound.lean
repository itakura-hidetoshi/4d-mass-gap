import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourcePairSecondMeanRMSOrderedReferenceEnergy
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourcePairFirstCrossHarnackStationarityBound
import Mathlib.Tactic

/-!
# Sharp Harnack/response bound for the second-mean RMS L2 energy

PR #4804 gives the exact identity

  ofReal(||RMS2L2||^2)
    =
  orderedFirstCrossEnergy + referenceUpdatedVarianceEnergy.

PR #4795 bounds the ordered first-cross term by

  K_H(beta) * referenceUpdatedVarianceEnergy
    + ofReal(||ResponseL2||^2).

Adding the unchanged second-variance term therefore gives

  ofReal(||RMS2L2||^2)
    <=
  (K_H(beta) + 1) * referenceUpdatedVarianceEnergy
    + ofReal(||ResponseL2||^2).

This is only an algebraic composition of already-proved theorem units.
No factor two, cardinality factor, extra response coefficient, or additional
Harnack loss is introduced.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

noncomputable section

local instance secondMeanRMSHarnackResponseBoundSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance secondMeanRMSHarnackResponseBoundSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance secondMeanRMSHarnackResponseBoundSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance secondMeanRMSHarnackResponseBoundSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance secondMeanRMSHarnackResponseBoundSpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance secondMeanRMSHarnackResponseBoundSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The exact second-mean RMS energy is bounded by one Harnack-weighted updated
variance plus its unchanged second-variance contribution and the exact
response-L2 square. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeL2_norm_sq_ofReal_le_harnackLawFactor_add_one_mul_referenceUpdatedVariance_add_responseL2_norm_sq
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource source target :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (hne : target ≠ source)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound)
    (left : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    ENNReal.ofReal
        (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeL2
            H N hN beta hbeta B distinguishedSource source target k g₂
            F hF bound hbound left‖ ^ 2) ≤
      (ENNReal.ofReal ((Real.exp (32 * beta)) ^ 2) + 1) *
        (∫⁻ A,
          ENNReal.ofReal
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawUpdatedBackgroundVarianceEnergy
              H N hN beta hbeta B distinguishedSource source target k g₂
              F left A)
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
            H N hN beta hbeta B source distinguishedSource k g₂) +
      ENNReal.ofReal
        (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseL2
            H N hN beta hbeta B distinguishedSource source target k g₂
            F hF bound hbound left 0‖ ^ 2) := by
  let V : ℝ≥0∞ :=
    ∫⁻ A,
      ENNReal.ofReal
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawUpdatedBackgroundVarianceEnergy
          H N hN beta hbeta B distinguishedSource source target k g₂
          F left A)
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
        H N hN beta hbeta B source distinguishedSource k g₂
  let R2 : ℝ≥0∞ :=
    ENNReal.ofReal
      (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseL2
          H N hN beta hbeta B distinguishedSource source target k g₂
          F hF bound hbound left 0‖ ^ 2)
  let K : ℝ≥0∞ :=
    ENNReal.ofReal ((Real.exp (32 * beta)) ^ 2)
  have hExact :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeL2_norm_sq_ofReal_eq_orderedFirstCross_lintegral_add_referenceUpdatedVariance_lintegral
      H N hN beta hbeta B distinguishedSource source target hne k g₂
      F hF bound hbound left
  have hCross :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedFirstCrossEnergy_lintegral_le_harnackLawFactor_mul_reference_updatedBackgroundVarianceEnergy_lintegral_add_responseL2_norm_sq_ofReal
      H N hN beta hbeta B distinguishedSource source target hne k g₂
      F hF bound hbound left
  rw [hExact]
  have hStep :
      (∫⁻ Cvg,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedFirstCrossEnergy
          H N hN beta hbeta B distinguishedSource source target k g₂
          F left Cvg
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceSecondTargetOrderedMeasure
          H N hN beta hbeta B distinguishedSource source target k g₂) + V ≤
        (K * V + R2) + V := by
    exact add_le_add hCross (le_refl V)
  calc
    (∫⁻ Cvg,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedFirstCrossEnergy
        H N hN beta hbeta B distinguishedSource source target k g₂
        F left Cvg
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceSecondTargetOrderedMeasure
        H N hN beta hbeta B distinguishedSource source target k g₂) + V
        ≤ (K * V + R2) + V := hStep
    _ = (K + 1) * V + R2 := by ring
    _ =
      (ENNReal.ofReal ((Real.exp (32 * beta)) ^ 2) + 1) *
        (∫⁻ A,
          ENNReal.ofReal
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawUpdatedBackgroundVarianceEnergy
              H N hN beta hbeta B distinguishedSource source target k g₂
              F left A)
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
            H N hN beta hbeta B source distinguishedSource k g₂) +
      ENNReal.ofReal
        (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseL2
            H N hN beta hbeta B distinguishedSource source target k g₂
            F hF bound hbound left 0‖ ^ 2) := by
      rfl

end

end MGAP4D.MathlibAnalytic
