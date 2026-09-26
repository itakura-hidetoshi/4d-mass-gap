import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourcePairOldVarianceHarnackStationarityReturn
import Mathlib.Tactic

/-!
# First-cross energy after Harnack comparison and stationarity return

PR #4785 splits the complete ordered first-cross energy exactly into

  old target variance + response L2 norm-square.

PR #4794 bounds the old target variance by the sharp Harnack factor times the
updated-background target variance after exact one-link stationarity return.

This file composes those theorem units:

  firstCrossEnergy
    <= K_H(beta) * referenceUpdatedBackgroundVariance
       + ofReal (||responseL2||^2),

with

  K_H(beta) = (exp (32 beta))^2 = exp (64 beta).

No new analytic comparison, triangle inequality, factor two, response
coefficient, or finite-cardinality loss is introduced.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

noncomputable section

local instance firstCrossHarnackStationaritySpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance firstCrossHarnackStationaritySpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance firstCrossHarnackStationaritySpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance firstCrossHarnackStationaritySpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance firstCrossHarnackStationaritySpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance firstCrossHarnackStationaritySpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Sharp first-cross bound after composing the exact Pythagorean/response-L2
split with the Harnack old-variance comparison and exact stationarity return. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedFirstCrossEnergy_lintegral_le_harnackLawFactor_mul_reference_updatedBackgroundVarianceEnergy_lintegral_add_responseL2_norm_sq_ofReal
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
    (∫⁻ Cvg,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedFirstCrossEnergy
        H N hN beta hbeta B distinguishedSource source target k g₂
        F left Cvg
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceSecondTargetOrderedMeasure
        H N hN beta hbeta B distinguishedSource source target k g₂) ≤
      ENNReal.ofReal ((Real.exp (32 * beta)) ^ 2) *
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
  have hVariance :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedFirstVarianceEnergy_lintegral_le_harnackLawFactor_mul_reference_updatedBackgroundVarianceEnergy_lintegral_of_bounded
      H N hN beta hbeta B distinguishedSource source target hne k g₂
      F hF bound hbound left
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedFirstCrossEnergy_lintegral_eq_firstVariance_lintegral_add_responseL2_norm_sq_ofReal
      H N hN beta hbeta B distinguishedSource source target hne k g₂
      F hF bound hbound left]
  exact add_le_add_right hVariance _

end

end MGAP4D.MathlibAnalytic
