import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourcePairOldVarianceHarnack
import Mathlib.Tactic

/-!
# Outer integration of the ordered Harnack variance comparison

PR #4787 proves the sharp pointwise comparison

  ofReal(oldVariance(C,v))
    <= ofReal((exp (32 beta))^2) * ofReal(updatedVariance(C,v)).

The Harnack factor is independent of the ordered outer point (C,v).  This file
integrates the pointwise inequality against the actual source-second-background
law and pulls the finite ENNReal scalar outside the lintegral.

No new measurability hypothesis, triangle inequality, factor two, response
coefficient, or cardinality factor is introduced.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

noncomputable section

local instance sourcePairOldVarianceHarnackOuterSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance sourcePairOldVarianceHarnackOuterSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance sourcePairOldVarianceHarnackOuterSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance sourcePairOldVarianceHarnackOuterSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance sourcePairOldVarianceHarnackOuterSpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance sourcePairOldVarianceHarnackOuterSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Integrate the pointwise old-to-updated target-variance Harnack comparison
over the ordered source/background law.  Since the Harnack factor is finite
and independent of the outer point, it exits the lintegral with coefficient
exactly one. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedFirstVarianceEnergy_lintegral_le_harnackLawFactor_mul_updatedVariance_lintegral_of_bounded
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
    (∫⁻ Cv,
      ENNReal.ofReal
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedFirstVarianceEnergy
          H N hN beta hbeta B distinguishedSource source target k g₂
          F left Cv)
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceSecondBackgroundMeasure
        H N hN beta hbeta B distinguishedSource source k g₂) ≤
      ENNReal.ofReal ((Real.exp (32 * beta)) ^ 2) *
        (∫⁻ Cv,
          ENNReal.ofReal
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedUpdatedVarianceEnergy
              H N hN beta hbeta B distinguishedSource source target k g₂
              F left Cv)
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceSecondBackgroundMeasure
            H N hN beta hbeta B distinguishedSource source k g₂) := by
  let rho :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceSecondBackgroundMeasure
      H N hN beta hbeta B distinguishedSource source k g₂
  let harnackFactor : ℝ≥0∞ :=
    ENNReal.ofReal ((Real.exp (32 * beta)) ^ 2)
  let oldVariance :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ≥0∞ :=
    fun Cv =>
      ENNReal.ofReal
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedFirstVarianceEnergy
          H N hN beta hbeta B distinguishedSource source target k g₂
          F left Cv)
  let updatedVariance :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ≥0∞ :=
    fun Cv =>
      ENNReal.ofReal
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedUpdatedVarianceEnergy
          H N hN beta hbeta B distinguishedSource source target k g₂
          F left Cv)
  have hPointwise : ∀ Cv, oldVariance Cv ≤ harnackFactor * updatedVariance Cv := by
    intro Cv
    simpa [oldVariance, updatedVariance, harnackFactor] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedFirstVarianceEnergy_ofReal_le_harnackLawFactor_mul_updatedVariance_of_bounded
        H N hN beta hbeta B distinguishedSource source target hne k g₂
        F hF bound hbound left Cv
  have hIntegrated :
      (∫⁻ Cv, oldVariance Cv ∂rho) ≤
        harnackFactor * ∫⁻ Cv, updatedVariance Cv ∂rho := by
    calc
      (∫⁻ Cv, oldVariance Cv ∂rho) ≤
          ∫⁻ Cv, harnackFactor * updatedVariance Cv ∂rho :=
        lintegral_mono hPointwise
      _ = harnackFactor * ∫⁻ Cv, updatedVariance Cv ∂rho := by
        rw [lintegral_const_mul']
        simp [harnackFactor]
  simpa [rho, oldVariance, updatedVariance, harnackFactor] using hIntegrated

end

end MGAP4D.MathlibAnalytic
