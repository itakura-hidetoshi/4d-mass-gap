import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourcePairCrossEnergyResponseL2Split
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceBackgroundUpdateVarianceComparison
import Mathlib.Tactic

/-!
# Harnack comparison of ordered old and updated target-fiber variance

PR #4785 leaves exactly one new term in the global first-cross energy:
the old-target-law variance on ordered coordinates (C,v).

PR #4786 exposes the sharp background-update variance comparison for the
actual continuous-vacuum one-link fiber laws.

At an ordered point (C,v), the frozen target section is

  X_v(g) = F(left, C[source <- v][target <- g]).

The old variance samples X_v under the target law based at C.  The updated
variance samples the same X_v under the target law based at C[source <- v].
This file proves the pointwise comparison

  ofReal(oldVariance(C,v))
    <= ofReal((exp (32 beta))^2) * ofReal(updatedVariance(C,v)).

No triangle inequality, factor two, response coefficient, or cardinality
factor is introduced.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

noncomputable section

local instance sourcePairOldVarianceHarnackSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance sourcePairOldVarianceHarnackSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance sourcePairOldVarianceHarnackSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance sourcePairOldVarianceHarnackSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance sourcePairOldVarianceHarnackSpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance sourcePairOldVarianceHarnackSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Literal old-target-law mean of the frozen section on ordered coordinates. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedFirstFiberMean_eq_literal
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource source target :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (left : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (Cv :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedFirstFiberMean
        H N hN beta hbeta B distinguishedSource source target k g₂
        F left Cv =
      ∫ g,
        F
          (left,
            Function.update
              (Function.update Cv.1 source Cv.2)
              target g)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
          H N hN beta hbeta B source distinguishedSource target k g₂ Cv.1 := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedFirstFiberMean
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFirstMean
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairTargetFiberKernel_apply]
  simp only [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairOrderedSection]
  rw [Function.update_eq_self source Cv.1]
  apply integral_congr_ae
  filter_upwards with g
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawCenteredSection
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairSecondUpdatedBackground
  rw [
    periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection_offTargetRestriction_eq_update]
  simp

/-- Updated-target-law variance of the same frozen ordered section, centered at
its own updated-law mean. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedUpdatedVarianceEnergy
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource source target :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (left : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (Cv :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondCenteredEnergy
    H N hN beta hbeta B distinguishedSource source target k g₂
    F left
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedSecondFiberMean
      H N hN beta hbeta B distinguishedSource source target k g₂
      F left Cv)
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairOrderedSection
      H N source Cv)

/-- Pointwise Harnack comparison of the ordered old-target variance with the
updated-background target variance. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedFirstVarianceEnergy_ofReal_le_harnackLawFactor_mul_updatedVariance_of_bounded
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
    (left : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (Cv :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        Matrix.specialUnitaryGroup (Fin N) ℂ) :
    ENNReal.ofReal
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedFirstVarianceEnergy
          H N hN beta hbeta B distinguishedSource source target k g₂
          F left Cv) ≤
      ENNReal.ofReal ((Real.exp (32 * beta)) ^ 2) *
        ENNReal.ofReal
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedUpdatedVarianceEnergy
            H N hN beta hbeta B distinguishedSource source target k g₂
            F left Cv) := by
  let X : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ :=
    fun g =>
      F
        (left,
          Function.update
            (Function.update Cv.1 source Cv.2)
            target g)
  let μOld :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
      H N hN beta hbeta B source distinguishedSource target k g₂ Cv.1
  let μNew :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
      H N hN beta hbeta B source distinguishedSource target k g₂
      (Function.update Cv.1 source Cv.2)
  letI : IsProbabilityMeasure μOld :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_isProbabilityMeasure
      H N hN beta hbeta B source distinguishedSource target k g₂ Cv.1
  letI : IsProbabilityMeasure μNew :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_isProbabilityMeasure
      H N hN beta hbeta B source distinguishedSource target k g₂
      (Function.update Cv.1 source Cv.2)
  have hRight :
      Measurable
        (fun g : Matrix.specialUnitaryGroup (Fin N) ℂ =>
          Function.update
            (Function.update Cv.1 source Cv.2)
            target g) :=
    measurable_update _
  have hXStrong : StronglyMeasurable X := by
    exact hF.comp_measurable (measurable_const.prodMk hRight)
  have hXBound : ∀ g, ‖X g‖ ≤ |bound| := by
    intro g
    exact (hbound _).trans (le_abs_self bound)
  have hXOld : MemLp X 2 μOld :=
    MemLp.of_bound hXStrong.aestronglyMeasurable |bound|
      (Filter.Eventually.of_forall hXBound)
  have hXNew : MemLp X 2 μNew :=
    MemLp.of_bound hXStrong.aestronglyMeasurable |bound|
      (Filter.Eventually.of_forall hXBound)
  have hOldMean :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedFirstFiberMean
          H N hN beta hbeta B distinguishedSource source target k g₂
          F left Cv =
        ∫ g, X g ∂μOld := by
    simpa [X, μOld] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedFirstFiberMean_eq_literal
        H N hN beta hbeta B distinguishedSource source target k g₂
        F left Cv
  have hNewMean :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedSecondFiberMean
          H N hN beta hbeta B distinguishedSource source target k g₂
          F left Cv =
        ∫ g, X g ∂μNew := by
    simpa [X, μNew] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedSecondFiberMean_eq_literal
        H N hN beta hbeta B distinguishedSource source target k g₂
        F left Cv
  have hOldEnergy :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedFirstVarianceEnergy
          H N hN beta hbeta B distinguishedSource source target k g₂
          F left Cv =
        ∫ g,
          (X g -
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedFirstFiberMean
              H N hN beta hbeta B distinguishedSource source target k g₂
              F left Cv) ^ 2
          ∂μOld := by
    unfold
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedFirstVarianceEnergy
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFirstCenteredEnergy
    rw [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairTargetFiberKernel_apply]
    simp [
      X, μOld,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairFirstUpdatedBackground,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairOrderedSection,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawCenteredSection,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairSecondUpdatedBackground,
      periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection_offTargetRestriction_eq_update,
      Function.update_eq_self]
  have hNewEnergy :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedUpdatedVarianceEnergy
          H N hN beta hbeta B distinguishedSource source target k g₂
          F left Cv =
        ∫ g,
          (X g -
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedSecondFiberMean
              H N hN beta hbeta B distinguishedSource source target k g₂
              F left Cv) ^ 2
          ∂μNew := by
    unfold
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedUpdatedVarianceEnergy
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondCenteredEnergy
    rw [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairSecondTargetFiberKernel_apply]
    simp [
      X, μNew,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairOrderedSection,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawCenteredSection,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairSecondUpdatedBackground,
      periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection_offTargetRestriction_eq_update]
  have hOldVar :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedFirstVarianceEnergy
          H N hN beta hbeta B distinguishedSource source target k g₂
          F left Cv =
        variance X μOld := by
    rw [hOldEnergy, hOldMean]
    exact (variance_eq_integral hXStrong.aemeasurable).symm
  have hNewVar :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedUpdatedVarianceEnergy
          H N hN beta hbeta B distinguishedSource source target k g₂
          F left Cv =
        variance X μNew := by
    rw [hNewEnergy, hNewMean]
    exact (variance_eq_integral hXStrong.aemeasurable).symm
  have hOldOf :
      ENNReal.ofReal
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedFirstVarianceEnergy
            H N hN beta hbeta B distinguishedSource source target k g₂
            F left Cv) =
        evariance X μOld := by
    rw [hOldVar]
    exact hXOld.ofReal_variance_eq
  have hNewOf :
      ENNReal.ofReal
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedUpdatedVarianceEnergy
            H N hN beta hbeta B distinguishedSource source target k g₂
            F left Cv) =
        evariance X μNew := by
    rw [hNewVar]
    exact hXNew.ofReal_variance_eq
  have hXRaw :
      MemLp X 2
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
          H N hN beta hbeta B source distinguishedSource target k g₂
          (Function.update Cv.1 source (Cv.1 source))) := by
    simpa [μOld, Function.update_eq_self source Cv.1] using hXOld
  have hCompareRaw :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_backgroundUpdate_evariance_le_harnackLawFactor_mul
      H N hN beta hbeta B source distinguishedSource target source hne
      k g₂ (Cv.1 source) Cv.2 Cv.1 X hXRaw
  have hCompare :
      evariance X μOld ≤
        ENNReal.ofReal ((Real.exp (32 * beta)) ^ 2) *
          evariance X μNew := by
    simpa [μOld, μNew, Function.update_eq_self source Cv.1] using hCompareRaw
  calc
    ENNReal.ofReal
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedFirstVarianceEnergy
          H N hN beta hbeta B distinguishedSource source target k g₂
          F left Cv) =
      evariance X μOld := hOldOf
    _ ≤ ENNReal.ofReal ((Real.exp (32 * beta)) ^ 2) *
        evariance X μNew := hCompare
    _ =
      ENNReal.ofReal ((Real.exp (32 * beta)) ^ 2) *
        ENNReal.ofReal
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedUpdatedVarianceEnergy
            H N hN beta hbeta B distinguishedSource source target k g₂
            F left Cv) := by
      rw [hNewOf]

end

end MGAP4D.MathlibAnalytic
