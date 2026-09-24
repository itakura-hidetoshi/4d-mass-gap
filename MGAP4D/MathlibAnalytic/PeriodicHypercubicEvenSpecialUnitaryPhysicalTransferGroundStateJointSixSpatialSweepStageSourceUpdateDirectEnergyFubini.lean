import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSixSpatialSweepStageSourceUpdateOrderedDirectAverage
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Tactic

/-!
# Fubini identification of the averaged direct source-update energy

PR #4729 identifies the averaged canonical direct square on the explicit
source-pair / target-fiber triple law with the ordered-law average.

This file performs the remaining real-integral Fubini step.  For a bounded
strongly measurable concrete representative, the canonical triple square is
integrable.  Therefore its triple-law integral is exactly the source-pair /
background average of the PR #4720 direct difference energy.

Combining with PR #4729 gives the exact identity

  average_{nu_source} E_direct(A,u,v)
    = orderedDirectAverage.

No source/target heat-bath commutation and no change of coefficient is used.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

noncomputable section

local instance directEnergyFubiniSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance directEnergyFubiniSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance directEnergyFubiniSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance directEnergyFubiniSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance directEnergyFubiniSpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance directEnergyFubiniSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The ordered direct square has the uniform bound inherited from a bounded
concrete representative. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateOrderedDirectDifferenceSquare_norm_le
    (H N : ℕ)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound)
    (left C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (v g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateOrderedDirectDifferenceSquare
        H N target source F left C v g‖ ≤
      (2 * |bound|) ^ 2 := by
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateOrderedDirectDifferenceSquare_eq_fullUpdates]
  let x := F (left, Function.update C target g)
  let y := F
    (left, Function.update (Function.update C source v) target g)
  have hx0 : |x| ≤ bound := by
    simpa [x, Real.norm_eq_abs] using
      hbound (left, Function.update C target g)
  have hy0 : |y| ≤ bound := by
    simpa [y, Real.norm_eq_abs] using
      hbound
        (left, Function.update (Function.update C source v) target g)
  have hx : |x| ≤ |bound| :=
    hx0.trans (le_abs_self bound)
  have hy : |y| ≤ |bound| :=
    hy0.trans (le_abs_self bound)
  have hdiff : |x - y| ≤ 2 * |bound| := by
    calc
      |x - y| ≤ |x| + |y| := abs_sub x y
      _ ≤ |bound| + |bound| := add_le_add hx hy
      _ = 2 * |bound| := by ring
  have hright : 0 ≤ 2 * |bound| :=
    mul_nonneg (by norm_num) (abs_nonneg bound)
  have hsq :
      |x - y| ^ 2 ≤ (2 * |bound|) ^ 2 :=
    (sq_le_sq₀ (abs_nonneg (x - y)) hright).2 hdiff
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (x - y))]
  simpa [x, y, sq_abs] using hsq

/-- The ordered direct square is integrable under the exact ordered
source/target law. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateOrderedDirectDifferenceSquare_integrable
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound)
    (left B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    Integrable
      (fun Cvg :
          ((PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
              Matrix.specialUnitaryGroup (Fin N) ℂ) ×
            Matrix.specialUnitaryGroup (Fin N) ℂ) =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateOrderedDirectDifferenceSquare
          H N target source F left Cvg.1.1 Cvg.1.2 Cvg.2)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceSecondTargetOrderedMeasure
        H N hN beta hbeta B distinguishedSource source target k g₂) := by
  let μ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceSecondTargetOrderedMeasure
      H N hN beta hbeta B distinguishedSource source target k g₂
  letI : IsProbabilityMeasure μ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceSecondTargetOrderedMeasure_isProbabilityMeasure
      H N hN beta hbeta B distinguishedSource source target k g₂
  have hSM :
      StronglyMeasurable
        (fun Cvg :
            ((PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
                Matrix.specialUnitaryGroup (Fin N) ℂ) ×
              Matrix.specialUnitaryGroup (Fin N) ℂ) =>
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateOrderedDirectDifferenceSquare
            H N target source F left Cvg.1.1 Cvg.1.2 Cvg.2) :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateOrderedDirectDifferenceSquare_stronglyMeasurable
      H N target source F hF left
  refine Integrable.mono'
    (integrable_const ((2 * |bound|) ^ 2))
    hSM.aestronglyMeasurable ?_
  filter_upwards with Cvg
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateOrderedDirectDifferenceSquare_norm_le
      H N target source F bound hbound left Cvg.1.1 Cvg.1.2 Cvg.2

/-- The canonical triple direct square is strongly measurable, by transport
through the exact reordering map. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateCanonicalTripleDirectDifferenceSquare_stronglyMeasurable
    (H N : ℕ)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (hne : target ≠ source)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (left : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    StronglyMeasurable
      (fun zg :
          (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
              (Matrix.specialUnitaryGroup (Fin N) ℂ ×
                Matrix.specialUnitaryGroup (Fin N) ℂ)) ×
            Matrix.specialUnitaryGroup (Fin N) ℂ =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateCanonicalTripleDirectDifferenceSquare
          H N target source hne F left zg) := by
  let reorder :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairTargetFiberReorderedMap
      H N source
  let square :=
    fun Cvg :
      ((PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          Matrix.specialUnitaryGroup (Fin N) ℂ) ×
        Matrix.specialUnitaryGroup (Fin N) ℂ) =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateOrderedDirectDifferenceSquare
        H N target source F left Cvg.1.1 Cvg.1.2 Cvg.2
  have hSquare : StronglyMeasurable square := by
    simpa [square] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateOrderedDirectDifferenceSquare_stronglyMeasurable
        H N target source F hF left
  have hComp : StronglyMeasurable (fun zg => square (reorder zg)) :=
    hSquare.comp_measurable
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairTargetFiberReorderedMap_measurable
        H N source)
  have hEq :
      (fun zg :
          (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
              (Matrix.specialUnitaryGroup (Fin N) ℂ ×
                Matrix.specialUnitaryGroup (Fin N) ℂ)) ×
            Matrix.specialUnitaryGroup (Fin N) ℂ =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateCanonicalTripleDirectDifferenceSquare
          H N target source hne F left zg) =
        fun zg => square (reorder zg) := by
    funext zg
    simpa [square, reorder] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateCanonicalTripleDirectDifferenceSquare_eq_ordered
        H N target source hne F left zg
  rw [hEq]
  exact hComp

/-- The canonical triple direct square is integrable under the explicit triple
law. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateCanonicalTripleDirectDifferenceSquare_integrable
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (hne : target ≠ source)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound)
    (left B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    Integrable
      (fun zg :
          (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
              (Matrix.specialUnitaryGroup (Fin N) ℂ ×
                Matrix.specialUnitaryGroup (Fin N) ℂ)) ×
            Matrix.specialUnitaryGroup (Fin N) ℂ =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateCanonicalTripleDirectDifferenceSquare
          H N target source hne F left zg)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairTargetFiberTripleMeasure
        H N hN beta hbeta B distinguishedSource source target k g₂) := by
  let μ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairTargetFiberTripleMeasure
      H N hN beta hbeta B distinguishedSource source target k g₂
  letI : IsProbabilityMeasure μ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairTargetFiberTripleMeasure_isProbabilityMeasure
      H N hN beta hbeta B distinguishedSource source target k g₂
  have hSM :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateCanonicalTripleDirectDifferenceSquare_stronglyMeasurable
      H N target source hne F hF left
  refine Integrable.mono'
    (integrable_const ((2 * |bound|) ^ 2))
    hSM.aestronglyMeasurable ?_
  filter_upwards with zg
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateCanonicalTripleDirectDifferenceSquare_eq_ordered
      H N target source hne F left zg]
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateOrderedDirectDifferenceSquare_norm_le
      H N target source F bound hbound left
      (Function.update zg.1.1 source zg.1.2.1) zg.1.2.2 zg.2

/-- Fubini identifies the canonical triple-square average with the
source-pair/background average of the PR #4720 direct difference energy. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateCanonicalTripleDirectAverage_eq_pairBackgroundDirectEnergyAverage
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (hne : target ≠ source)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound)
    (left B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    (∫ zg,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateCanonicalTripleDirectDifferenceSquare
        H N target source hne F left zg
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairTargetFiberTripleMeasure
        H N hN beta hbeta B distinguishedSource source target k g₂) =
      ∫ z,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateDirectDifferenceEnergy
          H N hN beta hbeta target source hne F left B z.1
          (periodicHypercubicEvenSpatialSliceOffTargetRestriction target z.1)
          distinguishedSource k g₂ z.2.1 z.2.2
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceIndependentPairBackgroundMeasure
          H N hN beta hbeta B distinguishedSource source k g₂ := by
  let triple :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairTargetFiberTripleMeasure
      H N hN beta hbeta B distinguishedSource source target k g₂
  let pair :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceIndependentPairBackgroundMeasure
      H N hN beta hbeta B distinguishedSource source k g₂
  let κ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairTargetFiberKernel
      H N hN beta hbeta B distinguishedSource source target k g₂
  let directSq :=
    fun zg :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          (Matrix.specialUnitaryGroup (Fin N) ℂ ×
            Matrix.specialUnitaryGroup (Fin N) ℂ)) ×
        Matrix.specialUnitaryGroup (Fin N) ℂ =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateCanonicalTripleDirectDifferenceSquare
        H N target source hne F left zg
  have hInt : Integrable directSq triple := by
    simpa [directSq, triple] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateCanonicalTripleDirectDifferenceSquare_integrable
        H N hN beta hbeta target source hne F hF bound hbound
        left B distinguishedSource k g₂
  have hIntComp :
      Integrable directSq (pair ⊗ₘ κ) := by
    simpa [triple, pair, κ,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairTargetFiberTripleMeasure]
      using hInt
  have hFubini :
      (∫ zg, directSq zg ∂triple) =
        ∫ z, ∫ g, directSq (z, g) ∂κ z ∂pair := by
    have hComp := Measure.integral_compProd hIntComp
    simpa [triple, pair, κ,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairTargetFiberTripleMeasure]
      using hComp
  calc
    (∫ zg,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateCanonicalTripleDirectDifferenceSquare
        H N target source hne F left zg ∂triple) =
      ∫ z, ∫ g, directSq (z, g) ∂κ z ∂pair := by
        simpa [directSq] using hFubini
    _ = ∫ z,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateDirectDifferenceEnergy
          H N hN beta hbeta target source hne F left B z.1
          (periodicHypercubicEvenSpatialSliceOffTargetRestriction target z.1)
          distinguishedSource k g₂ z.2.1 z.2.2
        ∂pair := by
      apply integral_congr_ae
      filter_upwards with z
      rw [
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairTargetFiberKernel_apply]
      rfl

/-- Main exact law-ordering identity for the PR #4720 energy itself. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdate_pairBackgroundDirectEnergyAverage_eq_orderedDirectAverage
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (hne : target ≠ source)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound)
    (left B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    (∫ z,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateDirectDifferenceEnergy
        H N hN beta hbeta target source hne F left B z.1
        (periodicHypercubicEvenSpatialSliceOffTargetRestriction target z.1)
        distinguishedSource k g₂ z.2.1 z.2.2
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceIndependentPairBackgroundMeasure
        H N hN beta hbeta B distinguishedSource source k g₂) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateOrderedDirectAverageEnergy
        H N hN beta hbeta target source F left B distinguishedSource k g₂ := by
  calc
    (∫ z,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateDirectDifferenceEnergy
        H N hN beta hbeta target source hne F left B z.1
        (periodicHypercubicEvenSpatialSliceOffTargetRestriction target z.1)
        distinguishedSource k g₂ z.2.1 z.2.2
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceIndependentPairBackgroundMeasure
        H N hN beta hbeta B distinguishedSource source k g₂) =
      ∫ zg,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateCanonicalTripleDirectDifferenceSquare
          H N target source hne F left zg
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairTargetFiberTripleMeasure
          H N hN beta hbeta B distinguishedSource source target k g₂ := by
      symm
      exact
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateCanonicalTripleDirectAverage_eq_pairBackgroundDirectEnergyAverage
          H N hN beta hbeta target source hne F hF bound hbound
          left B distinguishedSource k g₂
    _ =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateOrderedDirectAverageEnergy
        H N hN beta hbeta target source F left B distinguishedSource k g₂ :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateCanonicalTripleDirectAverage_eq_ordered
        H N hN beta hbeta target source hne F hF
        left B distinguishedSource k g₂

end

end MGAP4D.MathlibAnalytic
