import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourcePairDirectDifferenceL2Energy
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSixSpatialSweepStageSourceUpdateDirectEnergyFubini
import Mathlib.Tactic

/-!
# Direct target-law L2 energy is bounded by the exact ordered direct energy

PR #4864 identifies the squared norm of the actual direct-difference L2 vector
with the source-pair-background integral of the squared physical direct mean
difference.

PR #4720 gives the coefficient-one pointwise Jensen/Cauchy estimate from that
mean difference to the exact target-fiber direct difference energy, while
PR #4730 identifies the corresponding source-pair-background energy average
exactly with the ordered direct average.

This file composes those facts without introducing a cardinality factor,
response term, arbitrary factor two, or stage-residual identification:

  ||directDifferenceL2(target,source)||^2
    <= orderedDirectAverageEnergy(target,source).

The only inequality is the already proved one-fiber probability-space
coefficient-one estimate.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

local instance directL2OrderedEnergySpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance directL2OrderedEnergySpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance directL2OrderedEnergySpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance directL2OrderedEnergySpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance directL2OrderedEnergySpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance directL2OrderedEnergySpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The actual source-pair direct-difference L2 energy is bounded with
coefficient one by the exact PR #4729/#4730 ordered direct average. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawDirectDifferenceL2_norm_sq_le_orderedDirectAverageEnergy
    (H N : ℕ) (hN : 0 < N)
    (beta : ℝ) (hbeta : 0 ≤ beta)
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
    (center : ℝ) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawDirectDifferenceL2
        H N hN beta hbeta B distinguishedSource source target k g₂
        F hF bound hbound left center‖ ^ 2 ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateOrderedDirectAverageEnergy
        H N hN beta hbeta target source F left B distinguishedSource k g₂ := by
  let pair :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceIndependentPairBackgroundMeasure
      H N hN beta hbeta B distinguishedSource source k g₂
  let q :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawDirectDifferenceL2
      H N hN beta hbeta B distinguishedSource source target k g₂
      F hF bound hbound left center
  let delta :=
    fun z :
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          (Matrix.specialUnitaryGroup (Fin N) ℂ ×
            Matrix.specialUnitaryGroup (Fin N) ℂ) =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateDirectMeanDifference
        H N hN beta hbeta target source hne F left B z.1
        (periodicHypercubicEvenSpatialSliceOffTargetRestriction target z.1)
        distinguishedSource k g₂ z.2.1 z.2.2 center
  let energy :=
    fun z :
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          (Matrix.specialUnitaryGroup (Fin N) ℂ ×
            Matrix.specialUnitaryGroup (Fin N) ℂ) =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateDirectDifferenceEnergy
        H N hN beta hbeta target source hne F left B z.1
        (periodicHypercubicEvenSpatialSliceOffTargetRestriction target z.1)
        distinguishedSource k g₂ z.2.1 z.2.2
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
  have hRep :
      (fun z => q z) =ᵐ[pair] delta := by
    simpa [q, pair, delta] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawDirectDifferenceL2_coeFn_semantic
        H N hN beta hbeta B distinguishedSource source target hne k g₂
        F hF bound hbound left center
  have hDeltaSq : Integrable (fun z => delta z ^ 2) pair := by
    have hqSq : Integrable (fun z => q z ^ 2) pair :=
      (Lp.memLp q).integrable_sq
    exact hqSq.congr (hRep.mono fun z hz => by rw [hz])
  have hJoint :
      Integrable directSq (pair ⊗ₘ κ) := by
    simpa [
      directSq, pair, κ,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairTargetFiberTripleMeasure] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateCanonicalTripleDirectDifferenceSquare_integrable
        H N hN beta hbeta target source hne F hF bound hbound
        left B distinguishedSource k g₂
  have hOuterNorm :
      Integrable
        (fun z => ∫ g, ‖directSq (z, g)‖ ∂κ z)
        pair := by
    exact
      ((Measure.integrable_compProd_iff hJoint.aestronglyMeasurable).mp hJoint).2
  have hOuter :
      Integrable
        (fun z => ∫ g, directSq (z, g) ∂κ z)
        pair := by
    apply hOuterNorm.congr
    filter_upwards with z
    apply integral_congr_ae
    filter_upwards with g
    have hNonneg : 0 ≤ directSq (z, g) := by
      dsimp [
        directSq,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateCanonicalTripleDirectDifferenceSquare]
      exact sq_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg hNonneg]
  have hInner :
      ∀ z,
        (∫ g, directSq (z, g) ∂κ z) = energy z := by
    intro z
    dsimp [directSq, energy]
    unfold
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateDirectDifferenceEnergy
    rw [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairTargetFiberKernel_apply
        H N hN beta hbeta B distinguishedSource source target k g₂ z]
    rfl
  have hEnergy : Integrable energy pair := by
    exact hOuter.congr (Filter.Eventually.of_forall hInner)
  have hPoint : ∀ z, delta z ^ 2 ≤ energy z := by
    intro z
    have hEnergyNonneg : 0 ≤ energy z := by
      dsimp [
        energy,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateDirectDifferenceEnergy]
      exact integral_nonneg fun g => sq_nonneg _
    have hRoot :
        |delta z| ≤ Real.sqrt (energy z) := by
      simpa [
        delta, energy,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateDirectMeanDifference] using
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSection_sourceUpdatedCenteredMean_direct_difference_le_sqrt_directDifferenceEnergy_of_bounded
          H N hN beta hbeta target source hne F hF bound hbound
          left B z.1
          (periodicHypercubicEvenSpatialSliceOffTargetRestriction target z.1)
          distinguishedSource k g₂ z.2.1 z.2.2 center
    have hSq :
        |delta z| ^ 2 ≤ (Real.sqrt (energy z)) ^ 2 :=
      (sq_le_sq₀ (abs_nonneg (delta z)) (Real.sqrt_nonneg (energy z))).2 hRoot
    rw [sq_abs, Real.sq_sqrt hEnergyNonneg] at hSq
    exact hSq
  have hIntegral :
      (∫ z, delta z ^ 2 ∂pair) ≤ ∫ z, energy z ∂pair :=
    integral_mono_ae hDeltaSq hEnergy
      (Filter.Eventually.of_forall hPoint)
  have hNorm :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawDirectDifferenceL2_norm_sq_eq_integral_directMeanDifference_sq
      H N hN beta hbeta B distinguishedSource source target hne k g₂
      F hF bound hbound left center
  have hOrdered :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdate_pairBackgroundDirectEnergyAverage_eq_orderedDirectAverage
      H N hN beta hbeta target source hne F hF bound hbound
      left B distinguishedSource k g₂
  calc
    ‖q‖ ^ 2 = ∫ z, delta z ^ 2 ∂pair := by
      simpa [q, delta, pair] using hNorm
    _ ≤ ∫ z, energy z ∂pair := hIntegral
    _ =
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateOrderedDirectAverageEnergy
          H N hN beta hbeta target source F left B distinguishedSource k g₂ := by
      simpa [energy, pair] using hOrdered

end

end MGAP4D.MathlibAnalytic
