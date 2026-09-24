import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSixSpatialSweepStageSourceUpdateCanonicalDirectEnergy
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointOneLinkSplitDirectFiberBridge
import Mathlib.Tactic

/-!
# Exact averaged direct energy under the reordered physical law

PR #4727 proves the exact pushforward identity

  ((A,u,v),g) |-> ((A[source <- u],v),g)

from the physical source-pair / target-fiber triple law to the ordered law

  mu_source(dC) kappa_source(C)(dv) kappa_target(C)(dg).

PR #4728 proves the corresponding pointwise coordinate identity for the direct
source-update square.

This file lifts those two exact facts to the averaged direct square.  No Fubini
order is silently changed: the equality is obtained by the already-proved
measure pushforward and Mathlib's integral-under-map theorem.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory Set
open scoped ENNReal

noncomputable section

local instance orderedDirectAverageSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance orderedDirectAverageSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance orderedDirectAverageSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance orderedDirectAverageSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance orderedDirectAverageSpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance orderedDirectAverageSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The ordered direct square is literally the source-coordinate square
computed on two complete configurations which share the same target value
`g`.

This form is useful because all measurability is then ordinary measurability of
finite-coordinate updates of the bounded-concrete representative. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateOrderedDirectDifferenceSquare_eq_fullUpdates
    (H N : ℕ)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (left C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (v g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateOrderedDirectDifferenceSquare
        H N target source F left C v g =
      (F (left, Function.update C target g) -
        F (left,
          Function.update (Function.update C source v) target g)) ^ 2 := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateOrderedDirectDifferenceSquare
    periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
  rw [
    periodicHypercubicEvenSpatialSliceTargetOffTarget_symm_offTargetRestriction_eq_update,
    periodicHypercubicEvenSpatialSliceTargetOffTarget_symm_offTargetRestriction_eq_update]
  simp

/-- Joint strong measurability of the ordered direct square in `((C,v),g)`. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateOrderedDirectDifferenceSquare_stronglyMeasurable
    (H N : ℕ)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (left : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    StronglyMeasurable
      (fun Cvg :
          ((PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
              Matrix.specialUnitaryGroup (Fin N) ℂ) ×
            Matrix.specialUnitaryGroup (Fin N) ℂ) =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateOrderedDirectDifferenceSquare
          H N target source F left Cvg.1.1 Cvg.1.2 Cvg.2) := by
  let firstInput :
      ((PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          Matrix.specialUnitaryGroup (Fin N) ℂ) ×
        Matrix.specialUnitaryGroup (Fin N) ℂ) →
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          Matrix.specialUnitaryGroup (Fin N) ℂ) :=
    fun z => (z.1.1, z.2)
  let sourceInput :
      ((PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          Matrix.specialUnitaryGroup (Fin N) ℂ) ×
        Matrix.specialUnitaryGroup (Fin N) ℂ) →
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          Matrix.specialUnitaryGroup (Fin N) ℂ) :=
    fun z => (z.1.1, z.1.2)
  have hFirstInput : Measurable firstInput :=
    (measurable_fst.comp measurable_fst).prodMk measurable_snd
  have hSourceInput : Measurable sourceInput :=
    (measurable_fst.comp measurable_fst).prodMk
      (measurable_snd.comp measurable_fst)
  have hSourceUpdated : Measurable
      (fun z :
          ((PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
              Matrix.specialUnitaryGroup (Fin N) ℂ) ×
            Matrix.specialUnitaryGroup (Fin N) ℂ) =>
        Function.update z.1.1 source z.1.2) := by
    exact
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkUpdate_uncurry_measurable
        H N source).comp hSourceInput
  have hFirstRight : Measurable
      (fun z :
          ((PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
              Matrix.specialUnitaryGroup (Fin N) ℂ) ×
            Matrix.specialUnitaryGroup (Fin N) ℂ) =>
        Function.update z.1.1 target z.2) := by
    exact
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkUpdate_uncurry_measurable
        H N target).comp hFirstInput
  have hSecondInput : Measurable
      (fun z :
          ((PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
              Matrix.specialUnitaryGroup (Fin N) ℂ) ×
            Matrix.specialUnitaryGroup (Fin N) ℂ) =>
        (Function.update z.1.1 source z.1.2, z.2)) :=
    hSourceUpdated.prodMk measurable_snd
  have hSecondRight : Measurable
      (fun z :
          ((PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
              Matrix.specialUnitaryGroup (Fin N) ℂ) ×
            Matrix.specialUnitaryGroup (Fin N) ℂ) =>
        Function.update (Function.update z.1.1 source z.1.2) target z.2) := by
    exact
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkUpdate_uncurry_measurable
        H N target).comp hSecondInput
  have hFirstF : StronglyMeasurable
      (fun z :
          ((PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
              Matrix.specialUnitaryGroup (Fin N) ℂ) ×
            Matrix.specialUnitaryGroup (Fin N) ℂ) =>
        F (left, Function.update z.1.1 target z.2)) :=
    hF.comp_measurable (measurable_const.prodMk hFirstRight)
  have hSecondF : StronglyMeasurable
      (fun z :
          ((PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
              Matrix.specialUnitaryGroup (Fin N) ℂ) ×
            Matrix.specialUnitaryGroup (Fin N) ℂ) =>
        F (left,
          Function.update (Function.update z.1.1 source z.1.2) target z.2)) :=
    hF.comp_measurable (measurable_const.prodMk hSecondRight)
  have hSquare : StronglyMeasurable
      (fun z :
          ((PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
              Matrix.specialUnitaryGroup (Fin N) ℂ) ×
            Matrix.specialUnitaryGroup (Fin N) ℂ) =>
        (F (left, Function.update z.1.1 target z.2) -
          F (left,
            Function.update (Function.update z.1.1 source z.1.2) target z.2)) ^ 2) := by
    have hDiff := hFirstF.sub hSecondF
    simpa [pow_two] using hDiff.mul hDiff
  have hEq :
      (fun z :
          ((PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
              Matrix.specialUnitaryGroup (Fin N) ℂ) ×
            Matrix.specialUnitaryGroup (Fin N) ℂ) =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateOrderedDirectDifferenceSquare
          H N target source F left z.1.1 z.1.2 z.2) =
      (fun z =>
        (F (left, Function.update z.1.1 target z.2) -
          F (left,
            Function.update (Function.update z.1.1 source z.1.2) target z.2)) ^ 2) := by
    funext z
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateOrderedDirectDifferenceSquare_eq_fullUpdates
        H N target source F left z.1.1 z.1.2 z.2
  rw [hEq]
  exact hSquare

/-- Canonical direct square on the original PR #4725 triple-law coordinates
`((A,(u,v)),g)`. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateCanonicalTripleDirectDifferenceSquare
    (H N : ℕ)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (hne : target ≠ source)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (left : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (zg :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          (Matrix.specialUnitaryGroup (Fin N) ℂ ×
            Matrix.specialUnitaryGroup (Fin N) ℂ)) ×
        Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ :=
  (periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
      H N target F left
      (periodicHypercubicEvenSpatialSliceOffTargetSourceUpdate
        target source hne
        (periodicHypercubicEvenSpatialSliceOffTargetRestriction target zg.1.1)
        zg.1.2.1)
      zg.2 -
    periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
      H N target F left
      (periodicHypercubicEvenSpatialSliceOffTargetSourceUpdate
        target source hne
        (periodicHypercubicEvenSpatialSliceOffTargetRestriction target zg.1.1)
        zg.1.2.2)
      zg.2) ^ 2

/-- The original triple-law direct square is pointwise the ordered square after
the PR #4727 reordering map. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateCanonicalTripleDirectDifferenceSquare_eq_ordered
    (H N : ℕ)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (hne : target ≠ source)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (left : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (zg :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          (Matrix.specialUnitaryGroup (Fin N) ℂ ×
            Matrix.specialUnitaryGroup (Fin N) ℂ)) ×
        Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateCanonicalTripleDirectDifferenceSquare
        H N target source hne F left zg =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateOrderedDirectDifferenceSquare
        H N target source F left
        (Function.update zg.1.1 source zg.1.2.1)
        zg.1.2.2 zg.2 := by
  simpa [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateCanonicalTripleDirectDifferenceSquare] using
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSection_sourceUpdateCanonicalRetained_square_eq_ordered
      H N target source hne F left zg.1.1 zg.1.2.1 zg.1.2.2 zg.2

/-- Averaged ordered direct square under the exact PR #4727 law

  mu_source(dC) kappa_source(C)(dv) kappa_target(C)(dg).
-/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateOrderedDirectAverageEnergy
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (left B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ :=
  ∫ Cvg,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateOrderedDirectDifferenceSquare
      H N target source F left Cvg.1.1 Cvg.1.2 Cvg.2
    ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceSecondTargetOrderedMeasure
      H N hN beta hbeta B distinguishedSource source target k g₂

/-- The exact triple-law average of the canonical direct square equals the
ordered direct average energy.

This is a pure change-of-variables theorem through the exact pushforward from
PR #4727.  No source/target kernel commutativity is used. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateCanonicalTripleDirectAverage_eq_ordered
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (hne : target ≠ source)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (left B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    (∫ zg,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateCanonicalTripleDirectDifferenceSquare
        H N target source hne F left zg
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairTargetFiberTripleMeasure
        H N hN beta hbeta B distinguishedSource source target k g₂) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateOrderedDirectAverageEnergy
        H N hN beta hbeta target source F left B distinguishedSource k g₂ := by
  let reorder :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairTargetFiberReorderedMap
      H N source
  let triple :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairTargetFiberTripleMeasure
      H N hN beta hbeta B distinguishedSource source target k g₂
  let ordered :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceSecondTargetOrderedMeasure
      H N hN beta hbeta B distinguishedSource source target k g₂
  let square :=
    fun Cvg :
      ((PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          Matrix.specialUnitaryGroup (Fin N) ℂ) ×
        Matrix.specialUnitaryGroup (Fin N) ℂ) =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateOrderedDirectDifferenceSquare
        H N target source F left Cvg.1.1 Cvg.1.2 Cvg.2
  have hReorder : Measurable reorder :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairTargetFiberReorderedMap_measurable
      H N source
  have hSquare : StronglyMeasurable square := by
    simpa [square] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateOrderedDirectDifferenceSquare_stronglyMeasurable
        H N target source F hF left
  have hMap : Measure.map reorder triple = ordered := by
    simpa [reorder, triple, ordered] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairTargetFiberTripleMeasure_map_reordered
        H N hN beta hbeta B distinguishedSource source target k g₂
  calc
    (∫ zg,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateCanonicalTripleDirectDifferenceSquare
        H N target source hne F left zg ∂triple) =
      ∫ zg, square (reorder zg) ∂triple := by
        apply integral_congr_ae
        filter_upwards with zg
        simpa [square, reorder] using
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateCanonicalTripleDirectDifferenceSquare_eq_ordered
            H N target source hne F left zg
    _ = ∫ Cvg, square Cvg ∂Measure.map reorder triple := by
      symm
      exact
        MeasureTheory.integral_map hReorder.aemeasurable hSquare.aestronglyMeasurable
    _ = ∫ Cvg, square Cvg ∂ordered := by rw [hMap]
    _ =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateOrderedDirectAverageEnergy
        H N hN beta hbeta target source F left B distinguishedSource k g₂ := by
      rfl

/-- The ordered direct average is nonnegative. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateOrderedDirectAverageEnergy_nonneg
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (left B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    0 ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateOrderedDirectAverageEnergy
        H N hN beta hbeta target source F left B distinguishedSource k g₂ := by
  apply integral_nonneg
  intro Cvg
  exact sq_nonneg _

end

end MGAP4D.MathlibAnalytic
