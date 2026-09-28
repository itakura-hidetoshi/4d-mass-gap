import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSweepBlockDefectCyclicSecondVisit
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointBoundedConcreteOneLinkSweepInvariance
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointCanonicalResidualSweepStagePrefixWitness
import Mathlib.Tactic

/-!
# Bounded concrete representatives on the cyclic second-visit carrier

PR #4894 identifies the vector immediately before the second visit to a fixed
target link `e` with the first post-`e` vector propagated through the cyclic
between-visits order

  suffix ++ pre.

The response machinery is formulated for bounded strongly measurable concrete
representatives.  This file closes that compatibility point.

Because every finite same-color one-link sweep preserves the bounded concrete
core, the first terminal sweep vector `S_c f` remains in that core.  We can
therefore reapply the canonical-prefix representative theorem to `S_c f`.
PR #4894 then rewrites the selected second-sweep stage representative exactly
as the cyclic between-visits state.

The result is packaged first for one fixed-color target, then for an ordinary
spatial link, and finally simultaneously for the full finite spatial-link
family.

No response estimate, commutativity assumption, symmetry assumption,
finite-cardinality factor, or new coefficient is introduced.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

local instance cyclicSecondVisitRepresentativeSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance cyclicSecondVisitRepresentativeSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- For one fixed-color target, choose the canonical second-sweep stage
representative and identify it exactly with the cyclic between-visits state
`suffix ++ pre` applied after the first visit to `e`. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSecondSweep_exists_boundedRepresentative_cyclicPrefixWitness
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor)
    (e : PeriodicHypercubicEvenFixedSpatialColorLink H color)
    (f :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta)
    (hf :
      f ∈
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore
          H N hN beta hbeta) :
    ∃
      (pre suffix :
        List (PeriodicHypercubicEvenFixedSpatialColorLink H color))
      (F :
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
      (hF : StronglyMeasurable F)
      (bound : ℝ)
      (hbound : ∀ z, ‖F z‖ ≤ bound),
      (Finset.univ :
        Finset (PeriodicHypercubicEvenFixedSpatialColorLink H color)).toList =
          pre ++ e :: suffix ∧
      e ∉ pre ∧
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
          H N hN beta hbeta F hF bound hbound =
        realHilbertProjectionSweep
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
            H N hN beta hbeta color)
          (suffix ++ pre)
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
            H N hN beta hbeta color e
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepStageVector
              H N hN beta hbeta color pre f)) ∧
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMeanResidualL2
          H N hN beta hbeta e.1 F hF bound hbound‖ ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepStageLocalProfile
          H N hN beta hbeta color
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkFullSweepVector
            H N hN beta hbeta color f) e := by
  let S :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkFullSweepVector
      H N hN beta hbeta color f
  have hSCore :
      S ∈
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore
          H N hN beta hbeta := by
    unfold
      S
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkFullSweepVector
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweep_mem_boundedConcreteCore
        H N hN beta hbeta color
        ((Finset.univ :
          Finset (PeriodicHypercubicEvenFixedSpatialColorLink H color)).toList)
        f hf
  rcases
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweep_exists_boundedRepresentative_canonicalPrefixWitness
        H N hN beta hbeta color e S hSCore with
    ⟨pre, suffix, F, hF, bound, hbound,
      hSplit, hFresh, hRep, hLocal⟩
  have hCyclic :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSecondSweepStageVector_eq_cyclicBetweenVisits
      H N hN beta hbeta color pre suffix e f hSplit
  refine
    ⟨pre, suffix, F, hF, bound, hbound,
      hSplit, hFresh, ?_, ?_⟩
  · exact hRep.trans hCyclic
  · simpa [S] using hLocal

/-- Ordinary spatial-link wrapper of the fixed-color cyclic second-visit
representative theorem. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSecondSweep_exists_boundedRepresentative_cyclicPrefixWitness
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (f :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta)
    (hf :
      f ∈
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore
          H N hN beta hbeta) :
    ∃
      (pre suffix :
        List
          (PeriodicHypercubicEvenFixedSpatialColorLink H
            (periodicHypercubicEvenSpatialSliceLinkColor H e)))
      (F :
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
      (hF : StronglyMeasurable F)
      (bound : ℝ)
      (hbound : ∀ z, ‖F z‖ ≤ bound),
      (Finset.univ :
        Finset
          (PeriodicHypercubicEvenFixedSpatialColorLink H
            (periodicHypercubicEvenSpatialSliceLinkColor H e))).toList =
          pre ++
            (⟨e, rfl⟩ :
              PeriodicHypercubicEvenFixedSpatialColorLink H
                (periodicHypercubicEvenSpatialSliceLinkColor H e)) ::
              suffix ∧
      (⟨e, rfl⟩ :
        PeriodicHypercubicEvenFixedSpatialColorLink H
          (periodicHypercubicEvenSpatialSliceLinkColor H e)) ∉ pre ∧
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
          H N hN beta hbeta F hF bound hbound =
        realHilbertProjectionSweep
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
            H N hN beta hbeta
            (periodicHypercubicEvenSpatialSliceLinkColor H e))
          (suffix ++ pre)
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
            H N hN beta hbeta e
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepStageVector
              H N hN beta hbeta
              (periodicHypercubicEvenSpatialSliceLinkColor H e) pre f)) ∧
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMeanResidualL2
          H N hN beta hbeta e F hF bound hbound‖ ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepStageLocalProfile
          H N hN beta hbeta
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkFullSweepVector
            H N hN beta hbeta
            (periodicHypercubicEvenSpatialSliceLinkColor H e) f) e := by
  let color :=
    periodicHypercubicEvenSpatialSliceLinkColor H e
  let eColor :
      PeriodicHypercubicEvenFixedSpatialColorLink H color :=
    ⟨e, rfl⟩
  rcases
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSecondSweep_exists_boundedRepresentative_cyclicPrefixWitness
        H N hN beta hbeta color eColor f hf with
    ⟨pre, suffix, F, hF, bound, hbound,
      hSplit, hFresh, hRep, hLocal⟩
  refine
    ⟨pre, suffix, F, hF, bound, hbound,
      ?_, ?_, ?_, ?_⟩
  · simpa [color, eColor] using hSplit
  · simpa [color, eColor] using hFresh
  · simpa [
      color, eColor,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2] using hRep
  · simpa [
      color, eColor,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepStageLocalProfile] using hLocal

/-- Choose the cyclic second-visit bounded representative data simultaneously
for every genuine spatial link. -/
theorem
    exists_periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSecondSweep_linkIndexedRepresentatives_with_cyclicPrefixWitness
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta)
    (hf :
      f ∈
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore
          H N hN beta hbeta) :
    ∃
      (pre suffix :
        (e : PeriodicHypercubicEvenSpatialSliceLink H) →
          List
            (PeriodicHypercubicEvenFixedSpatialColorLink H
              (periodicHypercubicEvenSpatialSliceLinkColor H e)))
      (F :
        PeriodicHypercubicEvenSpatialSliceLink H →
          (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
      (hF : ∀ e, StronglyMeasurable (F e))
      (bound : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
      (hbound : ∀ e z, ‖F e z‖ ≤ bound e),
      (∀ e,
        (Finset.univ :
          Finset
            (PeriodicHypercubicEvenFixedSpatialColorLink H
              (periodicHypercubicEvenSpatialSliceLinkColor H e))).toList =
            pre e ++
              (⟨e, rfl⟩ :
                PeriodicHypercubicEvenFixedSpatialColorLink H
                  (periodicHypercubicEvenSpatialSliceLinkColor H e)) ::
                suffix e) ∧
      (∀ e,
        (⟨e, rfl⟩ :
          PeriodicHypercubicEvenFixedSpatialColorLink H
            (periodicHypercubicEvenSpatialSliceLinkColor H e)) ∉ pre e) ∧
      (∀ e,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
            H N hN beta hbeta
            (F e) (hF e) (bound e) (hbound e) =
          realHilbertProjectionSweep
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
              H N hN beta hbeta
              (periodicHypercubicEvenSpatialSliceLinkColor H e))
            (suffix e ++ pre e)
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
              H N hN beta hbeta e
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepStageVector
                H N hN beta hbeta
                (periodicHypercubicEvenSpatialSliceLinkColor H e)
                (pre e) f))) ∧
      (∀ e,
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMeanResidualL2
            H N hN beta hbeta e
            (F e) (hF e) (bound e) (hbound e)‖ ≤
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepStageLocalProfile
            H N hN beta hbeta
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkFullSweepVector
              H N hN beta hbeta
              (periodicHypercubicEvenSpatialSliceLinkColor H e) f) e) := by
  have hWitness :
      ∀ e : PeriodicHypercubicEvenSpatialSliceLink H,
        ∃
          (pre suffix :
            List
              (PeriodicHypercubicEvenFixedSpatialColorLink H
                (periodicHypercubicEvenSpatialSliceLinkColor H e)))
          (F :
            (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
              PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
          (hF : StronglyMeasurable F)
          (bound : ℝ)
          (hbound : ∀ z, ‖F z‖ ≤ bound),
          (Finset.univ :
            Finset
              (PeriodicHypercubicEvenFixedSpatialColorLink H
                (periodicHypercubicEvenSpatialSliceLinkColor H e))).toList =
              pre ++
                (⟨e, rfl⟩ :
                  PeriodicHypercubicEvenFixedSpatialColorLink H
                    (periodicHypercubicEvenSpatialSliceLinkColor H e)) ::
                  suffix ∧
          (⟨e, rfl⟩ :
            PeriodicHypercubicEvenFixedSpatialColorLink H
              (periodicHypercubicEvenSpatialSliceLinkColor H e)) ∉ pre ∧
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
              H N hN beta hbeta F hF bound hbound =
            realHilbertProjectionSweep
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
                H N hN beta hbeta
                (periodicHypercubicEvenSpatialSliceLinkColor H e))
              (suffix ++ pre)
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
                H N hN beta hbeta e
                (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepStageVector
                  H N hN beta hbeta
                  (periodicHypercubicEvenSpatialSliceLinkColor H e) pre f)) ∧
          ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMeanResidualL2
              H N hN beta hbeta e F hF bound hbound‖ ≤
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepStageLocalProfile
              H N hN beta hbeta
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkFullSweepVector
                H N hN beta hbeta
                (periodicHypercubicEvenSpatialSliceLinkColor H e) f) e := by
    intro e
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSecondSweep_exists_boundedRepresentative_cyclicPrefixWitness
        H N hN beta hbeta e f hf
  choose pre suffix F hF bound hbound
    hSplit hFresh hRep hLocal using hWitness
  exact
    ⟨pre, suffix, F, hF, bound, hbound,
      hSplit, hFresh, hRep, hLocal⟩

end

end MGAP4D.MathlibAnalytic
