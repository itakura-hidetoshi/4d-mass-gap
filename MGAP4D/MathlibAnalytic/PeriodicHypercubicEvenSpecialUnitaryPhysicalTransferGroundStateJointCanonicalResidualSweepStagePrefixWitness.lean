import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointCanonicalResidualSweepStageLocalProfile
import Mathlib.Tactic

/-!
# Preserve the canonical sweep-prefix witness of each stage representative

The PR #4770 local-profile theorem already chooses, for each spatial link, the
bounded concrete representative at the canonical one-link sweep prefix ending
immediately before that link.  Its public conclusion retained only an arbitrary
`pre` witness and discarded the equally important suffix equation

  canonicalList = pre ++ e :: suffix.

That information is needed for exact ordered telescoping.  This file exposes
it without changing any analytic estimate.

For each fixed-color link e we retain:

* the prefix pre;
* the suffix suffix;
* the exact canonical-list decomposition;
* freshness e ∉ pre;
* the bounded concrete representative identity;
* the coefficient-one canonical local-profile bound.

The same information is then lifted to ordinary spatial links and finally
chosen simultaneously for the entire finite spatial-link family.

No new probability law, response estimate, cutoff, coefficient, or
finite-cardinality factor is introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

attribute [local instance]
  groundStateJointOneLinkBoundedCoreSpecialUnitaryIsTopologicalGroup
  groundStateJointOneLinkBoundedCoreSpecialUnitaryCompactSpace
  groundStateJointOneLinkBoundedCoreSpecialUnitarySecondCountableTopology
  groundStateJointOneLinkBoundedCoreSpecialUnitaryMeasurableSpace
  groundStateJointOneLinkBoundedCoreSpecialUnitaryBorelSpace
  groundStateJointOneLinkBoundedCoreSpatialLinkFintype
  groundStateJointOneLinkBoundedCoreTargetLinkFintype
  groundStateJointOneLinkBoundedCoreTargetLinkUnique

local instance canonicalSweepPrefixWitnessSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Fixed-color form retaining the exact canonical prefix/suffix decomposition
used internally by the PR #4770 local-profile theorem. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweep_exists_boundedRepresentative_canonicalPrefixWitness
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor)
    (e : PeriodicHypercubicEvenFixedSpatialColorLink H color)
    (f : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
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
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepStageVector
          H N hN beta hbeta color pre f ∧
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMeanResidualL2
          H N hN beta hbeta e.1 F hF bound hbound‖ ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepStageLocalProfile
          H N hN beta hbeta color f e := by
  let cs :=
    (Finset.univ :
      Finset (PeriodicHypercubicEvenFixedSpatialColorLink H color)).toList
  have heMem : e ∈ cs := by
    simp [cs]
  rcases List.eq_append_cons_of_mem heMem with
    ⟨pre, suffix, hcs, hprefix⟩
  rcases
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepStage_exists_boundedRepresentative_canonicalResidualL2_norm_le_residual
        H N hN beta hbeta color pre e f hf with
    ⟨F, hF, bound, hbound, hRep, hLocal⟩
  refine
    ⟨pre, suffix, F, hF, bound, hbound,
      by simpa [cs] using hcs,
      hprefix,
      hRep,
      hLocal.trans ?_⟩
  have hAmp :=
    realHilbertProjectionSweepStageResidual_norm_le_amplitude_append_cons
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
        H N hN beta hbeta color)
      pre suffix f e hprefix
  rw [← hcs] at hAmp
  simpa [
    cs,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepStageVector,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepStageLocalProfile]
    using hAmp

/-- Ordinary spatial-link form retaining the canonical prefix/suffix witness
inside the link's own six-spatial color sweep. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweep_exists_boundedRepresentative_canonicalPrefixWitness
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (f : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
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
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepStageVector
          H N hN beta hbeta
          (periodicHypercubicEvenSpatialSliceLinkColor H e) pre f ∧
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMeanResidualL2
          H N hN beta hbeta e F hF bound hbound‖ ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepStageLocalProfile
          H N hN beta hbeta f e := by
  let eColor :
      PeriodicHypercubicEvenFixedSpatialColorLink H
        (periodicHypercubicEvenSpatialSliceLinkColor H e) :=
    ⟨e, rfl⟩
  rcases
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweep_exists_boundedRepresentative_canonicalPrefixWitness
        H N hN beta hbeta
        (periodicHypercubicEvenSpatialSliceLinkColor H e)
        eColor f hf with
    ⟨pre, suffix, F, hF, bound, hbound,
      hSplit, hFresh, hRep, hLocal⟩
  refine
    ⟨pre, suffix, F, hF, bound, hbound,
      ?_, ?_, hRep, ?_⟩
  · simpa [eColor] using hSplit
  · simpa [eColor] using hFresh
  · simpa [
      eColor,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepStageLocalProfile]
      using hLocal

/-- Choose the canonical-prefix representative data simultaneously for every
spatial link.  Unlike the earlier link-indexed packaging, this theorem retains
the exact canonical position of each chosen stage representative. -/
theorem
    exists_periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweep_linkIndexedRepresentatives_with_canonicalPrefixWitness
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
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
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepStageVector
            H N hN beta hbeta
            (periodicHypercubicEvenSpatialSliceLinkColor H e)
            (pre e) f) ∧
      (∀ e,
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMeanResidualL2
            H N hN beta hbeta e
            (F e) (hF e) (bound e) (hbound e)‖ ≤
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepStageLocalProfile
            H N hN beta hbeta f e) := by
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
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepStageVector
              H N hN beta hbeta
              (periodicHypercubicEvenSpatialSliceLinkColor H e)
              pre f ∧
          ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMeanResidualL2
              H N hN beta hbeta e F hF bound hbound‖ ≤
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepStageLocalProfile
              H N hN beta hbeta f e := by
    intro e
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweep_exists_boundedRepresentative_canonicalPrefixWitness
        H N hN beta hbeta e f hf
  choose pre suffix F hF bound hbound
    hSplit hFresh hRep hLocal using hWitness
  exact
    ⟨pre, suffix, F, hF, bound, hbound,
      hSplit, hFresh, hRep, hLocal⟩

end

end MathlibAnalytic
end MGAP4D
