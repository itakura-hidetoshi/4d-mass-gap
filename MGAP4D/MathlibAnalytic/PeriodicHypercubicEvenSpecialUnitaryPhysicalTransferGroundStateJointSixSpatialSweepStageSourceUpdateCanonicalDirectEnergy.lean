import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceSourcePairExactReorderedLaw
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSixSpatialSweepStageSourceUpdateDirectRMS
import Mathlib.Tactic

/-!
# Canonical retained-background form of the direct source-update energy

PR #4727 rewrites the physical source-pair / target-fiber law in the ordered
coordinates

  C = A[source <- u],  v,  g.

The PR #4720 direct energy is still written with an arbitrary retained
off-target target background.  This file specializes that retained background
to the canonical off-target restriction of the complete configuration.

For target != source, updating that retained background at source is exactly
the same as updating the full configuration at source and then restricting
away from target.  Consequently the direct square and its target-fiber energy
can be written only in terms of the ordered coordinates (C,v,g).

This is a coordinate identity.  No source/target heat-bath commutation, no
conditional-law identification, and no residual-energy inequality is used.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory Set
open scoped ENNReal

noncomputable section

local instance canonicalRetainedDirectEnergySpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance canonicalRetainedDirectEnergySpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance canonicalRetainedDirectEnergySpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance canonicalRetainedDirectEnergySpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance canonicalRetainedDirectEnergySpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance canonicalRetainedDirectEnergySpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Updating one off-target source coordinate after restricting away from the
target is exactly restriction after updating the complete configuration. -/
theorem
    periodicHypercubicEvenSpatialSliceOffTargetSourceUpdate_offTargetRestriction
    {H : ℕ}
    {Gauge : Type}
    [DecidableEq (PeriodicHypercubicEvenSpatialSliceLink H)]
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (hne : target ≠ source)
    (A : PeriodicHypercubicEvenSpatialSliceConfiguration H Gauge)
    (value : Gauge) :
    periodicHypercubicEvenSpatialSliceOffTargetSourceUpdate
        target source hne
        (periodicHypercubicEvenSpatialSliceOffTargetRestriction target A)
        value =
      periodicHypercubicEvenSpatialSliceOffTargetRestriction target
        (Function.update A source value) := by
  funext e
  by_cases he : e.1 = source
  · have hsub :
        e =
          (⟨source, hne.symm⟩ :
            PeriodicHypercubicEvenSpatialSliceOffTargetLink H target) :=
      Subtype.ext he
    rw [hsub]
    simp [
      periodicHypercubicEvenSpatialSliceOffTargetSourceUpdate,
      periodicHypercubicEvenSpatialSliceOffTargetRestriction]
  · have hsub :
        e ≠
          (⟨source, hne.symm⟩ :
            PeriodicHypercubicEvenSpatialSliceOffTargetLink H target) := by
      intro h
      apply he
      exact congrArg Subtype.val h
    simp [
      periodicHypercubicEvenSpatialSliceOffTargetSourceUpdate,
      periodicHypercubicEvenSpatialSliceOffTargetRestriction,
      hsub, he]

/-- Replacing the same complete-configuration coordinate twice keeps only the
second value.  Kept explicit so downstream proofs do not depend on a particular
simp presentation of `Function.update` in the pinned Lean environment. -/
theorem periodicHypercubicEvenSpatialSliceSourceUpdate_update
    {H : ℕ}
    {Gauge : Type}
    [DecidableEq (PeriodicHypercubicEvenSpatialSliceLink H)]
    (A : PeriodicHypercubicEvenSpatialSliceConfiguration H Gauge)
    (source : PeriodicHypercubicEvenSpatialSliceLink H)
    (u v : Gauge) :
    Function.update (Function.update A source u) source v =
      Function.update A source v := by
  funext e
  by_cases he : e = source
  · subst e
    simp
  · simp [Function.update, he]

/-- The retained background obtained by changing source to `v` can equally
be read after first changing source to any `u`. -/
theorem
    periodicHypercubicEvenSpatialSliceOffTargetSourceUpdate_offTargetRestriction_eq_after_firstUpdate
    {H : ℕ}
    {Gauge : Type}
    [DecidableEq (PeriodicHypercubicEvenSpatialSliceLink H)]
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (hne : target ≠ source)
    (A : PeriodicHypercubicEvenSpatialSliceConfiguration H Gauge)
    (u v : Gauge) :
    periodicHypercubicEvenSpatialSliceOffTargetSourceUpdate
        target source hne
        (periodicHypercubicEvenSpatialSliceOffTargetRestriction target A)
        v =
      periodicHypercubicEvenSpatialSliceOffTargetRestriction target
        (Function.update (Function.update A source u) source v) := by
  rw [
    periodicHypercubicEvenSpatialSliceOffTargetSourceUpdate_offTargetRestriction
      target source hne A v,
    periodicHypercubicEvenSpatialSliceSourceUpdate_update A source u v]

/-- Pointwise direct squared difference in the ordered coordinates
`(C,v,g)`.

The first section uses the retained off-target part of `C`; the second uses
the same background after replacing source by `v`. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateOrderedDirectDifferenceSquare
    (H N : ℕ)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (left C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (v g : Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ :=
  (periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
      H N target F left
      (periodicHypercubicEvenSpatialSliceOffTargetRestriction target C) g -
    periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
      H N target F left
      (periodicHypercubicEvenSpatialSliceOffTargetRestriction target
        (Function.update C source v)) g) ^ 2

/-- The canonical-retained PR #4720 square is exactly the ordered square after
putting `C = A[source <- u]`. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSection_sourceUpdateCanonicalRetained_square_eq_ordered
    (H N : ℕ)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (hne : target ≠ source)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (left A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (u v g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    (periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
        H N target F left
        (periodicHypercubicEvenSpatialSliceOffTargetSourceUpdate
          target source hne
          (periodicHypercubicEvenSpatialSliceOffTargetRestriction target A) u) g -
      periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
        H N target F left
        (periodicHypercubicEvenSpatialSliceOffTargetSourceUpdate
          target source hne
          (periodicHypercubicEvenSpatialSliceOffTargetRestriction target A) v) g) ^ 2 =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateOrderedDirectDifferenceSquare
        H N target source F left (Function.update A source u) v g := by
  rw [
    periodicHypercubicEvenSpatialSliceOffTargetSourceUpdate_offTargetRestriction
      target source hne A u,
    periodicHypercubicEvenSpatialSliceOffTargetSourceUpdate_offTargetRestriction_eq_after_firstUpdate
      target source hne A u v]
  rfl

/-- Target-fiber average of the ordered direct squared difference. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateOrderedDirectDifferenceEnergy
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (left B C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ v : Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ :=
  ∫ g,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateOrderedDirectDifferenceSquare
      H N target source F left C v g
    ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
      H N hN beta hbeta B source distinguishedSource target k g₂ C

/-- The ordered direct energy is nonnegative. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateOrderedDirectDifferenceEnergy_nonneg
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (left B C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ v : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    0 ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateOrderedDirectDifferenceEnergy
        H N hN beta hbeta target source F left B C
        distinguishedSource k g₂ v := by
  apply integral_nonneg
  intro g
  exact sq_nonneg _

/-- With canonical retained background, the PR #4720 direct difference energy
is exactly the ordered energy at `C = A[source <- u]`.

In particular, the apparent dependence on the first source value `u` is now
entirely absorbed into the updated background `C`; the remaining explicit
source value is only `v`. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSection_sourceUpdateDirectDifferenceEnergy_canonicalRetained_eq_ordered
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (hne : target ≠ source)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (left B A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ u v : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateDirectDifferenceEnergy
        H N hN beta hbeta target source hne F left B A
        (periodicHypercubicEvenSpatialSliceOffTargetRestriction target A)
        distinguishedSource k g₂ u v =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateOrderedDirectDifferenceEnergy
        H N hN beta hbeta target source F left B
        (Function.update A source u) distinguishedSource k g₂ v := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateDirectDifferenceEnergy
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateOrderedDirectDifferenceEnergy
  apply integral_congr_ae
  filter_upwards with g
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSection_sourceUpdateCanonicalRetained_square_eq_ordered
      H N target source hne F left A u v g

end

end MGAP4D.MathlibAnalytic
