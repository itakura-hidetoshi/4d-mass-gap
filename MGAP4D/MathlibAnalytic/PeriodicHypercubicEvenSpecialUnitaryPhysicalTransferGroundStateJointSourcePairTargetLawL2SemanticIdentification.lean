import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourcePairTargetLawL2Decomposition
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSixSpatialSweepStageSourceUpdateDirectL2
import Mathlib.Tactic

/-!
# Semantic identification of the target-law L2 decomposition

PR #4850 constructs old-first, first, and second target means in one full
source-pair L2 carrier and proves the exact vector identity

  fullDifferenceL2 = directDifferenceL2 + responseL2.

This file identifies those auxiliary-looking means with the actual physical
source-updated centered means already used in PR #4775.

For target != source and z=(A,(u,v)):

* old-first mean is the centered target mean of the section at A[source<-u]
  under the target law based at A[source<-u];
* first mean is the centered target mean of the section at A[source<-v]
  under the target law based at A[source<-u];
* second mean is the same section under the target law based at A[source<-v].

Consequently, the PR #4850 direct and full L2 differences have as their a.e.
representatives exactly the PR #4775 direct source-update difference and full
source-update difference.

No new probability law, estimate, coefficient, or finite-volume factor is
introduced.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

local instance targetLawL2SemanticSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance targetLawL2SemanticSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance targetLawL2SemanticSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance targetLawL2SemanticSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance targetLawL2SemanticSpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance targetLawL2SemanticSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The old-first mean is literally the source-updated centered target mean at
the first updated section and first updated target law. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOldFirstMean_eq_sourceUpdatedCenteredMean
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource source target :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (hne : target ≠ source)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (left : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (center : ℝ)
    (z :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        (Matrix.specialUnitaryGroup (Fin N) ℂ ×
          Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOldFirstMean
        H N hN beta hbeta B distinguishedSource source target k g₂
        F left center z =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdatedCenteredMean
        H N hN beta hbeta target source F left B z.1
        (periodicHypercubicEvenSpatialSliceOffTargetSourceUpdate
          target source hne
          (periodicHypercubicEvenSpatialSliceOffTargetRestriction target z.1)
          z.2.1)
        distinguishedSource k g₂ z.2.1 center := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOldFirstMean
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairTargetFiberKernel_apply]
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOldCenteredSection
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairFirstUpdatedBackground
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdatedCenteredMean
  rw [
    periodicHypercubicEvenSpatialSliceOffTargetSourceUpdate_offTargetRestriction
      target source hne z.1 z.2.1]

/-- The first mean is the second updated section integrated against the first
updated target law. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFirstMean_eq_sourceUpdatedCenteredMean
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource source target :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (hne : target ≠ source)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (left : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (center : ℝ)
    (z :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        (Matrix.specialUnitaryGroup (Fin N) ℂ ×
          Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFirstMean
        H N hN beta hbeta B distinguishedSource source target k g₂
        F left center z =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdatedCenteredMean
        H N hN beta hbeta target source F left B z.1
        (periodicHypercubicEvenSpatialSliceOffTargetSourceUpdate
          target source hne
          (periodicHypercubicEvenSpatialSliceOffTargetRestriction target z.1)
          z.2.2)
        distinguishedSource k g₂ z.2.1 center := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFirstMean
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairTargetFiberKernel_apply]
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawCenteredSection
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairSecondUpdatedBackground
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdatedCenteredMean
  rw [
    periodicHypercubicEvenSpatialSliceOffTargetSourceUpdate_offTargetRestriction
      target source hne z.1 z.2.2]

/-- The second mean is the second updated section integrated against the second
updated target law. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMean_eq_sourceUpdatedCenteredMean
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource source target :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (hne : target ≠ source)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (left : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (center : ℝ)
    (z :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        (Matrix.specialUnitaryGroup (Fin N) ℂ ×
          Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMean
        H N hN beta hbeta B distinguishedSource source target k g₂
        F left center z =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdatedCenteredMean
        H N hN beta hbeta target source F left B z.1
        (periodicHypercubicEvenSpatialSliceOffTargetSourceUpdate
          target source hne
          (periodicHypercubicEvenSpatialSliceOffTargetRestriction target z.1)
          z.2.2)
        distinguishedSource k g₂ z.2.2 center := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMean
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairSecondTargetFiberKernel_apply]
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawCenteredSection
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairSecondUpdatedBackground
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdatedCenteredMean
  rw [
    periodicHypercubicEvenSpatialSliceOffTargetSourceUpdate_offTargetRestriction
      target source hne z.1 z.2.2]

/-- The direct-difference L2 vector has exactly the PR #4775 direct
source-update difference as its a.e. representative. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawDirectDifferenceL2_coeFn_semantic
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
    (bound : ℝ) (hbound : ∀ z, ‖F z‖ ≤ bound)
    (left : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (center : ℝ) :
    (fun z =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawDirectDifferenceL2
        H N hN beta hbeta B distinguishedSource source target k g₂
        F hF bound hbound left center z) =ᵐ[
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceIndependentPairBackgroundMeasure
        H N hN beta hbeta B distinguishedSource source k g₂]
      (fun z =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateDirectMeanDifference
          H N hN beta hbeta target source hne F left B z.1
          (periodicHypercubicEvenSpatialSliceOffTargetRestriction target z.1)
          distinguishedSource k g₂ z.2.1 z.2.2 center) := by
  filter_upwards [
    Lp.coeFn_sub
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOldFirstMeanL2
        H N hN beta hbeta B distinguishedSource source target k g₂
        F hF bound hbound left center)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFirstMeanL2
        H N hN beta hbeta B distinguishedSource source target k g₂
        F hF bound hbound left center),
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOldFirstMeanL2_coeFn
      H N hN beta hbeta B distinguishedSource source target k g₂
      F hF bound hbound left center,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFirstMeanL2_coeFn
      H N hN beta hbeta B distinguishedSource source target k g₂
      F hF bound hbound left center
  ] with z hSub hOld hFirst
  rw [show
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawDirectDifferenceL2
        H N hN beta hbeta B distinguishedSource source target k g₂
        F hF bound hbound left center =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOldFirstMeanL2
          H N hN beta hbeta B distinguishedSource source target k g₂
          F hF bound hbound left center -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFirstMeanL2
          H N hN beta hbeta B distinguishedSource source target k g₂
          F hF bound hbound left center by rfl]
  rw [hSub]
  change
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOldFirstMeanL2
        H N hN beta hbeta B distinguishedSource source target k g₂
        F hF bound hbound left center z -
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFirstMeanL2
        H N hN beta hbeta B distinguishedSource source target k g₂
        F hF bound hbound left center z =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdateDirectMeanDifference
        H N hN beta hbeta target source hne F left B z.1
        (periodicHypercubicEvenSpatialSliceOffTargetRestriction target z.1)
        distinguishedSource k g₂ z.2.1 z.2.2 center
  rw [hOld, hFirst]
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOldFirstMean_eq_sourceUpdatedCenteredMean
      H N hN beta hbeta B distinguishedSource source target hne k g₂ F left center z,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFirstMean_eq_sourceUpdatedCenteredMean
      H N hN beta hbeta B distinguishedSource source target hne k g₂ F left center z]
  rfl

/-- The full-difference L2 vector has exactly the physical full source-update
difference as its a.e. representative. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFullDifferenceL2_coeFn_semantic
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
    (bound : ℝ) (hbound : ∀ z, ‖F z‖ ≤ bound)
    (left : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (center : ℝ) :
    (fun z =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFullDifferenceL2
        H N hN beta hbeta B distinguishedSource source target k g₂
        F hF bound hbound left center z) =ᵐ[
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceIndependentPairBackgroundMeasure
        H N hN beta hbeta B distinguishedSource source k g₂]
      (fun z =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdatedCenteredMean
            H N hN beta hbeta target source F left B z.1
            (periodicHypercubicEvenSpatialSliceOffTargetSourceUpdate
              target source hne
              (periodicHypercubicEvenSpatialSliceOffTargetRestriction target z.1)
              z.2.1)
            distinguishedSource k g₂ z.2.1 center -
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdatedCenteredMean
            H N hN beta hbeta target source F left B z.1
            (periodicHypercubicEvenSpatialSliceOffTargetSourceUpdate
              target source hne
              (periodicHypercubicEvenSpatialSliceOffTargetRestriction target z.1)
              z.2.2)
            distinguishedSource k g₂ z.2.2 center) := by
  filter_upwards [
    Lp.coeFn_sub
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOldFirstMeanL2
        H N hN beta hbeta B distinguishedSource source target k g₂
        F hF bound hbound left center)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanL2
        H N hN beta hbeta B distinguishedSource source target k g₂
        F hF bound hbound left center),
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOldFirstMeanL2_coeFn
      H N hN beta hbeta B distinguishedSource source target k g₂
      F hF bound hbound left center,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanL2_coeFn
      H N hN beta hbeta B distinguishedSource source target k g₂
      F hF bound hbound left center
  ] with z hSub hOld hSecond
  rw [show
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFullDifferenceL2
        H N hN beta hbeta B distinguishedSource source target k g₂
        F hF bound hbound left center =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOldFirstMeanL2
          H N hN beta hbeta B distinguishedSource source target k g₂
          F hF bound hbound left center -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanL2
          H N hN beta hbeta B distinguishedSource source target k g₂
          F hF bound hbound left center by rfl]
  rw [hSub]
  change
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOldFirstMeanL2
        H N hN beta hbeta B distinguishedSource source target k g₂
        F hF bound hbound left center z -
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanL2
        H N hN beta hbeta B distinguishedSource source target k g₂
        F hF bound hbound left center z =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdatedCenteredMean
          H N hN beta hbeta target source F left B z.1
          (periodicHypercubicEvenSpatialSliceOffTargetSourceUpdate
            target source hne
            (periodicHypercubicEvenSpatialSliceOffTargetRestriction target z.1)
            z.2.1)
          distinguishedSource k g₂ z.2.1 center -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSectionSourceUpdatedCenteredMean
          H N hN beta hbeta target source F left B z.1
          (periodicHypercubicEvenSpatialSliceOffTargetSourceUpdate
            target source hne
            (periodicHypercubicEvenSpatialSliceOffTargetRestriction target z.1)
            z.2.2)
          distinguishedSource k g₂ z.2.2 center
  rw [hOld, hSecond]
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOldFirstMean_eq_sourceUpdatedCenteredMean
      H N hN beta hbeta B distinguishedSource source target hne k g₂ F left center z,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMean_eq_sourceUpdatedCenteredMean
      H N hN beta hbeta B distinguishedSource source target hne k g₂ F left center z]

end

end MGAP4D.MathlibAnalytic
