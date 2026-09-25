import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointOneLinkCanonicalResidualSweepStageNorm
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSixSpatialOneLinkSweepStageProfile
import Mathlib.Tactic

/-!
# Canonical residual localPart under the ordered sweep-stage profile

PR #4769 provides, for every bounded-concrete sweep prefix and next link, a
canonical genuine-joint L2 localPart vector whose norm is bounded by the exact
next-link conditional-expectation residual.

The receiver profile is indexed by links rather than by explicit prefix
positions.  This file supplies the missing purely finite-list bridge.  If a
label `d` occurs after a prefix in an ordered projection sweep, the residual
at that occurrence is bounded by the square-root stage amplitude attributed to
`d`.  For the canonical `Finset.univ.toList` sweep every link occurs, so the
PR #4769 localPart can be chosen with norm bounded directly by the existing
sweep-stage local profile.

No new probability, response, influence, or Poincare input is introduced.
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

local instance canonicalResidualSweepStageLocalProfileSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- If `d` occurs immediately after `prefix` in an ordered sweep, and has
not already occurred in the prefix, then the norm of that stage residual is
bounded by the total stage amplitude attributed to `d`.

The suffix may contain further occurrences; their contributions are
nonnegative, so no `Nodup` hypothesis is needed for this inequality. -/
theorem
    realHilbertProjectionSweepStageResidual_norm_le_amplitude_append_cons
    {E C : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [DecidableEq C]
    (P : C → E →L[ℝ] E)
    (prefix suffix : List C)
    (x : E)
    (d : C)
    (hprefix : d ∉ prefix) :
    ‖realHilbertProjectionSweep P prefix x -
        P d (realHilbertProjectionSweep P prefix x)‖ ≤
      realHilbertProjectionSweepStageResidualAmplitude
        P (prefix ++ d :: suffix) x d := by
  induction prefix generalizing x with
  | nil =>
      have hTail :
          0 ≤
            realHilbertProjectionSweepStageResidualSqProfile
              P suffix (P d x) d :=
        realHilbertProjectionSweepStageResidualSqProfile_nonneg
          P suffix (P d x) d
      unfold realHilbertProjectionSweepStageResidualAmplitude
      simp only [
        List.nil_append,
        realHilbertProjectionSweep,
        ContinuousLinearMap.id_apply,
        realHilbertProjectionSweepStageResidualSqProfile,
        if_pos]
      apply
        (sq_le_sq₀
          (norm_nonneg (x - P d x))
          (Real.sqrt_nonneg _)).mp
      rw [Real.sq_sqrt (add_nonneg (sq_nonneg _) hTail)]
      exact le_add_of_nonneg_right hTail
  | cons c prefix ih =>
      have hdc : d ≠ c := by
        intro h
        apply hprefix
        simp [h]
      have htail : d ∉ prefix := by
        intro h
        apply hprefix
        simp [h]
      simpa [
        realHilbertProjectionSweep,
        realHilbertProjectionSweepStageResidualAmplitude,
        realHilbertProjectionSweepStageResidualSqProfile,
        hdc] using
        (ih (x := P c x) htail)

/-- For one fixed spatial color and one link of that color, choose the prefix
ending immediately before the link in the canonical one-link sweep.  The
bounded-concrete representative at that prefix then yields a canonical
genuine-joint L2 localPart vector whose norm is bounded by the existing
fixed-color sweep-stage local profile at that link. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweep_exists_boundedRepresentative_canonicalResidualL2_norm_le_localProfile
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
      (prefix : List (PeriodicHypercubicEvenFixedSpatialColorLink H color))
      (F :
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
      (hF : StronglyMeasurable F)
      (bound : ℝ)
      (hbound : ∀ z, ‖F z‖ ≤ bound),
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
          H N hN beta hbeta F hF bound hbound =
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepStageVector
          H N hN beta hbeta color prefix f ∧
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
    ⟨prefix, suffix, hcs, hprefix⟩
  rcases
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepStage_exists_boundedRepresentative_canonicalResidualL2_norm_le_residual
        H N hN beta hbeta color prefix e f hf with
    ⟨F, hF, bound, hbound, hRep, hLocal⟩
  refine ⟨prefix, F, hF, bound, hbound, hRep, hLocal.trans ?_⟩
  have hAmp :=
    realHilbertProjectionSweepStageResidual_norm_le_amplitude_append_cons
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
        H N hN beta hbeta color)
      prefix suffix f e hprefix
  rw [← hcs] at hAmp
  simpa [
    cs,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepStageVector,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepStageLocalProfile]
    using hAmp

/-- Genuine spatial-link form of the localPart witness.  Each link uses the
canonical sweep of its own six-spatial color, exactly matching the profile
consumed by the transpose Schur receiver. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweep_exists_boundedRepresentative_canonicalResidualL2_norm_le_localProfile
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
      (prefix :
        List
          (PeriodicHypercubicEvenFixedSpatialColorLink H
            (periodicHypercubicEvenSpatialSliceLinkColor H e)))
      (F :
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
      (hF : StronglyMeasurable F)
      (bound : ℝ)
      (hbound : ∀ z, ‖F z‖ ≤ bound),
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
          H N hN beta hbeta F hF bound hbound =
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepStageVector
          H N hN beta hbeta
          (periodicHypercubicEvenSpatialSliceLinkColor H e) prefix f ∧
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMeanResidualL2
          H N hN beta hbeta e F hF bound hbound‖ ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepStageLocalProfile
          H N hN beta hbeta f e := by
  let eColor :
      PeriodicHypercubicEvenFixedSpatialColorLink H
        (periodicHypercubicEvenSpatialSliceLinkColor H e) :=
    ⟨e, rfl⟩
  rcases
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweep_exists_boundedRepresentative_canonicalResidualL2_norm_le_localProfile
        H N hN beta hbeta
        (periodicHypercubicEvenSpatialSliceLinkColor H e)
        eColor f hf with
    ⟨prefix, F, hF, bound, hbound, hRep, hLocal⟩
  refine ⟨prefix, F, hF, bound, hbound, hRep, ?_⟩
  simpa [
    eColor,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepStageLocalProfile]
    using hLocal

end

end MathlibAnalytic
end MGAP4D
