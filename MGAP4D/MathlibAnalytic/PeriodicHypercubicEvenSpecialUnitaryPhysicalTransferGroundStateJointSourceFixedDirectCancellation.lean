import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointOneLinkSourceFixedBoundedRepresentative
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourcePairTargetLawL2Decomposition
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointOneLinkSplitDirectFiberBridge
import Mathlib.Tactic

/-!
# Exact direct cancellation for source-fixed bounded representatives

The representative constructed in PR #4925 is pointwise invariant under a
source-coordinate replacement. At an off-diagonal target, the old and new
observable sections therefore agree before integration. The old-first and
first means use the SAME target law, so they agree without any conditional-law
comparison. Their existing source-pair L2 classes agree by `Lp.ext`.

Consequently `directDifferenceL2 = 0` and the existing exact decomposition
reduces to `fullDifferenceL2 = responseL2`. A single representative of the
actual update `P_source f` has these properties for all target/background
contexts. Coordinate-update commutation is not projection commutation.

No source-pair norm is identified with a genuine joint-L2 norm. The beta-small
leakage bound, its integrated RMS control, envelope domination, terminal
recurrence, and strict renewal contraction remain separate analytic tasks.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory ProbabilityTheory Filter

noncomputable section

local instance sourceFixedDirectCancellationIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance sourceFixedDirectCancellationCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance sourceFixedDirectCancellationSecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance sourceFixedDirectCancellationMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance sourceFixedDirectCancellationBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance sourceFixedDirectCancellationSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) := Fintype.ofFinite _

/-- Source invariance survives evaluating an off-diagonal concrete target section.
Only coordinate replacements commute here; no conditional expectations do. -/
theorem
    periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection_sourceUpdate_eq_of_sourceInvariant
    (H N : ℕ) (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (hne : target ≠ source)
    (F : (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hInvariant : ∀ (left right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
      (value : Matrix.specialUnitaryGroup (Fin N) ℂ),
      F (left, Function.update right source value) = F (left, right))
    (left A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (u g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
        H N target F left
        (periodicHypercubicEvenSpatialSliceOffTargetRestriction target (Function.update A source u)) g =
      periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
        H N target F left
        (periodicHypercubicEvenSpatialSliceOffTargetRestriction target A) g := by
  simp only [periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection,
    periodicHypercubicEvenSpatialSliceTargetOffTarget_symm_offTargetRestriction_eq_update,
    MeasurableEquiv.apply_symm_apply]
  rw [Function.update_comm hne.symm u g A]
  exact hInvariant left (Function.update A target g) u

/-- The direct old-first and first means have identical integrands under the
literal same target law. No integrability or law-identification premise is added. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOldFirstMean_eq_firstMean_of_sourceInvariant
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource source target : PeriodicHypercubicEvenSpatialSliceLink H)
    (hne : target ≠ source) (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (F : (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hInvariant : ∀ (left right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
      (value : Matrix.specialUnitaryGroup (Fin N) ℂ),
      F (left, Function.update right source value) = F (left, right))
    (left : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (center : ℝ)
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      (Matrix.specialUnitaryGroup (Fin N) ℂ × Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOldFirstMean
        H N hN beta hbeta B distinguishedSource source target k g₂ F left center z =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFirstMean
        H N hN beta hbeta B distinguishedSource source target k g₂ F left center z := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOldFirstMean
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFirstMean
  apply integral_congr_ae
  filter_upwards with g
  change
    periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
        H N target F left
        (periodicHypercubicEvenSpatialSliceOffTargetRestriction target
          (Function.update z.1 source z.2.1)) g - center =
      periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
        H N target F left
        (periodicHypercubicEvenSpatialSliceOffTargetRestriction target
          (Function.update z.1 source z.2.2)) g - center
  rw [periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection_sourceUpdate_eq_of_sourceInvariant
      H N target source hne F hInvariant left z.1 z.2.1 g,
    periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection_sourceUpdate_eq_of_sourceInvariant
      H N target source hne F hInvariant left z.1 z.2.2 g]

/-- Exact vanishing of the direct vector on its existing source-pair L2 carrier. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawDirectDifferenceL2_eq_zero_of_sourceInvariant
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource source target : PeriodicHypercubicEvenSpatialSliceLink H)
    (hne : target ≠ source) (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (F : (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F) (bound : ℝ) (hbound : ∀ z, ‖F z‖ ≤ bound)
    (hInvariant : ∀ (left right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
      (value : Matrix.specialUnitaryGroup (Fin N) ℂ),
      F (left, Function.update right source value) = F (left, right))
    (left : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (center : ℝ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawDirectDifferenceL2
      H N hN beta hbeta B distinguishedSource source target k g₂
      F hF bound hbound left center = 0 := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawDirectDifferenceL2
  apply sub_eq_zero.mpr
  apply Lp.ext
  filter_upwards [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOldFirstMeanL2_coeFn
      H N hN beta hbeta B distinguishedSource source target k g₂ F hF bound hbound left center,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFirstMeanL2_coeFn
      H N hN beta hbeta B distinguishedSource source target k g₂ F hF bound hbound left center
  ] with z hOld hFirst
  rw [hOld, hFirst]
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOldFirstMean_eq_firstMean_of_sourceInvariant
      H N hN beta hbeta B distinguishedSource source target hne k g₂ F hInvariant left center z

/-- After direct cancellation, the full vector is exactly the existing response.
The source-pair measure is kept unchanged throughout this equality. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFullDifferenceL2_eq_responseL2_of_sourceInvariant
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource source target : PeriodicHypercubicEvenSpatialSliceLink H)
    (hne : target ≠ source) (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (F : (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F) (bound : ℝ) (hbound : ∀ z, ‖F z‖ ≤ bound)
    (hInvariant : ∀ (left right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
      (value : Matrix.specialUnitaryGroup (Fin N) ℂ),
      F (left, Function.update right source value) = F (left, right))
    (left : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (center : ℝ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFullDifferenceL2
        H N hN beta hbeta B distinguishedSource source target k g₂
        F hF bound hbound left center =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseL2
        H N hN beta hbeta B distinguishedSource source target k g₂
        F hF bound hbound left center := by
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFullDifferenceL2_eq_directDifferenceL2_add_responseL2_of_ne
      H N hN beta hbeta B distinguishedSource source target hne k g₂ F hF bound hbound left center,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawDirectDifferenceL2_eq_zero_of_sourceInvariant
      H N hN beta hbeta B distinguishedSource source target hne k g₂ F hF bound hbound hInvariant left center,
    zero_add]

/-- One bounded representative of the actual source update cancels the direct
term simultaneously in every off-diagonal target/background context. The
representative is chosen before all those contexts, by the existing #4925 API. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2_exists_bounded_representative_directCancellation
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (source : PeriodicHypercubicEvenSpatialSliceLink H)
    (f : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2 H N hN beta hbeta)
    (hf : f ∈ periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore
      H N hN beta hbeta) :
    ∃ (F : (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
      (hF : StronglyMeasurable F) (bound : ℝ) (hbound : ∀ z, ‖F z‖ ≤ bound),
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
          H N hN beta hbeta F hF bound hbound =
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
          H N hN beta hbeta source f ∧
      (∀ (left right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
        (value : Matrix.specialUnitaryGroup (Fin N) ℂ),
        F (left, Function.update right source value) = F (left, right)) ∧
      ∀ (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
        (distinguishedSource target : PeriodicHypercubicEvenSpatialSliceLink H),
        target ≠ source →
        ∀ (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
          (left : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) (center : ℝ),
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawDirectDifferenceL2
              H N hN beta hbeta B distinguishedSource source target k g₂
              F hF bound hbound left center = 0 ∧
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFullDifferenceL2
                H N hN beta hbeta B distinguishedSource source target k g₂
                F hF bound hbound left center =
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseL2
                H N hN beta hbeta B distinguishedSource source target k g₂
                F hF bound hbound left center := by
  obtain ⟨F, hF, bound, hbound, hRep, hInvariant⟩ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2_exists_bounded_sourceInvariant_representative
      H N hN beta hbeta source f hf
  refine ⟨F, hF, bound, hbound, hRep, hInvariant, ?_⟩
  intro B distinguishedSource target hne k g₂ left center
  exact ⟨
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawDirectDifferenceL2_eq_zero_of_sourceInvariant
      H N hN beta hbeta B distinguishedSource source target hne k g₂ F hF bound hbound hInvariant left center,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFullDifferenceL2_eq_responseL2_of_sourceInvariant
      H N hN beta hbeta B distinguishedSource source target hne k g₂ F hF bound hbound hInvariant left center⟩

end

end MGAP4D.MathlibAnalytic
