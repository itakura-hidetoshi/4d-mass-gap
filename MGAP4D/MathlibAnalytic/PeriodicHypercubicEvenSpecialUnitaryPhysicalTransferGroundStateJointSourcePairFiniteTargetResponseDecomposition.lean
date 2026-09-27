import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourcePairTargetLawL2SemanticIdentification
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourcePairFullResponseSumEnergy
import Mathlib.Tactic

/-!
# Finite target decomposition of the physical source-update response

PR #4850 proves, for every off-diagonal target/source pair in one common
source-pair Hilbert carrier,

  fullDifferenceL2 = directDifferenceL2 + responseL2.

PR #4851 identifies the direct and full L2 differences with the actual
physical source-updated centered-mean differences.  PR #4849 proves the
current-value response is zero on the diagonal and controls the complete
finite response sum in L2.

This file performs the finite target assembly at fixed outer boundary C and
fixed source s:

  sum_{t != s} fullDifference(s,t)
    =
  sum_{t != s} directDifference(s,t)
    + sum_t response(s,t).

The diagonal response disappears exactly, so the final response sum can be
taken over all targets and matches the PR #4849 Schur-controlled quantity.

Consequently the difference between the finite full-update sum and the finite
direct-update sum is exactly the actual response sum, and its vacuum-integrated
source energy inherits the PR #4849 bound.

No target ordering, sweep telescoping, response symmetry, new coefficient, or
finite-cardinality factor is introduced here.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory BigOperators

noncomputable section

local instance finiteTargetResponseDecompositionSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance finiteTargetResponseDecompositionSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance finiteTargetResponseDecompositionSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance finiteTargetResponseDecompositionSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance finiteTargetResponseDecompositionSpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance finiteTargetResponseDecompositionSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- At fixed C and fixed source, the sum of all off-diagonal physical full
source-update differences is the sum of the corresponding direct differences
plus the complete target-law response sum. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairLinkIndexedCurrentValueOffDiagonalFullDifferenceL2_sum_eq_directDifferenceL2_sum_add_responseL2_sum
    (H N : ℕ) (hN : 0 < N)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource source :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      PeriodicHypercubicEvenSpatialSliceLink H →
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : ∀ e, StronglyMeasurable (F e))
    (bound : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hbound : ∀ e z, ‖F e z‖ ≤ bound e) :
    (∑ target ∈
        (Finset.univ.erase source :
          Finset (PeriodicHypercubicEvenSpatialSliceLink H)),
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFullDifferenceL2
        H N hN beta hbeta C distinguishedSource source target
        (C distinguishedSource) (C source)
        (F target) (hF target) (bound target) (hbound target) C 0) =
      (∑ target ∈
          (Finset.univ.erase source :
            Finset (PeriodicHypercubicEvenSpatialSliceLink H)),
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawDirectDifferenceL2
          H N hN beta hbeta C distinguishedSource source target
          (C distinguishedSource) (C source)
          (F target) (hF target) (bound target) (hbound target) C 0) +
        ∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseL2
            H N hN beta hbeta C distinguishedSource source target
            (C distinguishedSource) (C source)
            (F target) (hF target) (bound target) (hbound target) C 0 := by
  classical
  let S :=
    (Finset.univ.erase source :
      Finset (PeriodicHypercubicEvenSpatialSliceLink H))
  let direct :=
    fun target : PeriodicHypercubicEvenSpatialSliceLink H =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawDirectDifferenceL2
        H N hN beta hbeta C distinguishedSource source target
        (C distinguishedSource) (C source)
        (F target) (hF target) (bound target) (hbound target) C 0
  let response :=
    fun target : PeriodicHypercubicEvenSpatialSliceLink H =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseL2
        H N hN beta hbeta C distinguishedSource source target
        (C distinguishedSource) (C source)
        (F target) (hF target) (bound target) (hbound target) C 0
  have hOff :
      (∑ target ∈ S,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFullDifferenceL2
          H N hN beta hbeta C distinguishedSource source target
          (C distinguishedSource) (C source)
          (F target) (hF target) (bound target) (hbound target) C 0) =
        ∑ target ∈ S, (direct target + response target) := by
    apply Finset.sum_congr rfl
    intro target htarget
    have hne : target ≠ source :=
      (Finset.mem_erase.mp htarget).1
    simpa [direct, response] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFullDifferenceL2_eq_directDifferenceL2_add_responseL2_of_ne
        H N hN beta hbeta C distinguishedSource source target hne
        (C distinguishedSource) (C source)
        (F target) (hF target) (bound target) (hbound target) C 0
  have hDiag : response source = 0 := by
    simpa [response] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseL2_currentValue_diag
        H N hN beta hbeta C distinguishedSource source
        (F source) (hF source) (bound source) (hbound source)
  have hErase :
      (∑ target ∈ S, response target) =
        ∑ target : PeriodicHypercubicEvenSpatialSliceLink H, response target := by
    have hSplit :=
      Finset.sum_erase_add
        (s := (Finset.univ :
          Finset (PeriodicHypercubicEvenSpatialSliceLink H)))
        response
        (Finset.mem_univ source)
    simpa [S, hDiag] using hSplit
  calc
    (∑ target ∈ S,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFullDifferenceL2
        H N hN beta hbeta C distinguishedSource source target
        (C distinguishedSource) (C source)
        (F target) (hF target) (bound target) (hbound target) C 0) =
        ∑ target ∈ S, (direct target + response target) := hOff
    _ = (∑ target ∈ S, direct target) + ∑ target ∈ S, response target := by
      exact Finset.sum_add_distrib
    _ = (∑ target ∈ S, direct target) +
        ∑ target : PeriodicHypercubicEvenSpatialSliceLink H, response target := by
      rw [hErase]
    _ = _ := by
      rfl

/-- The finite full-minus-direct update error is exactly the actual target-law
response sum, so the PR #4849 response-energy estimate transfers to that
physical error without any new loss. -/
theorem
    exists_periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweep_linkIndexedRepresentatives_fullMinusDirectDifference_vacuum_lintegral_le_responseResidualCoefficient_mul_sixSpatialResidualEnergy_ofReal
    (N : ℕ) (hN : 0 < N)
    (s : ℝ) (hs : 8 < s)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeBidirectionalShellCutoff
          s hs)
    (H : ℕ)
    (distinguishedSource : PeriodicHypercubicEvenSpatialSliceLink H)
    (f : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
      H N hN beta hbeta)
    (hf :
      f ∈
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore
          H N hN beta hbeta) :
    ∃
      (F :
        PeriodicHypercubicEvenSpatialSliceLink H →
          (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
      (hF : ∀ e, StronglyMeasurable (F e))
      (bound : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
      (hbound : ∀ e z, ‖F e z‖ ≤ bound e),
      (∀ e,
        ∃ pre :
          List
            (PeriodicHypercubicEvenFixedSpatialColorLink H
              (periodicHypercubicEvenSpatialSliceLinkColor H e)),
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
              H N hN beta hbeta
              (F e) (hF e) (bound e) (hbound e) =
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepStageVector
              H N hN beta hbeta
              (periodicHypercubicEvenSpatialSliceLinkColor H e) pre f) ∧
      (∫⁻ C,
        ENNReal.ofReal
          (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
            (‖
              (∑ target ∈
                  (Finset.univ.erase source :
                    Finset (PeriodicHypercubicEvenSpatialSliceLink H)),
                periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFullDifferenceL2
                  H N hN beta hbeta C distinguishedSource source target
                  (C distinguishedSource) (C source)
                  (F target) (hF target) (bound target) (hbound target) C 0) -
              (∑ target ∈
                  (Finset.univ.erase source :
                    Finset (PeriodicHypercubicEvenSpatialSliceLink H)),
                periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawDirectDifferenceL2
                  H N hN beta hbeta C distinguishedSource source target
                  (C distinguishedSource) (C source)
                  (F target) (hF target) (bound target) (hbound target) C 0)
            ‖ : ℝ) ^ 2)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
          H N hN beta hbeta) ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundResponseResidualCoefficient
            s beta *
          ENNReal.ofReal
            (6 *
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSixSpatialResidualEnergy
                H N hN beta hbeta f) := by
  rcases
      exists_periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweep_linkIndexedRepresentatives_fullResponseL2Sum_vacuum_lintegral_le_responseResidualCoefficient_mul_sixSpatialResidualEnergy_ofReal
        N hN s hs beta hbeta hcut H distinguishedSource f hf with
    ⟨F, hF, bound, hbound, hRep, hResponse⟩
  refine ⟨F, hF, bound, hbound, hRep, ?_⟩
  have hErr :
      ∀ C source,
        (∑ target ∈
            (Finset.univ.erase source :
              Finset (PeriodicHypercubicEvenSpatialSliceLink H)),
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFullDifferenceL2
            H N hN beta hbeta C distinguishedSource source target
            (C distinguishedSource) (C source)
            (F target) (hF target) (bound target) (hbound target) C 0) -
          (∑ target ∈
              (Finset.univ.erase source :
                Finset (PeriodicHypercubicEvenSpatialSliceLink H)),
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawDirectDifferenceL2
              H N hN beta hbeta C distinguishedSource source target
              (C distinguishedSource) (C source)
              (F target) (hF target) (bound target) (hbound target) C 0) =
          ∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseL2
              H N hN beta hbeta C distinguishedSource source target
              (C distinguishedSource) (C source)
              (F target) (hF target) (bound target) (hbound target) C 0 := by
    intro C source
    have hDecomp :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairLinkIndexedCurrentValueOffDiagonalFullDifferenceL2_sum_eq_directDifferenceL2_sum_add_responseL2_sum
        H N hN beta hbeta C distinguishedSource source
        F hF bound hbound
    rw [hDecomp]
    abel
  calc
    (∫⁻ C,
      ENNReal.ofReal
        (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
          (‖
            (∑ target ∈
                (Finset.univ.erase source :
                  Finset (PeriodicHypercubicEvenSpatialSliceLink H)),
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFullDifferenceL2
                H N hN beta hbeta C distinguishedSource source target
                (C distinguishedSource) (C source)
                (F target) (hF target) (bound target) (hbound target) C 0) -
            (∑ target ∈
                (Finset.univ.erase source :
                  Finset (PeriodicHypercubicEvenSpatialSliceLink H)),
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawDirectDifferenceL2
                H N hN beta hbeta C distinguishedSource source target
                (C distinguishedSource) (C source)
                (F target) (hF target) (bound target) (hbound target) C 0)
          ‖ : ℝ) ^ 2)
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
        H N hN beta hbeta) =
      ∫⁻ C,
        ENNReal.ofReal
          (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
            ‖∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseL2
                H N hN beta hbeta C distinguishedSource source target
                (C distinguishedSource) (C source)
                (F target) (hF target) (bound target) (hbound target) C 0‖ ^ 2)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
          H N hN beta hbeta := by
      apply lintegral_congr
      intro C
      apply congrArg ENNReal.ofReal
      apply Finset.sum_congr rfl
      intro source hsource
      rw [hErr C source]
    _ ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundResponseResidualCoefficient
          s beta *
        ENNReal.ofReal
          (6 *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSixSpatialResidualEnergy
              H N hN beta hbeta f) :=
      hResponse

end

end MGAP4D.MathlibAnalytic
