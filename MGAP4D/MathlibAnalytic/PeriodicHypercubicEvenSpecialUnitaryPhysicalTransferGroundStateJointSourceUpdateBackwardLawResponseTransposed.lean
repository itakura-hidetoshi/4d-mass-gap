import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferCurrentValueReferenceReanchor
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourcePairCanonicalTargetLawResponse
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSixSpatialSweepStageSourceUpdateBackwardDirectMeanSplit
import Mathlib.Tactic

/-!
# Exact transposed presentation of the backward source-law response

For a current-value outer boundary C, fix a source link and change a distinct
target link of a right background A:

  D = A[target <- g].

The backward source-law response is the change of the source conditional mean
caused only by replacing the source law based at A by the source law based at
D.

PR #4875 proves that at current-value parameters the bookkeeping reference
target/source can be re-anchored exactly without changing the physical fiber
law.  Re-anchor the source fiber from referenceTarget = source to
referenceTarget = target.  The resulting difference is exactly the negative
of the already-existing canonical target-law response with geometric indices
transposed:

  BackwardLawResponse(source; A,D)
    =
  - Response(target = source, source = target; u = g, v = A target).

This is an exact identity.  It is not a response-symmetry assumption and
introduces no comparison coefficient, triangle inequality, factor two, or
finite-cardinality factor.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory ProbabilityTheory

noncomputable section

local instance backwardLawResponseTransposedSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance backwardLawResponseTransposedSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance backwardLawResponseTransposedSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance backwardLawResponseTransposedSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance backwardLawResponseTransposedSpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance backwardLawResponseTransposedSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- At current-value parameters, one off-source target update turns the pure
backward source-law response exactly into the negative canonical response with
the geometric source/target roles transposed. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardLawResponse_currentValue_targetUpdate_eq_neg_transposedCanonicalTargetLawResponse_of_bounded
    (H N : ℕ) (hN : 0 < N)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (C A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource source target :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (hne : source ≠ target)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardLawResponse
        H N hN beta hbeta source F C C distinguishedSource
        (C distinguishedSource) (C source)
        (A, Function.update A target g) =
      -periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponse
        H N hN beta hbeta source target F C C A distinguishedSource
        (C distinguishedSource) (C target) g (A target) 0 := by
  let D := Function.update A target g
  let Y : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ :=
    fun v => F (C, Function.update A source v)
  let μA :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
      H N hN beta hbeta C source distinguishedSource source
      (C distinguishedSource) (C source) A
  let μD :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
      H N hN beta hbeta C source distinguishedSource source
      (C distinguishedSource) (C source) D
  let νA :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
      H N hN beta hbeta C target distinguishedSource source
      (C distinguishedSource) (C target) A
  let νD :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
      H N hN beta hbeta C target distinguishedSource source
      (C distinguishedSource) (C target) D
  letI : IsProbabilityMeasure μA :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_isProbabilityMeasure
      H N hN beta hbeta C source distinguishedSource source
      (C distinguishedSource) (C source) A
  letI : IsProbabilityMeasure μD :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_isProbabilityMeasure
      H N hN beta hbeta C source distinguishedSource source
      (C distinguishedSource) (C source) D
  letI : IsProbabilityMeasure νA :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_isProbabilityMeasure
      H N hN beta hbeta C target distinguishedSource source
      (C distinguishedSource) (C target) A
  letI : IsProbabilityMeasure νD :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_isProbabilityMeasure
      H N hN beta hbeta C target distinguishedSource source
      (C distinguishedSource) (C target) D
  have hYStrong : StronglyMeasurable Y := by
    exact
      (hF.comp_measurable
        (measurable_const.prodMk (measurable_update A))).sub
        stronglyMeasurable_const |>.add stronglyMeasurable_const
  have hYBound : ∀ v, ‖Y v‖ ≤ |bound| := by
    intro v
    exact (hbound (C, Function.update A source v)).trans (le_abs_self bound)
  have hYA : Integrable Y μA := by
    exact
      (MemLp.of_bound hYStrong.aestronglyMeasurable |bound|
        (Filter.Eventually.of_forall hYBound)).integrable one_le_two
  have hYD : Integrable Y μD := by
    exact
      (MemLp.of_bound hYStrong.aestronglyMeasurable |bound|
        (Filter.Eventually.of_forall hYBound)).integrable one_le_two
  have hReanchorA : μA = νA := by
    simpa [μA, νA] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_currentValue_reanchor
        H N hN beta hbeta C A
        source distinguishedSource target distinguishedSource source
  have hReanchorD : μD = νD := by
    simpa [μD, νD, D] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_currentValue_reanchor
        H N hN beta hbeta C D
        source distinguishedSource target distinguishedSource source
  have hBackward :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardLawResponse
          H N hN beta hbeta source F C C distinguishedSource
          (C distinguishedSource) (C source) (A, D) =
        -((∫ v, Y v ∂μD) - ∫ v, Y v ∂μA) := by
    unfold
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardLawResponse
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardDirectMean
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateDiagonalLocalMean
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateFullConfigurationDifference
    rw [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkConditionalKernel_apply,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkConditionalKernel_apply]
    change
      (∫ v, F (C, A) - Y v ∂μD) -
          (∫ v, F (C, A) - Y v ∂μA) =
        -((∫ v, Y v ∂μD) - ∫ v, Y v ∂μA)
    rw [
      integral_sub (integrable_const _) hYD,
      integral_sub (integrable_const _) hYA,
      integral_const, integral_const]
    simp
    ring
  have hResponse :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponse
          H N hN beta hbeta source target F C C A distinguishedSource
          (C distinguishedSource) (C target) g (A target) 0 =
        (∫ v, Y v ∂νD) - ∫ v, Y v ∂νA := by
    have hne' : source ≠ target := hne
    unfold
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponse
    rw [if_neg hne']
    simp only [sub_zero]
    have hUpdateSelf :
        Function.update A target (A target) = A := by
      simp
    rw [hUpdateSelf]
    change
      (∫ v,
        periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
          H N source F C
          (periodicHypercubicEvenSpatialSliceOffTargetRestriction source A) v
        ∂νD) -
        ∫ v,
          periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
            H N source F C
            (periodicHypercubicEvenSpatialSliceOffTargetRestriction source A) v
          ∂νA =
        (∫ v, Y v ∂νD) - ∫ v, Y v ∂νA
    apply congrArg₂ (fun x y : ℝ => x - y)
    · apply integral_congr_ae
      filter_upwards with v
      simpa [Y] using
        periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection_offTargetRestriction_eq_update
          H N source F C A v
    · apply integral_congr_ae
      filter_upwards with v
      simpa [Y] using
        periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection_offTargetRestriction_eq_update
          H N source F C A v
  rw [show Function.update A target g = D by rfl]
  rw [hBackward, hResponse]
  rw [← hReanchorD, ← hReanchorA]

end

end MGAP4D.MathlibAnalytic
