import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourcePairSweepResponseResidualEnergy
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourcePairFixedBackgroundResponseFubini
import Mathlib.Tactic

/-!
# Actual full source-pair response sums inherit the Schur amplitude bound

The fixed-C response amplitude matrix introduced in PR #4836 is not merely an
auxiliary scalar majorant.  Off the response diagonal its entries are exactly
the norms of the corresponding full source-pair response L2 vectors, by the
exact fixed-background/full-background Fubini identity.  On the diagonal both
the response and the amplitude vanish.

For each fixed source all target response vectors lie in the same
source-specific Hilbert carrier.  Hence Mathlib's finite norm triangle
inequality gives

  || sum_target ResponseL2(source,target) ||
    <= sum_target A_resp^C(source,target).

Squaring and summing in source therefore transfers the PR #4848
vacuum-integrated amplitude estimate to the actual finite response sums,
without a finite-cardinality Cauchy loss.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory BigOperators

noncomputable section

local instance fullResponseSumEnergySpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance fullResponseSumEnergySpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance fullResponseSumEnergySpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance fullResponseSumEnergySpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance fullResponseSumEnergySpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance fullResponseSumEnergySpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The full current-value source-pair response vanishes on the response
diagonal. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseL2_currentValue_diag
    (H N : ℕ) (hN : 0 < N)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource source :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseL2
        H N hN beta hbeta C distinguishedSource source source
        (C distinguishedSource) (C source)
        F hF bound hbound C 0 = 0 := by
  apply Lp.ext
  filter_upwards [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseL2_coeFn
      H N hN beta hbeta C distinguishedSource source source
      (C distinguishedSource) (C source)
      F hF bound hbound C 0] with z hz
  have hPoint :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseOnCarrier_eq
      H N hN beta hbeta C distinguishedSource source source
      (C distinguishedSource) (C source)
      F C 0 z
  simpa using hz.trans hPoint

/-- Every fixed-C amplitude-matrix entry is exactly the norm of the
corresponding full current-value source-pair response L2 vector. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundResponseAmplitudeMatrix_eq_fullResponseL2_norm
    (H N : ℕ) (hN : 0 < N)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource source target :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundResponseAmplitudeMatrix
        H N hN beta hbeta C distinguishedSource F hF bound hbound
        source target =
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseL2
          H N hN beta hbeta C distinguishedSource source target
          (C distinguishedSource) (C source)
          F hF bound hbound C 0‖ := by
  by_cases hEq : source = target
  · subst target
    rw [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundResponseAmplitudeMatrix_diag,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseL2_currentValue_diag,
      norm_zero]
  · unfold
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundResponseAmplitudeMatrix
    unfold
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundResponseEnergyMatrix
    rw [if_neg hEq]
    rw [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundResponseAmplitudeEnergy_eq_fullResponseL2_norm_sq_ofReal]
    rw [ENNReal.toReal_ofReal (sq_nonneg _)]
    exact Real.sqrt_sq (norm_nonneg _)

/-- At each fixed outer boundary C, the actual full source-pair finite response
sums are dominated by the response-amplitude matrix energy. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairLinkIndexedFullResponseL2_sum_norm_sq_sum_le_fixedBackgroundResponseAmplitude_sum_sq
    (H N : ℕ) (hN : 0 < N)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource : PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      PeriodicHypercubicEvenSpatialSliceLink H →
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : ∀ e, StronglyMeasurable (F e))
    (bound : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hbound : ∀ e z, ‖F e z‖ ≤ bound e) :
    (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
      ‖∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseL2
          H N hN beta hbeta C distinguishedSource source target
          (C distinguishedSource) (C source)
          (F target) (hF target) (bound target) (hbound target) C 0‖ ^ 2) ≤
      ∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
        (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundResponseAmplitudeMatrix
            H N hN beta hbeta C distinguishedSource
            (F target) (hF target) (bound target) (hbound target)
            source target) ^ 2 := by
  apply Finset.sum_le_sum
  intro source hsource
  have hNorm :
      ‖∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseL2
          H N hN beta hbeta C distinguishedSource source target
          (C distinguishedSource) (C source)
          (F target) (hF target) (bound target) (hbound target) C 0‖ ≤
        ∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundResponseAmplitudeMatrix
            H N hN beta hbeta C distinguishedSource
            (F target) (hF target) (bound target) (hbound target)
            source target := by
    calc
      ‖∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseL2
          H N hN beta hbeta C distinguishedSource source target
          (C distinguishedSource) (C source)
          (F target) (hF target) (bound target) (hbound target) C 0‖ ≤
        ∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
          ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseL2
            H N hN beta hbeta C distinguishedSource source target
            (C distinguishedSource) (C source)
            (F target) (hF target) (bound target) (hbound target) C 0‖ :=
        norm_sum_le _ _
      _ =
        ∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundResponseAmplitudeMatrix
            H N hN beta hbeta C distinguishedSource
            (F target) (hF target) (bound target) (hbound target)
            source target := by
        apply Finset.sum_congr rfl
        intro target htarget
        symm
        exact
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundResponseAmplitudeMatrix_eq_fullResponseL2_norm
            H N hN beta hbeta C distinguishedSource source target
            (F target) (hF target) (bound target) (hbound target)
  have hRight0 :
      0 ≤
        ∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundResponseAmplitudeMatrix
            H N hN beta hbeta C distinguishedSource
            (F target) (hF target) (bound target) (hbound target)
            source target := by
    exact Finset.sum_nonneg (fun target _ =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundResponseAmplitudeMatrix_nonneg
        H N hN beta hbeta C distinguishedSource
        (F target) (hF target) (bound target) (hbound target)
        source target)
  exact
    (sq_le_sq₀
      (norm_nonneg _)
      hRight0).2 hNorm

/-- For every bounded-core vector one can choose the canonical link-indexed
sweep-stage representatives so that the actual full response sums, not only
their scalar amplitude matrix, are charged to the genuine six-spatial
residual energy. -/
theorem
    exists_periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweep_linkIndexedRepresentatives_fullResponseL2Sum_vacuum_lintegral_le_responseResidualCoefficient_mul_sixSpatialResidualEnergy_ofReal
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
            ‖∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseL2
                H N hN beta hbeta C distinguishedSource source target
                (C distinguishedSource) (C source)
                (F target) (hF target) (bound target) (hbound target) C 0‖ ^ 2)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
          H N hN beta hbeta) ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundResponseResidualCoefficient
            s beta *
          ENNReal.ofReal
            (6 *
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSixSpatialResidualEnergy
                H N hN beta hbeta f) := by
  rcases
      exists_periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweep_linkIndexedRepresentatives_responseAmplitude_vacuum_lintegral_le_responseResidualCoefficient_mul_sixSpatialResidualEnergy_ofReal
        N hN s hs beta hbeta hcut H distinguishedSource f hf with
    ⟨F, hF, bound, hbound, hRep, hAmplitude⟩
  refine ⟨F, hF, bound, hbound, hRep, ?_⟩
  have hPoint :
      ∀ C,
        ENNReal.ofReal
          (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
            ‖∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseL2
                H N hN beta hbeta C distinguishedSource source target
                (C distinguishedSource) (C source)
                (F target) (hF target) (bound target) (hbound target) C 0‖ ^ 2) ≤
          ENNReal.ofReal
            (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
              (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
                periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundResponseAmplitudeMatrix
                  H N hN beta hbeta C distinguishedSource
                  (F target) (hF target) (bound target) (hbound target)
                  source target) ^ 2) := by
    intro C
    exact ENNReal.ofReal_le_ofReal
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairLinkIndexedFullResponseL2_sum_norm_sq_sum_le_fixedBackgroundResponseAmplitude_sum_sq
        H N hN beta hbeta C distinguishedSource
        F hF bound hbound)
  exact
    (lintegral_mono hPoint).trans hAmplitude

end

end MGAP4D.MathlibAnalytic
