import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointStrictResponsePathLoss
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourcePairFiniteTargetResponseDecomposition
import Mathlib.Tactic

/-!
# Full-minus-direct physical update error is charged to sweep path loss

PR #4852 proves, for every fixed outer boundary and source, that the finite
off-diagonal full update minus the finite off-diagonal direct update is exactly
the complete target-law response sum.

PR #4858 charges that actual response sum to the exact canonical one-link sweep
path loss with the coefficient rhoResp(s,beta), and PR #4859/#4860 provide the
strict positive-beta cutoff on which rhoResp < 1.

This file combines those two theorem lines without introducing a new estimate:

  fullOffDiagonalSum - directOffDiagonalSum = sum_target ResponseL2

is substituted pointwise inside the outer vacuum lower integral.  Therefore

  errorEnergy
    <= rhoResp(s,beta) * ofReal(6 * sweepPathLoss(f)).

On the canonical strict-response cutoff the coefficient is at most one, giving

  errorEnergy <= ofReal(6 * sweepPathLoss(f)).

This is the first energy theorem whose left-hand side is the physical
full-versus-direct finite-update error rather than the auxiliary response sum.

No response symmetry, target reordering, factor two, new probability law, or
finite-cardinality factor is introduced.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory BigOperators

noncomputable section

local instance fullDirectErrorPathLossSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance fullDirectErrorPathLossSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- On the shell cutoff, choose the canonical-prefix representative family so
that the physical full-minus-direct finite-update error is charged to the exact
sweep path-loss carrier with the same response coefficient. -/
theorem
    exists_periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweep_linkIndexedRepresentatives_fullMinusDirectDifference_vacuum_lintegral_le_responseResidualCoefficient_mul_sixSweepPathLoss_ofReal
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
      (∫⁻ C,
        ENNReal.ofReal
          (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
            norm
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairLinkIndexedCurrentValueOffDiagonalFullDifferenceL2Sum
                  H N hN beta hbeta C distinguishedSource source
                  F hF bound hbound -
                periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairLinkIndexedCurrentValueOffDiagonalDirectDifferenceL2Sum
                  H N hN beta hbeta C distinguishedSource source
                  F hF bound hbound) ^ 2)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
          H N hN beta hbeta) ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundResponseResidualCoefficient
            s beta *
          ENNReal.ofReal
            (6 *
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepPathLoss
                H N hN beta hbeta f) := by
  rcases
      exists_periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweep_linkIndexedRepresentatives_fullResponseL2Sum_vacuum_lintegral_le_responseResidualCoefficient_mul_sixSweepPathLoss_ofReal
        N hN s hs beta hbeta hcut H distinguishedSource f hf with
    ⟨pre, suffix, F, hF, bound, hbound,
      hSplit, hFresh, hRep, hResponse⟩
  refine
    ⟨pre, suffix, F, hF, bound, hbound,
      hSplit, hFresh, hRep, ?_⟩
  have hErr :
      ∀ C source,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairLinkIndexedCurrentValueOffDiagonalFullDifferenceL2Sum
            H N hN beta hbeta C distinguishedSource source
            F hF bound hbound -
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairLinkIndexedCurrentValueOffDiagonalDirectDifferenceL2Sum
            H N hN beta hbeta C distinguishedSource source
            F hF bound hbound =
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
  have hEq :
      (∫⁻ C,
        ENNReal.ofReal
          (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
            norm
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairLinkIndexedCurrentValueOffDiagonalFullDifferenceL2Sum
                  H N hN beta hbeta C distinguishedSource source
                  F hF bound hbound -
                periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairLinkIndexedCurrentValueOffDiagonalDirectDifferenceL2Sum
                  H N hN beta hbeta C distinguishedSource source
                  F hF bound hbound) ^ 2)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
          H N hN beta hbeta) =
        ∫⁻ C,
          ENNReal.ofReal
            (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
              norm
                (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
                  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseL2
                    H N hN beta hbeta C distinguishedSource source target
                    (C distinguishedSource) (C source)
                    (F target) (hF target) (bound target) (hbound target) C 0) ^ 2)
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
            H N hN beta hbeta := by
    apply lintegral_congr
    intro C
    apply congrArg ENNReal.ofReal
    apply Finset.sum_congr rfl
    intro source hsource
    rw [hErr C source]
  rw [hEq]
  exact hResponse

/-- On the strict response cutoff, the same physical full-minus-direct update
error is bounded by the exact sweep path-loss carrier itself. -/
theorem
    exists_periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweep_linkIndexedRepresentatives_fullMinusDirectDifference_vacuum_lintegral_le_sixSweepPathLoss_ofReal
    (N : ℕ) (hN : 0 < N)
    (s : ℝ) (hs : 8 < s)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundResponseResidualStrictCutoff
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
      (∫⁻ C,
        ENNReal.ofReal
          (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
            norm
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairLinkIndexedCurrentValueOffDiagonalFullDifferenceL2Sum
                  H N hN beta hbeta C distinguishedSource source
                  F hF bound hbound -
                periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairLinkIndexedCurrentValueOffDiagonalDirectDifferenceL2Sum
                  H N hN beta hbeta C distinguishedSource source
                  F hF bound hbound) ^ 2)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
          H N hN beta hbeta) ≤
        ENNReal.ofReal
          (6 *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepPathLoss
              H N hN beta hbeta f) := by
  have hShell :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeBidirectionalShellCutoff
          s hs :=
    hcut.trans
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundResponseResidualStrictCutoff_le_shellCutoff
        s hs)
  rcases
      exists_periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweep_linkIndexedRepresentatives_fullMinusDirectDifference_vacuum_lintegral_le_responseResidualCoefficient_mul_sixSweepPathLoss_ofReal
        N hN s hs beta hbeta hShell H distinguishedSource f hf with
    ⟨pre, suffix, F, hF, bound, hbound,
      hSplit, hFresh, hRep, hError⟩
  refine
    ⟨pre, suffix, F, hF, bound, hbound,
      hSplit, hFresh, hRep, ?_⟩
  let rho :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundResponseResidualCoefficient
      s beta
  let E : ℝ≥0∞ :=
    ENNReal.ofReal
      (6 *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepPathLoss
          H N hN beta hbeta f)
  have hRho : rho < 1 := by
    simpa [rho] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundResponseResidualStrictCutoff_spec
        s hs beta hbeta hcut
  have hMul : rho * E ≤ E := by
    calc
      rho * E ≤ 1 * E := by
        gcongr
      _ = E := one_mul E
  exact hError.trans (by simpa [rho, E] using hMul)

end

end MGAP4D.MathlibAnalytic
