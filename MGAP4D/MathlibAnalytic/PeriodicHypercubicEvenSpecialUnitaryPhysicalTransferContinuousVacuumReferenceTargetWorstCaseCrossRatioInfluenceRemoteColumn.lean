import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceTargetWorstCaseCrossRatioInfluenceMajorant
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceFixedRightTargetRatioRemoteAggregateIterateSuperposition
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

local instance targetWorstCaseCrossRatioInfluenceRemoteColumnSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Sum the targetwise worst-case transformed remote cross-ratio majorants over
the canonical C5 remote target family.  Each target takes its own supremum over
all four SU(N) test values before the finite spatial sum is formed. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioWorstCaseRemoteCrossRatioInfluenceColumn
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (source distinguishedTarget : PeriodicHypercubicEvenSpatialSliceLink H) : ℝ :=
  ∑ target ∈
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceC5RemoteTargetFibers
        H source distinguishedTarget,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioWorstCaseCrossRatioInfluenceMajorant
      H N hN beta hbeta B target source

/-- The entire targetwise worst-case remote column is controlled by the same
aggregate finite-step tagged transport as the chosen-family column.  Taking the
targetwise supremum introduces neither a remote-target cardinality multiplier
nor a common global SU(N) tuple.

This is still a transformed cross-ratio majorant column.  It does not identify
the older dense tagged carrier with a sparse physical kernel and does not yet
assert an actual conditional-law influence coefficient. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioWorstCaseRemoteCrossRatioInfluenceColumn_le_exp_sixteen_mul_nStepAggregateRight_add_two_mul_leftVariationTotal
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (source distinguishedTarget : PeriodicHypercubicEvenSpatialSliceLink H)
    (n : ℕ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioWorstCaseRemoteCrossRatioInfluenceColumn
        H N hN beta hbeta B source distinguishedTarget ≤
      Real.exp (16 * beta) *
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanVariationIterate
            H beta hbeta
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioRemoteAggregateVariation
              H beta source distinguishedTarget)
            n (Sum.inr source) +
          2 *
            ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanVariationIterate
                H beta hbeta
                (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioRemoteAggregateVariation
                  H beta source distinguishedTarget)
                n (Sum.inl e)) := by
  classical
  let remote :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceC5RemoteTargetFibers
      H source distinguishedTarget
  let q :=
    fun target : PeriodicHypercubicEvenSpatialSliceLink H =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation
        H beta target
  let Q :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanVariationIterate
      H beta hbeta
  calc
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioWorstCaseRemoteCrossRatioInfluenceColumn
        H N hN beta hbeta B source distinguishedTarget =
      ∑ target ∈ remote,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioWorstCaseCrossRatioInfluenceMajorant
          H N hN beta hbeta B target source := by
            rfl
    _ ≤
      ∑ target ∈ remote,
        Real.exp (16 * beta) *
          (Q (q target) n (Sum.inr source) +
            2 *
              ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
                Q (q target) n (Sum.inl e)) := by
      apply Finset.sum_le_sum
      intro target hTarget
      have hRemote :
          target ∉
            periodicHypercubicEvenSpatialSliceC5ExceptionalBackgroundFibers
              H source distinguishedTarget := by
        simpa [
          remote,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceC5RemoteTargetFibers] using
          hTarget
      rcases
        periodicHypercubicEvenSpatialSlice_not_mem_C5ExceptionalBackgroundFibers
          H source distinguishedTarget target hRemote with
        ⟨hSourceTarget, _hTargetDistinguished, hNoShare⟩
      simpa [Q, q] using
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioWorstCaseCrossRatioInfluenceMajorant_le_exp_sixteen_mul_nStepTargetBound_of_remote
          H N hN beta hbeta B
          (target := target) (source := source)
          (Ne.symm hSourceTarget) hNoShare n
    _ =
      Real.exp (16 * beta) *
        (∑ target ∈ remote,
            Q (q target) n (Sum.inr source) +
          2 *
            ∑ target ∈ remote,
              ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
                Q (q target) n (Sum.inl e)) := by
      rw [Finset.mul_sum]
      congr 1
      rw [Finset.sum_add_distrib]
      congr 1
      rw [Finset.mul_sum]
    _ =
      Real.exp (16 * beta) *
        (∑ target ∈ remote,
            Q (q target) n (Sum.inr source) +
          2 *
            ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
              ∑ target ∈ remote,
                Q (q target) n (Sum.inl e)) := by
      congr 1
      congr 1
      rw [Finset.sum_comm]
    _ =
      Real.exp (16 * beta) *
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanVariationIterate
            H beta hbeta
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioRemoteAggregateVariation
              H beta source distinguishedTarget)
            n (Sum.inr source) +
          2 *
            ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanVariationIterate
                H beta hbeta
                (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioRemoteAggregateVariation
                  H beta source distinguishedTarget)
                n (Sum.inl e)) := by
      congr 1
      · symm
        simpa [remote, Q, q] using
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioRemoteAggregateVariation_iterate_eq_sum
            H beta hbeta source distinguishedTarget n (Sum.inr source)
      · congr 1
        apply Finset.sum_congr rfl
        intro e hE
        symm
        simpa [remote, Q, q] using
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioRemoteAggregateVariation_iterate_eq_sum
            H beta hbeta source distinguishedTarget n (Sum.inl e)

end

end MathlibAnalytic
end MGAP4D
