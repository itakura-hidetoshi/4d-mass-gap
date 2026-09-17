import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceFixedRightTargetRatioRemoteAggregateTwoStepSourceTransport
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceFixedRightTargetRatioTwoStepRemoteColumn
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

local instance fixedRightTargetRatioRemoteAggregateTwoStepBoundSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The first nonzero represented-source transport of the support-preserving
remote aggregate is bounded independently of periodic volume.  This packages
the exact aggregate two-step identity into the existing complete non-source
column bound without replacing the remote support by a targetwise supremum. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioRemoteAggregateVariation_twoStep_rightSource_le
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (source distinguishedTarget : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanVariationIterate
        H beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioRemoteAggregateVariation
          H beta source distinguishedTarget)
        2 (Sum.inr source) ≤
      2 * (((Real.exp (8 * beta)) ^ 2 - 1) /
        ((Real.exp (8 * beta)) ^ 2 + 1)) *
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberOffFiberInfluence
          beta * Real.exp (16 * beta)) := by
  classical
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioRemoteAggregateVariation_iterate_eq_sum]
  calc
    (∑ target ∈
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceC5RemoteTargetFibers
          H source distinguishedTarget,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanVariationIterate
        H beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation
          H beta target)
        2 (Sum.inr source)) ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation_twoStep_remoteRightColumnSum
          H beta hbeta source := by
      unfold
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation_twoStep_remoteRightColumnSum
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro target hTarget
        have hRemote :
            target ∉
              periodicHypercubicEvenSpatialSliceC5ExceptionalBackgroundFibers
                H source distinguishedTarget := by
          simpa [
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceC5RemoteTargetFibers] using
            hTarget
        rcases
          periodicHypercubicEvenSpatialSlice_not_mem_C5ExceptionalBackgroundFibers
            H source distinguishedTarget target hRemote with
          ⟨hSourceTarget, _hTargetDistinguished, _hNoShare⟩
        exact Finset.mem_erase.mpr ⟨Ne.symm hSourceTarget, Finset.mem_univ target⟩
      · intro target _hTarget _hNotRemote
        exact
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanVariationIterate_nonneg
            H beta hbeta
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation
              H beta target)
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation_nonneg
              H beta target)
            2 (Sum.inr source)
    _ ≤
      2 * (((Real.exp (8 * beta)) ^ 2 - 1) /
        ((Real.exp (8 * beta)) ^ 2 + 1)) *
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberOffFiberInfluence
          beta * Real.exp (16 * beta)) :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation_twoStep_remoteRightColumnSum_le
        H beta hbeta source

end

end MathlibAnalytic
end MGAP4D
