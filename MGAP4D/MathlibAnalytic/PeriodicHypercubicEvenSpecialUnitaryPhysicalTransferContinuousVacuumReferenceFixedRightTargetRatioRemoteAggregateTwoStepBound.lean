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
  rfl

end

end MathlibAnalytic
end MGAP4D
