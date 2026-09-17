import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceFixedRightTargetRatioRemoteAggregateOneStepLeftTransport
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceFixedRightTargetRatioTwoStepRemoteTransport
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

local instance fixedRightTargetRatioRemoteAggregateTwoStepSourceTransportSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The first nonzero represented-source response of the support-preserving
remote aggregate appears at two restricted random-scan steps and is exactly the
remote-target count times the singleton two-step coefficient.  Both scan
normalizations remain explicit. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioRemoteAggregateVariation_twoStep_rightSource_eq
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (source distinguishedTarget : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanVariationIterate
        H beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioRemoteAggregateVariation
          H beta source distinguishedTarget)
        2 (Sum.inr source) =
      ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceC5RemoteTargetFibers
          H source distinguishedTarget).card : ℝ) *
        ((Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ)⁻¹ *
          (2 * (((Real.exp (8 * beta)) ^ 2 - 1) /
            ((Real.exp (8 * beta)) ^ 2 + 1)) *
            ((Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ)⁻¹ *
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberOffFiberInfluence
                beta * Real.exp (16 * beta))))) := by
  rfl

end

end MathlibAnalytic
end MGAP4D
