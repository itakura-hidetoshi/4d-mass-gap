import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceFixedRightTargetRatioOneStepRemoteTransport
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

local instance fixedRightTargetRatioOneStepRemoteLeftTransportSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- After one physical-target restricted random-scan step, a remote physical
left coordinate receives exactly one averaged off-fiber contribution from the
singleton target variation.  This is the first nonzero propagation coefficient
behind the delayed represented-source response. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation_oneStep_remoteLeft_eq
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    {target source : PeriodicHypercubicEvenSpatialSliceLink H}
    (hne : target ≠ source) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanVariationIterate
        H beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation
          H beta target)
        1 (Sum.inl source) =
      (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ)⁻¹ *
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberOffFiberInfluence
            beta * Real.exp (16 * beta)) := by
  rfl

end

end MathlibAnalytic
end MGAP4D
