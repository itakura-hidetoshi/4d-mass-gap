import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceFixedRightTargetRatioRemoteTransportAggregate
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

local instance fixedRightTargetRatioRemoteAggregateVariationPointwiseSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The support-preserving aggregate remote target-ratio variation is exactly
`exp (16 * beta)` on the actual C5 remote target set and zero off that set.
No cardinality factor or targetwise supremum is introduced. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioRemoteAggregateVariation_eq
    (H : ℕ)
    (beta : ℝ)
    (source distinguishedTarget e : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioRemoteAggregateVariation
        H beta source distinguishedTarget e =
      if e ∈
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceC5RemoteTargetFibers
            H source distinguishedTarget then
        Real.exp (16 * beta)
      else 0 := by
  classical
  simp [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioRemoteAggregateVariation,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation]

end

end MathlibAnalytic
end MGAP4D
