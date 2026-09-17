import MGAP4D.MathlibAnalytic.FiniteInfluenceKernelRestrictedTargetRandomScanSuperposition
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceFixedRightTargetRatioArbitraryStepRemoteResidualColumn
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

local instance fixedRightTargetRatioRemoteTransportAggregateSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The support-preserving aggregate of the singleton fixed-right target-ratio
variation profiles over the actual C5 remote target set. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioRemoteAggregateVariation
    (H : ℕ)
    (beta : ℝ)
    (source distinguishedTarget : PeriodicHypercubicEvenSpatialSliceLink H)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) : ℝ :=
  ∑ target ∈
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceC5RemoteTargetFibers
        H source distinguishedTarget,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation
      H beta target e

/-- The complete remote represented-source transport column is exactly one
restricted-target iterate of the aggregate remote singleton variation profile.
No targetwise supremum or volume-wide initial variation is introduced. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioNStepRemoteTransportColumn_eq_aggregateIterate
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (source distinguishedTarget : PeriodicHypercubicEvenSpatialSliceLink H)
    (n : ℕ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioNStepRemoteTransportColumn
        H beta hbeta source distinguishedTarget n =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanVariationIterate
        H beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioRemoteAggregateVariation
          H beta source distinguishedTarget)
        n (Sum.inr source) := by
  rfl

end

end MathlibAnalytic
end MGAP4D
