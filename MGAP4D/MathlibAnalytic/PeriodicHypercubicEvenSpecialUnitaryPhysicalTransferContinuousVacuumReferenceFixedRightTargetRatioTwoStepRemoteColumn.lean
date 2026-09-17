import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceFixedRightTargetRatioTwoStepRemoteTransport
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

local instance fixedRightTargetRatioTwoStepRemoteColumnSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Sum of the exact two-step represented-source transport over every target
other than the distinguished source.  This is deliberately larger than the
later geometric remote set, so any bound proved here is safe for the genuinely
remote column as well. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation_twoStep_remoteRightColumnSum
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (source : PeriodicHypercubicEvenSpatialSliceLink H) : ℝ :=
  ∑ target ∈ (Finset.univ.erase source),
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanVariationIterate
      H beta hbeta
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation
        H beta target)
      2 (Sum.inr source)

/-- The complete non-source two-step represented-right transport column is
bounded independently of the periodic volume.  The two random-scan factors
cancel the possible target count, leaving only the physical diagonal
cross-boundary coefficient times the off-fiber coefficient and the singleton
`exp (16 * beta)` magnitude. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation_twoStep_remoteRightColumnSum_le
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (source : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation_twoStep_remoteRightColumnSum
        H beta hbeta source ≤
      2 * (((Real.exp (8 * beta)) ^ 2 - 1) /
        ((Real.exp (8 * beta)) ^ 2 + 1)) *
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberOffFiberInfluence
          beta * Real.exp (16 * beta)) := by
  rfl

end

end MathlibAnalytic
end MGAP4D
