import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceFixedRightTargetRatioOneStepRemoteLeftTransport
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceTwoStepTerminalExponentialShellCertificate
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Spatial-flatness certificate for the first coarse restricted random-scan
propagation of a singleton fixed-right target-ratio variation.

The certificate deliberately quantifies over all off-target sources and says
that the one-step propagated value is independent of the source coordinate.
It records an obstruction of the current coarse distinct-fiber carrier only;
it is not a statement about the exact physical covariance. -/
def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariationOneStepOffTargetSpatialFlat
    (H : Nat)
    (beta : Real)
    (hbeta : 0 <= beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) : Prop :=
  forall source₁ source₂ : PeriodicHypercubicEvenSpatialSliceLink H,
    source₁ ≠ target ->
    source₂ ≠ target ->
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanVariationIterate
        H beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation
          H beta target)
        1 (Sum.inl source₁) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanVariationIterate
        H beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation
          H beta target)
        1 (Sum.inl source₂)

/-- The current coarse distinct-fiber restricted-scan carrier is spatially flat
off the target after one step.  This follows from the already-canonical exact
one-step formula, whose off-fiber coefficient is independent of base-L1
distance. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation_oneStep_offTarget_spatialFlat
    (H : Nat)
    (beta : Real)
    (hbeta : 0 <= beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariationOneStepOffTargetSpatialFlat
      H beta hbeta target := by
  intro source₁ source₂ hne₁ hne₂
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation_oneStep_remoteLeft_eq
      H beta hbeta hne₁,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation_oneStep_remoteLeft_eq
      H beta hbeta hne₂]

/-- Even when two off-target sources have different terminal base-L1 radii,
the current coarse one-step restricted-scan profile assigns them the same
value.  The distance hypotheses are retained explicitly to mark the lost
spatial information; no claim is made that such pairs exist in every volume. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation_oneStep_eq_of_distinct_baseL1Distances
    (H : Nat)
    (beta : Real)
    (hbeta : 0 <= beta)
    (target source₁ source₂ : PeriodicHypercubicEvenSpatialSliceLink H)
    (hne₁ : source₁ ≠ target)
    (hne₂ : source₂ ≠ target)
    (_hDistance :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalSpatialBaseL1Distance
          H target source₁ ≠
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalSpatialBaseL1Distance
          H target source₂) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanVariationIterate
        H beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation
          H beta target)
        1 (Sum.inl source₁) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanVariationIterate
        H beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation
          H beta target)
        1 (Sum.inl source₂) :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation_oneStep_offTarget_spatialFlat
    H beta hbeta target source₁ source₂ hne₁ hne₂

end

end MathlibAnalytic
end MGAP4D
