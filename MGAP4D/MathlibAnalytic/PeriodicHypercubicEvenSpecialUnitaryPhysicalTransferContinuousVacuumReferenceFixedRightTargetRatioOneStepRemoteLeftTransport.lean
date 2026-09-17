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
  classical
  rw [show (1 : ℕ) = 0 + 1 by norm_num]
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanVariationIterate_succ,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanVariationIterate_zero]
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanUpdatedVariation
  unfold finiteInfluenceKernelRestrictedTargetRandomScanUpdatedVariation
  congr 1
  rw [Finset.sum_eq_single target]
  · unfold finiteInfluenceKernelUpdatedVariation
    simp only [Sum.inl.injEq, Ne.symm hne, if_false]
    rw [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedKernel_left_left_of_ne
        H beta hbeta target source hne]
    simp [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTaggedLeftVariation,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation,
      Ne.symm hne]
  · intro fiber _hmem hFiber
    by_cases hFiberSource : fiber = source
    · subst fiber
      simp [finiteInfluenceKernelUpdatedVariation]
    · unfold finiteInfluenceKernelUpdatedVariation
      simp [
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTaggedLeftVariation,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation,
        Ne.symm hne, hFiber, hFiberSource]
  · simp

end

end MathlibAnalytic
end MGAP4D
