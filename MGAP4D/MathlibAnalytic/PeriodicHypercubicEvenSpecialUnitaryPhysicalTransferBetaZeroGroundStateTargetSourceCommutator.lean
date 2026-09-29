import MGAP4D.MathlibAnalytic.RealHilbertProjectionSweepTargetSourceCommutatorForcing
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferBetaZeroGroundStateOneLinkPairHaarCommutation
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferBetaZeroGroundStateSweepBlockDefectZero
import Mathlib.Tactic

/-!
# Beta-zero vanishing of the genuine target/source commutator

At beta zero the genuine ground-state joint measure is exactly pair Haar.
The existing exact measure cast intertwines every genuine one-link conditional
expectation with the corresponding literal pair-Haar projection, and the
pair-Haar projections commute pairwise.

This file transports that commutation back to the genuine beta-zero
ground-state L2 carrier.  Consequently the target/source commutator forcing
from the preceding theorem unit vanishes exactly on the physical carrier.

No perturbative estimate is used here.  This is the exact endpoint anchor
against which the positive-beta commutator coefficient will be measured.
-/

namespace MGAP4D.MathlibAnalytic

noncomputable section

/-- Genuine beta-zero one-link conditional expectations commute pairwise on
the ground-state joint L2 carrier. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2_zero_commute
    (H N : ℕ)
    (hN : 0 < N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (x :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN 0 (by norm_num)) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
        H N hN 0 (by norm_num) target
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
          H N hN 0 (by norm_num) source x) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
        H N hN 0 (by norm_num) source
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
          H N hN 0 (by norm_num) target x) := by
  apply
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroJointToPairHaarL2_injective
      H N hN
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroJointToPairHaarL2_spatialLinkCondExp
      H N hN target,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroJointToPairHaarL2_spatialLinkCondExp
      H N hN source,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroJointToPairHaarL2_spatialLinkCondExp
      H N hN source,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroJointToPairHaarL2_spatialLinkCondExp
      H N hN target]
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkPairHaarProjection_commute
      H N target source
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroJointToPairHaarL2
        H N hN x)

/-- The physical fixed-color target/source commutator operator is exactly zero
at beta zero. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkTargetSourceCommutator_zero
    (H N : ℕ)
    (hN : 0 < N)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor)
    (target source :
      PeriodicHypercubicEvenFixedSpatialColorLink H color) :
    realHilbertProjectionSweepTargetSourceCommutatorLinearMap
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
          H N hN 0 (by norm_num) color)
        target source = 0 := by
  apply ContinuousLinearMap.ext
  intro x
  rw [realHilbertProjectionSweepTargetSourceCommutatorLinearMap_apply]
  change
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
          H N hN 0 (by norm_num) target.1
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
            H N hN 0 (by norm_num) source.1 x) -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
          H N hN 0 (by norm_num) source.1
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
            H N hN 0 (by norm_num) target.1 x) =
      0
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2_zero_commute
      H N hN target.1 source.1 x,
    sub_self]

/-- Hence the projected forcing term itself vanishes exactly at beta zero. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkTargetCrossResidual_projected_zero
    (H N : ℕ)
    (hN : 0 < N)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor)
    (target source :
      PeriodicHypercubicEvenFixedSpatialColorLink H color)
    (x :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN 0 (by norm_num)) :
    realHilbertProjectionSweepTargetCrossResidual
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
          H N hN 0 (by norm_num) color)
        target source
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
          H N hN 0 (by norm_num) color target x) = 0 := by
  let P :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
      H N hN 0 (by norm_num) color
  have hIdem : (P target).comp (P target) = P target := by
    simpa [
      P,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2_idempotent
        H N hN 0 (by norm_num) target.1
  calc
    realHilbertProjectionSweepTargetCrossResidual
        P target source (P target x) =
      realHilbertProjectionSweepTargetSourceCommutatorLinearMap
        P target source (P target x) :=
          realHilbertProjectionSweepTargetCrossResidual_projected_eq_commutator_of_idempotent
            P target source hIdem x
    _ = 0 := by
      rw [
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkTargetSourceCommutator_zero
          H N hN color target source]
      rfl

end

end MGAP4D.MathlibAnalytic
