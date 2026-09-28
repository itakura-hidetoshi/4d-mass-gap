import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferBetaZeroGroundStateOneLinkPairHaarTransport
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSixSpatialOneLinkSweepContractionReceiver
import Mathlib.Tactic

/-!
# Beta-zero same-color one-link sweep transport to pair Haar

PR #4883 transports one genuine beta-zero one-link conditional expectation
exactly to the corresponding literal pair-Haar projection.

This file lifts that intertwining through an arbitrary finite ordered sweep and
then specializes it to the canonical complete same-color sweep.

No commutativity is needed for this transport step.  The list order is
preserved literally.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace InnerProduct

noncomputable section

local instance betaZeroSameColorSweepPairHaarTransportSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Literal pair-Haar one-link projection family for a fixed six-spatial
color. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkPairHaarProjection
    (H N : ℕ)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor) :
    PeriodicHypercubicEvenFixedSpatialColorLink H color →
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStatePairHaarL2 H N →L[ℝ]
        PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStatePairHaarL2 H N :=
  fun e =>
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkPairHaarProjection
      H N e.1

/-- Exact transport of an arbitrary ordered same-color one-link projection
sweep from the genuine beta-zero ground-state carrier to literal pair Haar. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroJointToPairHaarL2_fixedSpatialColor_projectionSweep
    (H N : ℕ)
    (hN : 0 < N)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor)
    (cs : List (PeriodicHypercubicEvenFixedSpatialColorLink H color))
    (z :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN 0 (by norm_num)) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroJointToPairHaarL2
        H N hN
        (realHilbertProjectionSweep
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
            H N hN 0 (by norm_num) color)
          cs z) =
      realHilbertProjectionSweep
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkPairHaarProjection
          H N color)
        cs
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroJointToPairHaarL2
          H N hN z) := by
  let P :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
      H N hN 0 (by norm_num) color
  let Q :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkPairHaarProjection
      H N color
  change
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroJointToPairHaarL2
        H N hN (realHilbertProjectionSweep P cs z) =
      realHilbertProjectionSweep Q cs
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroJointToPairHaarL2
          H N hN z)
  induction cs generalizing z with
  | nil =>
      rfl
  | cons e es ih =>
      have hstep :
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroJointToPairHaarL2
              H N hN (P e z) =
            Q e
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroJointToPairHaarL2
                H N hN z) := by
        simpa [
          P, Q,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkPairHaarProjection] using
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroJointToPairHaarL2_spatialLinkCondExp
            H N hN e.1 z)
      calc
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroJointToPairHaarL2
            H N hN (realHilbertProjectionSweep P (e :: es) z) =
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroJointToPairHaarL2
            H N hN (realHilbertProjectionSweep P es (P e z)) := by
              rfl
        _ = realHilbertProjectionSweep Q es
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroJointToPairHaarL2
              H N hN (P e z)) :=
          ih (P e z)
        _ = realHilbertProjectionSweep Q es
            (Q e
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroJointToPairHaarL2
                H N hN z)) := by
          rw [hstep]
        _ = realHilbertProjectionSweep Q (e :: es)
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroJointToPairHaarL2
              H N hN z) := by
          rfl

/-- Exact transport of the complete canonical same-color one-link sweep.
The canonical list and its order are unchanged. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroJointToPairHaarL2_fixedSpatialColor_fullOneLinkSweep
    (H N : ℕ)
    (hN : 0 < N)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor)
    (z :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN 0 (by norm_num)) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroJointToPairHaarL2
        H N hN
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkFullSweepVector
          H N hN 0 (by norm_num) color z) =
      realHilbertProjectionSweep
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkPairHaarProjection
          H N color)
        ((Finset.univ :
          Finset (PeriodicHypercubicEvenFixedSpatialColorLink H color)).toList)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroJointToPairHaarL2
          H N hN z) := by
  simpa [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkFullSweepVector] using
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroJointToPairHaarL2_fixedSpatialColor_projectionSweep
      H N hN color
      ((Finset.univ :
        Finset (PeriodicHypercubicEvenFixedSpatialColorLink H color)).toList)
      z

end

end MGAP4D.MathlibAnalytic
