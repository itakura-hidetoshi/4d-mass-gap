import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferBetaZeroGroundStateOneLinkPairHaarTransport
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSixSpatialOneLinkSweepContractionReceiver
import Mathlib.Tactic

/-!
# Beta-zero same-color one-link sweep transport to pair Haar

PR #4883 transports one genuine beta-zero one-link conditional expectation
exactly to the corresponding literal pair-Haar projection.

This file lifts that intertwining through an arbitrary finite ordered sweep and
then specializes it to the canonical complete same-color sweep.

No commutativity is needed for this transport step. The list order is
preserved literally.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace InnerProduct

noncomputable section

set_option maxHeartbeats 2000000

local instance betaZeroSameColorSweepPairHaarTransportSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Intertwining a projection family step by step intertwines its complete
ordered sweep. This is purely functorial and uses no projection algebra. -/
theorem realHilbertProjectionSweep_map_of_intertwine
    {E F C : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (T : E → F)
    (P : C → E →L[ℝ] E)
    (Q : C → F →L[ℝ] F)
    (h : ∀ c x, T (P c x) = Q c (T x))
    (cs : List C) (x : E) :
    T (realHilbertProjectionSweep P cs x) =
      realHilbertProjectionSweep Q cs (T x) := by
  induction cs generalizing x with
  | nil =>
      rfl
  | cons c cs ih =>
      calc
        T (realHilbertProjectionSweep P (c :: cs) x) =
            T (realHilbertProjectionSweep P cs (P c x)) := by
              rfl
        _ = realHilbertProjectionSweep Q cs (T (P c x)) :=
          ih (P c x)
        _ = realHilbertProjectionSweep Q cs (Q c (T x)) := by
          rw [h c x]
        _ = realHilbertProjectionSweep Q (c :: cs) (T x) := by
          rfl

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
  apply realHilbertProjectionSweep_map_of_intertwine
  intro e x
  simpa [
    P, Q,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkPairHaarProjection] using
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabBetaZeroJointToPairHaarL2_spatialLinkCondExp
      H N hN e.1 x)

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
