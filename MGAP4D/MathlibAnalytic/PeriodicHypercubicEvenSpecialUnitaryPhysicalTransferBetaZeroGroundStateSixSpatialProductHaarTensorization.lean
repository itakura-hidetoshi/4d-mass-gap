import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferBetaZeroGroundStateSixSpatialProductHaarCommutation
import MGAP4D.MathlibAnalytic.RealHilbertCommutingProjectionSweepTensorization
import Mathlib.Tactic

/-!
# Beta-zero six-spatial pair-Haar full-sweep tensorization

The actual six beta-zero pair-Haar spatial-color projections are now
idempotent, symmetric, and pairwise commuting.  This file specializes the
generic finite Hilbert-projection sweep machinery to that Wilson family.

It exposes a named full-sweep operator, proves the full-sweep defect
tensorization inequality, and identifies its fixed vectors with the common
fixed vectors of all six color projections.
-/

namespace MGAP4D.MathlibAnalytic

open scoped BigOperators InnerProductSpace InnerProduct

noncomputable section

/-- The ordered full sweep through all six actual beta-zero pair-Haar spatial
color projections. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarFullSweep
    (H N : ℕ) :
    PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStatePairHaarL2 H N →L[ℝ]
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStatePairHaarL2 H N :=
  realHilbertProjectionSweep
    (fun c =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarProjection
        H N c)
    ((Finset.univ : Finset (Fin 6)).toList)

/-- The actual beta-zero six-spatial full sweep satisfies the finite
commuting-projection tensorization inequality. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarFullSweep_tensorization
    (H N : ℕ)
    (x :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStatePairHaarL2 H N) :
    ‖x -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarFullSweep
          H N x‖ ^ 2 ≤
      ∑ c : Fin 6,
        ‖x -
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarProjection
            H N c x‖ ^ 2 := by
  exact
    realHilbertProjectionFullSweep_tensorization
      (fun c =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarProjection
          H N c)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarProjection_idempotent
        H N)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarProjection_symmetric
        H N)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarProjection_commute
        H N)
      x

/-- A vector is fixed by the actual six-spatial beta-zero full sweep exactly
when every one of the six color projections fixes it. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarFullSweep_eq_self_iff
    (H N : ℕ)
    (x :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStatePairHaarL2 H N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarFullSweep
        H N x = x ↔
      ∀ c : Fin 6,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarProjection
          H N c x = x := by
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarFullSweep,
    realHilbertProjectionSweep_apply_eq_self_iff_forall_mem_fixed
      (fun c =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarProjection
          H N c)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarProjection_idempotent
        H N)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarProjection_symmetric
        H N)]
  simp

end

end MGAP4D.MathlibAnalytic
