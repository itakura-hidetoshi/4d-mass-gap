import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferBetaZeroGroundStateSixSpatialProductHaarRangeInvariant
import MGAP4D.MathlibAnalytic.RealHilbertRangeInvariantProjectionCommute
import Mathlib.Tactic

/-!
# Beta-zero six-spatial pair-Haar projection commutation

The preceding Wilson-specific unit proves pairwise range invariance for the
actual six beta-zero pair-Haar spatial-color projections.  This file feeds
that exact invariant-range statement into the generic real-Hilbert receiver
and closes pairwise commutation on the literal pair-Haar L2 carrier.
-/

namespace MGAP4D.MathlibAnalytic

open scoped InnerProductSpace InnerProduct

noncomputable section

/-- The actual beta-zero six-spatial pair-Haar projections commute pairwise
pointwise on the literal pair-Haar L2 carrier. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarProjection_commute
    (H N : ℕ)
    (c d : Fin 6)
    (x :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStatePairHaarL2 H N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarProjection
        H N c
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarProjection
          H N d x) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarProjection
        H N d
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarProjection
          H N c x) := by
  exact
    realHilbertProjectionFamily_commute_of_range_invariant
      (fun e =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarProjection
          H N e)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarProjection_idempotent
        H N)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarProjection_symmetric
        H N)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarProjection_range_invariant
        H N)
      c d x

/-- Operator form of pairwise commutation for the actual beta-zero six-spatial
pair-Haar family. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarProjection_comp_commute
    (H N : ℕ)
    (c d : Fin 6) :
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarProjection
      H N c).comp
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarProjection
        H N d) =
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarProjection
      H N d).comp
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarProjection
        H N c) := by
  apply ContinuousLinearMap.ext
  intro x
  simpa only [ContinuousLinearMap.comp_apply] using
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialPairHaarProjection_commute
      H N c d x

end

end MGAP4D.MathlibAnalytic
