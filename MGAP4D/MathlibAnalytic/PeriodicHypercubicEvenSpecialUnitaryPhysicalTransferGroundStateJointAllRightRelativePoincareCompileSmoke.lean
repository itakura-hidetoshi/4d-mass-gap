import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointOrderedAllLinkSweepResidual
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourceFixedOrderedLossContraction
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateSixRetainedBoundaryEquality

open MGAP4D.MathlibAnalytic
open MGAP4D.MathlibAnalytic.GroundStateSourceFixedPairEnergy

#check realHilbertProjectionSweepSourceResidualProfile_le_budget_add_initial
#check allLinkSweep_pathLoss_controlled_by_initialResidual
#check allLinkSweep_pathLoss_le_lossRatio_mul
#check allLinkSweep_iteratedPathLoss_le_geometric
#check allRightLink_fixed_iff_leftRetained
#check allLinkSweep_iterates_tendsto_leftRetained
#check allLink_relativePoincare

-- The coefficient must not contain the length of the link list or a core premise.
example (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (s : ℝ) (hs : 8 < s) (hcut : beta ≤ jointLeakageLossContractionCutoff s hs)
    (f : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2 H N hN beta hbeta) :
    letI : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) := Fintype.ofFinite _
    (1 - 2 * jointLeakageSchurCoefficient s beta) *
      ‖f - allRightLeftRetainedCondExpL2 H N hN beta hbeta f‖ ^ 2 ≤
        ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
          ‖f - periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
            H N hN beta hbeta e f‖ ^ 2 := by
  exact allLink_relativePoincare H N hN beta hbeta s hs hcut f
