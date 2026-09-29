import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourceFixedOrderedLossContraction

open MGAP4D.MathlibAnalytic
open MGAP4D.MathlibAnalytic.GroundStateSourceFixedPairEnergy

#check realHilbertProjectionSweep_displacement_le_length_mul_sqrt_pathLoss
#check realHilbertProjectionSweep_tendsto_block_of_geometric_pathLoss
#check fixedColor_iterates_tendsto_colorProjection
#check fixedColor_defect_iterates_tendsto_zero
#check fixedColor_nextDefect_le_lossRatio_mul
#check sixSpatial_nextDefectMean_le_lossRatio_mul

-- The physical theorem must have no externally supplied zero-tail hypothesis.
example (H N : ℕ) (hN : 0 < N) (s : ℝ) (hs : 8 < s)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hcut : beta ≤ jointLeakageLossContractionCutoff s hs)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor)
    (f : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2 H N hN beta hbeta)
    (hf : f ∈ periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore H N hN beta hbeta) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepBlockDefectVector
      H N hN beta hbeta color
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkFullSweepVector H N hN beta hbeta color f)‖ ^ 2 ≤
      jointLeakageLossRatio s beta *
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepBlockDefectVector H N hN beta hbeta color f‖ ^ 2 := by
  exact fixedColor_nextDefect_le_lossRatio_mul H N hN beta hbeta s hs hcut color f hf

#print axioms realHilbertProjectionSweep_tendsto_block_of_geometric_pathLoss
#print axioms fixedColor_iterates_tendsto_colorProjection
#print axioms fixedColor_defect_iterates_tendsto_zero
#print axioms fixedColor_nextDefect_le_lossRatio_mul
#print axioms sixSpatial_nextDefectMean_le_lossRatio_mul
