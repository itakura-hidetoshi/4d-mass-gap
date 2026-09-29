import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourceFixedOrderedDefectSmallness

open MGAP4D.MathlibAnalytic
open MGAP4D.MathlibAnalytic.GroundStateSourceFixedPairEnergy
open scoped BigOperators

#check realHilbertProjectionSweepSourceResidualProfile
#check realHilbertProjectionSweepSourceResidualProfile_sq_sum_eq_pathLoss
#check realHilbertProjectionSweepTargetResidualForcingBudget_eq_weightedSourceProfile
#check sourceUpdate_targetResidual_norm_le_add_sourceResidual_allL2
#check allLinkSweep_targetResidual_le_orderedBudget_add_initial
#check allLinkSweep_orderedBudget_sq_sum_le_schurCoefficient_sq_mul_pathLoss
#check allLinkSweep_terminalResidual_sq_sum_le_schurCoefficient_sq_mul_pathLoss

-- All right links, arbitrary duplicate-free complete order, arbitrary joint L2.
-- No bounded-core, same-color, sector, or additional analytic premise.
example (H N : ℕ) (hN : 0 < N) (s : ℝ) (hs : 8 < s)
    (beta : ℝ) (hbeta : 0 ≤ beta) (hcut : beta ≤ jointLeakageSchurCutoff s hs)
    (sources : List (PeriodicHypercubicEvenSpatialSliceLink H))
    (hNodup : sources.Nodup) (hComplete : ∀ t, t ∈ sources)
    (f : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2 H N hN beta hbeta) :
    let P := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2 H N hN beta hbeta
    (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
      ‖realHilbertProjectionSweep P sources f - P target (realHilbertProjectionSweep P sources f)‖ ^ 2) ≤
      jointLeakageSchurCoefficient s beta ^ 2 * realHilbertProjectionSweepPathLoss P sources f := by
  exact allLinkSweep_terminalResidual_sq_sum_le_schurCoefficient_sq_mul_pathLoss
    H N hN s hs beta hbeta hcut sources hNodup hComplete f
