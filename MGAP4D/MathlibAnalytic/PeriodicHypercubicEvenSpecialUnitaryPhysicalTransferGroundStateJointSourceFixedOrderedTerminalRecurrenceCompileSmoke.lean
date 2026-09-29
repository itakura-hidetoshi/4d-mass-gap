import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourceFixedOrderedSchurEnvelope

open MGAP4D.MathlibAnalytic
open MGAP4D.MathlibAnalytic.GroundStateSourceFixedPairEnergy

#check realHilbertProjectionSweepTargetResidualForcingBudget_append
#check realHilbertProjectionSweepTargetResidualForcingBudget_eq_sum_of_trajectory
#check fixedColor_terminalProfile_le_ordered_forcing_feedback
#check sixSpatial_terminalProfile_le_ordered_forcing_feedback
#check sixSpatial_terminalPathLoss_le_ordered_schur_feedback

example (H N : ℕ) (hN : 0 < N) (s : ℝ) (hs : 8 < s)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hcut : beta ≤ jointLeakageSchurCutoff s hs)
    (f : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2 H N hN beta hbeta)
    (hf : f ∈ periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore
      H N hN beta hbeta) :
    (1 - jointLeakageSchurCoefficient s beta) ^ 2 *
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkTerminalSweepPathLoss
        H N hN beta hbeta f ≤
    jointLeakageSchurCoefficient s beta ^ 2 *
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepPathLoss
        H N hN beta hbeta f := by
  exact sixSpatial_terminalPathLoss_le_ordered_schur_feedback
    H N hN s hs beta hbeta hcut f hf

#print axioms realHilbertProjectionSweepTargetResidualForcingBudget_eq_sum_of_trajectory
#print axioms fixedColor_terminalProfile_le_ordered_forcing_feedback
#print axioms sixSpatial_terminalProfile_le_ordered_forcing_feedback
#print axioms sixSpatial_terminalPathLoss_le_ordered_schur_feedback
