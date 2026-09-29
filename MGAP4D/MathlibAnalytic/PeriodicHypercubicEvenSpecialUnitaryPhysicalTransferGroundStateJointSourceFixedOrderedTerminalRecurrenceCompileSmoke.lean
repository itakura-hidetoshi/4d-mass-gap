import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourceFixedOrderedTerminalRecurrence

open MGAP4D.MathlibAnalytic
open MGAP4D.MathlibAnalytic.GroundStateSourceFixedPairEnergy

#check realHilbertProjectionSweepTargetResidualForcingBudget_append
#check realHilbertProjectionSweepTargetResidualForcingBudget_eq_sum_of_trajectory
#check fixedColor_orderedBudget_eq_split_profiles
#check fixedColor_terminalProfile_le_ordered_forcing_feedback
#check sixSpatial_terminalProfile_le_ordered_forcing_feedback
#check sixSpatial_terminalPathLoss_le_ordered_schur_feedback

-- Repeated sources must remain repeated in the original budget.
example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : Unit → E →L[ℝ] E) (x : E) :
    realHilbertProjectionSweepTargetResidualForcingBudget P (fun _ _ => 1) [(), ()] x = 2 := by
  norm_num [realHilbertProjectionSweepTargetResidualForcingBudget]

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

example (H N : ℕ) (hN : 0 < N) (s : ℝ) (hs : 8 < s)
    (f : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2 H N hN 0 (by norm_num))
    (hf : f ∈ periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore
      H N hN 0 (by norm_num)) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkTerminalSweepPathLoss
      H N hN 0 (by norm_num) f ≤ 0 := by
  have h := sixSpatial_terminalPathLoss_le_ordered_schur_feedback
    H N hN s hs 0 (by norm_num) (jointLeakageSchurCutoff_pos s hs).le f hf
  simpa using h

#print axioms realHilbertProjectionSweepTargetResidualForcingBudget_eq_sum_of_trajectory
#print axioms fixedColor_orderedBudget_eq_split_profiles
#print axioms fixedColor_terminalProfile_le_ordered_forcing_feedback
#print axioms sixSpatial_terminalProfile_le_ordered_forcing_feedback
#print axioms sixSpatial_terminalPathLoss_le_ordered_schur_feedback
