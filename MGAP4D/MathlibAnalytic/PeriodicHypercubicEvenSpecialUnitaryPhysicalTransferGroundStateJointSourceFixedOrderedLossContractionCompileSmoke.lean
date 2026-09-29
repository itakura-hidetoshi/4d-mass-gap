import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourceFixedOrderedLossContraction

open MGAP4D.MathlibAnalytic
open MGAP4D.MathlibAnalytic.GroundStateSourceFixedPairEnergy
open Filter
open scoped Topology

#check RenewalTail.defect_sub_tail_le_mul
#check RenewalTail.defect_succ_sub_limit_le_mul
#check RenewalTail.defect_succ_le_mul_of_tendsto_zero
#check exists_jointLeakageLossContractionCutoff
#check jointLeakageLossContractionCutoff_pos
#check jointLeakageLossRatio_nonneg_lt_one
#check fixedColor_terminalPathLoss_le_ordered_schur_feedback
#check fixedColor_terminalPathLoss_le_lossRatio_mul
#check fixedColor_iteratedPathLoss_le_geometric

-- A nonzero renewal tail cannot be silently erased.
example : (∀ _n : ℕ, (1 : ℝ) = 0 + 1) ∧
    (∀ _n : ℕ, (0 : ℝ) ≤ (1 / 2) * 0) ∧ ¬((1 : ℝ) ≤ (1 / 2) * 1) := by
  norm_num

-- The additional input is visible in the usable zero-tail receiver.
example (D L : ℕ → ℝ) (eta : ℝ)
    (hRenew : ∀ n, D n = L (n + 1) + D (n + 1))
    (hLoss : ∀ n, L (n + 2) ≤ eta * L (n + 1))
    (hTail : Tendsto D atTop (𝓝 0)) : D 1 ≤ eta * D 0 := by
  exact RenewalTail.defect_succ_le_mul_of_tendsto_zero D L eta hRenew hLoss hTail

example (s : ℝ) : jointLeakageLossRatio s 0 = 0 := by simp

example (H N : ℕ) (hN : 0 < N) (s : ℝ) (hs : 8 < s)
    (beta : ℝ) (hbeta : 0 ≤ beta) (hcut : beta ≤ jointLeakageLossContractionCutoff s hs)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor)
    (f : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2 H N hN beta hbeta)
    (hf : f ∈ periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore
      H N hN beta hbeta) (n : ℕ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepPathLoss
      H N hN beta hbeta color
      ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkFullSweepVector
        H N hN beta hbeta color)^[n] f) ≤
    jointLeakageLossRatio s beta ^ n *
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepPathLoss
        H N hN beta hbeta color f := by
  exact fixedColor_iteratedPathLoss_le_geometric H N hN beta hbeta s hs hcut color f hf n

example (H N : ℕ) (hN : 0 < N) (s : ℝ) (hs : 8 < s)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor)
    (f : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2 H N hN 0 le_rfl)
    (hf : f ∈ periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore
      H N hN 0 le_rfl) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepPathLoss
      H N hN 0 le_rfl color
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkFullSweepVector
        H N hN 0 le_rfl color f) ≤ 0 := by
  have h := fixedColor_terminalPathLoss_le_lossRatio_mul H N hN 0 le_rfl s hs
    (jointLeakageLossContractionCutoff_pos s hs).le color f hf
  simpa only [jointLeakageLossRatio_zero, zero_mul] using h

#print axioms RenewalTail.defect_sub_tail_le_mul
#print axioms RenewalTail.defect_succ_le_mul_of_tendsto_zero
#print axioms jointLeakageLossRatio_nonneg_lt_one
#print axioms fixedColor_terminalPathLoss_le_lossRatio_mul
#print axioms fixedColor_iteratedPathLoss_le_geometric
