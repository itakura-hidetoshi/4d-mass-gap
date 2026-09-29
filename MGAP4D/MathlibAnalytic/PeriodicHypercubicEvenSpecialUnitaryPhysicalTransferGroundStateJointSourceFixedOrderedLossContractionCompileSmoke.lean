import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourceFixedOrderedTerminalRecurrence

open MGAP4D.MathlibAnalytic
open MGAP4D.MathlibAnalytic.GroundStateSourceFixedPairEnergy

#check RenewalTail.defect_sub_tail_le_mul
#check RenewalTail.defect_succ_le_mul_of_tendsto_zero
#check exists_jointLeakageLossContractionCutoff
#check jointLeakageLossContractionCutoff_pos
#check jointLeakageLossRatio_nonneg_lt_one
#check fixedColor_terminalPathLoss_le_ordered_schur_feedback
#check fixedColor_terminalPathLoss_le_lossRatio_mul
#check fixedColor_iteratedPathLoss_le_geometric

-- A nonzero renewal tail cannot be silently erased.
example : (∀ n : ℕ, (1 : ℝ) = 0 + 1) ∧
    (∀ n : ℕ, (0 : ℝ) ≤ (1 / 2) * 0) ∧ ¬((1 : ℝ) ≤ (1 / 2) * 1) := by
  norm_num

#print axioms RenewalTail.defect_succ_le_mul_of_tendsto_zero
#print axioms jointLeakageLossRatio_nonneg_lt_one
#print axioms fixedColor_terminalPathLoss_le_lossRatio_mul
#print axioms fixedColor_iteratedPathLoss_le_geometric
