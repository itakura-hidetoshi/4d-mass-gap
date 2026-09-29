import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourceFixedOrderedSchurEnvelope

open MGAP4D.MathlibAnalytic
open MGAP4D.MathlibAnalytic.GroundStateSourceFixedPairEnergy

#check jointLeakageNormCoefficient_eq_rmsMultiplier_mul_pinFree
#check jointLeakageNormCoefficient_rowSum_le_schurCoefficient
#check jointLeakageNormCoefficient_columnSum_le_schurCoefficient
#check jointLeakageNormCoefficient_transpose_action_sq_sum_le
#check jointLeakageRMSMultiplier_eq_realFormula
#check continuousAt_jointLeakageRMSMultiplierRealFormula
#check jointLeakageSchurCutoff_pos
#check jointLeakageSchurCutoff_le_shellCutoff
#check jointLeakageSchurCutoff_le_strictPhysicalSweepCutoff
#check jointLeakageSchurCoefficient_nonneg_lt_one

-- The RMS multiplier cannot be erased even at zero coupling.
example (s : ℝ) : jointLeakageRMSMultiplier s 0 ^ 2 = 4 / 3 :=
  jointLeakageRMSMultiplier_zero_sq s

example (s : ℝ) : jointLeakageRMSMultiplier s 0 ≠ 1 := by
  intro h
  have hsq := jointLeakageRMSMultiplier_zero_sq s
  rw [h] at hsq
  norm_num at hsq

-- The full influence coefficient nevertheless vanishes at zero.
example (s : ℝ) : jointLeakageSchurCoefficient s 0 = 0 :=
  jointLeakageSchurCoefficient_zero s

-- A genuinely positive, volume/rank-independent admissible interval.
example (s : ℝ) (hs : 8 < s) :
    0 < jointLeakageSchurCutoff s hs ∧
      ∀ beta : ℝ, 0 ≤ beta → beta ≤ jointLeakageSchurCutoff s hs →
        0 ≤ jointLeakageSchurCoefficient s beta ∧ jointLeakageSchurCoefficient s beta < 1 :=
  ⟨jointLeakageSchurCutoff_pos s hs,
    fun beta hbeta hcut => jointLeakageSchurCoefficient_nonneg_lt_one s hs beta hbeta hcut⟩

#print axioms jointLeakageNormCoefficient_eq_rmsMultiplier_mul_pinFree
#print axioms jointLeakageRMSMultiplier_eq_realFormula
#print axioms jointLeakageNormCoefficient_transpose_action_sq_sum_le
#print axioms jointLeakageSchurCoefficient_nonneg_lt_one
