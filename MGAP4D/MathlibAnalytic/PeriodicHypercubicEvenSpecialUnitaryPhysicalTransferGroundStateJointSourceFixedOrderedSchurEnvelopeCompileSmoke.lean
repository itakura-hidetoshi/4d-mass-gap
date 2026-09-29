import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourceFixedRealNormLeakage

open MGAP4D.MathlibAnalytic
open MGAP4D.MathlibAnalytic.GroundStateSourceFixedPairEnergy

-- These APIs must be provided by the ordered-envelope theorem unit.
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

-- The full influence coefficient nevertheless vanishes at zero.
example (s : ℝ) : jointLeakageSchurCoefficient s 0 = 0 :=
  jointLeakageSchurCoefficient_zero s

#print axioms jointLeakageNormCoefficient_eq_rmsMultiplier_mul_pinFree
#print axioms jointLeakageNormCoefficient_transpose_action_sq_sum_le
#print axioms jointLeakageSchurCoefficient_nonneg_lt_one
