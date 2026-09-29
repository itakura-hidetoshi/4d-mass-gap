import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourceFixedRealNormLeakage

open MGAP4D.MathlibAnalytic
open MGAP4D.MathlibAnalytic.GroundStateSourceFixedPairEnergy
open scoped ENNReal

#check norm_sq_le_toReal_mul_norm_sq_of_ofReal_norm_sq_le
#check norm_le_sqrt_toReal_mul_norm_of_ofReal_norm_sq_le
#check jointLeakageHalfOrderedCoefficient
#check jointLeakageHalfOrderedCoefficient_ne_top
#check jointLeakageNormCoefficient
#check jointLeakageNormCoefficient_nonneg
#check jointLeakageNormCoefficient_sq
#check sourceUpdate_jointLeakage_norm_le_orderedNormCoefficient
#check jointLeakage_norm_le_orderedNormCoefficient_of_sourceFixed
#check sourceUpdate_targetResidual_norm_le_add_sourceResidual
#check periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkTerminalSweepStageLocalProfile_le_cyclicOrderedNormSourceResidualBudget

-- Zero target residual requires neither cancellation nor strict positivity.
example {E : Type*} [NormedAddCommGroup E]
    (A : ℝ≥0∞) (hA : A ≠ ⊤) (u : E)
    (h : ENNReal.ofReal (‖u‖ ^ 2) ≤ A * ENNReal.ofReal (‖(0 : E)‖ ^ 2)) :
    u = 0 := by
  have hNorm := norm_le_sqrt_toReal_mul_norm_of_ofReal_norm_sq_le A hA u (0 : E) h
  have hz : ‖u‖ ≤ 0 := by simpa only [norm_zero, mul_zero] using hNorm
  exact norm_eq_zero.mp (le_antisymm hz (norm_nonneg u))

-- Zero coefficient is also included, with an arbitrary residual.
example {E F : Type*} [NormedAddCommGroup E] [SeminormedAddCommGroup F]
    (u : E) (v : F)
    (h : ENNReal.ofReal (‖u‖ ^ 2) ≤ (0 : ℝ≥0∞) * ENNReal.ofReal (‖v‖ ^ 2)) :
    u = 0 := by
  have hNorm := norm_le_sqrt_toReal_mul_norm_of_ofReal_norm_sq_le 0 (by simp) u v h
  have hz : ‖u‖ ≤ 0 := by simpa using hNorm
  exact norm_eq_zero.mp (le_antisymm hz (norm_nonneg u))

-- The iid half-factor stays inside the square root.
example : Real.sqrt (((2 : ℝ≥0∞)⁻¹ * 2).toReal) = 1 := by
  norm_num

#print axioms norm_le_sqrt_toReal_mul_norm_of_ofReal_norm_sq_le
#print axioms sourceUpdate_jointLeakage_norm_le_orderedNormCoefficient
#print axioms jointLeakage_norm_le_orderedNormCoefficient_of_sourceFixed
#print axioms sourceUpdate_targetResidual_norm_le_add_sourceResidual
#print axioms periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkTerminalSweepStageLocalProfile_le_cyclicOrderedNormSourceResidualBudget
