import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointTwoBoundaryOrderedSchur

open MGAP4D.MathlibAnalytic
open MGAP4D.MathlibAnalytic.GroundStateSourceFixedPairEnergy
open scoped BigOperators

noncomputable section

#check twoBoundaryOrderedKernel
#check twoBoundaryOrderedSchurCoefficient
#check twoBoundaryOrderedKernel_nonneg
#check twoBoundaryOrderedKernel_rowSum_le
#check twoBoundaryOrderedKernel_columnSum_le
#check twoBoundaryOrderedKernel_action_sq_sum_le
#check twoBoundaryOrderedSchurCutoff
#check twoBoundaryOrderedSchurCutoff_pos
#check twoBoundaryOrderedSchurCoefficient_nonneg_lt_one

example (s beta : ℝ) :
    twoBoundaryOrderedSchurCoefficient s beta =
      jointLeakageSchurCoefficient s beta +
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryContractionCoefficient beta := rfl

example (s : ℝ) : twoBoundaryOrderedSchurCoefficient s 0 = 0 := by
  simp [twoBoundaryOrderedSchurCoefficient,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryContractionCoefficient]

example (s : ℝ) (hs : 8 < s) :
    0 < twoBoundaryOrderedSchurCutoff s hs :=
  twoBoundaryOrderedSchurCutoff_pos s hs

#print axioms twoBoundaryOrderedKernel_action_sq_sum_le
#print axioms twoBoundaryOrderedSchurCoefficient_nonneg_lt_one

end
