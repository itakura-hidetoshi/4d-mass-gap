import MGAP4D.MathlibAnalytic.FiniteNonnegativeInfluenceKernelBidirectionalSchurL2

namespace MGAP4D.MathlibAnalytic

noncomputable section

#check FiniteNonnegativeSchur.action_sq_sum_le_row_mul_column
#check finiteInfluenceKernelBidirectionalSchurCoefficient
#check finiteInfluenceKernelBidirectionalSchurCoefficient_nonneg
#check finiteInfluenceKernelRowSum_le_bidirectionalSchurCoefficient
#check finiteInfluenceKernelColumnSum_le_bidirectionalSchurCoefficient
#check finiteInfluenceKernel_action_sq_sum_le_bidirectionalSchurCoefficient_sq
#check finiteInfluenceKernelBidirectionalSchurCoefficient_lt_one_iff
#check finiteInfluenceKernelBidirectional_oneSided_global_energy_coercive

example
    {ι : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Nonempty ι]
    (K : FiniteNonnegativeInfluenceKernelData ι)
    (hRow : finiteInfluenceKernelMaximumRowSum K < 1)
    (hColumn : finiteInfluenceKernelMaximumColumnSum K < 1) :
    finiteInfluenceKernelBidirectionalSchurCoefficient K < 1 := by
  exact
    (finiteInfluenceKernelBidirectionalSchurCoefficient_lt_one_iff K).2
      ⟨hRow, hColumn⟩

end

end MGAP4D.MathlibAnalytic
