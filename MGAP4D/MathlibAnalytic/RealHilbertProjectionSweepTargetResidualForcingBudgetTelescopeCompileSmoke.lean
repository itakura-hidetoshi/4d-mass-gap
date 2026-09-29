import MGAP4D.MathlibAnalytic.RealHilbertProjectionSweepTargetResidualForcingBudgetTelescope

namespace MGAP4D.MathlibAnalytic

#check realHilbertProjectionSweepTargetResidualForcingBudget
#check realHilbertProjectionSweep_targetResidual_norm_le_forcingBudget_add_initial
#check realHilbertProjectionSweep_targetResidual_norm_le_forcingBudget_of_fixed
#check realHilbertProjectionSweepTargetResidualCommutatorForcingBudget
#check realHilbertProjectionSweep_targetResidual_norm_le_commutatorForcingBudget_add_initial
#check realHilbertProjectionSweep_targetResidual_norm_le_commutatorForcingBudget_of_fixed

-- Check both additive positions in the full imported namespace.
example (a b c : ℝ) (h : a ≤ b) : a + c ≤ b + c :=
  _root_.add_le_add h le_rfl

example (a b c : ℝ) (h : a ≤ b) : c + a ≤ c + b :=
  _root_.add_le_add le_rfl h

-- Check the explicit recursor against the intended trajectory equations.
example {E C : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : C → E →L[ℝ] E) (forcing : C → E → ℝ) (x : E) :
    realHilbertProjectionSweepTargetResidualForcingBudget P forcing [] x = 0 := rfl

example {E C : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : C → E →L[ℝ] E) (forcing : C → E → ℝ)
    (source : C) (sources : List C) (x : E) :
    realHilbertProjectionSweepTargetResidualForcingBudget P forcing (source :: sources) x =
      forcing source x +
        realHilbertProjectionSweepTargetResidualForcingBudget P forcing sources (P source x) := rfl

end MGAP4D.MathlibAnalytic
