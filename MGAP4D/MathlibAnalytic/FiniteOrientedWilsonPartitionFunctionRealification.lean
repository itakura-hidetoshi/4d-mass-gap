import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonGibbsMeasure
import MGAP4D.MathlibAnalytic.FiniteGibbsExpectationBetaDerivative
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal

noncomputable section

noncomputable local instance finiteOrientedConfigurationFintype
    (L : FiniteOrientedLatticeWilsonSystem) : Fintype L.Configuration :=
  Fintype.ofFinite L.Configuration

/-- The ENNReal partition function used by the finite Wilson PMF has the same
real value as the finite-sum partition function used by Gibbs calculus. -/
theorem finite_oriented_partitionFunction_toReal_eq_finiteGibbs
    (L : FiniteOrientedLatticeWilsonSystem) :
    L.partitionFunction.toReal =
      FiniteGibbsExpectationBetaDerivative.partitionFunction
        L.wilsonAction L.beta := by
  classical
  unfold FiniteOrientedLatticeWilsonSystem.partitionFunction
  rw [tsum_fintype]
  rw [ENNReal.toReal_sum]
  · simp [FiniteOrientedLatticeWilsonSystem.boltzmannWeight,
      FiniteGibbsExpectationBetaDerivative.partitionFunction,
      FiniteGibbsExpectationBetaDerivative.weightedSum,
      FiniteGibbsExpectationBetaDerivative.boltzmannWeight,
      Real.exp_nonneg]
  · intro A _hA
    simp [FiniteOrientedLatticeWilsonSystem.boltzmannWeight]

end

end MathlibAnalytic
end MGAP4D
