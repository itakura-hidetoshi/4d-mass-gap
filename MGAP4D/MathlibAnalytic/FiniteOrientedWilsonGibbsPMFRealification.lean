import MGAP4D.MathlibAnalytic.FiniteOrientedWilsonPartitionFunctionRealification
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

noncomputable local instance finiteOrientedConfigurationFintypeForPMF
    (L : FiniteOrientedLatticeWilsonSystem) : Fintype L.Configuration :=
  Fintype.ofFinite L.Configuration

/-- The real mass of the finite oriented Wilson Gibbs PMF is the ordinary
Boltzmann weight divided by the real finite partition function. -/
theorem finite_oriented_gibbsPMF_toReal_eq_finiteGibbs
    (L : FiniteOrientedLatticeWilsonSystem)
    (A : L.Configuration) :
    (L.gibbsPMF A).toReal =
      FiniteGibbsExpectationBetaDerivative.boltzmannWeight
        L.wilsonAction L.beta A /
      FiniteGibbsExpectationBetaDerivative.partitionFunction
        L.wilsonAction L.beta := by
  rw [finite_oriented_gibbsPMF_apply]
  simp [FiniteOrientedLatticeWilsonSystem.boltzmannWeight,
    FiniteGibbsExpectationBetaDerivative.boltzmannWeight,
    finite_oriented_partitionFunction_toReal_eq_finiteGibbs,
    div_eq_mul_inv, Real.exp_nonneg]

end

end MathlibAnalytic
end MGAP4D
