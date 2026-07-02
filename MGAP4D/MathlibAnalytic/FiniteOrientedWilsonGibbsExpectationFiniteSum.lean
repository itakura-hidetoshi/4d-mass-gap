import MGAP4D.MathlibAnalytic.FiniteOrientedWilsonGibbsPMFRealification
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped BigOperators

noncomputable section

noncomputable local instance finiteOrientedConfigurationFintypeForExpectation
    (L : FiniteOrientedLatticeWilsonSystem) : Fintype L.Configuration :=
  Fintype.ofFinite L.Configuration

/-- Integration against the finite oriented Wilson Gibbs measure agrees with
the normalized finite-sum Gibbs expectation. -/
theorem finite_oriented_gibbsIntegral_eq_finiteGibbsExpectation
    (L : FiniteOrientedLatticeWilsonSystem)
    (F : L.Configuration -> Real) :
    (integral F L.gibbsMeasure) =
      FiniteGibbsExpectationBetaDerivative.expectation
        F L.wilsonAction L.beta := by
  rw [FiniteOrientedLatticeWilsonSystem.gibbsMeasure, PMF.integral_eq_sum]
  simp_rw [finite_oriented_gibbsPMF_toReal_eq_finiteGibbs]
  unfold FiniteGibbsExpectationBetaDerivative.expectation
  unfold FiniteGibbsExpectationBetaDerivative.weightedSum
  calc
    (Finset.univ.sum fun A : L.Configuration =>
        (FiniteGibbsExpectationBetaDerivative.boltzmannWeight
          L.wilsonAction L.beta A /
          FiniteGibbsExpectationBetaDerivative.partitionFunction
            L.wilsonAction L.beta) • F A) =
      Finset.univ.sum (fun A : L.Configuration =>
        (F A * FiniteGibbsExpectationBetaDerivative.boltzmannWeight
          L.wilsonAction L.beta A) /
          FiniteGibbsExpectationBetaDerivative.partitionFunction
            L.wilsonAction L.beta) := by
        apply Finset.sum_congr rfl
        intro A _hA
        simp [smul_eq_mul]
        ring
    _ = (Finset.univ.sum fun A : L.Configuration =>
        F A * FiniteGibbsExpectationBetaDerivative.boltzmannWeight
          L.wilsonAction L.beta A) /
          FiniteGibbsExpectationBetaDerivative.partitionFunction
            L.wilsonAction L.beta := by
        rw [Finset.sum_div]

end

end MathlibAnalytic
end MGAP4D
