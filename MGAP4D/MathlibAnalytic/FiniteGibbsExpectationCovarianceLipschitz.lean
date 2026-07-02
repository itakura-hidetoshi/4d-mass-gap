import MGAP4D.MathlibAnalytic.FiniteGibbsExpectationBetaDerivative
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace FiniteGibbsExpectationBetaDerivative

variable {Omega : Type*} [Fintype Omega] [Nonempty Omega]

structure UniformCovarianceBound (F S : Omega -> Real) where
  factor : Real
  factor_nonneg : 0 <= factor
  abs_covariance_le : forall beta : Real, abs (covariance F S beta) <= factor

namespace UniformCovarianceBound

variable {F S : Omega -> Real}

theorem abs_expectation_sub_le
    (C : UniformCovarianceBound F S) (beta0 beta1 : Real) :
    abs (expectation F S beta1 - expectation F S beta0) <=
      C.factor * abs (beta1 - beta0) := by
  have h := convex_univ.norm_image_sub_le_of_norm_deriv_le
    (fun beta _ =>
      (hasDerivAt_expectation_eq_neg_covariance F S beta).differentiableAt)
    (fun beta _ => by
      rw [deriv_expectation_eq_neg_covariance]
      simpa [Real.norm_eq_abs] using C.abs_covariance_le beta)
    (Set.mem_univ beta0) (Set.mem_univ beta1)
  simpa [Real.norm_eq_abs] using h

end UniformCovarianceBound

end FiniteGibbsExpectationBetaDerivative

end

end MathlibAnalytic
end MGAP4D
