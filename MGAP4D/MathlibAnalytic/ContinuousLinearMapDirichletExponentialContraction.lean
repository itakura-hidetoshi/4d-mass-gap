import MGAP4D.MathlibAnalytic.ContinuousLinearMapDirichletDefectOpNorm
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

noncomputable section

namespace MGAP4D
namespace MathlibAnalytic

universe u

/-- The elementary square-root/exponential comparison needed for a direct
Poincare-to-semigroup route:

`sqrt (1 - c) <= exp (-c/2)`.

It follows from Mathlib's global tangent-line inequality
`1 + x <= exp x`; no logarithm or Taylor expansion is used. -/
theorem sqrt_one_sub_le_exp_neg_half (c : ℝ) :
    Real.sqrt (1 - c) ≤ Real.exp (-c / 2) := by
  have hbase : 1 - c ≤ Real.exp (-c) := by
    have h := Real.add_one_le_exp (-c)
    linarith
  calc
    Real.sqrt (1 - c) ≤ Real.sqrt (Real.exp (-c)) :=
      Real.sqrt_le_sqrt hbase
    _ = Real.exp ((-c) / 2) := (Real.exp_half (-c)).symm
    _ = Real.exp (-c / 2) := rfl

/-- A quadratic Dirichlet coercivity estimate directly yields exponential
operator-norm contraction:

`c ||x||^2 <= ||x||^2 - ||T x||^2`

with `0 <= c <= 1` implies

`||T|| <= exp (-c/2)`.

This factors through the sharp square-root bound already proved for bounded
operators and then uses `sqrt(1-c) <= exp(-c/2)`. -/
theorem continuousLinearMap_opNorm_le_exp_neg_half_of_dirichlet_coercive
    {E : Type u}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (T : E →L[ℝ] E)
    (c : ℝ)
    (hc0 : 0 ≤ c)
    (hc1 : c ≤ 1)
    (hcoercive : ∀ x : E,
      c * ‖x‖ ^ 2 ≤ ‖x‖ ^ 2 - ‖T x‖ ^ 2) :
    ‖T‖ ≤ Real.exp (-c / 2) :=
  (continuousLinearMap_opNorm_le_sqrt_one_sub_of_dirichlet_coercive
      T c hc0 hc1 hcoercive).trans
    (sqrt_one_sub_le_exp_neg_half c)

end MathlibAnalytic
end MGAP4D

end