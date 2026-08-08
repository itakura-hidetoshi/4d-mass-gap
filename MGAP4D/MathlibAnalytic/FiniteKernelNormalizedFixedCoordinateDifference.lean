import MGAP4D.MathlibAnalytic.FiniteOSGramKernelEuclideanTransfer
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- A fixed vector of an operator-norm-normalized finite kernel satisfies an
exact output-coordinate difference equation.  This generic identity isolates
the finite sum algebra from later model-specific Perron arguments. -/
theorem finiteKernelNormalizedOperator_fixed_coordinateDifference
    {α : Type} [Fintype α]
    (K : α → α → ℝ)
    (p : FiniteBoundaryHilbert α)
    (hfix : finiteKernelNormalizedOperator K p = p)
    (y y' : α) :
    p y - p y' =
      ‖finiteKernelOperator K‖⁻¹ *
        ∑ x : α, (K x y - K x y') * p x := by
  have hy := congrArg (fun q : FiniteBoundaryHilbert α => q y) hfix
  have hy' := congrArg (fun q : FiniteBoundaryHilbert α => q y') hfix
  unfold finiteKernelNormalizedOperator at hy hy'
  simp only [PiLp.smul_apply, smul_eq_mul] at hy hy'
  rw [finiteKernelOperator_apply] at hy hy'
  rw [← hy, ← hy']
  rw [← Finset.mul_sum]
  apply congrArg (fun z : ℝ => ‖finiteKernelOperator K‖⁻¹ * z)
  rw [Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x _hx
  ring

end

end MathlibAnalytic
end MGAP4D
