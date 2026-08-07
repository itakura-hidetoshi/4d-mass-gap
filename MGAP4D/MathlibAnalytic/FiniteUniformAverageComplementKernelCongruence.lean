import MGAP4D.MathlibAnalytic.FiniteUniformAverageComplementKernelCancellation
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators InnerProduct

noncomputable section

/-- Subtracting a boundary-additive kernel does not change the double-centered
finite kernel operator.  This is the congruence form of Package T's `Q K Q = 0`
criterion and is convenient for removing normalization-derivative terms. -/
theorem finiteUniformAverageComplement_comp_finiteKernelOperator_congr_of_sub_right_independent
    {α : Type} [Fintype α] [Nonempty α]
    (K L : α → α → ℝ)
    (hKL : ∀ x x' y y' : α,
      (K x y - L x y) - (K x y' - L x y') =
        (K x' y - L x' y) - (K x' y' - L x' y')) :
    finiteUniformAverageComplementLinearMap.comp
        ((finiteKernelOperator K).toLinearMap.comp
          finiteUniformAverageComplementLinearMap) =
      finiteUniformAverageComplementLinearMap.comp
        ((finiteKernelOperator L).toLinearMap.comp
          finiteUniformAverageComplementLinearMap) := by
  classical
  let R : α → α → ℝ := fun x y => K x y - L x y
  apply LinearMap.ext
  intro f
  let qf : FiniteBoundaryHilbert α := finiteUniformAverageComplementLinearMap f
  let g : FiniteBoundaryHilbert α := finiteKernelOperator R qf
  have hqf : (∑ x : α, qf x) = 0 := by
    dsimp [qf]
    exact finiteUniformAverageComplementLinearMap_sum_apply f
  have hgconst : ∀ y y' : α, g y = g y' := by
    intro y y'
    dsimp [g]
    exact
      finiteKernelOperator_apply_eq_of_sum_eq_zero_of_sub_right_independent
        R hKL qf hqf y y'
  have hQg : finiteUniformAverageComplementLinearMap g = 0 :=
    finiteUniformAverageComplementLinearMap_eq_zero_of_constant g hgconst
  have hdiff :
      finiteKernelOperator K qf - finiteKernelOperator L qf = g := by
    ext y
    dsimp [g, R]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x _hx
    ring
  change
    finiteUniformAverageComplementLinearMap (finiteKernelOperator K qf) =
      finiteUniformAverageComplementLinearMap (finiteKernelOperator L qf)
  have hzero :
      finiteUniformAverageComplementLinearMap
        (finiteKernelOperator K qf - finiteKernelOperator L qf) = 0 := by
    rw [hdiff]
    exact hQg
  rw [map_sub] at hzero
  exact sub_eq_zero.mp hzero

end

end MathlibAnalytic
end MGAP4D
