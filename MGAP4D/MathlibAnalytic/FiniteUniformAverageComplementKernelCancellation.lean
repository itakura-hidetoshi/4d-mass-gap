import MGAP4D.MathlibAnalytic.FiniteConstantOneKernelNormalization
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators InnerProduct

noncomputable section

/-- Uniform-averaging projector on a finite Euclidean boundary space, written as
the already-established operator-norm normalization of the all-ones kernel. -/
noncomputable def finiteUniformAverageProjectorLinearMap
    {α : Type} [Fintype α] :
    FiniteBoundaryHilbert α →ₗ[ℝ] FiniteBoundaryHilbert α :=
  (finiteKernelNormalizedOperator (fun _ _ : α => (1 : ℝ))).toLinearMap

@[simp] theorem finiteUniformAverageProjectorLinearMap_apply
    {α : Type} [Fintype α]
    (f : FiniteBoundaryHilbert α)
    (y : α) :
    finiteUniformAverageProjectorLinearMap f y =
      (Fintype.card α : ℝ)⁻¹ * ∑ x : α, f x := by
  simpa [finiteUniformAverageProjectorLinearMap] using
    finiteKernelNormalizedOperator_one_apply f y

/-- Complement of the uniform-average projector. -/
noncomputable def finiteUniformAverageComplementLinearMap
    {α : Type} [Fintype α] :
    FiniteBoundaryHilbert α →ₗ[ℝ] FiniteBoundaryHilbert α :=
  (LinearMap.id : FiniteBoundaryHilbert α →ₗ[ℝ] FiniteBoundaryHilbert α) -
    finiteUniformAverageProjectorLinearMap

@[simp] theorem finiteUniformAverageComplementLinearMap_apply
    {α : Type} [Fintype α]
    (f : FiniteBoundaryHilbert α)
    (y : α) :
    finiteUniformAverageComplementLinearMap f y =
      f y - (Fintype.card α : ℝ)⁻¹ * ∑ x : α, f x := by
  change f y - finiteUniformAverageProjectorLinearMap f y = _
  rw [finiteUniformAverageProjectorLinearMap_apply]

/-- The uniform-average complement has zero total coordinate mass. -/
theorem finiteUniformAverageComplementLinearMap_sum_apply
    {α : Type} [Fintype α]
    (f : FiniteBoundaryHilbert α) :
    (∑ y : α, finiteUniformAverageComplementLinearMap f y) = 0 := by
  classical
  have hn : (Fintype.card α : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  simp_rw [finiteUniformAverageComplementLinearMap_apply]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp [hn]

/-- The complement kills every constant finite boundary vector. -/
theorem finiteUniformAverageComplementLinearMap_eq_zero_of_constant
    {α : Type} [Fintype α] [Nonempty α]
    (g : FiniteBoundaryHilbert α)
    (hg : ∀ y y' : α, g y = g y') :
    finiteUniformAverageComplementLinearMap g = 0 := by
  classical
  have hn : (Fintype.card α : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  ext y
  rw [finiteUniformAverageComplementLinearMap_apply]
  have hsum :
      (∑ z : α, g z) = (Fintype.card α : ℝ) * g y := by
    calc
      (∑ z : α, g z) = ∑ _z : α, g y := by
        apply Finset.sum_congr rfl
        intro z _hz
        exact hg z y
      _ = (Fintype.card α : ℝ) * g y := by simp
  rw [hsum]
  field_simp [hn]

/-- If every right-coordinate difference of a kernel is independent of the left
coordinate, then the kernel operator maps every zero-mass input to a constant
output. -/
theorem finiteKernelOperator_apply_eq_of_sum_eq_zero_of_sub_right_independent
    {α : Type} [Fintype α] [Nonempty α]
    (K : α → α → ℝ)
    (hK : ∀ x x' y y' : α,
      K x y - K x y' = K x' y - K x' y')
    (f : FiniteBoundaryHilbert α)
    (hf : (∑ x : α, f x) = 0)
    (y y' : α) :
    finiteKernelOperator K f y = finiteKernelOperator K f y' := by
  classical
  let x₀ : α := Classical.choice inferInstance
  apply sub_eq_zero.mp
  rw [finiteKernelOperator_apply, finiteKernelOperator_apply,
    ← Finset.sum_sub_distrib]
  calc
    (∑ x : α, (K x y * f x - K x y' * f x)) =
        ∑ x : α, (K x y - K x y') * f x := by
      apply Finset.sum_congr rfl
      intro x _hx
      ring
    _ = ∑ x : α, (K x₀ y - K x₀ y') * f x := by
      apply Finset.sum_congr rfl
      intro x _hx
      rw [hK x x₀ y y']
    _ = (K x₀ y - K x₀ y') * ∑ x : α, f x := by
      rw [Finset.mul_sum]
    _ = 0 := by rw [hf, mul_zero]

/-- Exact finite double-centering theorem.  A kernel whose right-coordinate
differences are independent of its left coordinate has no
complement-to-complement block with respect to uniform averaging:

`Q K Q = 0`. -/
theorem finiteUniformAverageComplement_comp_finiteKernelOperator_comp_complement_eq_zero
    {α : Type} [Fintype α] [Nonempty α]
    (K : α → α → ℝ)
    (hK : ∀ x x' y y' : α,
      K x y - K x y' = K x' y - K x' y') :
    finiteUniformAverageComplementLinearMap.comp
        ((finiteKernelOperator K).toLinearMap.comp
          finiteUniformAverageComplementLinearMap) = 0 := by
  apply LinearMap.ext
  intro f
  change
    finiteUniformAverageComplementLinearMap
        (finiteKernelOperator K
          (finiteUniformAverageComplementLinearMap f)) = 0
  apply finiteUniformAverageComplementLinearMap_eq_zero_of_constant
  intro y y'
  exact
    finiteKernelOperator_apply_eq_of_sum_eq_zero_of_sub_right_independent
      K hK (finiteUniformAverageComplementLinearMap f)
      (finiteUniformAverageComplementLinearMap_sum_apply f) y y'

/-- Scaling a boundary-additive kernel cannot create a double-centered block. -/
theorem finiteUniformAverageComplement_comp_smul_finiteKernelOperator_comp_complement_eq_zero
    {α : Type} [Fintype α] [Nonempty α]
    (K : α → α → ℝ)
    (hK : ∀ x x' y y' : α,
      K x y - K x y' = K x' y - K x' y')
    (c : ℝ) :
    finiteUniformAverageComplementLinearMap.comp
        ((c • (finiteKernelOperator K).toLinearMap).comp
          finiteUniformAverageComplementLinearMap) = 0 := by
  apply LinearMap.ext
  intro f
  change
    finiteUniformAverageComplementLinearMap
      (c • finiteKernelOperator K (finiteUniformAverageComplementLinearMap f)) = 0
  rw [map_smul]
  have hzero := LinearMap.congr_fun
    (finiteUniformAverageComplement_comp_finiteKernelOperator_comp_complement_eq_zero K hK) f
  change
    finiteUniformAverageComplementLinearMap
      (finiteKernelOperator K (finiteUniformAverageComplementLinearMap f)) = 0 at hzero
  rw [hzero, smul_zero]

end

end MathlibAnalytic
end MGAP4D
