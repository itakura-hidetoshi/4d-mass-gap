import MGAP4D.MathlibAnalytic.FiniteOSGramKernelEuclideanTransfer
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- The finite-kernel operator construction is linear in the kernel entries. -/
noncomputable def finiteKernelOperatorLinearMap
    {α : Type}
    [Fintype α] :
    (α → α → ℝ) →ₗ[ℝ]
      (FiniteBoundaryHilbert α →L[ℝ] FiniteBoundaryHilbert α) where
  toFun := finiteKernelOperator
  map_add' K L := by
    ext f y
    change
      (∑ x : α, (K x y + L x y) * f x) =
        (∑ x : α, K x y * f x) +
          ∑ x : α, L x y * f x
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _hx
    ring
  map_smul' c K := by
    ext f y
    change
      (∑ x : α, (c * K x y) * f x) =
        c * ∑ x : α, K x y * f x
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _hx
    ring

/-- Because the kernel space is finite-dimensional, the linear finite-kernel
operator construction is continuous in operator norm. -/
theorem continuous_finiteKernelOperatorLinearMap
    {α : Type}
    [Fintype α] :
    Continuous
      (finiteKernelOperatorLinearMap (α := α)) := by
  exact
    LinearMap.continuous_of_finiteDimensional
      (finiteKernelOperatorLinearMap (α := α))

/-- Pointwise continuity of all entries of a finite kernel family implies
operator-norm continuity of the associated raw transfer operators. -/
theorem continuous_finiteKernelOperator
    {X α : Type}
    [TopologicalSpace X]
    [Fintype α]
    (kernel : X → α → α → ℝ)
    (hkernel : ∀ a b : α,
      Continuous (fun x => kernel x a b)) :
    Continuous (fun x => finiteKernelOperator (kernel x)) := by
  have hKernelFunction : Continuous kernel := by
    apply continuous_pi
    intro a
    apply continuous_pi
    intro b
    exact hkernel a b
  exact
    continuous_finiteKernelOperatorLinearMap.comp hKernelFunction

/-- The Perron normalization scalar of a finite kernel, namely the operator
norm of its raw transfer, varies continuously with every pointwise continuous
finite kernel family. -/
theorem continuous_finiteKernelOperator_norm
    {X α : Type}
    [TopologicalSpace X]
    [Fintype α]
    (kernel : X → α → α → ℝ)
    (hkernel : ∀ a b : α,
      Continuous (fun x => kernel x a b)) :
    Continuous (fun x => ‖finiteKernelOperator (kernel x)‖) :=
  continuous_norm.comp (continuous_finiteKernelOperator kernel hkernel)

/-- If no raw transfer in the family vanishes, operator normalization is
continuous in operator norm. -/
theorem continuous_finiteKernelNormalizedOperator
    {X α : Type}
    [TopologicalSpace X]
    [Fintype α]
    (kernel : X → α → α → ℝ)
    (hkernel : ∀ a b : α,
      Continuous (fun x => kernel x a b))
    (hraw : ∀ x, finiteKernelOperator (kernel x) ≠ 0) :
    Continuous (fun x => finiteKernelNormalizedOperator (kernel x)) := by
  have hOperator := continuous_finiteKernelOperator kernel hkernel
  have hNorm := continuous_finiteKernelOperator_norm kernel hkernel
  have hInv : Continuous (fun x => ‖finiteKernelOperator (kernel x)‖⁻¹) :=
    hNorm.inv₀ (fun x => norm_ne_zero_iff.mpr (hraw x))
  simpa [finiteKernelNormalizedOperator] using hInv.smul hOperator

/-- Every matrix coefficient of a continuously normalized finite transfer is
continuous. -/
theorem continuous_finiteKernelNormalizedOperator_apply
    {X α : Type}
    [TopologicalSpace X]
    [Fintype α]
    (kernel : X → α → α → ℝ)
    (hkernel : ∀ a b : α,
      Continuous (fun x => kernel x a b))
    (hraw : ∀ x, finiteKernelOperator (kernel x) ≠ 0)
    (f : FiniteBoundaryHilbert α)
    (a : α) :
    Continuous (fun x => finiteKernelNormalizedOperator (kernel x) f a) := by
  have hNormalized :=
    continuous_finiteKernelNormalizedOperator kernel hkernel hraw
  exact
    (ContinuousLinearMap.apply ℝ
      (FiniteBoundaryHilbert α)).continuous.comp
      ((hNormalized.prodMk continuous_const).prodMk continuous_const)

end

end MathlibAnalytic
end MGAP4D
