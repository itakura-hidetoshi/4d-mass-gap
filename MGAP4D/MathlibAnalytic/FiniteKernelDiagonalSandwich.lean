import MGAP4D.MathlibAnalytic.FiniteOSGramKernelEuclideanTransfer
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators InnerProduct

noncomputable section

/-- Pointwise multiplication by a real boundary weight on a finite Euclidean
boundary Hilbert space. -/
noncomputable def finiteBoundaryMultiplicationOperator
    {α : Type} [Fintype α]
    (a : α → ℝ) :
    FiniteBoundaryHilbert α →L[ℝ] FiniteBoundaryHilbert α :=
  LinearMap.toContinuousLinearMap
    { toFun := fun f => WithLp.toLp 2 fun x : α => a x * f x
      map_add' := by
        intro f g
        ext x
        change a x * (f x + g x) = a x * f x + a x * g x
        ring
      map_smul' := by
        intro c f
        ext x
        change a x * (c * f x) = c * (a x * f x)
        ring }

@[simp] theorem finiteBoundaryMultiplicationOperator_apply
    {α : Type} [Fintype α]
    (a : α → ℝ)
    (f : FiniteBoundaryHilbert α)
    (x : α) :
    finiteBoundaryMultiplicationOperator a f x = a x * f x :=
  rfl

/-- A pointwise kernel sandwich is exactly operator composition by the same
boundary multiplication operator on the input and output sides. -/
theorem finiteKernelOperator_diagonalSandwich_eq
    {α : Type} [Fintype α]
    (kernel : α → α → ℝ)
    (a : α → ℝ) :
    finiteKernelOperator (fun x y => a x * kernel x y * a y) =
      (finiteBoundaryMultiplicationOperator a).comp
        ((finiteKernelOperator kernel).comp
          (finiteBoundaryMultiplicationOperator a)) := by
  ext f y
  change
    (∑ x : α, (a x * kernel x y * a y) * f x) =
      a y * ∑ x : α, kernel x y * (a x * f x)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _hx
  ring

/-- The operator of a Gram-kernel sandwich has the exact diagonal
factorization `M_a K M_a`. -/
theorem finiteGramKernelOperator_sandwich_eq
    {α : Type} [Fintype α]
    (K : FiniteOSGramKernelOn α)
    (a : α → ℝ) :
    finiteKernelOperator (K.sandwich a).kernel =
      (finiteBoundaryMultiplicationOperator a).comp
        ((finiteKernelOperator K.kernel).comp
          (finiteBoundaryMultiplicationOperator a)) := by
  exact finiteKernelOperator_diagonalSandwich_eq K.kernel a

/-- The quadratic form of a diagonal kernel sandwich is the original kernel
quadratic form evaluated on the weighted boundary vector. -/
theorem finiteKernelOperator_diagonalSandwich_quadratic
    {α : Type} [Fintype α]
    (kernel : α → α → ℝ)
    (a : α → ℝ)
    (f : FiniteBoundaryHilbert α) :
    inner ℝ
        (finiteKernelOperator (fun x y => a x * kernel x y * a y) f) f =
      inner ℝ
        (finiteKernelOperator kernel
          (finiteBoundaryMultiplicationOperator a f))
        (finiteBoundaryMultiplicationOperator a f) := by
  rw [finiteKernelOperator_matrixElement,
    finiteKernelOperator_matrixElement]
  apply Finset.sum_congr rfl
  intro x _hx
  apply Finset.sum_congr rfl
  intro y _hy
  simp only [finiteBoundaryMultiplicationOperator_apply]
  ring

/-- Gram-kernel sandwich quadratic forms have the same exact weighted-vector
representation. -/
theorem finiteGramKernelOperator_sandwich_quadratic
    {α : Type} [Fintype α]
    (K : FiniteOSGramKernelOn α)
    (a : α → ℝ)
    (f : FiniteBoundaryHilbert α) :
    inner ℝ (finiteKernelOperator (K.sandwich a).kernel f) f =
      inner ℝ
        (finiteKernelOperator K.kernel
          (finiteBoundaryMultiplicationOperator a f))
        (finiteBoundaryMultiplicationOperator a f) :=
  finiteKernelOperator_diagonalSandwich_quadratic K.kernel a f

/-- A nowhere-zero finite boundary weight gives an injective multiplication
operator. -/
theorem finiteBoundaryMultiplicationOperator_injective
    {α : Type} [Fintype α]
    (a : α → ℝ)
    (ha : ∀ x, a x ≠ 0) :
    Function.Injective (finiteBoundaryMultiplicationOperator a) := by
  intro f g hfg
  ext x
  have hx := congrArg (fun h : FiniteBoundaryHilbert α => h x) hfg
  change a x * f x = a x * g x at hx
  exact mul_left_cancel₀ (ha x) hx

end

end MathlibAnalytic
end MGAP4D
