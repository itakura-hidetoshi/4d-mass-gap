import MGAP4D.MathlibAnalytic.FiniteOSGramKernelEuclideanTransfer
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators InnerProduct

noncomputable section

/-- Pointwise nonnegative vectors in a finite Euclidean boundary Hilbert
space. -/
def FiniteBoundaryPointwiseNonnegative
    {α : Type} [Fintype α]
    (f : FiniteBoundaryHilbert α) : Prop :=
  ∀ x : α, 0 ≤ f x

/-- Pointwise strictly positive vectors in a finite Euclidean boundary Hilbert
space. -/
def FiniteBoundaryPointwisePositive
    {α : Type} [Fintype α]
    (f : FiniteBoundaryHilbert α) : Prop :=
  ∀ x : α, 0 < f x

/-- Coordinatewise absolute value on a finite Euclidean boundary Hilbert
space. -/
noncomputable def finiteBoundaryAbs
    {α : Type} [Fintype α]
    (f : FiniteBoundaryHilbert α) : FiniteBoundaryHilbert α :=
  WithLp.toLp 2 fun x : α => |f x|

@[simp] theorem finiteBoundaryAbs_apply
    {α : Type} [Fintype α]
    (f : FiniteBoundaryHilbert α)
    (x : α) :
    finiteBoundaryAbs f x = |f x| :=
  rfl

/-- Coordinatewise absolute value is pointwise nonnegative. -/
theorem finiteBoundaryAbs_pointwiseNonnegative
    {α : Type} [Fintype α]
    (f : FiniteBoundaryHilbert α) :
    FiniteBoundaryPointwiseNonnegative (finiteBoundaryAbs f) := by
  intro x
  exact abs_nonneg _

/-- Coordinatewise absolute value vanishes exactly when the original vector
vanishes. -/
theorem finiteBoundaryAbs_eq_zero_iff
    {α : Type} [Fintype α]
    (f : FiniteBoundaryHilbert α) :
    finiteBoundaryAbs f = 0 ↔ f = 0 := by
  constructor
  · intro h
    ext x
    have hx := congrArg (fun z : FiniteBoundaryHilbert α => z x) h
    change |f x| = 0 at hx
    exact abs_eq_zero.mp hx
  · intro h
    rw [h]
    ext x
    simp

/-- Coordinatewise absolute value preserves the Euclidean norm. -/
theorem norm_finiteBoundaryAbs
    {α : Type} [Fintype α]
    (f : FiniteBoundaryHilbert α) :
    ‖finiteBoundaryAbs f‖ = ‖f‖ := by
  have hsquare : ‖finiteBoundaryAbs f‖ ^ 2 = ‖f‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq,
      EuclideanSpace.real_norm_sq_eq]
    apply Finset.sum_congr rfl
    intro x _hx
    simp [sq_abs]
  nlinarith [norm_nonneg (finiteBoundaryAbs f), norm_nonneg f]

/-- A nonzero pointwise nonnegative finite vector has a strictly positive
coordinate. -/
theorem exists_pos_coordinate_of_pointwiseNonnegative
    {α : Type} [Fintype α]
    (f : FiniteBoundaryHilbert α)
    (hf : FiniteBoundaryPointwiseNonnegative f)
    (hne : f ≠ 0) :
    ∃ x : α, 0 < f x := by
  by_contra h
  push Not at h
  apply hne
  ext x
  exact le_antisymm (h x) (hf x)

/-- A kernel with every entry strictly positive sends every nonzero
pointwise-nonnegative vector to a pointwise-strictly-positive vector. -/
theorem finiteKernelOperator_pointwisePositive
    {α : Type} [Fintype α]
    (kernel : α → α → ℝ)
    (hkernel : ∀ x y : α, 0 < kernel x y)
    (f : FiniteBoundaryHilbert α)
    (hf : FiniteBoundaryPointwiseNonnegative f)
    (hne : f ≠ 0) :
    FiniteBoundaryPointwisePositive (finiteKernelOperator kernel f) := by
  classical
  obtain ⟨x₀, hx₀⟩ :=
    exists_pos_coordinate_of_pointwiseNonnegative f hf hne
  intro y
  rw [finiteKernelOperator_apply]
  refine (Finset.sum_pos_iff_of_nonneg ?_).2 ?_
  · intro x _hx
    exact mul_nonneg (le_of_lt (hkernel x y)) (hf x)
  · exact ⟨x₀, Finset.mem_univ x₀,
      mul_pos (hkernel x₀ y) hx₀⟩

/-- A strictly-positive finite kernel operator is nonzero as soon as it is
applied to one nonzero nonnegative vector. -/
theorem finiteKernelOperator_ne_zero_of_strictlyPositive
    {α : Type} [Fintype α]
    (kernel : α → α → ℝ)
    (hkernel : ∀ x y : α, 0 < kernel x y)
    (f : FiniteBoundaryHilbert α)
    (hf : FiniteBoundaryPointwiseNonnegative f)
    (hne : f ≠ 0) :
    finiteKernelOperator kernel ≠ 0 := by
  intro hzero
  obtain ⟨y, _hy⟩ :=
    exists_pos_coordinate_of_pointwiseNonnegative f hf hne
  have hpos := finiteKernelOperator_pointwisePositive
    kernel hkernel f hf hne y
  rw [hzero] at hpos
  simp at hpos

/-- Operator-norm normalization preserves strict positivity improvement. -/
theorem finiteKernelNormalizedOperator_pointwisePositive
    {α : Type} [Fintype α]
    (kernel : α → α → ℝ)
    (hkernel : ∀ x y : α, 0 < kernel x y)
    (f : FiniteBoundaryHilbert α)
    (hf : FiniteBoundaryPointwiseNonnegative f)
    (hne : f ≠ 0) :
    FiniteBoundaryPointwisePositive
      (finiteKernelNormalizedOperator kernel f) := by
  have hraw : finiteKernelOperator kernel ≠ 0 :=
    finiteKernelOperator_ne_zero_of_strictlyPositive
      kernel hkernel f hf hne
  have hnorm : 0 < ‖finiteKernelOperator kernel‖ :=
    norm_pos_iff.mpr hraw
  intro y
  unfold finiteKernelNormalizedOperator
  rw [ContinuousLinearMap.smul_apply]
  change 0 < ‖finiteKernelOperator kernel‖⁻¹ *
    finiteKernelOperator kernel f y
  exact mul_pos (inv_pos.mpr hnorm)
    (finiteKernelOperator_pointwisePositive
      kernel hkernel f hf hne y)

end

end MathlibAnalytic
end MGAP4D
