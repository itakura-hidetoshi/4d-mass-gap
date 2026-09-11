import MGAP4D.MathlibAnalytic.FiniteStrictlyPositiveKernelPerronFixedSpace
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators InnerProduct

noncomputable section

/-- Replacing a finite vector by its coordinatewise absolute value can only
increase the quadratic form of a kernel whose entries are strictly positive. -/
theorem finiteKernelNormalizedOperator_inner_le_abs_inner
    {α : Type} [Fintype α]
    (kernel : α → α → ℝ)
    (hkernel : ∀ x y : α, 0 < kernel x y)
    (f : FiniteBoundaryHilbert α) :
    inner ℝ (finiteKernelNormalizedOperator kernel f) f ≤
      inner ℝ
        (finiteKernelNormalizedOperator kernel (finiteBoundaryAbs f))
        (finiteBoundaryAbs f) := by
  rw [finiteKernelNormalizedOperator_matrixElement,
    finiteKernelNormalizedOperator_matrixElement]
  apply mul_le_mul_of_nonneg_left
  · apply Finset.sum_le_sum
    intro x _hx
    apply Finset.sum_le_sum
    intro y _hy
    change
      f x * kernel x y * f y ≤
        |f x| * kernel x y * |f y|
    calc
      f x * kernel x y * f y =
          kernel x y * (f x * f y) := by ring
      _ ≤ kernel x y * |f x * f y| :=
        mul_le_mul_of_nonneg_left
          (le_abs_self (f x * f y)) (le_of_lt (hkernel x y))
      _ = |f x| * kernel x y * |f y| := by
        rw [abs_mul]
        ring
  · exact inv_nonneg.mpr (norm_nonneg _)

/-- Every nonzero eigenvalue-one vector of a normalized strictly-positive
finite kernel yields, by coordinatewise absolute value, a nonzero pointwise
strictly-positive eigenvalue-one vector. -/
theorem finiteKernelNormalizedOperator_exists_pointwisePositive_fixed
    {α : Type} [Fintype α]
    (kernel : α → α → ℝ)
    (hkernel : ∀ x y : α, 0 < kernel x y)
    (f : FiniteBoundaryHilbert α)
    (hfne : f ≠ 0)
    (hffix : finiteKernelNormalizedOperator kernel f = f) :
    ∃ p : FiniteBoundaryHilbert α,
      p ≠ 0 ∧
      FiniteBoundaryPointwisePositive p ∧
      finiteKernelNormalizedOperator kernel p = p := by
  let p : FiniteBoundaryHilbert α := finiteBoundaryAbs f
  have hp_nonneg : FiniteBoundaryPointwiseNonnegative p := by
    simpa [p] using finiteBoundaryAbs_pointwiseNonnegative f
  have hpne : p ≠ 0 := by
    intro hpzero
    apply hfne
    exact (finiteBoundaryAbs_eq_zero_iff f).mp (by simpa [p] using hpzero)
  have hraw : finiteKernelOperator kernel ≠ 0 :=
    finiteKernelOperator_ne_zero_of_strictlyPositive
      kernel hkernel p hp_nonneg hpne
  have hlower :
      ‖p‖ ^ 2 ≤
        inner ℝ (finiteKernelNormalizedOperator kernel p) p := by
    calc
      ‖p‖ ^ 2 = ‖f‖ ^ 2 := by
        rw [show ‖p‖ = ‖f‖ by simpa [p] using norm_finiteBoundaryAbs f]
      _ = inner ℝ (finiteKernelNormalizedOperator kernel f) f := by
        rw [hffix, real_inner_self_eq_norm_sq]
      _ ≤ inner ℝ (finiteKernelNormalizedOperator kernel p) p := by
        simpa [p] using
          finiteKernelNormalizedOperator_inner_le_abs_inner
            kernel hkernel f
  have hcontract :
      ‖finiteKernelNormalizedOperator kernel p‖ ≤ ‖p‖ :=
    finiteKernelNormalizedOperator_norm_apply_le kernel hraw p
  have hupper :
      inner ℝ (finiteKernelNormalizedOperator kernel p) p ≤
        ‖p‖ ^ 2 := by
    calc
      inner ℝ (finiteKernelNormalizedOperator kernel p) p ≤
          ‖finiteKernelNormalizedOperator kernel p‖ * ‖p‖ :=
        real_inner_le_norm _ _
      _ ≤ ‖p‖ * ‖p‖ :=
        mul_le_mul_of_nonneg_right hcontract (norm_nonneg p)
      _ = ‖p‖ ^ 2 := by ring
  have hinner :
      inner ℝ (finiteKernelNormalizedOperator kernel p) p =
        ‖p‖ ^ 2 :=
    le_antisymm hupper hlower
  have hnormsq :
      ‖finiteKernelNormalizedOperator kernel p‖ ^ 2 ≤ ‖p‖ ^ 2 := by
    nlinarith [norm_nonneg (finiteKernelNormalizedOperator kernel p),
      norm_nonneg p]
  have hdiffsq :
      ‖finiteKernelNormalizedOperator kernel p - p‖ ^ 2 ≤ 0 := by
    rw [norm_sub_sq_real, hinner]
    nlinarith
  have hnormdiff :
      ‖finiteKernelNormalizedOperator kernel p - p‖ = 0 := by
    nlinarith [norm_nonneg
      (finiteKernelNormalizedOperator kernel p - p)]
  have hpfix : finiteKernelNormalizedOperator kernel p = p :=
    sub_eq_zero.mp (norm_eq_zero.mp hnormdiff)
  have hp_pos : FiniteBoundaryPointwisePositive p := by
    have hTpos :=
      finiteKernelNormalizedOperator_pointwisePositive
        kernel hkernel p hp_nonneg hpne
    rw [hpfix] at hTpos
    exact hTpos
  exact ⟨p, hpne, hp_pos, hpfix⟩

/-- A nonzero fixed vector therefore determines the complete one-dimensional
fixed space of a normalized strictly-positive finite kernel. -/
theorem finiteKernelNormalizedOperator_fixed_space_generated_by_positive_ground
    {α : Type} [Fintype α] [Nonempty α]
    (kernel : α → α → ℝ)
    (hkernel : ∀ x y : α, 0 < kernel x y)
    (f : FiniteBoundaryHilbert α)
    (hfne : f ≠ 0)
    (hffix : finiteKernelNormalizedOperator kernel f = f) :
    ∃ p : FiniteBoundaryHilbert α,
      p ≠ 0 ∧
      FiniteBoundaryPointwisePositive p ∧
      finiteKernelNormalizedOperator kernel p = p ∧
      ∀ g : FiniteBoundaryHilbert α,
        finiteKernelNormalizedOperator kernel g = g →
          ∃ c : ℝ, g = c • p := by
  obtain ⟨p, hpne, hp, hpfix⟩ :=
    finiteKernelNormalizedOperator_exists_pointwisePositive_fixed
      kernel hkernel f hfne hffix
  refine ⟨p, hpne, hp, hpfix, ?_⟩
  intro g hgfix
  exact
    finiteKernelNormalizedOperator_fixed_eq_smul_of_pointwisePositive_fixed
      kernel hkernel p g hp hpfix hgfix

end

end MathlibAnalytic
end MGAP4D
