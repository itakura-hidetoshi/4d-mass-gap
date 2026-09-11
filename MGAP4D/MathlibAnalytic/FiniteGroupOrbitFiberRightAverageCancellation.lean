import MGAP4D.MathlibAnalytic.FiniteGroupInvariantKernelRightAverage
import MGAP4D.MathlibAnalytic.FiniteGroupInvariantOrbitFiberKernelCriterion
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- On an equivariant coarse fibre, a right group average of a diagonally
invariant kernel disappears after orbit aggregation whenever the scalar weight
is invariant under the fine group action.  This is the generic finite-group
cancellation used to descend the actual unfixed-gauge obstruction to the
underlying temporal-gauge Gram kernel. -/
theorem finiteGroupOrbitFiberCoefficient_rightAverage_eq_raw
    (Gf Gc αf αc : Type)
    [Group Gf]
    [Fintype Gf]
    [Group Gc]
    [Fintype αf]
    [Fintype αc]
    [MulAction Gf αf]
    [MulAction Gc αc]
    (φ : Gf → Gc)
    (C : αf → αc)
    (hC : ∀ g : Gf, ∀ x : αf, C (g • x) = φ g • C x)
    (kernel : αf → αf → ℝ)
    (hKernel : ∀ g : Gf, ∀ x y : αf,
      kernel (g • x) (g • y) = kernel x y)
    (scale : αf → ℝ)
    (hScale : ∀ g : Gf, ∀ x : αf, scale (g • x) = scale x)
    (A : αf)
    (q : FiniteGroupOrbitQuotient Gc αc) :
    finiteGroupOrbitFiberCoefficient Gc αc C
        (fun B => finiteGroupRightAveragedKernel Gf αf kernel B A * scale B) q =
      finiteGroupOrbitFiberCoefficient Gc αc C
        (fun B => kernel B A * scale B) q := by
  classical
  have hcard : (Fintype.card Gf : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hFixed (g : Gf) :
      (∑ B : αf,
        if finiteGroupOrbitClass Gc αc (C B) = q then
          kernel B (g • A) * scale B
        else 0) =
      ∑ B : αf,
        if finiteGroupOrbitClass Gc αc (C B) = q then
          kernel B A * scale B
        else 0 := by
    refine Fintype.sum_equiv (finiteMulActionEquiv Gf αf g⁻¹) _ _ ?_
    intro B
    have hClass :
        finiteGroupOrbitClass Gc αc (C (g⁻¹ • B)) =
          finiteGroupOrbitClass Gc αc (C B) := by
      rw [hC]
      exact finiteGroupOrbitClass_smul Gc αc (φ g⁻¹) (C B)
    have hScaleInv : scale (g⁻¹ • B) = scale B := hScale g⁻¹ B
    have hKernelMove :
        kernel B (g • A) = kernel (g⁻¹ • B) A := by
      simpa using hKernel g (g⁻¹ • B) A
    change
      (if finiteGroupOrbitClass Gc αc (C B) = q then
        kernel B (g • A) * scale B
      else 0) =
        if finiteGroupOrbitClass Gc αc (C (g⁻¹ • B)) = q then
          kernel (g⁻¹ • B) A * scale (g⁻¹ • B)
        else 0
    rw [hClass, hScaleInv]
    by_cases hB : finiteGroupOrbitClass Gc αc (C B) = q
    · simp [hB, hKernelMove]
    · simp [hB]
  unfold finiteGroupOrbitFiberCoefficient finiteGroupRightAveragedKernel
  calc
    (∑ B : αf,
      if finiteGroupOrbitClass Gc αc (C B) = q then
        ((Fintype.card Gf : ℝ)⁻¹ *
            ∑ g : Gf, kernel B (g • A)) * scale B
      else 0) =
        ∑ B : αf, ∑ g : Gf,
          if finiteGroupOrbitClass Gc αc (C B) = q then
            (Fintype.card Gf : ℝ)⁻¹ *
              (kernel B (g • A) * scale B)
          else 0 := by
      apply Finset.sum_congr rfl
      intro B _hB
      by_cases hBq : finiteGroupOrbitClass Gc αc (C B) = q
      · rw [if_pos hBq, Finset.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro g _hg
        rw [if_pos hBq]
        ring
      · simp [hBq]
    _ = ∑ g : Gf, ∑ B : αf,
          if finiteGroupOrbitClass Gc αc (C B) = q then
            (Fintype.card Gf : ℝ)⁻¹ *
              (kernel B (g • A) * scale B)
          else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ g : Gf,
          (Fintype.card Gf : ℝ)⁻¹ *
            (∑ B : αf,
              if finiteGroupOrbitClass Gc αc (C B) = q then
                kernel B (g • A) * scale B
              else 0) := by
      apply Finset.sum_congr rfl
      intro g _hg
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro B _hB
      by_cases hBq : finiteGroupOrbitClass Gc αc (C B) = q
      · simp [hBq]
      · simp [hBq]
    _ = (Fintype.card Gf : ℝ)⁻¹ *
          ∑ g : Gf,
            (∑ B : αf,
              if finiteGroupOrbitClass Gc αc (C B) = q then
                kernel B (g • A) * scale B
              else 0) := by
      rw [Finset.mul_sum]
    _ = (Fintype.card Gf : ℝ)⁻¹ *
          ∑ _g : Gf,
            (∑ B : αf,
              if finiteGroupOrbitClass Gc αc (C B) = q then
                kernel B A * scale B
              else 0) := by
      congr 1
      apply Finset.sum_congr rfl
      intro g _hg
      exact hFixed g
    _ = (Fintype.card Gf : ℝ)⁻¹ *
          ((Fintype.card Gf : ℝ) *
            (∑ B : αf,
              if finiteGroupOrbitClass Gc αc (C B) = q then
                kernel B A * scale B
              else 0)) := by
      simp
    _ = ∑ B : αf,
          if finiteGroupOrbitClass Gc αc (C B) = q then
            kernel B A * scale B
          else 0 := by
      rw [← mul_assoc, inv_mul_cancel₀ hcard, one_mul]

/-- The same cancellation specialized to ordinary orbit aggregation on one
acted finite type. -/
theorem finiteGroupOrbitAggregateCoefficient_rightAverage_eq_raw
    (G α : Type)
    [Group G]
    [Fintype G]
    [Fintype α]
    [MulAction G α]
    (kernel : α → α → ℝ)
    (hKernel : ∀ g : G, ∀ x y : α,
      kernel (g • x) (g • y) = kernel x y)
    (scale : α → ℝ)
    (hScale : ∀ g : G, ∀ x : α, scale (g • x) = scale x)
    (A : α)
    (q : FiniteGroupOrbitQuotient G α) :
    finiteGroupOrbitAggregateCoefficient G α
        (fun B => finiteGroupRightAveragedKernel G α kernel B A * scale B) q =
      finiteGroupOrbitAggregateCoefficient G α
        (fun B => kernel B A * scale B) q := by
  simpa only [finiteGroupOrbitAggregateCoefficient,
    finiteGroupOrbitFiberCoefficient] using
    (finiteGroupOrbitFiberCoefficient_rightAverage_eq_raw
      G G α α (fun g => g) (fun x => x)
      (by intro g x; rfl) kernel hKernel scale hScale A q)

/-- A constant scalar weight is automatically compatible with the aggregate
right-average cancellation. -/
theorem finiteGroupOrbitAggregateCoefficient_rightAverage_mul_constant_eq_raw
    (G α : Type)
    [Group G]
    [Fintype G]
    [Fintype α]
    [MulAction G α]
    (kernel : α → α → ℝ)
    (hKernel : ∀ g : G, ∀ x y : α,
      kernel (g • x) (g • y) = kernel x y)
    (c : ℝ)
    (A : α)
    (q : FiniteGroupOrbitQuotient G α) :
    finiteGroupOrbitAggregateCoefficient G α
        (fun B => c * finiteGroupRightAveragedKernel G α kernel B A) q =
      finiteGroupOrbitAggregateCoefficient G α
        (fun B => c * kernel B A) q := by
  have h := finiteGroupOrbitAggregateCoefficient_rightAverage_eq_raw
    G α kernel hKernel (fun _ : α => c) (by intro g x; rfl) A q
  simpa only [mul_comm] using h

end

end MathlibAnalytic
end MGAP4D
