import MGAP4D.MathlibAnalytic.FiniteGroupInvariantKernelCompressedTransfer
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators InnerProduct

noncomputable section

/-- Inversion as a finite reindexing equivalence. -/
def finiteGroupInverseEquiv
    (G : Type) [Group G] : G ≃ G where
  toFun := fun g => g⁻¹
  invFun := fun g => g⁻¹
  left_inv := by
    intro g
    simp
  right_inv := by
    intro g
    simp

/-- Average a finite kernel over the group action on its right boundary. -/
def finiteGroupRightAveragedKernel
    (G α : Type) [Group G] [Fintype G] [MulAction G α]
    (kernel : α → α → ℝ) :
    α → α → ℝ :=
  fun x y =>
    (Fintype.card G : ℝ)⁻¹ * ∑ g : G, kernel x (g • y)

@[simp] theorem finiteGroupRightAveragedKernel_apply
    (G α : Type) [Group G] [Fintype G] [MulAction G α]
    (kernel : α → α → ℝ)
    (x y : α) :
    finiteGroupRightAveragedKernel G α kernel x y =
      (Fintype.card G : ℝ)⁻¹ * ∑ g : G, kernel x (g • y) :=
  rfl

/-- Right averaging makes the second boundary separately gauge invariant. -/
theorem finiteGroupRightAveragedKernel_right_invariant
    (G α : Type) [Group G] [Fintype G] [MulAction G α]
    (kernel : α → α → ℝ)
    (a : G)
    (x y : α) :
    finiteGroupRightAveragedKernel G α kernel x (a • y) =
      finiteGroupRightAveragedKernel G α kernel x y := by
  classical
  unfold finiteGroupRightAveragedKernel
  congr 1
  refine Fintype.sum_equiv (finiteGroupActionRightMulEquiv G a) _ _ ?_
  intro g
  change kernel x (g • (a • y)) = kernel x ((g * a) • y)
  rw [mul_smul]

/-- For a symmetric diagonally invariant kernel, the right average is
symmetric. -/
theorem finiteGroupRightAveragedKernel_symmetric
    (G α : Type) [Group G] [Fintype G] [MulAction G α]
    (kernel : α → α → ℝ)
    (hsymm : ∀ x y : α, kernel x y = kernel y x)
    (hinv : ∀ g : G, ∀ x y : α,
      kernel (g • x) (g • y) = kernel x y)
    (x y : α) :
    finiteGroupRightAveragedKernel G α kernel x y =
      finiteGroupRightAveragedKernel G α kernel y x := by
  classical
  unfold finiteGroupRightAveragedKernel
  congr 1
  refine Fintype.sum_equiv (finiteGroupInverseEquiv G) _ _ ?_
  intro g
  calc
    kernel x (g • y) = kernel (g • y) x := hsymm _ _
    _ = kernel y (g⁻¹ • x) := by
      simpa using (hinv g⁻¹ (g • y) x).symm

/-- Symmetry plus right invariance also gives separate invariance on the left
boundary. -/
theorem finiteGroupRightAveragedKernel_left_invariant
    (G α : Type) [Group G] [Fintype G] [MulAction G α]
    (kernel : α → α → ℝ)
    (hsymm : ∀ x y : α, kernel x y = kernel y x)
    (hinv : ∀ g : G, ∀ x y : α,
      kernel (g • x) (g • y) = kernel x y)
    (a : G)
    (x y : α) :
    finiteGroupRightAveragedKernel G α kernel (a • x) y =
      finiteGroupRightAveragedKernel G α kernel x y := by
  calc
    finiteGroupRightAveragedKernel G α kernel (a • x) y =
        finiteGroupRightAveragedKernel G α kernel y (a • x) :=
      finiteGroupRightAveragedKernel_symmetric
        G α kernel hsymm hinv _ _
    _ = finiteGroupRightAveragedKernel G α kernel y x :=
      finiteGroupRightAveragedKernel_right_invariant
        G α kernel a y x
    _ = finiteGroupRightAveragedKernel G α kernel x y :=
      finiteGroupRightAveragedKernel_symmetric
        G α kernel hsymm hinv _ _

/-- The finite-group averaging projector is symmetric on the Euclidean
boundary Hilbert space. -/
theorem finiteGroupAveragingProjector_isSymmetric
    (G α : Type) [Group G] [Fintype G] [Fintype α] [MulAction G α] :
    (finiteGroupAveragingProjector G α).toLinearMap.IsSymmetric := by
  intro f h
  have hPf :
      finiteGroupAveragingProjector G α f ∈
        finiteGroupInvariantSubmodule G α :=
    finiteGroupAveragingProjector_mem_invariant G α f
  have hPh :
      finiteGroupAveragingProjector G α h ∈
        finiteGroupInvariantSubmodule G α :=
    finiteGroupAveragingProjector_mem_invariant G α h
  calc
    inner ℝ (finiteGroupAveragingProjector G α f) h =
        inner ℝ h (finiteGroupAveragingProjector G α f) :=
      real_inner_comm _ _
    _ = inner ℝ (finiteGroupAveragingProjector G α h)
          (finiteGroupAveragingProjector G α f) := by
      symm
      exact finiteGroupAveragingProjector_inner_invariant
        G α h (finiteGroupAveragingProjector G α f) hPf
    _ = inner ℝ (finiteGroupAveragingProjector G α f)
          (finiteGroupAveragingProjector G α h) :=
      real_inner_comm _ _
    _ = inner ℝ f (finiteGroupAveragingProjector G α h) :=
      finiteGroupAveragingProjector_inner_invariant
        G α f (finiteGroupAveragingProjector G α h) hPh

/-- The transfer represented by the right-averaged kernel is exactly the raw
transfer followed by gauge projection on the output boundary. -/
theorem finiteKernelOperator_rightAveraged_eq_projector_comp
    (G α : Type) [Group G] [Fintype G] [Fintype α] [MulAction G α]
    (kernel : α → α → ℝ) :
    finiteKernelOperator (finiteGroupRightAveragedKernel G α kernel) =
      (finiteGroupAveragingProjector G α).comp
        (finiteKernelOperator kernel) := by
  classical
  apply ContinuousLinearMap.ext
  intro f
  ext y
  change
    (∑ x : α,
      ((Fintype.card G : ℝ)⁻¹ *
        ∑ g : G, kernel x (g • y)) * f x) =
      (Fintype.card G : ℝ)⁻¹ *
        ∑ g : G, ∑ x : α, kernel x (g • y) * f x
  calc
    (∑ x : α,
      ((Fintype.card G : ℝ)⁻¹ *
        ∑ g : G, kernel x (g • y)) * f x) =
        ∑ x : α, ∑ g : G,
          (Fintype.card G : ℝ)⁻¹ *
            (kernel x (g • y) * f x) := by
      apply Finset.sum_congr rfl
      intro x _hx
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro g _hg
      ring
    _ = ∑ g : G, ∑ x : α,
          (Fintype.card G : ℝ)⁻¹ *
            (kernel x (g • y) * f x) := by
      rw [Finset.sum_comm]
    _ = ∑ g : G,
          (Fintype.card G : ℝ)⁻¹ *
            (∑ x : α, kernel x (g • y) * f x) := by
      apply Finset.sum_congr rfl
      intro g _hg
      rw [Finset.mul_sum]
    _ = (Fintype.card G : ℝ)⁻¹ *
        ∑ g : G, ∑ x : α, kernel x (g • y) * f x := by
      rw [Finset.mul_sum]

/-- Diagonal invariance lets the same averaged transfer be written as raw
transfer after projection on the input boundary. -/
theorem finiteKernelOperator_rightAveraged_eq_comp_projector
    (G α : Type) [Group G] [Fintype G] [Fintype α] [MulAction G α]
    (kernel : α → α → ℝ)
    (hinv : ∀ g : G, ∀ x y : α,
      kernel (g • x) (g • y) = kernel x y) :
    finiteKernelOperator (finiteGroupRightAveragedKernel G α kernel) =
      (finiteKernelOperator kernel).comp
        (finiteGroupAveragingProjector G α) := by
  calc
    finiteKernelOperator (finiteGroupRightAveragedKernel G α kernel) =
        (finiteGroupAveragingProjector G α).comp
          (finiteKernelOperator kernel) :=
      finiteKernelOperator_rightAveraged_eq_projector_comp
        G α kernel
    _ = (finiteKernelOperator kernel).comp
          (finiteGroupAveragingProjector G α) :=
      (finiteKernelOperator_commutes_groupAveraging
        G α kernel hinv).symm

/-- Every right-averaged kernel transfer lands in the invariant boundary
subspace. -/
theorem finiteKernelOperator_rightAveraged_mem_invariant
    (G α : Type) [Group G] [Fintype G] [Fintype α] [MulAction G α]
    (kernel : α → α → ℝ)
    (f : FiniteBoundaryHilbert α) :
    finiteKernelOperator (finiteGroupRightAveragedKernel G α kernel) f ∈
      finiteGroupInvariantSubmodule G α := by
  rw [finiteKernelOperator_rightAveraged_eq_projector_comp]
  exact finiteGroupAveragingProjector_mem_invariant
    G α (finiteKernelOperator kernel f)

/-- Right averaging preserves positivity of a diagonally invariant finite Gram
kernel at the transfer-operator level. -/
theorem finiteKernelOperator_rightAveraged_quadratic_nonneg
    (G α : Type) [Group G] [Fintype G] [Fintype α] [MulAction G α]
    (K : FiniteOSGramKernelOn α)
    (hinv : ∀ g : G, ∀ x y : α,
      K.kernel (g • x) (g • y) = K.kernel x y)
    (f : FiniteBoundaryHilbert α) :
    0 ≤ inner ℝ
      (finiteKernelOperator
        (finiteGroupRightAveragedKernel G α K.kernel) f) f := by
  rw [finiteKernelOperator_rightAveraged_eq_comp_projector
    G α K.kernel hinv]
  change 0 ≤ inner ℝ
    (finiteKernelOperator K.kernel
      (finiteGroupAveragingProjector G α f)) f
  have hmap :
      finiteKernelOperator K.kernel
          (finiteGroupAveragingProjector G α f) ∈
        finiteGroupInvariantSubmodule G α := by
    exact finiteKernelOperator_maps_groupInvariant
      G α K.kernel hinv
      ⟨finiteGroupAveragingProjector G α f,
        finiteGroupAveragingProjector_mem_invariant G α f⟩
  have hpair :
      inner ℝ
          (finiteKernelOperator K.kernel
            (finiteGroupAveragingProjector G α f)) f =
        inner ℝ
          (finiteKernelOperator K.kernel
            (finiteGroupAveragingProjector G α f))
          (finiteGroupAveragingProjector G α f) := by
    calc
      inner ℝ
          (finiteKernelOperator K.kernel
            (finiteGroupAveragingProjector G α f)) f =
          inner ℝ f
            (finiteKernelOperator K.kernel
              (finiteGroupAveragingProjector G α f)) :=
        real_inner_comm _ _
      _ = inner ℝ (finiteGroupAveragingProjector G α f)
            (finiteKernelOperator K.kernel
              (finiteGroupAveragingProjector G α f)) := by
        symm
        exact finiteGroupAveragingProjector_inner_invariant
          G α f
          (finiteKernelOperator K.kernel
            (finiteGroupAveragingProjector G α f)) hmap
      _ = inner ℝ
            (finiteKernelOperator K.kernel
              (finiteGroupAveragingProjector G α f))
            (finiteGroupAveragingProjector G α f) :=
        real_inner_comm _ _
  rw [hpair]
  exact finiteGramKernelOperator_quadratic_nonneg
    K (finiteGroupAveragingProjector G α f)

/-- Nonnegative operator-norm scaling preserves positivity of the averaged
transfer. -/
theorem finiteKernelNormalizedOperator_rightAveraged_quadratic_nonneg
    (G α : Type) [Group G] [Fintype G] [Fintype α] [MulAction G α]
    (K : FiniteOSGramKernelOn α)
    (hinv : ∀ g : G, ∀ x y : α,
      K.kernel (g • x) (g • y) = K.kernel x y)
    (f : FiniteBoundaryHilbert α) :
    0 ≤ inner ℝ
      (finiteKernelNormalizedOperator
        (finiteGroupRightAveragedKernel G α K.kernel) f) f := by
  unfold finiteKernelNormalizedOperator
  rw [ContinuousLinearMap.smul_apply, real_inner_smul_left]
  exact mul_nonneg
    (inv_nonneg.mpr (norm_nonneg _))
    (finiteKernelOperator_rightAveraged_quadratic_nonneg
      G α K hinv f)

/-- Op-norm normalization preserves symmetry of any symmetric finite kernel. -/
theorem finiteKernelNormalizedOperator_isSymmetric_of_kernel_symmetric
    {α : Type} [Fintype α]
    (kernel : α → α → ℝ)
    (hsymm : ∀ x y : α, kernel x y = kernel y x) :
    (finiteKernelNormalizedOperator kernel).toLinearMap.IsSymmetric := by
  intro f h
  unfold finiteKernelNormalizedOperator
  change
    inner ℝ
        (‖finiteKernelOperator kernel‖⁻¹ • finiteKernelOperator kernel f) h =
      inner ℝ f
        (‖finiteKernelOperator kernel‖⁻¹ • finiteKernelOperator kernel h)
  rw [real_inner_smul_left, real_inner_smul_right]
  congr 1
  exact finiteKernelOperator_isSymmetric kernel hsymm f h

/-- The normalized averaged transfer also lands in the invariant subspace. -/
theorem finiteKernelNormalizedOperator_rightAveraged_mem_invariant
    (G α : Type) [Group G] [Fintype G] [Fintype α] [MulAction G α]
    (kernel : α → α → ℝ)
    (f : FiniteBoundaryHilbert α) :
    finiteKernelNormalizedOperator
        (finiteGroupRightAveragedKernel G α kernel) f ∈
      finiteGroupInvariantSubmodule G α := by
  intro g x
  unfold finiteKernelNormalizedOperator
  rw [ContinuousLinearMap.smul_apply]
  change
    ‖finiteKernelOperator (finiteGroupRightAveragedKernel G α kernel)‖⁻¹ *
        finiteKernelOperator
          (finiteGroupRightAveragedKernel G α kernel) f (g • x) =
      ‖finiteKernelOperator (finiteGroupRightAveragedKernel G α kernel)‖⁻¹ *
        finiteKernelOperator
          (finiteGroupRightAveragedKernel G α kernel) f x
  congr 1
  exact finiteKernelOperator_rightAveraged_mem_invariant
    G α kernel f g x

end

end MathlibAnalytic
end MGAP4D
