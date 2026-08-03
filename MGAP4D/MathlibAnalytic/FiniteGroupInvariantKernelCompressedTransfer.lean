import MGAP4D.MathlibAnalytic.FiniteGroupEuclideanGaugeAveragingProjector
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators InnerProduct

noncomputable section

/-- A simultaneously invariant finite kernel sends invariant vectors to
invariant vectors. -/
theorem finiteKernelOperator_maps_groupInvariant
    (G α : Type) [Group G] [Fintype G] [Fintype α] [MulAction G α]
    (kernel : α → α → ℝ)
    (hinv : ∀ g : G, ∀ x y : α,
      kernel (g • x) (g • y) = kernel x y)
    (f : finiteGroupInvariantSubmodule G α) :
    finiteKernelOperator kernel f.1 ∈
      finiteGroupInvariantSubmodule G α := by
  classical
  intro g y
  rw [finiteKernelOperator_apply, finiteKernelOperator_apply]
  refine Fintype.sum_equiv (finiteMulActionEquiv G α g) _ _ ?_
  intro x
  simp only [finiteMulActionEquiv]
  rw [hinv g x y, f.2 g x]

/-- Raw finite kernel transfer commutes with the finite gauge-averaging
projector whenever the kernel is diagonally invariant. -/
theorem finiteKernelOperator_commutes_groupAveraging
    (G α : Type) [Group G] [Fintype G] [Fintype α] [MulAction G α]
    (kernel : α → α → ℝ)
    (hinv : ∀ g : G, ∀ x y : α,
      kernel (g • x) (g • y) = kernel x y) :
    (finiteKernelOperator kernel).comp
        (finiteGroupAveragingProjector G α) =
      (finiteGroupAveragingProjector G α).comp
        (finiteKernelOperator kernel) := by
  classical
  ext f y
  change
    (∑ x : α, kernel x y *
      ((Fintype.card G : ℝ)⁻¹ * ∑ g : G, f (g • x))) =
      (Fintype.card G : ℝ)⁻¹ *
        ∑ g : G, ∑ x : α, kernel x (g • y) * f x
  calc
    (∑ x : α, kernel x y *
      ((Fintype.card G : ℝ)⁻¹ * ∑ g : G, f (g • x))) =
        ∑ x : α, ∑ g : G,
          (Fintype.card G : ℝ)⁻¹ *
            (kernel x y * f (g • x)) := by
      apply Finset.sum_congr rfl
      intro x _hx
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro g _hg
      ring
    _ = ∑ g : G, ∑ x : α,
          (Fintype.card G : ℝ)⁻¹ *
            (kernel x y * f (g • x)) := by
      rw [Finset.sum_comm]
    _ = ∑ g : G,
          (Fintype.card G : ℝ)⁻¹ *
            (∑ x : α, kernel x y * f (g • x)) := by
      apply Finset.sum_congr rfl
      intro g _hg
      rw [Finset.mul_sum]
    _ = ∑ g : G,
          (Fintype.card G : ℝ)⁻¹ *
            (∑ x : α, kernel x (g • y) * f x) := by
      apply Finset.sum_congr rfl
      intro g _hg
      congr 1
      refine Fintype.sum_equiv (finiteMulActionEquiv G α g⁻¹) _ _ ?_
      intro x
      simp only [finiteMulActionEquiv]
      have h := hinv g (g⁻¹ • x) y
      simp at h
      rw [← h]
      simp
    _ = (Fintype.card G : ℝ)⁻¹ *
        ∑ g : G, ∑ x : α, kernel x (g • y) * f x := by
      rw [Finset.mul_sum]

/-- Op-norm normalization preserves commutation with gauge averaging. -/
theorem finiteKernelNormalizedOperator_commutes_groupAveraging
    (G α : Type) [Group G] [Fintype G] [Fintype α] [MulAction G α]
    (kernel : α → α → ℝ)
    (hinv : ∀ g : G, ∀ x y : α,
      kernel (g • x) (g • y) = kernel x y) :
    (finiteKernelNormalizedOperator kernel).comp
        (finiteGroupAveragingProjector G α) =
      (finiteGroupAveragingProjector G α).comp
        (finiteKernelNormalizedOperator kernel) := by
  ext f
  change
    ‖finiteKernelOperator kernel‖⁻¹ •
        finiteKernelOperator kernel
          (finiteGroupAveragingProjector G α f) =
      finiteGroupAveragingProjector G α
        (‖finiteKernelOperator kernel‖⁻¹ •
          finiteKernelOperator kernel f)
  rw [ContinuousLinearMap.map_smul]
  congr 1
  have hcomm :=
    finiteKernelOperator_commutes_groupAveraging G α kernel hinv
  exact ContinuousLinearMap.congr_fun hcomm f

/-- The normalized invariant kernel transfer preserves the invariant
subspace. -/
theorem finiteKernelNormalizedOperator_maps_groupInvariant
    (G α : Type) [Group G] [Fintype G] [Fintype α] [MulAction G α]
    (kernel : α → α → ℝ)
    (hinv : ∀ g : G, ∀ x y : α,
      kernel (g • x) (g • y) = kernel x y)
    (f : finiteGroupInvariantSubmodule G α) :
    finiteKernelNormalizedOperator kernel f.1 ∈
      finiteGroupInvariantSubmodule G α := by
  intro g x
  unfold finiteKernelNormalizedOperator
  rw [ContinuousLinearMap.smul_apply]
  change
    ‖finiteKernelOperator kernel‖⁻¹ *
        finiteKernelOperator kernel f.1 (g • x) =
      ‖finiteKernelOperator kernel‖⁻¹ *
        finiteKernelOperator kernel f.1 x
  congr 1
  exact finiteKernelOperator_maps_groupInvariant
    G α kernel hinv f g x

/-- Compression of the normalized transfer to the finite gauge-invariant
boundary Hilbert subspace. -/
noncomputable def finiteGroupInvariantCompressedNormalizedTransfer
    (G α : Type) [Group G] [Fintype G] [Fintype α] [MulAction G α]
    (kernel : α → α → ℝ)
    (hinv : ∀ g : G, ∀ x y : α,
      kernel (g • x) (g • y) = kernel x y) :
    finiteGroupInvariantSubmodule G α →L[ℝ]
      finiteGroupInvariantSubmodule G α :=
  LinearMap.toContinuousLinearMap
    { toFun := fun f =>
        ⟨finiteKernelNormalizedOperator kernel f.1,
          finiteKernelNormalizedOperator_maps_groupInvariant
            G α kernel hinv f⟩
      map_add' := by
        intro f h
        apply Subtype.ext
        simp
      map_smul' := by
        intro c f
        apply Subtype.ext
        simp }

@[simp] theorem finiteGroupInvariantCompressedNormalizedTransfer_apply_coe
    (G α : Type) [Group G] [Fintype G] [Fintype α] [MulAction G α]
    (kernel : α → α → ℝ)
    (hinv : ∀ g : G, ∀ x y : α,
      kernel (g • x) (g • y) = kernel x y)
    (f : finiteGroupInvariantSubmodule G α) :
    (finiteGroupInvariantCompressedNormalizedTransfer
      G α kernel hinv f).1 =
      finiteKernelNormalizedOperator kernel f.1 :=
  rfl

/-- Symmetry descends to the compressed invariant transfer. -/
theorem finiteGroupInvariantCompressedNormalizedTransfer_isSymmetric
    (G α : Type) [Group G] [Fintype G] [Fintype α] [MulAction G α]
    (K : FiniteOSGramKernelOn α)
    (hinv : ∀ g : G, ∀ x y : α,
      K.kernel (g • x) (g • y) = K.kernel x y) :
    (finiteGroupInvariantCompressedNormalizedTransfer
      G α K.kernel hinv).toLinearMap.IsSymmetric := by
  intro f h
  exact finiteGramKernelNormalizedOperator_isSymmetric K f.1 h.1

/-- Positivity descends to the compressed invariant transfer. -/
theorem finiteGroupInvariantCompressedNormalizedTransfer_quadratic_nonneg
    (G α : Type) [Group G] [Fintype G] [Fintype α] [MulAction G α]
    (K : FiniteOSGramKernelOn α)
    (hinv : ∀ g : G, ∀ x y : α,
      K.kernel (g • x) (g • y) = K.kernel x y)
    (f : finiteGroupInvariantSubmodule G α) :
    0 ≤ inner ℝ
      (finiteGroupInvariantCompressedNormalizedTransfer
        G α K.kernel hinv f) f :=
  finiteGramKernelNormalizedOperator_quadratic_nonneg K f.1

/-- Ambient contractivity descends to the gauge-invariant subspace. -/
theorem finiteGroupInvariantCompressedNormalizedTransfer_norm_apply_le
    (G α : Type) [Group G] [Fintype G] [Fintype α] [MulAction G α]
    (kernel : α → α → ℝ)
    (hinv : ∀ g : G, ∀ x y : α,
      kernel (g • x) (g • y) = kernel x y)
    (hne : finiteKernelOperator kernel ≠ 0)
    (f : finiteGroupInvariantSubmodule G α) :
    ‖finiteGroupInvariantCompressedNormalizedTransfer
      G α kernel hinv f‖ ≤ ‖f‖ :=
  finiteKernelNormalizedOperator_norm_apply_le kernel hne f.1

/-- Natural powers of the Gauss-compressed transfer. -/
noncomputable def finiteGroupInvariantCompressedTransferSemigroup
    (G α : Type) [Group G] [Fintype G] [Fintype α] [MulAction G α]
    (kernel : α → α → ℝ)
    (hinv : ∀ g : G, ∀ x y : α,
      kernel (g • x) (g • y) = kernel x y)
    (n : ℕ) :
    finiteGroupInvariantSubmodule G α →L[ℝ]
      finiteGroupInvariantSubmodule G α :=
  (finiteGroupInvariantCompressedNormalizedTransfer
    G α kernel hinv) ^ n

/-- Additive natural time remains operator composition after compression. -/
theorem finiteGroupInvariantCompressedTransferSemigroup_add
    (G α : Type) [Group G] [Fintype G] [Fintype α] [MulAction G α]
    (kernel : α → α → ℝ)
    (hinv : ∀ g : G, ∀ x y : α,
      kernel (g • x) (g • y) = kernel x y)
    (m n : ℕ) :
    finiteGroupInvariantCompressedTransferSemigroup
        G α kernel hinv (m + n) =
      (finiteGroupInvariantCompressedTransferSemigroup
        G α kernel hinv m).comp
      (finiteGroupInvariantCompressedTransferSemigroup
        G α kernel hinv n) := by
  unfold finiteGroupInvariantCompressedTransferSemigroup
  rw [pow_add]
  rfl

/-- Every compressed natural-time power is contractive. -/
theorem finiteGroupInvariantCompressedTransferSemigroup_norm_apply_le
    (G α : Type) [Group G] [Fintype G] [Fintype α] [MulAction G α]
    (kernel : α → α → ℝ)
    (hinv : ∀ g : G, ∀ x y : α,
      kernel (g • x) (g • y) = kernel x y)
    (hne : finiteKernelOperator kernel ≠ 0)
    (n : ℕ)
    (f : finiteGroupInvariantSubmodule G α) :
    ‖finiteGroupInvariantCompressedTransferSemigroup
      G α kernel hinv n f‖ ≤ ‖f‖ := by
  induction n with
  | zero =>
      simp [finiteGroupInvariantCompressedTransferSemigroup]
  | succ n ih =>
      change
        ‖((finiteGroupInvariantCompressedNormalizedTransfer
          G α kernel hinv) ^ (n + 1)) f‖ ≤ ‖f‖
      rw [pow_succ']
      exact
        (finiteGroupInvariantCompressedNormalizedTransfer_norm_apply_le
          G α kernel hinv hne
          (((finiteGroupInvariantCompressedNormalizedTransfer
            G α kernel hinv) ^ n) f)).trans ih

end

end MathlibAnalytic
end MGAP4D
