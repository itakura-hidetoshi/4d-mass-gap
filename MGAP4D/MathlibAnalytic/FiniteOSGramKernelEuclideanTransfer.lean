import MGAP4D.MathlibAnalytic.FiniteOSGramKernelProductClosure
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators InnerProduct

noncomputable section

/-- Standard finite-dimensional real boundary Hilbert space attached to a
finite configuration carrier. -/
abbrev FiniteBoundaryHilbert (α : Type) [Fintype α] : Type :=
  EuclideanSpace ℝ α

/-- The raw integral operator represented by a finite scalar kernel.  The
orientation is chosen so that its Hilbert matrix element is exactly
`∑ x,y, f x * K x y * g y`. -/
noncomputable def finiteKernelLinearMap
    {α : Type} [Fintype α]
    (kernel : α → α → ℝ) :
    FiniteBoundaryHilbert α →ₗ[ℝ] FiniteBoundaryHilbert α where
  toFun f := WithLp.toLp 2 fun y : α =>
    ∑ x : α, kernel x y * f x
  map_add' f g := by
    ext y
    change (∑ x : α, kernel x y * (f x + g x)) =
      (∑ x : α, kernel x y * f x) +
        ∑ x : α, kernel x y * g x
    simp_rw [mul_add]
    exact Finset.sum_add_distrib
  map_smul' c f := by
    ext y
    change (∑ x : α, kernel x y * (c * f x)) =
      c * ∑ x : α, kernel x y * f x
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _hx
    ring

/-- Every finite kernel linear map is automatically continuous. -/
noncomputable def finiteKernelOperator
    {α : Type} [Fintype α]
    (kernel : α → α → ℝ) :
    FiniteBoundaryHilbert α →L[ℝ] FiniteBoundaryHilbert α :=
  LinearMap.toContinuousLinearMap (finiteKernelLinearMap kernel)

@[simp] theorem finiteKernelOperator_apply
    {α : Type} [Fintype α]
    (kernel : α → α → ℝ)
    (f : FiniteBoundaryHilbert α) (y : α) :
    finiteKernelOperator kernel f y =
      ∑ x : α, kernel x y * f x :=
  rfl

/-- Exact dense-free finite matrix element formula for the kernel operator. -/
theorem finiteKernelOperator_matrixElement
    {α : Type} [Fintype α]
    (kernel : α → α → ℝ)
    (f g : FiniteBoundaryHilbert α) :
    inner ℝ (finiteKernelOperator kernel f) g =
      ∑ x : α, ∑ y : α, f x * kernel x y * g y := by
  classical
  rw [PiLp.inner_apply]
  calc
    (∑ y : α, inner ℝ (finiteKernelOperator kernel f y) (g y)) =
        ∑ y : α, g y * (∑ x : α, kernel x y * f x) := by
      apply Finset.sum_congr rfl
      intro y _hy
      change g y * finiteKernelOperator kernel f y = _
      rw [finiteKernelOperator_apply]
    _ = ∑ y : α, ∑ x : α, f x * kernel x y * g y := by
      apply Finset.sum_congr rfl
      intro y _hy
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _hx
      ring
    _ = ∑ x : α, ∑ y : α, f x * kernel x y * g y := by
      rw [Finset.sum_comm]

/-- A symmetric finite kernel gives a symmetric Euclidean transfer operator. -/
theorem finiteKernelOperator_isSymmetric
    {α : Type} [Fintype α]
    (kernel : α → α → ℝ)
    (hsymm : ∀ x y, kernel x y = kernel y x) :
    (finiteKernelOperator kernel).toLinearMap.IsSymmetric := by
  intro f g
  rw [finiteKernelOperator_matrixElement,
    finiteKernelOperator_matrixElement]
  calc
    (∑ x : α, ∑ y : α, f x * kernel x y * g y) =
        ∑ y : α, ∑ x : α, f x * kernel x y * g y := by
      rw [Finset.sum_comm]
    _ = ∑ y : α, ∑ x : α, g y * kernel y x * f x := by
      apply Finset.sum_congr rfl
      intro y _hy
      apply Finset.sum_congr rfl
      intro x _hx
      rw [hsymm]
      ring

/-- A finite nonnegative Gram kernel gives a positive Euclidean transfer
operator. -/
theorem finiteGramKernelOperator_quadratic_nonneg
    {α : Type} [Fintype α]
    (K : FiniteOSGramKernelOn α)
    (f : FiniteBoundaryHilbert α) :
    0 ≤ inner ℝ (finiteKernelOperator K.kernel f) f := by
  rw [finiteKernelOperator_matrixElement]
  simp_rw [K.kernel_decomposition]
  rw [finite_gram_quadratic_identity]
  exact Finset.sum_nonneg fun k _hk =>
    mul_nonneg (K.coefficient_nonneg k) (sq_nonneg _)

/-- A Gram kernel operator is symmetric. -/
theorem finiteGramKernelOperator_isSymmetric
    {α : Type} [Fintype α]
    (K : FiniteOSGramKernelOn α) :
    (finiteKernelOperator K.kernel).toLinearMap.IsSymmetric :=
  finiteKernelOperator_isSymmetric K.kernel fun x y =>
    finite_os_reflection_kernel_symmetric K.toCertificate x y

/-- Point mass at a finite boundary configuration. -/
noncomputable def finiteBoundaryPointVector
    {α : Type} [Fintype α] [DecidableEq α]
    (x : α) : FiniteBoundaryHilbert α :=
  WithLp.toLp 2 fun z : α => if z = x then 1 else 0

@[simp] theorem finiteBoundaryPointVector_apply
    {α : Type} [Fintype α] [DecidableEq α]
    (x z : α) :
    finiteBoundaryPointVector x z = if z = x then 1 else 0 :=
  rfl

/-- Point vectors recover individual kernel entries. -/
theorem finiteKernelOperator_point_matrixElement
    {α : Type} [Fintype α] [DecidableEq α]
    (kernel : α → α → ℝ)
    (x y : α) :
    inner ℝ
        (finiteKernelOperator kernel (finiteBoundaryPointVector x))
        (finiteBoundaryPointVector y) =
      kernel x y := by
  classical
  rw [finiteKernelOperator_matrixElement]
  simp [finiteBoundaryPointVector]

/-- A nonzero diagonal entry forces the raw kernel operator to be nonzero. -/
theorem finiteKernelOperator_ne_zero_of_diagonal_ne_zero
    {α : Type} [Fintype α] [DecidableEq α]
    (kernel : α → α → ℝ)
    (x : α)
    (hxx : kernel x x ≠ 0) :
    finiteKernelOperator kernel ≠ 0 := by
  intro hzero
  have hmatrix := finiteKernelOperator_point_matrixElement kernel x x
  rw [hzero] at hmatrix
  simp at hmatrix
  exact hxx hmatrix.symm

/-- Canonical nontrivial normalization of a finite kernel operator by its
operator norm. -/
noncomputable def finiteKernelNormalizedOperator
    {α : Type} [Fintype α]
    (kernel : α → α → ℝ) :
    FiniteBoundaryHilbert α →L[ℝ] FiniteBoundaryHilbert α :=
  ‖finiteKernelOperator kernel‖⁻¹ • finiteKernelOperator kernel

/-- A nonzero raw kernel operator has normalized operator norm exactly one. -/
theorem finiteKernelNormalizedOperator_norm_eq_one
    {α : Type} [Fintype α]
    (kernel : α → α → ℝ)
    (hne : finiteKernelOperator kernel ≠ 0) :
    ‖finiteKernelNormalizedOperator kernel‖ = 1 := by
  unfold finiteKernelNormalizedOperator
  rw [norm_smul]
  have hnorm : ‖finiteKernelOperator kernel‖ ≠ 0 := by
    exact norm_ne_zero_iff.mpr hne
  rw [Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg _)]
  exact inv_mul_cancel₀ hnorm

/-- The op-norm normalized transfer is a contraction on every boundary state. -/
theorem finiteKernelNormalizedOperator_norm_apply_le
    {α : Type} [Fintype α]
    (kernel : α → α → ℝ)
    (hne : finiteKernelOperator kernel ≠ 0)
    (f : FiniteBoundaryHilbert α) :
    ‖finiteKernelNormalizedOperator kernel f‖ ≤ ‖f‖ := by
  calc
    ‖finiteKernelNormalizedOperator kernel f‖ ≤
        ‖finiteKernelNormalizedOperator kernel‖ * ‖f‖ :=
      (finiteKernelNormalizedOperator kernel).le_opNorm f
    _ = ‖f‖ := by
      rw [finiteKernelNormalizedOperator_norm_eq_one kernel hne, one_mul]

/-- Matrix elements of the normalized transfer are the correspondingly
normalized kernel form. -/
theorem finiteKernelNormalizedOperator_matrixElement
    {α : Type} [Fintype α]
    (kernel : α → α → ℝ)
    (f g : FiniteBoundaryHilbert α) :
    inner ℝ (finiteKernelNormalizedOperator kernel f) g =
      ‖finiteKernelOperator kernel‖⁻¹ *
        (∑ x : α, ∑ y : α, f x * kernel x y * g y) := by
  unfold finiteKernelNormalizedOperator
  rw [ContinuousLinearMap.smul_apply, real_inner_smul_left,
    finiteKernelOperator_matrixElement]

/-- Symmetry survives nonnegative operator-norm normalization. -/
theorem finiteGramKernelNormalizedOperator_isSymmetric
    {α : Type} [Fintype α]
    (K : FiniteOSGramKernelOn α) :
    (finiteKernelNormalizedOperator K.kernel).toLinearMap.IsSymmetric := by
  intro f g
  rw [finiteKernelNormalizedOperator_matrixElement,
    finiteKernelNormalizedOperator_matrixElement]
  congr 1
  exact K.toCertificate |> finite_os_reflection_kernel_symmetric |> fun h => by
    calc
      (∑ x : α, ∑ y : α, f x * K.kernel x y * g y) =
          ∑ y : α, ∑ x : α, f x * K.kernel x y * g y := by
        rw [Finset.sum_comm]
      _ = ∑ y : α, ∑ x : α, g y * K.kernel y x * f x := by
        apply Finset.sum_congr rfl
        intro y _hy
        apply Finset.sum_congr rfl
        intro x _hx
        rw [h x y]
        ring

/-- Positivity survives operator-norm normalization. -/
theorem finiteGramKernelNormalizedOperator_quadratic_nonneg
    {α : Type} [Fintype α]
    (K : FiniteOSGramKernelOn α)
    (f : FiniteBoundaryHilbert α) :
    0 ≤ inner ℝ (finiteKernelNormalizedOperator K.kernel f) f := by
  rw [finiteKernelNormalizedOperator_matrixElement]
  apply mul_nonneg
  · exact inv_nonneg.mpr (norm_nonneg _)
  · have hraw := finiteGramKernelOperator_quadratic_nonneg K f
    rwa [finiteKernelOperator_matrixElement] at hraw

/-- Natural powers of the normalized transfer form a discrete semigroup. -/
noncomputable def finiteKernelNormalizedSemigroup
    {α : Type} [Fintype α]
    (kernel : α → α → ℝ)
    (n : ℕ) :
    FiniteBoundaryHilbert α →L[ℝ] FiniteBoundaryHilbert α :=
  (finiteKernelNormalizedOperator kernel) ^ n

@[simp] theorem finiteKernelNormalizedSemigroup_zero
    {α : Type} [Fintype α]
    (kernel : α → α → ℝ) :
    finiteKernelNormalizedSemigroup kernel 0 = 1 := by
  rfl

@[simp] theorem finiteKernelNormalizedSemigroup_one
    {α : Type} [Fintype α]
    (kernel : α → α → ℝ) :
    finiteKernelNormalizedSemigroup kernel 1 =
      finiteKernelNormalizedOperator kernel := by
  simp [finiteKernelNormalizedSemigroup]

/-- Additive natural time is operator composition. -/
theorem finiteKernelNormalizedSemigroup_add
    {α : Type} [Fintype α]
    (kernel : α → α → ℝ)
    (m n : ℕ) :
    finiteKernelNormalizedSemigroup kernel (m + n) =
      (finiteKernelNormalizedSemigroup kernel m).comp
        (finiteKernelNormalizedSemigroup kernel n) := by
  simp [finiteKernelNormalizedSemigroup, pow_add]

/-- Every natural-time normalized transfer is contractive. -/
theorem finiteKernelNormalizedSemigroup_norm_apply_le
    {α : Type} [Fintype α]
    (kernel : α → α → ℝ)
    (hne : finiteKernelOperator kernel ≠ 0)
    (n : ℕ)
    (f : FiniteBoundaryHilbert α) :
    ‖finiteKernelNormalizedSemigroup kernel n f‖ ≤ ‖f‖ := by
  have hop : ‖finiteKernelNormalizedOperator kernel‖ = 1 :=
    finiteKernelNormalizedOperator_norm_eq_one kernel hne
  calc
    ‖finiteKernelNormalizedSemigroup kernel n f‖ ≤
        ‖finiteKernelNormalizedSemigroup kernel n‖ * ‖f‖ :=
      (finiteKernelNormalizedSemigroup kernel n).le_opNorm f
    _ ≤ ‖f‖ := by
      have hpow : ‖finiteKernelNormalizedSemigroup kernel n‖ ≤ 1 := by
        unfold finiteKernelNormalizedSemigroup
        calc
          ‖finiteKernelNormalizedOperator kernel ^ n‖ ≤
              ‖finiteKernelNormalizedOperator kernel‖ ^ n := norm_pow_le _ _
          _ = 1 := by rw [hop, one_pow]
      simpa using mul_le_mul_of_nonneg_right hpow (norm_nonneg f)

/-- Public finite Gram-kernel Euclidean transfer package. -/
theorem finiteOSGramKernelEuclideanTransferPackage
    {α : Type} [Fintype α] [DecidableEq α]
    (K : FiniteOSGramKernelOn α)
    (x : α)
    (hxx : K.kernel x x ≠ 0) :
    (finiteKernelOperator K.kernel ≠ 0) ∧
    ((finiteKernelNormalizedOperator K.kernel).toLinearMap.IsSymmetric) ∧
    (∀ f : FiniteBoundaryHilbert α,
      0 ≤ inner ℝ (finiteKernelNormalizedOperator K.kernel f) f) ∧
    (∀ f : FiniteBoundaryHilbert α,
      ‖finiteKernelNormalizedOperator K.kernel f‖ ≤ ‖f‖) ∧
    (∀ m n : ℕ,
      finiteKernelNormalizedSemigroup K.kernel (m + n) =
        (finiteKernelNormalizedSemigroup K.kernel m).comp
          (finiteKernelNormalizedSemigroup K.kernel n)) := by
  have hne := finiteKernelOperator_ne_zero_of_diagonal_ne_zero
    K.kernel x hxx
  exact ⟨hne,
    finiteGramKernelNormalizedOperator_isSymmetric K,
    finiteGramKernelNormalizedOperator_quadratic_nonneg K,
    finiteKernelNormalizedOperator_norm_apply_le K.kernel hne,
    finiteKernelNormalizedSemigroup_add K.kernel⟩

end

end MathlibAnalytic
end MGAP4D
