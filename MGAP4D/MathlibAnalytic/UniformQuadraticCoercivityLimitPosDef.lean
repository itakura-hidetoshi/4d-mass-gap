import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Filter Matrix

noncomputable section

universe u v

/-- A nonzero real coefficient vector on a finite index type has strictly
positive Euclidean square energy. -/
theorem finset_sum_sq_pos_of_ne_zero
    {ι : Type u} [Fintype ι]
    (x : ι → ℝ) (hx : x ≠ 0) :
    0 < ∑ i, x i ^ 2 := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra h
    apply hx
    funext i
    exact not_ne_iff.mp ((not_exists.mp h) i)
  rw [Finset.sum_pos_iff_of_nonneg]
  · exact ⟨i, Finset.mem_univ i, sq_pos_of_ne_zero hi⟩
  · intro i _
    exact sq_nonneg (x i)

/-- A strictly positive lower bound which is uniform along a convergent real
sequence survives in the limit. -/
theorem positive_limit_of_uniform_positive_lower_bound
    {u : ℕ → ℝ} {a δ : ℝ}
    (hu : Tendsto u atTop (nhds a))
    (hδ : 0 < δ)
    (hlower : ∀ n, δ ≤ u n) :
    0 < a := by
  exact hδ.trans_le (ge_of_tendsto' hu hlower)

/-- The matrix obtained by evaluating a symmetric real bilinear form on a
finite family is Hermitian. -/
theorem bilinForm_matrix_isHermitian_of_isSymm
    {V : Type v} [AddCommGroup V] [Module ℝ V]
    {ι : Type u}
    (B : LinearMap.BilinForm ℝ V)
    (hB : B.IsSymm)
    (w : ι → V) :
    Matrix.IsHermitian
      ((fun i j => B (w i) (w j)) : Matrix ι ι ℝ) := by
  apply Matrix.IsHermitian.ext
  intro i j
  simpa using hB.eq (w j) (w i)

/-- The matrix quadratic form of a real bilinear Gram matrix is the bilinear
form evaluated on the corresponding finite linear combination. -/
theorem bilinForm_matrix_quadratic_eq
    {V : Type v} [AddCommGroup V] [Module ℝ V]
    {ι : Type u} [Fintype ι]
    (B : LinearMap.BilinForm ℝ V)
    (w : ι → V)
    (x : ι → ℝ) :
    star x ⬝ᵥ
        (((fun i j => B (w i) (w j)) : Matrix ι ι ℝ) *ᵥ x) =
      B (∑ i, x i • w i) (∑ i, x i • w i) := by
  classical
  let l : (ι → ℝ) →ₗ[ℝ] V := Fintype.linearCombination ℝ w
  have hMatrix :
      ((fun i j => B (w i) (w j)) : Matrix ι ι ℝ) =
        LinearMap.BilinForm.toMatrix' (B.comp l l) := by
    ext i j
    simp [l]
  rw [hMatrix]
  calc
    star x ⬝ᵥ (LinearMap.BilinForm.toMatrix' (B.comp l l) *ᵥ x) =
        x ⬝ᵥ (LinearMap.BilinForm.toMatrix' (B.comp l l) *ᵥ x) := by simp
    _ = Matrix.toBilin' (LinearMap.BilinForm.toMatrix' (B.comp l l)) x x :=
      (Matrix.toBilin'_apply'
        (LinearMap.BilinForm.toMatrix' (B.comp l l)) x x).symm
    _ = B (∑ i, x i • w i) (∑ i, x i • w i) := by
      simp [l, Fintype.linearCombination_apply]

/-- Quadratic-form convergence preserves finite-dimensional strict positivity
when the approximating matrices have a volume-uniform Euclidean coercivity
constant.

Only convergence of the scalar quadratic values is required; no entrywise
matrix convergence is assumed. The coercivity constant may therefore be
chosen separately for each finite family before this theorem is applied. -/
theorem matrix_posDef_of_uniform_quadratic_coercivity_tendsto
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (A : ℕ → Matrix ι ι ℝ)
    (A_limit : Matrix ι ι ℝ)
    (hHermitian : Matrix.IsHermitian A_limit)
    (δ : ℝ) (hδ : 0 < δ)
    (hTendsto : ∀ x : ι → ℝ,
      Tendsto
        (fun n : ℕ => star x ⬝ᵥ (A n *ᵥ x))
        atTop
        (nhds (star x ⬝ᵥ (A_limit *ᵥ x))))
    (hCoercive : ∀ n (x : ι → ℝ),
      δ * (∑ i, x i ^ 2) ≤ star x ⬝ᵥ (A n *ᵥ x)) :
    A_limit.PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos hHermitian
  intro x hx
  have henergy : 0 < δ * (∑ i, x i ^ 2) :=
    mul_pos hδ (finset_sum_sq_pos_of_ne_zero x hx)
  exact positive_limit_of_uniform_positive_lower_bound
    (hTendsto x) henergy (fun n => hCoercive n x)

end

end MathlibAnalytic
end MGAP4D
