import MGAP4D.MathlibAnalytic.OrthonormalDiagonalOperator
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Multiplication of two operators diagonal in the same orthonormal basis is
coefficientwise multiplication. -/
theorem orthonormalDiagonalOperator_mul
    {ι E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E)
    (a c : ι → ℝ) :
    orthonormalDiagonalOperator b a * orthonormalDiagonalOperator b c =
      orthonormalDiagonalOperator b (fun i => a i * c i) := by
  apply ContinuousLinearMap.ext
  intro x
  change orthonormalDiagonalOperator b a
      (orthonormalDiagonalOperator b c x) =
    orthonormalDiagonalOperator b (fun i => a i * c i) x
  rw [orthonormalDiagonalOperator_apply b c x]
  simp only [map_sum, map_smul, orthonormalDiagonalOperator_apply_basis]
  rw [orthonormalDiagonalOperator_apply]
  apply Finset.sum_congr rfl
  intro i hi
  simp [smul_smul, mul_comm, mul_left_comm, mul_assoc]

/-- The diagonal operator with constant coefficient one is the identity. -/
theorem orthonormalDiagonalOperator_one
    {ι E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) :
    orthonormalDiagonalOperator b (fun _ => 1) = 1 := by
  apply ContinuousLinearMap.ext
  intro x
  change orthonormalDiagonalOperator b (fun _ => 1) x = x
  rw [orthonormalDiagonalOperator_apply]
  simpa using b.sum_repr' x

/-- A diagonal operator with nonzero coefficients has the coefficientwise
reciprocal as a right inverse. -/
theorem orthonormalDiagonalOperator_mul_inv
    {ι E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E)
    (a : ι → ℝ)
    (ha : ∀ i : ι, a i ≠ 0) :
    orthonormalDiagonalOperator b a *
        orthonormalDiagonalOperator b (fun i => (a i)⁻¹) = 1 := by
  rw [orthonormalDiagonalOperator_mul]
  have hcoeff : (fun i => a i * (a i)⁻¹) = fun _ => 1 := by
    funext i
    exact mul_inv_cancel₀ (ha i)
  rw [hcoeff, orthonormalDiagonalOperator_one]

/-- A diagonal operator with nonzero coefficients has the coefficientwise
reciprocal as a left inverse. -/
theorem orthonormalDiagonalOperator_inv_mul
    {ι E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E)
    (a : ι → ℝ)
    (ha : ∀ i : ι, a i ≠ 0) :
    orthonormalDiagonalOperator b (fun i => (a i)⁻¹) *
        orthonormalDiagonalOperator b a = 1 := by
  rw [orthonormalDiagonalOperator_mul]
  have hcoeff : (fun i => (a i)⁻¹ * a i) = fun _ => 1 := by
    funext i
    exact inv_mul_cancel₀ (ha i)
  rw [hcoeff, orthonormalDiagonalOperator_one]

/-- The unit in the continuous-endomorphism ring represented by a diagonal
operator with nonzero coefficients. -/
noncomputable def orthonormalDiagonalOperatorUnit
    {ι E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E)
    (a : ι → ℝ)
    (ha : ∀ i : ι, a i ≠ 0) :
    (E →L[ℝ] E)ˣ where
  val := orthonormalDiagonalOperator b a
  inv := orthonormalDiagonalOperator b (fun i => (a i)⁻¹)
  val_inv := orthonormalDiagonalOperator_mul_inv b a ha
  inv_val := orthonormalDiagonalOperator_inv_mul b a ha

/-- A diagonal operator with nonzero coefficients is invertible. -/
theorem orthonormalDiagonalOperator_isUnit
    {ι E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E)
    (a : ι → ℝ)
    (ha : ∀ i : ι, a i ≠ 0) :
    IsUnit (orthonormalDiagonalOperator b a) :=
  (orthonormalDiagonalOperatorUnit b a ha).isUnit

end

end MathlibAnalytic
end MGAP4D
