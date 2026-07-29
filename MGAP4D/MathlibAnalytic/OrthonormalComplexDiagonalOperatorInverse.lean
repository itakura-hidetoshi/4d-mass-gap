import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open InnerProductSpace
open scoped ComplexOrder

/-- The complex-linear operator diagonal in a finite complex orthonormal basis,
with real coefficient function `a`. -/
noncomputable def orthonormalComplexDiagonalLinearMap
    {ι E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℂ E]
    (b : OrthonormalBasis ι ℂ E)
    (a : ι → ℝ) : E →ₗ[ℂ] E :=
  b.toBasis.constr ℂ (fun i => (a i : ℂ) • b i)

/-- In finite dimension, the complex diagonal linear map is continuous. -/
noncomputable def orthonormalComplexDiagonalOperator
    {ι E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E]
    (b : OrthonormalBasis ι ℂ E)
    (a : ι → ℝ) : E →L[ℂ] E :=
  LinearMap.toContinuousLinearMap (orthonormalComplexDiagonalLinearMap b a)

/-- The complex diagonal operator has the prescribed real eigenvalue on every
orthonormal basis vector. -/
@[simp]
theorem orthonormalComplexDiagonalOperator_apply_basis
    {ι E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E]
    (b : OrthonormalBasis ι ℂ E)
    (a : ι → ℝ)
    (i : ι) :
    orthonormalComplexDiagonalOperator b a (b i) =
      (a i : ℂ) • b i := by
  change (b.toBasis.constr ℂ (fun j => (a j : ℂ) • b j)) (b i) =
    (a i : ℂ) • b i
  simpa using b.toBasis.constr_basis ℂ (fun j => (a j : ℂ) • b j) i

/-- Coordinate formula for the complex diagonal operator. -/
theorem orthonormalComplexDiagonalOperator_apply
    {ι E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E]
    (b : OrthonormalBasis ι ℂ E)
    (a : ι → ℝ)
    (x : E) :
    orthonormalComplexDiagonalOperator b a x =
      ∑ i : ι, inner ℂ (b i) x • ((a i : ℂ) • b i) := by
  conv_lhs => rw [← b.sum_repr' x]
  simp only [map_sum, map_smul, orthonormalComplexDiagonalOperator_apply_basis]

/-- Multiplication of two operators diagonal in the same complex orthonormal
basis is coefficientwise multiplication. -/
theorem orthonormalComplexDiagonalOperator_mul
    {ι E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E]
    (b : OrthonormalBasis ι ℂ E)
    (a c : ι → ℝ) :
    orthonormalComplexDiagonalOperator b a *
        orthonormalComplexDiagonalOperator b c =
      orthonormalComplexDiagonalOperator b (fun i => a i * c i) := by
  apply ContinuousLinearMap.ext
  intro x
  change orthonormalComplexDiagonalOperator b a
      (orthonormalComplexDiagonalOperator b c x) =
    orthonormalComplexDiagonalOperator b (fun i => a i * c i) x
  rw [orthonormalComplexDiagonalOperator_apply b c x]
  simp only [map_sum, map_smul, orthonormalComplexDiagonalOperator_apply_basis]
  rw [orthonormalComplexDiagonalOperator_apply]
  apply Finset.sum_congr rfl
  intro i hi
  simp [smul_smul, mul_comm, mul_assoc]

/-- The complex diagonal operator with constant coefficient one is the identity. -/
theorem orthonormalComplexDiagonalOperator_one
    {ι E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E]
    (b : OrthonormalBasis ι ℂ E) :
    orthonormalComplexDiagonalOperator b (fun _ => 1) = 1 := by
  apply ContinuousLinearMap.ext
  intro x
  change orthonormalComplexDiagonalOperator b (fun _ => 1) x = x
  rw [orthonormalComplexDiagonalOperator_apply]
  simpa using b.sum_repr' x

/-- A complex diagonal operator is the sum of its scaled rank-one basis
projections. -/
theorem orthonormalComplexDiagonalOperator_eq_sum_rankOne
    {ι E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E]
    (b : OrthonormalBasis ι ℂ E)
    (a : ι → ℝ) :
    orthonormalComplexDiagonalOperator b a =
      ∑ i : ι, (a i : ℂ) • rankOne ℂ (b i) (b i) := by
  apply ContinuousLinearMap.ext
  intro x
  rw [orthonormalComplexDiagonalOperator_apply]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    rankOne_apply]
  apply Finset.sum_congr rfl
  intro i hi
  simp [smul_smul, mul_comm, mul_assoc]

/-- Nonnegative real diagonal coefficients produce a positive complex operator. -/
theorem orthonormalComplexDiagonalOperator_isPositive
    {ι E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E]
    (b : OrthonormalBasis ι ℂ E)
    (a : ι → ℝ)
    (ha : ∀ i : ι, 0 ≤ a i) :
    (orthonormalComplexDiagonalOperator b a).IsPositive := by
  rw [orthonormalComplexDiagonalOperator_eq_sum_rankOne]
  apply ContinuousLinearMap.isPositive_sum
  intro i hi
  exact (InnerProductSpace.isPositive_rankOne_self (b i)).smul_of_nonneg (by
    exact_mod_cast ha i)

/-- A complex diagonal operator with nonzero real coefficients has the
coefficientwise reciprocal as a right inverse. -/
theorem orthonormalComplexDiagonalOperator_mul_inv
    {ι E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E]
    (b : OrthonormalBasis ι ℂ E)
    (a : ι → ℝ)
    (ha : ∀ i : ι, a i ≠ 0) :
    orthonormalComplexDiagonalOperator b a *
        orthonormalComplexDiagonalOperator b (fun i => (a i)⁻¹) = 1 := by
  rw [orthonormalComplexDiagonalOperator_mul]
  have hcoeff : (fun i => a i * (a i)⁻¹) = fun _ => 1 := by
    funext i
    exact mul_inv_cancel₀ (ha i)
  rw [hcoeff, orthonormalComplexDiagonalOperator_one]

/-- A complex diagonal operator with nonzero real coefficients has the
coefficientwise reciprocal as a left inverse. -/
theorem orthonormalComplexDiagonalOperator_inv_mul
    {ι E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E]
    (b : OrthonormalBasis ι ℂ E)
    (a : ι → ℝ)
    (ha : ∀ i : ι, a i ≠ 0) :
    orthonormalComplexDiagonalOperator b (fun i => (a i)⁻¹) *
        orthonormalComplexDiagonalOperator b a = 1 := by
  rw [orthonormalComplexDiagonalOperator_mul]
  have hcoeff : (fun i => (a i)⁻¹ * a i) = fun _ => 1 := by
    funext i
    exact inv_mul_cancel₀ (ha i)
  rw [hcoeff, orthonormalComplexDiagonalOperator_one]

/-- The unit represented by a complex diagonal operator with nonzero real
coefficients. -/
noncomputable def orthonormalComplexDiagonalOperatorUnit
    {ι E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E]
    (b : OrthonormalBasis ι ℂ E)
    (a : ι → ℝ)
    (ha : ∀ i : ι, a i ≠ 0) :
    (E →L[ℂ] E)ˣ where
  val := orthonormalComplexDiagonalOperator b a
  inv := orthonormalComplexDiagonalOperator b (fun i => (a i)⁻¹)
  val_inv := orthonormalComplexDiagonalOperator_mul_inv b a ha
  inv_val := orthonormalComplexDiagonalOperator_inv_mul b a ha

/-- A complex diagonal operator with nonzero real coefficients is invertible. -/
theorem orthonormalComplexDiagonalOperator_isUnit
    {ι E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E]
    (b : OrthonormalBasis ι ℂ E)
    (a : ι → ℝ)
    (ha : ∀ i : ι, a i ≠ 0) :
    IsUnit (orthonormalComplexDiagonalOperator b a) :=
  (orthonormalComplexDiagonalOperatorUnit b a ha).isUnit

end

end MathlibAnalytic
end MGAP4D
