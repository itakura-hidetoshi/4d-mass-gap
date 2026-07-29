import MGAP4D.MathlibAnalytic.OrthonormalComplexDiagonalOperatorInverse

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open scoped ComplexOrder

/-- Subtraction of two operators diagonal in the same complex orthonormal basis
is coefficientwise subtraction. -/
theorem orthonormalComplexDiagonalOperator_sub
    {ι E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E]
    (b : OrthonormalBasis ι ℂ E)
    (c a : ι → ℝ) :
    orthonormalComplexDiagonalOperator b c -
        orthonormalComplexDiagonalOperator b a =
      orthonormalComplexDiagonalOperator b (fun i => c i - a i) := by
  apply ContinuousLinearMap.ext
  intro x
  rw [← b.sum_repr' x]
  rw [ContinuousLinearMap.sub_apply]
  simp only [map_sum, map_smul,
    orthonormalComplexDiagonalOperator_apply_basis]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  module

/-- Coefficientwise order implies Loewner order for complex diagonal operators. -/
theorem orthonormalComplexDiagonalOperator_le
    {ι E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E]
    (b : OrthonormalBasis ι ℂ E)
    (a c : ι → ℝ)
    (h : ∀ i : ι, a i ≤ c i) :
    orthonormalComplexDiagonalOperator b a ≤
      orthonormalComplexDiagonalOperator b c := by
  rw [ContinuousLinearMap.le_def,
    orthonormalComplexDiagonalOperator_sub b c a]
  exact orthonormalComplexDiagonalOperator_isPositive b
    (fun i => c i - a i) (fun i => sub_nonneg.mpr (h i))

/-- A constant real diagonal coefficient is the corresponding real scalar
multiple of the identity operator. -/
theorem orthonormalComplexDiagonalOperator_const_eq_algebraMap
    {ι E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E]
    (b : OrthonormalBasis ι ℂ E)
    (r : ℝ) :
    orthonormalComplexDiagonalOperator b (fun _ => r) =
      algebraMap ℝ (E →L[ℂ] E) r := by
  rw [Algebra.algebraMap_eq_smul_one]
  apply ContinuousLinearMap.ext
  intro x
  change orthonormalComplexDiagonalOperator b (fun _ => r) x =
    (r : ℂ) • x
  rw [← b.sum_repr' x]
  simp only [map_sum, map_smul,
    orthonormalComplexDiagonalOperator_apply_basis, smul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  module

end

end MathlibAnalytic
end MGAP4D
