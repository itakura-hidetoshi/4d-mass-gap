import MGAP4D.MathlibAnalytic.OrthonormalDiagonalOperator

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- A diagonal operator whose mode coefficients are bounded below by `δ`
satisfies the corresponding basis-free quadratic-form lower bound. -/
theorem orthonormalDiagonalOperator_quadratic_form_lower_bound
    {ι E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E)
    (a : ι → ℝ)
    (δ : ℝ)
    (hCoeff : ∀ i : ι, δ ≤ a i)
    (x : E) :
    δ * ‖x‖ ^ 2 ≤
      inner ℝ (orthonormalDiagonalOperator b a x) x := by
  rw [orthonormalDiagonalOperator_rayleigh]
  rw [← b.sum_sq_inner_right x, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  calc
    δ * inner ℝ (b i) x ^ 2 =
        inner ℝ (b i) x ^ 2 * δ := by ring
    _ ≤ inner ℝ (b i) x ^ 2 * a i :=
      mul_le_mul_of_nonneg_left (hCoeff i) (sq_nonneg _)

/-- The underlying linear map of a diagonally constructed finite-dimensional
operator is symmetric. -/
theorem orthonormalDiagonalLinearMap_isSymmetric
    {ι E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E)
    (a : ι → ℝ) :
    (orthonormalDiagonalOperator b a).toLinearMap.IsSymmetric :=
  orthonormalDiagonalOperator_isSymmetric b a

end

end MathlibAnalytic
end MGAP4D
