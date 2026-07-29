import MGAP4D.MathlibAnalytic.ContinuousLinearOperatorExpEigenvector
import MGAP4D.MathlibAnalytic.OrthonormalComplexDiagonalOperatorInverse
import MGAP4D.MathlibAnalytic.ComplexStrictlyPositiveLogHamiltonian

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Exponentiating the negative of a finite complex orthonormal diagonal
operator exponentiates its real mode coefficients. -/
theorem normedSpace_exp_neg_orthonormalComplexDiagonalOperator
    {ι E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E]
    [CompleteSpace E]
    (b : OrthonormalBasis ι ℂ E)
    (a : ι → ℝ) :
    NormedSpace.exp (-orthonormalComplexDiagonalOperator b a) =
      orthonormalComplexDiagonalOperator b (fun i => Real.exp (-a i)) := by
  apply ContinuousLinearMap.ext
  intro x
  rw [← b.sum_repr' x]
  simp only [map_sum, map_smul,
    orthonormalComplexDiagonalOperator_apply_basis]
  apply Finset.sum_congr rfl
  intro i hi
  rw [normedSpace_exp_apply_of_complex_eigenvector
    (-orthonormalComplexDiagonalOperator b a) (b i) (-(a i : ℂ))]
  · simp
  · simp [orthonormalComplexDiagonalOperator_apply_basis]

/-- For nonnegative real diagonal coefficients, the canonical logarithmic
Hamiltonian of the transfer operator with coefficients `exp (-aᵢ)` is exactly
the original diagonal Hamiltonian. -/
theorem complexStrictlyPositive_logHamiltonian_exp_neg_diagonal_eq
    {ι E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E]
    [CompleteSpace E]
    (b : OrthonormalBasis ι ℂ E)
    (a : ι → ℝ)
    (ha : ∀ i : ι, 0 ≤ a i) :
    ComplexStrictlyPositiveOperator.logHamiltonian
        (orthonormalComplexDiagonalOperator b (fun i => Real.exp (-a i))) =
      orthonormalComplexDiagonalOperator b a := by
  have hpositive :
      (orthonormalComplexDiagonalOperator b a).IsPositive :=
    orthonormalComplexDiagonalOperator_isPositive b a ha
  have hself :
      IsSelfAdjoint (-orthonormalComplexDiagonalOperator b a) :=
    hpositive.isSelfAdjoint.neg
  rw [← normedSpace_exp_neg_orthonormalComplexDiagonalOperator b a]
  unfold ComplexStrictlyPositiveOperator.logHamiltonian
  rw [CFC.log_exp (-orthonormalComplexDiagonalOperator b a) hself]
  simp

/-- The recovered logarithmic Hamiltonian acts on each diagonal basis mode with
the original real coefficient. -/
theorem complexStrictlyPositive_logHamiltonian_exp_neg_diagonal_apply_basis
    {ι E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E]
    [CompleteSpace E]
    (b : OrthonormalBasis ι ℂ E)
    (a : ι → ℝ)
    (ha : ∀ i : ι, 0 ≤ a i)
    (i : ι) :
    ComplexStrictlyPositiveOperator.logHamiltonian
        (orthonormalComplexDiagonalOperator b (fun j => Real.exp (-a j))) (b i) =
      (a i : ℂ) • b i := by
  rw [complexStrictlyPositive_logHamiltonian_exp_neg_diagonal_eq b a ha]
  exact orthonormalComplexDiagonalOperator_apply_basis b a i

end

end MathlibAnalytic
end MGAP4D
