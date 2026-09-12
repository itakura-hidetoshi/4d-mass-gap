import MGAP4D.MathlibAnalytic.ContinuousRealLinearOperatorExpEigenvector
import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianSemigroupEvolution

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Scaling all diagonal coefficients is the same as scaling the real diagonal
operator. -/
theorem orthonormalDiagonalOperator_mul_left_scalar
    {ι E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E)
    (a : ι → ℝ)
    (t : ℝ) :
    orthonormalDiagonalOperator b (fun i => t * a i) =
      t • orthonormalDiagonalOperator b a := by
  rw [orthonormalDiagonalOperator_eq_sum_rankOne,
    orthonormalDiagonalOperator_eq_sum_rankOne, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  module

/-- Ordinary operator-norm derivative form of the left evolution equation. -/
theorem orthonormalDiagonalHamiltonianSemigroup_deriv_operator_left
    {ι E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E)
    (a : ι → ℝ)
    (t : ℝ) :
    deriv (orthonormalDiagonalHamiltonianSemigroup b a) t =
      (-orthonormalDiagonalOperator b a) *
        orthonormalDiagonalHamiltonianSemigroup b a t :=
  (orthonormalDiagonalHamiltonianSemigroup_hasDerivAt_operator_left b a t).deriv

/-- Ordinary operator-norm derivative form of the right evolution equation. -/
theorem orthonormalDiagonalHamiltonianSemigroup_deriv_operator_right
    {ι E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E)
    (a : ι → ℝ)
    (t : ℝ) :
    deriv (orthonormalDiagonalHamiltonianSemigroup b a) t =
      orthonormalDiagonalHamiltonianSemigroup b a t *
        (-orthonormalDiagonalOperator b a) :=
  (orthonormalDiagonalHamiltonianSemigroup_hasDerivAt_operator_right b a t).deriv

/-- The finite real diagonal Hamiltonian commutes with every semigroup time
slice. -/
theorem orthonormalDiagonalHamiltonianSemigroup_commutes_hamiltonian_explicit
    {ι E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E)
    (a : ι → ℝ)
    (t : ℝ) :
    orthonormalDiagonalOperator b a *
        orthonormalDiagonalHamiltonianSemigroup b a t =
      orthonormalDiagonalHamiltonianSemigroup b a t *
        orthonormalDiagonalOperator b a := by
  unfold orthonormalDiagonalHamiltonianSemigroup
  rw [orthonormalDiagonalOperator_mul, orthonormalDiagonalOperator_mul]
  congr 1
  funext i
  ring

/-- The finite real diagonal Hamiltonian semigroup is exactly the
Banach-algebra exponential of the negative time-scaled Hamiltonian. -/
theorem normedSpace_exp_neg_scaled_orthonormalDiagonalOperator
    {ι E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    [CompleteSpace E]
    (b : OrthonormalBasis ι ℝ E)
    (a : ι → ℝ)
    (t : ℝ) :
    NormedSpace.exp
        (-orthonormalDiagonalOperator b (fun i => t * a i)) =
      orthonormalDiagonalHamiltonianSemigroup b a t := by
  apply ContinuousLinearMap.ext
  intro x
  rw [← b.sum_repr' x]
  simp only [map_sum, map_smul,
    orthonormalDiagonalHamiltonianSemigroup_apply_basis]
  apply Finset.sum_congr rfl
  intro i hi
  rw [normedSpace_exp_apply_of_real_eigenvector
    (-orthonormalDiagonalOperator b (fun j => t * a j))
    (b i) (-(t * a i))]
  all_goals simp [orthonormalDiagonalOperator_apply_basis]

/-- Equivalent scalar-multiple form `S_t = exp (-(t • H))`. -/
theorem normedSpace_exp_neg_smul_orthonormalDiagonalOperator
    {ι E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    [CompleteSpace E]
    (b : OrthonormalBasis ι ℝ E)
    (a : ι → ℝ)
    (t : ℝ) :
    NormedSpace.exp (-(t • orthonormalDiagonalOperator b a)) =
      orthonormalDiagonalHamiltonianSemigroup b a t := by
  rw [← orthonormalDiagonalOperator_mul_left_scalar b a t]
  exact normedSpace_exp_neg_scaled_orthonormalDiagonalOperator b a t

end

end MathlibAnalytic
end MGAP4D
