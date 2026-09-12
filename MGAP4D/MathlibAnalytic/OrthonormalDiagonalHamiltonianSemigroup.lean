import MGAP4D.MathlibAnalytic.OrthonormalDiagonalOperatorInverse
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open InnerProductSpace

/-- A real diagonal operator is the finite sum of its scaled rank-one basis
projections. -/
theorem orthonormalDiagonalOperator_eq_sum_rankOne
    {ι E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E)
    (a : ι → ℝ) :
    orthonormalDiagonalOperator b a =
      ∑ i : ι, a i • rankOne ℝ (b i) (b i) := by
  apply ContinuousLinearMap.ext
  intro x
  rw [orthonormalDiagonalOperator_apply]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    rankOne_apply]
  apply Finset.sum_congr rfl
  intro i hi
  module

/-- The explicit continuous-time semigroup diagonal in a finite real
orthonormal basis, with mode energies `aᵢ`. -/
noncomputable def orthonormalDiagonalHamiltonianSemigroup
    {ι E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E)
    (a : ι → ℝ)
    (t : ℝ) : E →L[ℝ] E :=
  orthonormalDiagonalOperator b (fun i => Real.exp (-(t * a i)))

/-- Time zero is the identity. -/
@[simp]
theorem orthonormalDiagonalHamiltonianSemigroup_zero
    {ι E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E)
    (a : ι → ℝ) :
    orthonormalDiagonalHamiltonianSemigroup b a 0 = 1 := by
  unfold orthonormalDiagonalHamiltonianSemigroup
  have hcoeff : (fun i => Real.exp (-((0 : ℝ) * a i))) = fun _ => 1 := by
    funext i
    simp
  rw [hcoeff, orthonormalDiagonalOperator_one]

/-- The explicit real diagonal family satisfies the semigroup addition law. -/
theorem orthonormalDiagonalHamiltonianSemigroup_add
    {ι E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E)
    (a : ι → ℝ)
    (s t : ℝ) :
    orthonormalDiagonalHamiltonianSemigroup b a (s + t) =
      orthonormalDiagonalHamiltonianSemigroup b a s *
        orthonormalDiagonalHamiltonianSemigroup b a t := by
  unfold orthonormalDiagonalHamiltonianSemigroup
  rw [orthonormalDiagonalOperator_mul]
  congr 1
  funext i
  rw [← Real.exp_add]
  congr 1
  ring

/-- Time one has the transfer coefficients `exp (-aᵢ)`. -/
theorem orthonormalDiagonalHamiltonianSemigroup_one
    {ι E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E)
    (a : ι → ℝ) :
    orthonormalDiagonalHamiltonianSemigroup b a 1 =
      orthonormalDiagonalOperator b (fun i => Real.exp (-a i)) := by
  unfold orthonormalDiagonalHamiltonianSemigroup
  congr 1
  funext i
  simp

/-- On every basis mode, real time evolution multiplies by `exp (-t aᵢ)`. -/
theorem orthonormalDiagonalHamiltonianSemigroup_apply_basis
    {ι E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E)
    (a : ι → ℝ)
    (t : ℝ)
    (i : ι) :
    orthonormalDiagonalHamiltonianSemigroup b a t (b i) =
      Real.exp (-(t * a i)) • b i := by
  exact orthonormalDiagonalOperator_apply_basis b
    (fun j => Real.exp (-(t * a j))) i

end

end MathlibAnalytic
end MGAP4D
