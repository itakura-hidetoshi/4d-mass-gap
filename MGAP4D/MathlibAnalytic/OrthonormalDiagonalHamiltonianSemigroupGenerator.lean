import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianSemigroupContinuity
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open InnerProductSpace

/-- The scalar real mode factor `exp (-t a)` has derivative `-a` at time zero. -/
theorem real_exp_neg_mul_hasDerivAt_zero_realSemigroup (a : ℝ) :
    HasDerivAt (fun t : ℝ => Real.exp (-(t * a))) (-a) 0 := by
  have hmul : HasDerivAt (fun t : ℝ => t * a) a 0 := by
    simpa using (hasDerivAt_id' (0 : ℝ)).mul_const a
  have hneg : HasDerivAt (fun t : ℝ => -(t * a)) (-a) 0 :=
    hmul.neg
  simpa using hneg.exp

/-- In operator norm, the derivative at time zero of the finite real diagonal
Hamiltonian semigroup is the negative diagonal Hamiltonian. -/
theorem orthonormalDiagonalHamiltonianSemigroup_hasDerivAt_zero_operator
    {ι E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E)
    (a : ι → ℝ) :
    HasDerivAt
      (orthonormalDiagonalHamiltonianSemigroup b a)
      (-orthonormalDiagonalOperator b a) 0 := by
  have hrepr :
      orthonormalDiagonalHamiltonianSemigroup b a =
        fun t : ℝ =>
          ∑ i : ι, Real.exp (-(t * a i)) •
            rankOne ℝ (b i) (b i) := by
    funext t
    exact orthonormalDiagonalOperator_eq_sum_rankOne b
      (fun i => Real.exp (-(t * a i)))
  rw [hrepr]
  have hsum :
      HasDerivAt
        (fun t : ℝ =>
          ∑ i : ι, Real.exp (-(t * a i)) • rankOne ℝ (b i) (b i))
        (∑ i : ι, (-a i) • rankOne ℝ (b i) (b i)) 0 := by
    simpa using
      (HasDerivAt.fun_sum (u := Finset.univ) (x := (0 : ℝ))
        (A := fun i t =>
          Real.exp (-(t * a i)) • rankOne ℝ (b i) (b i))
        (A' := fun i => (-a i) • rankOne ℝ (b i) (b i))
        (fun i hi =>
          (real_exp_neg_mul_hasDerivAt_zero_realSemigroup (a i)).smul_const
            (rankOne ℝ (b i) (b i))))
  have hderiv :
      (∑ i : ι, (-a i) • rankOne ℝ (b i) (b i)) =
        -orthonormalDiagonalOperator b a := by
    rw [orthonormalDiagonalOperator_eq_sum_rankOne, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    module
  rw [← hderiv]
  exact hsum

/-- On every real state, the strong derivative at time zero is the negative
Hamiltonian action. -/
theorem orthonormalDiagonalHamiltonianSemigroup_hasDerivAt_zero
    {ι E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E)
    (a : ι → ℝ)
    (x : E) :
    HasDerivAt
      (fun t : ℝ => orthonormalDiagonalHamiltonianSemigroup b a t x)
      (-(orthonormalDiagonalOperator b a x)) 0 := by
  have h :=
    (orthonormalDiagonalHamiltonianSemigroup_hasDerivAt_zero_operator b a).clm_apply
      (hasDerivAt_const (0 : ℝ) x)
  simpa using h

/-- The ordinary strong derivative at time zero is the negative real diagonal
Hamiltonian action. -/
theorem orthonormalDiagonalHamiltonianSemigroup_deriv_zero
    {ι E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E)
    (a : ι → ℝ)
    (x : E) :
    deriv (fun t : ℝ => orthonormalDiagonalHamiltonianSemigroup b a t x) 0 =
      -(orthonormalDiagonalOperator b a x) :=
  (orthonormalDiagonalHamiltonianSemigroup_hasDerivAt_zero b a x).deriv

end

end MathlibAnalytic
end MGAP4D
