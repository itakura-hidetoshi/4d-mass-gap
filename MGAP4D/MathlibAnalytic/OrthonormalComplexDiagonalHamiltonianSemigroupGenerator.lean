import MGAP4D.MathlibAnalytic.OrthonormalComplexDiagonalHamiltonianSemigroupContinuity
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open InnerProductSpace

/-- The scalar mode factor `exp (-t a)` has derivative `-a` at time zero. -/
theorem real_exp_neg_mul_hasDerivAt_zero (a : ℝ) :
    HasDerivAt (fun t : ℝ => Real.exp (-(t * a))) (-a) 0 := by
  have hmul : HasDerivAt (fun t : ℝ => t * a) a 0 := by
    simpa using (hasDerivAt_id' (0 : ℝ)).mul_const a
  have hneg : HasDerivAt (fun t : ℝ => -(t * a)) (-a) 0 :=
    hmul.neg
  simpa using hneg.exp

/-- On every vector, the strong derivative at time zero of the finite complex
Hamiltonian semigroup is the negative diagonal Hamiltonian action. -/
theorem orthonormalComplexDiagonalHamiltonianSemigroup_hasDerivAt_zero
    {ι E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E]
    (b : OrthonormalBasis ι ℂ E)
    (a : ι → ℝ)
    (x : E) :
    HasDerivAt
      (fun t : ℝ => orthonormalComplexDiagonalHamiltonianSemigroup b a t x)
      (-(orthonormalComplexDiagonalOperator b a x)) 0 := by
  have hrepr :
      (fun t : ℝ => orthonormalComplexDiagonalHamiltonianSemigroup b a t x) =
        fun t : ℝ =>
          ∑ i : ι, inner ℂ (b i) x •
            ((Real.exp (-(t * a i)) : ℂ) • b i) := by
    funext t
    unfold orthonormalComplexDiagonalHamiltonianSemigroup
    exact orthonormalComplexDiagonalOperator_apply b
      (fun i => Real.exp (-(t * a i))) x
  rw [hrepr]
  have hsum :
      HasDerivAt
        (fun t : ℝ =>
          ∑ i : ι, inner ℂ (b i) x •
            ((Real.exp (-(t * a i)) : ℂ) • b i))
        (∑ i : ι, inner ℂ (b i) x • (((-a i : ℝ) : ℂ) • b i)) 0 := by
    simpa using
      (HasDerivAt.fun_sum (u := Finset.univ) (x := (0 : ℝ))
        (A := fun i t =>
          inner ℂ (b i) x • ((Real.exp (-(t * a i)) : ℂ) • b i))
        (A' := fun i =>
          inner ℂ (b i) x • (((-a i : ℝ) : ℂ) • b i))
        (fun i hi =>
          ((real_exp_neg_mul_hasDerivAt_zero (a i)).ofReal_comp.smul_const (b i)).const_smul
            (inner ℂ (b i) x)))
  have hderiv :
      (∑ i : ι, inner ℂ (b i) x • (((-a i : ℝ) : ℂ) • b i)) =
        -(orthonormalComplexDiagonalOperator b a x) := by
    rw [orthonormalComplexDiagonalOperator_apply, Finset.neg_sum]
    apply Finset.sum_congr rfl
    intro i hi
    module
  rw [← hderiv]
  exact hsum

/-- The ordinary derivative at time zero is the negative diagonal Hamiltonian
action. -/
theorem orthonormalComplexDiagonalHamiltonianSemigroup_deriv_zero
    {ι E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E]
    (b : OrthonormalBasis ι ℂ E)
    (a : ι → ℝ)
    (x : E) :
    deriv (fun t : ℝ => orthonormalComplexDiagonalHamiltonianSemigroup b a t x) 0 =
      -(orthonormalComplexDiagonalOperator b a x) :=
  (orthonormalComplexDiagonalHamiltonianSemigroup_hasDerivAt_zero b a x).deriv

end

end MathlibAnalytic
end MGAP4D
