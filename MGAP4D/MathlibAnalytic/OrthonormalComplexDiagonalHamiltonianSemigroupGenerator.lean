import MGAP4D.MathlibAnalytic.OrthonormalComplexDiagonalHamiltonianSemigroupContinuity
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
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
          ∑ i : ι, Real.exp (-(t * a i)) •
            (inner ℂ (b i) x • b i) := by
    funext t
    unfold orthonormalComplexDiagonalHamiltonianSemigroup
    rw [orthonormalComplexDiagonalOperator_apply]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Complex.coe_smul]
    exact (smul_comm (Real.exp (-(t * a i))) (inner ℂ (b i) x) (b i)).symm
  rw [hrepr]
  have hsum :
      HasDerivAt
        (fun t : ℝ =>
          ∑ i : ι, Real.exp (-(t * a i)) •
            (inner ℂ (b i) x • b i))
        (∑ i : ι, (-a i) • (inner ℂ (b i) x • b i)) 0 := by
    simpa using
      (HasDerivAt.fun_sum (u := Finset.univ) (x := (0 : ℝ))
        (A := fun i t =>
          Real.exp (-(t * a i)) • (inner ℂ (b i) x • b i))
        (A' := fun i =>
          (-a i) • (inner ℂ (b i) x • b i))
        (fun i hi =>
          (real_exp_neg_mul_hasDerivAt_zero (a i)).smul_const
            (inner ℂ (b i) x • b i)))
  have hderiv :
      (∑ i : ι, (-a i) • (inner ℂ (b i) x • b i)) =
        -(orthonormalComplexDiagonalOperator b a x) := by
    rw [orthonormalComplexDiagonalOperator_apply, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    calc
      (-a i) • (inner ℂ (b i) x • b i) =
          inner ℂ (b i) x • ((-a i) • b i) :=
        smul_comm (-a i) (inner ℂ (b i) x) (b i)
      _ = inner ℂ (b i) x • (-(a i • b i)) := by
        rw [neg_smul]
      _ = -(inner ℂ (b i) x • (a i • b i)) := by
        rw [smul_neg]
      _ = -(inner ℂ (b i) x • ((a i : ℂ) • b i)) := by
        rw [Complex.coe_smul]
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
