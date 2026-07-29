import MGAP4D.MathlibAnalytic.OrthonormalComplexDiagonalHamiltonianSemigroup
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The finite complex diagonal Hamiltonian semigroup is smooth in operator norm. -/
theorem orthonormalComplexDiagonalHamiltonianSemigroup_contDiff
    {ι E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E]
    (b : OrthonormalBasis ι ℂ E)
    (a : ι → ℝ) :
    ContDiff ℝ ⊤ (orthonormalComplexDiagonalHamiltonianSemigroup b a) := by
  have hrepr :
      orthonormalComplexDiagonalHamiltonianSemigroup b a =
        fun t : ℝ =>
          ∑ i : ι, (Real.exp (-(t * a i)) : ℂ) •
            rankOne ℂ (b i) (b i) := by
    funext t
    exact orthonormalComplexDiagonalOperator_eq_sum_rankOne b
      (fun i => Real.exp (-(t * a i)))
  rw [hrepr]
  fun_prop

/-- The finite complex diagonal Hamiltonian semigroup is continuous in operator norm. -/
theorem orthonormalComplexDiagonalHamiltonianSemigroup_continuous
    {ι E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E]
    (b : OrthonormalBasis ι ℂ E)
    (a : ι → ℝ) :
    Continuous (orthonormalComplexDiagonalHamiltonianSemigroup b a) :=
  (orthonormalComplexDiagonalHamiltonianSemigroup_contDiff b a).continuous

/-- Operator-norm continuity implies strong continuity on every vector. -/
theorem orthonormalComplexDiagonalHamiltonianSemigroup_stronglyContinuous
    {ι E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E]
    (b : OrthonormalBasis ι ℂ E)
    (a : ι → ℝ)
    (x : E) :
    Continuous (fun t : ℝ =>
      orthonormalComplexDiagonalHamiltonianSemigroup b a t x) :=
  (orthonormalComplexDiagonalHamiltonianSemigroup_continuous b a).clm_apply
    continuous_const

end

end MathlibAnalytic
end MGAP4D
