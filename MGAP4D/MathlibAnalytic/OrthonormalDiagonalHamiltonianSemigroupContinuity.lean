import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianSemigroup
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open InnerProductSpace

/-- The finite real diagonal Hamiltonian semigroup is smooth in operator norm. -/
theorem orthonormalDiagonalHamiltonianSemigroup_contDiff
    {ι E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E)
    (a : ι → ℝ) :
    ContDiff ℝ ⊤ (orthonormalDiagonalHamiltonianSemigroup b a) := by
  have hrepr :
      orthonormalDiagonalHamiltonianSemigroup b a =
        fun t : ℝ =>
          ∑ i : ι, Real.exp (-(t * a i)) •
            rankOne ℝ (b i) (b i) := by
    funext t
    exact orthonormalDiagonalOperator_eq_sum_rankOne b
      (fun i => Real.exp (-(t * a i)))
  rw [hrepr]
  fun_prop

/-- The finite real diagonal Hamiltonian semigroup is continuous in operator norm. -/
theorem orthonormalDiagonalHamiltonianSemigroup_continuous
    {ι E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E)
    (a : ι → ℝ) :
    Continuous (orthonormalDiagonalHamiltonianSemigroup b a) :=
  (orthonormalDiagonalHamiltonianSemigroup_contDiff b a).continuous

/-- Operator-norm continuity implies strong continuity on every real state. -/
theorem orthonormalDiagonalHamiltonianSemigroup_stronglyContinuous
    {ι E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E)
    (a : ι → ℝ)
    (x : E) :
    Continuous (fun t : ℝ =>
      orthonormalDiagonalHamiltonianSemigroup b a t x) :=
  (orthonormalDiagonalHamiltonianSemigroup_continuous b a).clm_apply
    continuous_const

end

end MathlibAnalytic
end MGAP4D
