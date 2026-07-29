import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianSemigroupOperatorExp
import Mathlib.Analysis.Calculus.MeanValue

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The finite real diagonal Hamiltonian semigroup is the unique operator-norm
solution of the left initial-value problem `U' = -H U`, `U 0 = 1`.

The proof uses the inverse-time semigroup as an integrating factor. -/
theorem orthonormalDiagonalHamiltonianSemigroup_eq_of_hasDerivAt_operator_left
    {ι E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E)
    (a : ι → ℝ)
    (U : ℝ → (E →L[ℝ] E))
    (hU0 : U 0 = 1)
    (hU : ∀ t : ℝ,
      HasDerivAt U ((-orthonormalDiagonalOperator b a) * U t) t) :
    U = orthonormalDiagonalHamiltonianSemigroup b a := by
  funext t
  let S := orthonormalDiagonalHamiltonianSemigroup b a
  let H := orthonormalDiagonalOperator b a
  have hSneg (s : ℝ) :
      HasDerivAt (fun r : ℝ => S (-r)) (H * S (-s)) s := by
    have h :=
      (orthonormalDiagonalHamiltonianSemigroup_hasDerivAt_operator_left
        b a (-s)).scomp s ((hasDerivAt_id' s).neg)
    simpa [Function.comp_def, S, H] using h
  have hprod (s : ℝ) :
      HasDerivAt (fun r : ℝ => S (-r) * U r) 0 s := by
    convert (hSneg s).mul (hU s) using 1
    rw [orthonormalDiagonalHamiltonianSemigroup_commutes_hamiltonian_explicit
      b a (-s)]
    noncomm_ring
  have hdiff : Differentiable ℝ (fun r : ℝ => S (-r) * U r) :=
    fun s => (hprod s).differentiableAt
  have hzero : ∀ s : ℝ, deriv (fun r : ℝ => S (-r) * U r) s = 0 :=
    fun s => (hprod s).deriv
  have hconst := is_const_of_deriv_eq_zero hdiff hzero t 0
  have hintegrating : S (-t) * U t = 1 := by
    simpa [S, hU0] using hconst
  calc
    U t = (S t * S (-t)) * U t := by
      rw [← orthonormalDiagonalHamiltonianSemigroup_add b a t (-t)]
      simp
    _ = S t * (S (-t) * U t) := by rw [mul_assoc]
    _ = S t := by rw [hintegrating, mul_one]
    _ = orthonormalDiagonalHamiltonianSemigroup b a t := rfl

end

end MathlibAnalytic
end MGAP4D
