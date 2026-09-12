import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianSemigroupOperatorExp
import Mathlib.Analysis.Calculus.MeanValue

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The finite real diagonal Hamiltonian semigroup orbit through `x` is the unique
statewise solution of the initial-value problem `u' = -H u`, `u 0 = x`.

The proof applies the inverse-time semigroup to the evolving state. -/
theorem orthonormalDiagonalHamiltonianSemigroup_apply_eq_of_hasDerivAt
    {ι E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E)
    (a : ι → ℝ)
    (x : E)
    (u : ℝ → E)
    (hu0 : u 0 = x)
    (hu : ∀ t : ℝ,
      HasDerivAt u (-(orthonormalDiagonalOperator b a (u t))) t) :
    u = fun t : ℝ => orthonormalDiagonalHamiltonianSemigroup b a t x := by
  funext t
  let S := orthonormalDiagonalHamiltonianSemigroup b a
  let H := orthonormalDiagonalOperator b a
  have hSneg (s : ℝ) :
      HasDerivAt (fun r : ℝ => S (-r)) (S (-s) * H) s := by
    have h :=
      (orthonormalDiagonalHamiltonianSemigroup_hasDerivAt_operator_right
        b a (-s)).scomp s ((hasDerivAt_id' s).neg)
    simpa [Function.comp_def, S, H] using h
  have hprod (s : ℝ) :
      HasDerivAt (fun r : ℝ => S (-r) (u r)) 0 s := by
    convert (hSneg s).clm_apply (hu s) using 1
    change 0 = S (-s) (H (u s)) + S (-s) (-(H (u s)))
    rw [map_neg]
    exact (add_neg_cancel _).symm
  have hdiff : Differentiable ℝ (fun r : ℝ => S (-r) (u r)) :=
    fun s => (hprod s).differentiableAt
  have hzero : ∀ s : ℝ, deriv (fun r : ℝ => S (-r) (u r)) s = 0 :=
    fun s => (hprod s).deriv
  have hconst := is_const_of_deriv_eq_zero hdiff hzero t 0
  have hintegrating : S (-t) (u t) = x := by
    simpa [S, hu0] using hconst
  calc
    u t = (S t * S (-t)) (u t) := by
      rw [← orthonormalDiagonalHamiltonianSemigroup_add b a t (-t)]
      simp
    _ = S t (S (-t) (u t)) := rfl
    _ = S t x := by rw [hintegrating]
    _ = orthonormalDiagonalHamiltonianSemigroup b a t x := rfl

end

end MathlibAnalytic
end MGAP4D
