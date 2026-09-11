import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianSemigroupOperatorConstantInputMatrixElementExponentialTrackingFullGap
import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianSemigroupOperatorConstantInputFullGapAsymptoticConvergence
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Filter

noncomputable section

/-- Operator-norm convergence implies convergence to zero of every scalar matrix
    element of the operator error. -/
theorem continuousLinearMap_tendsto_inner_sub_apply_zero_of_tendsto
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (U : ℝ → (E →L[ℝ] E)) (S : E →L[ℝ] E) (x y : E)
    (hU : Tendsto U atTop (nhds S)) :
    Tendsto (fun t : ℝ => inner ℝ x ((U t - S) y)) atTop (nhds 0) := by
  rw [Metric.tendsto_atTop] at hU ⊢
  intro ε hε
  let c : ℝ := ‖x‖ * ‖y‖ + 1
  have hc : 0 < c := by
    dsimp [c]
    positivity
  let ε' : ℝ := ε / c
  have hε' : 0 < ε' := div_pos hε hc
  rcases hU ε' hε' with ⟨T, hT⟩
  refine ⟨T, ?_⟩
  intro t ht
  have hnorm : ‖U t - S‖ < ε' := by
    have hdist := hT t ht
    simpa [dist_eq_norm] using hdist
  have hcs :
      |inner ℝ x ((U t - S) y)| ≤ ‖x‖ * ‖(U t - S) y‖ := by
    simpa only [Real.norm_eq_abs] using
      (norm_inner_le_norm (𝕜 := ℝ) x ((U t - S) y))
  have hprod : ‖x‖ * ‖y‖ ≤ c := by
    dsimp [c]
    linarith
  have hlt : |inner ℝ x ((U t - S) y)| < ε := by
    calc
      |inner ℝ x ((U t - S) y)| ≤ ‖x‖ * ‖(U t - S) y‖ := hcs
      _ ≤ ‖x‖ * (‖U t - S‖ * ‖y‖) :=
        mul_le_mul_of_nonneg_left ((U t - S).le_opNorm y) (norm_nonneg x)
      _ = (‖x‖ * ‖y‖) * ‖U t - S‖ := by ring
      _ ≤ c * ‖U t - S‖ :=
        mul_le_mul_of_nonneg_right hprod (norm_nonneg (U t - S))
      _ < c * ε' := mul_lt_mul_of_pos_left hnorm hc
      _ = ε := by
        dsimp [ε']
        field_simp [hc.ne']
  simpa [dist_eq_norm, Real.norm_eq_abs] using hlt

/-- Under exactly constant input, every left matrix element of the tracking error
    converges to zero. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_constantInput_weakMatrixElement_tendsto_zero_fullGap_left
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i) (hδpos : 0 < δ) (t₀ : ℝ)
    (A : E →L[ℝ] E) (U : ℝ → (E →L[ℝ] E))
    (F_lim : E →L[ℝ] E) (x y : E)
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U ((-orthonormalDiagonalOperator b a) * U r + F_lim) r) :
    Tendsto
      (fun t : ℝ => inner ℝ x
        ((U t - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim) y))
      atTop (nhds 0) := by
  exact continuousLinearMap_tendsto_inner_sub_apply_zero_of_tendsto
    U (orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim) x y
    (orthonormalDiagonalHamiltonianSemigroup_operator_constantInput_tendsto_steadyState_fullGap_left
      b a δ hδ hδpos t₀ A U F_lim hU0 hU)

/-- Under exactly constant input, every right matrix element of the tracking error
    converges to zero, without a commutation hypothesis. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_constantInput_weakMatrixElement_tendsto_zero_fullGap_right
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i) (hδpos : 0 < δ) (t₀ : ℝ)
    (A : E →L[ℝ] E) (U : ℝ → (E →L[ℝ] E))
    (F_lim : E →L[ℝ] E) (x y : E)
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U (U r * (-orthonormalDiagonalOperator b a) + F_lim) r) :
    Tendsto
      (fun t : ℝ => inner ℝ x
        ((U t - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim) y))
      atTop (nhds 0) := by
  exact continuousLinearMap_tendsto_inner_sub_apply_zero_of_tendsto
    U (orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim) x y
    (orthonormalDiagonalHamiltonianSemigroup_operator_constantInput_tendsto_steadyState_fullGap_right
      b a δ hδ hδpos t₀ A U F_lim hU0 hU)

end

end MathlibAnalytic
end MGAP4D
