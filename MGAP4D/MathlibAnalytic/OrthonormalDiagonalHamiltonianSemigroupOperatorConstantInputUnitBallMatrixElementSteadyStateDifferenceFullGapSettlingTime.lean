import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianSemigroupOperatorConstantInputMatrixElementSteadyStateDifferenceFullGapSettlingTime
import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianSemigroupOperatorConstantInputExponentialTrackingEnvelopeFullGapSettlingTime
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- On the closed unit ball in both variables, every matrix-element difference is
    bounded by the operator-norm difference. -/
theorem continuousLinearMap_abs_inner_apply_sub_inner_apply_le_norm_of_norm_le_one
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (U S : E →L[ℝ] E) (x y : E)
    (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    |inner ℝ x (U y) - inner ℝ x (S y)| ≤ ‖U - S‖ := by
  rw [continuousLinearMap_abs_inner_apply_sub_inner_apply_eq_abs_inner_sub_apply]
  have hinner :
      |inner ℝ x ((U - S) y)| ≤ ‖x‖ * ‖(U - S) y‖ := by
    simpa only [Real.norm_eq_abs] using
      (norm_inner_le_norm (𝕜 := ℝ) x ((U - S) y))
  have hop : ‖(U - S) y‖ ≤ ‖U - S‖ * ‖y‖ := (U - S).le_opNorm y
  calc
    |inner ℝ x ((U - S) y)| ≤ ‖x‖ * ‖(U - S) y‖ := hinner
    _ ≤ ‖x‖ * (‖U - S‖ * ‖y‖) :=
      mul_le_mul_of_nonneg_left hop (norm_nonneg x)
    _ ≤ 1 * (‖U - S‖ * 1) := by
      exact mul_le_mul hx
        (mul_le_mul_of_nonneg_left hy (norm_nonneg (U - S)))
        (mul_nonneg (norm_nonneg (U - S)) (norm_nonneg y))
        (by norm_num)
    _ = ‖U - S‖ := by ring

/-- Constant-input left tracking reaches every tolerance uniformly over both
    closed unit balls after the operator-norm full-gap waiting time. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_constantInput_unitBall_matrixElement_sub_steadyState_abs_le_epsilon_after_exponentialTracking_fullGap_left
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i) (hδpos : 0 < δ) (t₀ : ℝ)
    (A : E →L[ℝ] E) (U : ℝ → (E →L[ℝ] E))
    (F_lim : E →L[ℝ] E)
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U ((-orthonormalDiagonalOperator b a) * U r + F_lim) r)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ t : ℝ,
      t₀ + max 0
          (Real.log
            (‖A - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim‖ / ε) / δ) ≤ t →
        ∀ x y : E, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
          |inner ℝ x (U t y) -
            inner ℝ x (orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim y)| ≤ ε := by
  intro t ht x y hx hy
  have hmatrix :=
    continuousLinearMap_abs_inner_apply_sub_inner_apply_le_norm_of_norm_le_one
      (U t) (orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim) x y hx hy
  exact hmatrix.trans
    (orthonormalDiagonalHamiltonianSemigroup_operator_constantInput_norm_sub_le_epsilon_after_exponentialTrackingEnvelope_fullGap_left
      b a δ hδ hδpos t₀ A U F_lim hU0 hU ε hε t ht)

/-- Constant-input right tracking has the identical uniform unit-ball waiting
    time, without a commutation hypothesis. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_constantInput_unitBall_matrixElement_sub_steadyState_abs_le_epsilon_after_exponentialTracking_fullGap_right
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i) (hδpos : 0 < δ) (t₀ : ℝ)
    (A : E →L[ℝ] E) (U : ℝ → (E →L[ℝ] E))
    (F_lim : E →L[ℝ] E)
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U (U r * (-orthonormalDiagonalOperator b a) + F_lim) r)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ t : ℝ,
      t₀ + max 0
          (Real.log
            (‖A - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim‖ / ε) / δ) ≤ t →
        ∀ x y : E, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
          |inner ℝ x (U t y) -
            inner ℝ x (orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim y)| ≤ ε := by
  intro t ht x y hx hy
  have hmatrix :=
    continuousLinearMap_abs_inner_apply_sub_inner_apply_le_norm_of_norm_le_one
      (U t) (orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim) x y hx hy
  exact hmatrix.trans
    (orthonormalDiagonalHamiltonianSemigroup_operator_constantInput_norm_sub_le_epsilon_after_exponentialTrackingEnvelope_fullGap_right
      b a δ hδ hδpos t₀ A U F_lim hU0 hU ε hε t ht)

end

end MathlibAnalytic
end MGAP4D
