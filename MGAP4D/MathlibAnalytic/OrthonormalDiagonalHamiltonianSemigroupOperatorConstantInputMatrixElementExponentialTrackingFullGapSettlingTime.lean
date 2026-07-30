import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianSemigroupOperatorConstantInputMatrixElementExponentialTrackingFullGap
import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianSemigroupOperatorConstantInputExponentialTrackingEnvelopeFullGapSettlingTime
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- A scalar exponential envelope reaches every positive tolerance after the
    corresponding logarithmic waiting time. -/
theorem realFunction_abs_le_epsilon_after_exponentialBound
    (δ ε K t₀ : ℝ) (hδpos : 0 < δ) (hε : 0 < ε) (hKnonneg : 0 ≤ K)
    (f : ℝ → ℝ)
    (hbound : ∀ t : ℝ, t₀ ≤ t → |f t| ≤ K * Real.exp (-((t - t₀) * δ))) :
    ∀ t : ℝ,
      t₀ + max 0 (Real.log (K / ε) / δ) ≤ t →
        |f t| ≤ ε := by
  intro t ht
  have hwait_nonneg : 0 ≤ max 0 (Real.log (K / ε) / δ) := le_max_left _ _
  have ht₀ : t₀ ≤ t := by linarith
  have hf := hbound t ht₀
  by_cases hK : K = 0
  · have hzero : |f t| ≤ 0 := by simpa [hK] using hf
    exact hzero.trans hε.le
  · have hKpos : 0 < K := lt_of_le_of_ne hKnonneg (Ne.symm hK)
    have hmaxle : max 0 (Real.log (K / ε) / δ) ≤ t - t₀ := by linarith
    have hwait : Real.log (K / ε) / δ ≤ t - t₀ :=
      (le_max_right _ _).trans hmaxle
    have hdecay :=
      exp_neg_mul_mul_le_of_log_div_div_le δ ε K (t - t₀)
        hδpos hε hKpos hwait
    exact hf.trans (by simpa [mul_comm] using hdecay)

/-- Every left matrix element of constant-input tracking reaches a prescribed
    tolerance after an explicit full-gap logarithmic waiting time. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_constantInput_matrixElement_abs_le_epsilon_after_exponentialTracking_fullGap_left
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i) (hδpos : 0 < δ) (t₀ : ℝ)
    (A : E →L[ℝ] E) (U : ℝ → (E →L[ℝ] E))
    (F_lim : E →L[ℝ] E) (x y : E)
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U ((-orthonormalDiagonalOperator b a) * U r + F_lim) r)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ t : ℝ,
      t₀ + max 0
          (Real.log
            ((‖A - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim‖ *
                ‖x‖ * ‖y‖) / ε) / δ) ≤ t →
        |inner ℝ x
          ((U t - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim) y)| ≤ ε := by
  refine realFunction_abs_le_epsilon_after_exponentialBound
    δ ε
      (‖A - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim‖ * ‖x‖ * ‖y‖)
      t₀ hδpos hε ?_
      (fun t : ℝ => inner ℝ x
        ((U t - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim) y)) ?_
  · positivity
  · intro t ht
    have hmatrix :=
      orthonormalDiagonalHamiltonianSemigroup_operator_constantInput_matrixElement_exponentialTracking_fullGap_left
        b a δ hδ hδpos t₀ t ht A U F_lim x y hU0 hU
    calc
      |inner ℝ x
          ((U t - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim) y)| ≤
          (‖A - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim‖ *
            Real.exp (-((t - t₀) * δ))) * ‖x‖ * ‖y‖ := hmatrix
      _ = (‖A - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim‖ *
            ‖x‖ * ‖y‖) * Real.exp (-((t - t₀) * δ)) := by ring

/-- Every right matrix element has the identical explicit settling time, without
    a commutation hypothesis. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_constantInput_matrixElement_abs_le_epsilon_after_exponentialTracking_fullGap_right
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i) (hδpos : 0 < δ) (t₀ : ℝ)
    (A : E →L[ℝ] E) (U : ℝ → (E →L[ℝ] E))
    (F_lim : E →L[ℝ] E) (x y : E)
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U (U r * (-orthonormalDiagonalOperator b a) + F_lim) r)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ t : ℝ,
      t₀ + max 0
          (Real.log
            ((‖A - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim‖ *
                ‖x‖ * ‖y‖) / ε) / δ) ≤ t →
        |inner ℝ x
          ((U t - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim) y)| ≤ ε := by
  refine realFunction_abs_le_epsilon_after_exponentialBound
    δ ε
      (‖A - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim‖ * ‖x‖ * ‖y‖)
      t₀ hδpos hε ?_
      (fun t : ℝ => inner ℝ x
        ((U t - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim) y)) ?_
  · positivity
  · intro t ht
    have hmatrix :=
      orthonormalDiagonalHamiltonianSemigroup_operator_constantInput_matrixElement_exponentialTracking_fullGap_right
        b a δ hδ hδpos t₀ t ht A U F_lim x y hU0 hU
    calc
      |inner ℝ x
          ((U t - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim) y)| ≤
          (‖A - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim‖ *
            Real.exp (-((t - t₀) * δ))) * ‖x‖ * ‖y‖ := hmatrix
      _ = (‖A - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim‖ *
            ‖x‖ * ‖y‖) * Real.exp (-((t - t₀) * δ)) := by ring

end

end MathlibAnalytic
end MGAP4D
