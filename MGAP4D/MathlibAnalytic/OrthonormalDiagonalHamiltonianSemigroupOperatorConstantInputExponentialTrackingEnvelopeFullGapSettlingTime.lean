import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianSemigroupOperatorConstantInputExponentialTrackingEnvelopeFullGap
import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianSemigroupOperatorDuhamelAsymptoticallyConstantInputExponentialTrackingEnvelopeUniformHalfMinSimplifiedSettlingTime

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Constant-input left tracking reaches every positive tolerance after an explicit
full-gap logarithmic waiting time. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_constantInput_norm_sub_le_epsilon_after_exponentialTrackingEnvelope_fullGap_left
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
        ‖U t - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim‖ ≤ ε := by
  intro t ht
  let S := orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim
  let K := ‖A - S‖
  have hKnonneg : 0 ≤ K := by simp [K]
  have hthreshold : t₀ + max 0 (Real.log (K / ε) / δ) ≤ t := by
    simpa [S, K] using ht
  have hwait_nonneg : 0 ≤ max 0 (Real.log (K / ε) / δ) := le_max_left _ _
  have ht₀ : t₀ ≤ t := by linarith
  have henv :=
    orthonormalDiagonalHamiltonianSemigroup_operator_constantInput_exponentialTrackingEnvelope_fullGap_left
      b a δ hδ hδpos t₀ t ht₀ A U F_lim hU0 hU
  by_cases hK : K = 0
  · have hzero : ‖U t - S‖ ≤ 0 := by simpa [S, K, hK] using henv
    simpa [S] using hzero.trans hε.le
  · have hKpos : 0 < K := lt_of_le_of_ne hKnonneg (Ne.symm hK)
    have hmaxle : max 0 (Real.log (K / ε) / δ) ≤ t - t₀ := by linarith
    have hwait : Real.log (K / ε) / δ ≤ t - t₀ :=
      (le_max_right _ _).trans hmaxle
    have hdecay :=
      exp_neg_mul_mul_le_of_log_div_div_le δ ε K (t - t₀)
        hδpos hε hKpos hwait
    calc
      ‖U t - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim‖ ≤
          K * Real.exp (-((t - t₀) * δ)) := by simpa [S, K] using henv
      _ ≤ ε := by simpa [mul_comm] using hdecay

/-- Constant-input right tracking has the identical full-gap waiting time. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_constantInput_norm_sub_le_epsilon_after_exponentialTrackingEnvelope_fullGap_right
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
        ‖U t - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim‖ ≤ ε := by
  intro t ht
  let S := orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim
  let K := ‖A - S‖
  have hKnonneg : 0 ≤ K := by simp [K]
  have hthreshold : t₀ + max 0 (Real.log (K / ε) / δ) ≤ t := by
    simpa [S, K] using ht
  have hwait_nonneg : 0 ≤ max 0 (Real.log (K / ε) / δ) := le_max_left _ _
  have ht₀ : t₀ ≤ t := by linarith
  have henv :=
    orthonormalDiagonalHamiltonianSemigroup_operator_constantInput_exponentialTrackingEnvelope_fullGap_right
      b a δ hδ hδpos t₀ t ht₀ A U F_lim hU0 hU
  by_cases hK : K = 0
  · have hzero : ‖U t - S‖ ≤ 0 := by simpa [S, K, hK] using henv
    simpa [S] using hzero.trans hε.le
  · have hKpos : 0 < K := lt_of_le_of_ne hKnonneg (Ne.symm hK)
    have hmaxle : max 0 (Real.log (K / ε) / δ) ≤ t - t₀ := by linarith
    have hwait : Real.log (K / ε) / δ ≤ t - t₀ :=
      (le_max_right _ _).trans hmaxle
    have hdecay :=
      exp_neg_mul_mul_le_of_log_div_div_le δ ε K (t - t₀)
        hδpos hε hKpos hwait
    calc
      ‖U t - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim‖ ≤
          K * Real.exp (-((t - t₀) * δ)) := by simpa [S, K] using henv
      _ ≤ ε := by simpa [mul_comm] using hdecay

end

end MathlibAnalytic
end MGAP4D
