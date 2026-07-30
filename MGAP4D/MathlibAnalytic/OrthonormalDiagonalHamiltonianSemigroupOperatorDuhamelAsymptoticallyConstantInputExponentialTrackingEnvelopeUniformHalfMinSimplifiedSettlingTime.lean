import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianSemigroupOperatorDuhamelAsymptoticallyConstantInputExponentialTrackingEnvelopeUniformHalfMinSimplified

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Simplified half-min left tracking has an explicit logarithmic settling time. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_norm_sub_le_epsilon_after_exponentialTrackingEnvelope_uniform_halfMin_simplified_left
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ μ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i) (hδpos : 0 < δ) (hμpos : 0 < μ) (t₀ : ℝ)
    (A : E →L[ℝ] E) (F U : ℝ → (E →L[ℝ] E))
    (F_lim : E →L[ℝ] E) (C : ℝ) (hC : 0 ≤ C) (hF : Continuous F)
    (hFC : ∀ s : ℝ, t₀ ≤ s →
      ‖F s - F_lim‖ ≤ C * Real.exp (-((s - t₀) * μ)))
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U ((-orthonormalDiagonalOperator b a) * U r + F r) r)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ t : ℝ,
      t₀ + max 0
          (Real.log
            ((‖A - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim‖ +
                2 * C / max δ μ) / ε) / (min δ μ / 2)) ≤ t →
        ‖U t - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim‖ ≤ ε := by
  intro t ht
  let S := orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim
  let ν := min δ μ / 2
  let K := ‖A - S‖ + 2 * C / max δ μ
  have hminpos : 0 < min δ μ := lt_min hδpos hμpos
  have hνpos : 0 < ν := div_pos hminpos (by norm_num)
  have hmaxpos : 0 < max δ μ := lt_of_lt_of_le hδpos (le_max_left δ μ)
  have hKnonneg : 0 ≤ K := by
    dsimp [K]
    exact add_nonneg (norm_nonneg _) (div_nonneg (mul_nonneg (by norm_num) hC) hmaxpos.le)
  have ht₀ : t₀ ≤ t := by
    have : 0 ≤ max 0 (Real.log (K / ε) / ν) := le_max_left _ _
    simpa [S, K, ν] using show t₀ ≤ t from by linarith
  have henv :=
    orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_exponentialTrackingEnvelope_uniform_halfMin_simplified_left
      b a δ μ hδ hδpos hμpos t₀ t ht₀ A F U F_lim C hC hF
      (by intro s hs; exact hFC s hs.1) hU0 hU
  by_cases hK : K = 0
  · have hzero : ‖U t - S‖ ≤ 0 := by simpa [S, K, hK, ν] using henv
    simpa [S] using hzero.trans hε.le
  · have hKpos : 0 < K := lt_of_le_of_ne hKnonneg (Ne.symm hK)
    have hwait : Real.log (K / ε) / ν ≤ t - t₀ := by
      have hmaxle : max 0 (Real.log (K / ε) / ν) ≤ t - t₀ := by
        simpa [S, K, ν] using show max 0
          (Real.log
            ((‖A - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim‖ +
                2 * C / max δ μ) / ε) / (min δ μ / 2)) ≤ t - t₀ from by linarith
      exact (le_max_right _ _).trans hmaxle
    have hdecay := exp_neg_mul_mul_le_of_log_div_div_le ν ε K (t - t₀) hνpos hε hKpos hwait
    calc
      ‖U t - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim‖ ≤ K * Real.exp (-((t - t₀) * ν)) := by simpa [S, K, ν] using henv
      _ ≤ ε := by simpa [mul_comm] using hdecay

/-- Simplified half-min right tracking has the identical settling time. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_norm_sub_le_epsilon_after_exponentialTrackingEnvelope_uniform_halfMin_simplified_right
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ μ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i) (hδpos : 0 < δ) (hμpos : 0 < μ) (t₀ : ℝ)
    (A : E →L[ℝ] E) (F U : ℝ → (E →L[ℝ] E))
    (F_lim : E →L[ℝ] E) (C : ℝ) (hC : 0 ≤ C) (hF : Continuous F)
    (hFC : ∀ s : ℝ, t₀ ≤ s →
      ‖F s - F_lim‖ ≤ C * Real.exp (-((s - t₀) * μ)))
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U (U r * (-orthonormalDiagonalOperator b a) + F r) r)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ t : ℝ,
      t₀ + max 0
          (Real.log
            ((‖A - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim‖ +
                2 * C / max δ μ) / ε) / (min δ μ / 2)) ≤ t →
        ‖U t - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim‖ ≤ ε := by
  intro t ht
  let S := orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim
  let ν := min δ μ / 2
  let K := ‖A - S‖ + 2 * C / max δ μ
  have hminpos : 0 < min δ μ := lt_min hδpos hμpos
  have hνpos : 0 < ν := div_pos hminpos (by norm_num)
  have hmaxpos : 0 < max δ μ := lt_of_lt_of_le hδpos (le_max_left δ μ)
  have hKnonneg : 0 ≤ K := by
    dsimp [K]
    exact add_nonneg (norm_nonneg _) (div_nonneg (mul_nonneg (by norm_num) hC) hmaxpos.le)
  have ht₀ : t₀ ≤ t := by
    have : 0 ≤ max 0 (Real.log (K / ε) / ν) := le_max_left _ _
    simpa [S, K, ν] using show t₀ ≤ t from by linarith
  have henv :=
    orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_exponentialTrackingEnvelope_uniform_halfMin_simplified_right
      b a δ μ hδ hδpos hμpos t₀ t ht₀ A F U F_lim C hC hF
      (by intro s hs; exact hFC s hs.1) hU0 hU
  by_cases hK : K = 0
  · have hzero : ‖U t - S‖ ≤ 0 := by simpa [S, K, hK, ν] using henv
    simpa [S] using hzero.trans hε.le
  · have hKpos : 0 < K := lt_of_le_of_ne hKnonneg (Ne.symm hK)
    have hwait : Real.log (K / ε) / ν ≤ t - t₀ := by
      have hmaxle : max 0 (Real.log (K / ε) / ν) ≤ t - t₀ := by
        simpa [S, K, ν] using show max 0
          (Real.log
            ((‖A - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim‖ +
                2 * C / max δ μ) / ε) / (min δ μ / 2)) ≤ t - t₀ from by linarith
      exact (le_max_right _ _).trans hmaxle
    have hdecay := exp_neg_mul_mul_le_of_log_div_div_le ν ε K (t - t₀) hνpos hε hKpos hwait
    calc
      ‖U t - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim‖ ≤ K * Real.exp (-((t - t₀) * ν)) := by simpa [S, K, ν] using henv
      _ ≤ ε := by simpa [mul_comm] using hdecay

end

end MathlibAnalytic
end MGAP4D
