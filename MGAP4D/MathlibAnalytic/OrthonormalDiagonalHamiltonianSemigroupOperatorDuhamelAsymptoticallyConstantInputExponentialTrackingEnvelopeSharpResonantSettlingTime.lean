import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianSemigroupOperatorDuhamelAsymptoticallyConstantInputExponentialTrackingEnvelopeSharpResonant

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The sharp resonant left envelope yields an explicit logarithmic tracking time. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_norm_sub_le_epsilon_after_exponentialTrackingEnvelope_sharp_resonant_left
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i) (hδpos : 0 < δ) (t₀ : ℝ)
    (A : E →L[ℝ] E) (F U : ℝ → (E →L[ℝ] E))
    (F_lim : E →L[ℝ] E) (C : ℝ) (hC : 0 ≤ C) (hF : Continuous F)
    (hFC : ∀ s : ℝ, t₀ ≤ s →
      ‖F s - F_lim‖ ≤ C * Real.exp (-((s - t₀) * δ)))
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U ((-orthonormalDiagonalOperator b a) * U r + F r) r)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ t : ℝ,
      t₀ + max 0
          (Real.log
            ((‖A - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim‖ +
                2 * C / (Real.exp 1 * δ)) / ε) / (δ / 2)) ≤ t →
        ‖U t - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim‖ ≤ ε := by
  intro t ht
  let S := orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim
  let K := ‖A - S‖ + 2 * C / (Real.exp 1 * δ)
  have hratepos : 0 < δ / 2 := by linarith
  have hdenpos : 0 < Real.exp 1 * δ := mul_pos (Real.exp_pos _) hδpos
  have hKnonneg : 0 ≤ K := by
    dsimp [K]
    exact add_nonneg (norm_nonneg _)
      (div_nonneg (mul_nonneg (by norm_num) hC) hdenpos.le)
  have hwait_nonneg : 0 ≤ max 0 (Real.log (K / ε) / (δ / 2)) :=
    le_max_left _ _
  have ht₀ : t₀ ≤ t := by
    simpa [S, K] using show t₀ ≤ t from by linarith
  have henv :=
    orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_exponentialTrackingEnvelope_sharp_resonant_left
      b a δ hδ hδpos t₀ t ht₀ A F U F_lim C hC hF
      (by
        intro s hs
        exact hFC s hs.1)
      hU0 hU
  by_cases hK : K = 0
  · have hzero : ‖U t - S‖ ≤ 0 := by
      simpa [S, K, hK] using henv
    simpa [S] using hzero.trans hε.le
  · have hKpos : 0 < K := lt_of_le_of_ne hKnonneg (Ne.symm hK)
    have hwait_le : max 0 (Real.log (K / ε) / (δ / 2)) ≤ t - t₀ := by
      simpa [S, K] using show max 0
        (Real.log
          ((‖A - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim‖ +
              2 * C / (Real.exp 1 * δ)) / ε) / (δ / 2)) ≤ t - t₀ from by
            linarith
    have htime : Real.log (K / ε) / (δ / 2) ≤ t - t₀ :=
      (le_max_right _ _).trans hwait_le
    have hdecay :
        Real.exp (-((t - t₀) * (δ / 2))) * K ≤ ε :=
      exp_neg_mul_mul_le_of_log_div_div_le
        (δ / 2) ε K (t - t₀) hratepos hε hKpos htime
    calc
      ‖U t - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim‖ ≤
          K * Real.exp (-((t - t₀) * (δ / 2))) := by
        simpa [S, K] using henv
      _ ≤ ε := by simpa [mul_comm] using hdecay

/-- The sharp resonant right envelope has the identical explicit tracking time. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_norm_sub_le_epsilon_after_exponentialTrackingEnvelope_sharp_resonant_right
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i) (hδpos : 0 < δ) (t₀ : ℝ)
    (A : E →L[ℝ] E) (F U : ℝ → (E →L[ℝ] E))
    (F_lim : E →L[ℝ] E) (C : ℝ) (hC : 0 ≤ C) (hF : Continuous F)
    (hFC : ∀ s : ℝ, t₀ ≤ s →
      ‖F s - F_lim‖ ≤ C * Real.exp (-((s - t₀) * δ)))
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U (U r * (-orthonormalDiagonalOperator b a) + F r) r)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ t : ℝ,
      t₀ + max 0
          (Real.log
            ((‖A - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim‖ +
                2 * C / (Real.exp 1 * δ)) / ε) / (δ / 2)) ≤ t →
        ‖U t - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim‖ ≤ ε := by
  intro t ht
  let S := orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim
  let K := ‖A - S‖ + 2 * C / (Real.exp 1 * δ)
  have hratepos : 0 < δ / 2 := by linarith
  have hdenpos : 0 < Real.exp 1 * δ := mul_pos (Real.exp_pos _) hδpos
  have hKnonneg : 0 ≤ K := by
    dsimp [K]
    exact add_nonneg (norm_nonneg _)
      (div_nonneg (mul_nonneg (by norm_num) hC) hdenpos.le)
  have hwait_nonneg : 0 ≤ max 0 (Real.log (K / ε) / (δ / 2)) :=
    le_max_left _ _
  have ht₀ : t₀ ≤ t := by
    simpa [S, K] using show t₀ ≤ t from by linarith
  have henv :=
    orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_exponentialTrackingEnvelope_sharp_resonant_right
      b a δ hδ hδpos t₀ t ht₀ A F U F_lim C hC hF
      (by
        intro s hs
        exact hFC s hs.1)
      hU0 hU
  by_cases hK : K = 0
  · have hzero : ‖U t - S‖ ≤ 0 := by
      simpa [S, K, hK] using henv
    simpa [S] using hzero.trans hε.le
  · have hKpos : 0 < K := lt_of_le_of_ne hKnonneg (Ne.symm hK)
    have hwait_le : max 0 (Real.log (K / ε) / (δ / 2)) ≤ t - t₀ := by
      simpa [S, K] using show max 0
        (Real.log
          ((‖A - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim‖ +
              2 * C / (Real.exp 1 * δ)) / ε) / (δ / 2)) ≤ t - t₀ from by
            linarith
    have htime : Real.log (K / ε) / (δ / 2) ≤ t - t₀ :=
      (le_max_right _ _).trans hwait_le
    have hdecay :
        Real.exp (-((t - t₀) * (δ / 2))) * K ≤ ε :=
      exp_neg_mul_mul_le_of_log_div_div_le
        (δ / 2) ε K (t - t₀) hratepos hε hKpos htime
    calc
      ‖U t - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim‖ ≤
          K * Real.exp (-((t - t₀) * (δ / 2))) := by
        simpa [S, K] using henv
      _ ≤ ε := by simpa [mul_comm] using hdecay

end

end MathlibAnalytic
end MGAP4D
