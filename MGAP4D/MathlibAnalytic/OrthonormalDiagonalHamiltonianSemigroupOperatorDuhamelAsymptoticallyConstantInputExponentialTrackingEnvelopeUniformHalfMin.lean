import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianSemigroupOperatorDuhamelAsymptoticallyConstantInputExponentialTrackingEnvelopeUniformSubcritical

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Resonance-free left tracking at the canonical rate `min δ μ / 2`. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_exponentialTrackingEnvelope_uniform_halfMin_left
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ μ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i) (hδpos : 0 < δ) (hμpos : 0 < μ)
    (t₀ t : ℝ) (ht : t₀ ≤ t) (A : E →L[ℝ] E)
    (F U : ℝ → (E →L[ℝ] E)) (F_lim : E →L[ℝ] E)
    (C : ℝ) (hC : 0 ≤ C) (hF : Continuous F)
    (hFC : ∀ s ∈ Set.Icc t₀ t,
      ‖F s - F_lim‖ ≤ C * Real.exp (-((s - t₀) * μ)))
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U ((-orthonormalDiagonalOperator b a) * U r + F r) r) :
    ‖U t - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim‖ ≤
      (‖A - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim‖ +
          C / (max δ μ - min δ μ / 2)) *
        Real.exp (-((t - t₀) * (min δ μ / 2))) := by
  have hminpos : 0 < min δ μ := lt_min hδpos hμpos
  have hνpos : 0 < min δ μ / 2 := by linarith
  have hνδ : min δ μ / 2 < δ := by
    have hminδ : min δ μ ≤ δ := min_le_left _ _
    linarith
  have hνμ : min δ μ / 2 < μ := by
    have hminμ : min δ μ ≤ μ := min_le_right _ _
    linarith
  exact
    orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_exponentialTrackingEnvelope_uniform_subcritical_left
      b a δ μ (min δ μ / 2) hδ hδpos hνpos hνδ hνμ
      t₀ t ht A F U F_lim C hC hF hFC hU0 hU

/-- Resonance-free right tracking at the canonical rate `min δ μ / 2`. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_exponentialTrackingEnvelope_uniform_halfMin_right
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ μ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i) (hδpos : 0 < δ) (hμpos : 0 < μ)
    (t₀ t : ℝ) (ht : t₀ ≤ t) (A : E →L[ℝ] E)
    (F U : ℝ → (E →L[ℝ] E)) (F_lim : E →L[ℝ] E)
    (C : ℝ) (hC : 0 ≤ C) (hF : Continuous F)
    (hFC : ∀ s ∈ Set.Icc t₀ t,
      ‖F s - F_lim‖ ≤ C * Real.exp (-((s - t₀) * μ)))
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U (U r * (-orthonormalDiagonalOperator b a) + F r) r) :
    ‖U t - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim‖ ≤
      (‖A - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim‖ +
          C / (max δ μ - min δ μ / 2)) *
        Real.exp (-((t - t₀) * (min δ μ / 2))) := by
  have hminpos : 0 < min δ μ := lt_min hδpos hμpos
  have hνpos : 0 < min δ μ / 2 := by linarith
  have hνδ : min δ μ / 2 < δ := by
    have hminδ : min δ μ ≤ δ := min_le_left _ _
    linarith
  have hνμ : min δ μ / 2 < μ := by
    have hminμ : min δ μ ≤ μ := min_le_right _ _
    linarith
  exact
    orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_exponentialTrackingEnvelope_uniform_subcritical_right
      b a δ μ (min δ μ / 2) hδ hδpos hνpos hνδ hνμ
      t₀ t ht A F U F_lim C hC hF hFC hU0 hU

end

end MathlibAnalytic
end MGAP4D
