import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianSemigroupOperatorDuhamelAsymptoticallyConstantInputExponentialTrackingEnvelopeUniformHalfMinSimplified

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- When the forcing tail decays at least as fast as the spectral gap, left tracking
has the canonical half-gap rate and forcing constant `2 * C / μ`. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_exponentialTrackingEnvelope_fastForcing_halfGap_left
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ μ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i) (hδpos : 0 < δ) (hδμ : δ ≤ μ)
    (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A : E →L[ℝ] E) (F U : ℝ → (E →L[ℝ] E))
    (F_lim : E →L[ℝ] E) (C : ℝ) (hC : 0 ≤ C) (hF : Continuous F)
    (hFC : ∀ s ∈ Set.Icc t₀ t,
      ‖F s - F_lim‖ ≤ C * Real.exp (-((s - t₀) * μ)))
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U ((-orthonormalDiagonalOperator b a) * U r + F r) r) :
    ‖U t - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim‖ ≤
      (‖A - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim‖ +
          2 * C / μ) *
        Real.exp (-((t - t₀) * (δ / 2))) := by
  have hμpos : 0 < μ := lt_of_lt_of_le hδpos hδμ
  simpa [min_eq_left hδμ, max_eq_right hδμ] using
    orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_exponentialTrackingEnvelope_uniform_halfMin_simplified_left
      b a δ μ hδ hδpos hμpos t₀ t ht A F U F_lim C hC hF hFC hU0 hU

/-- The corresponding right evolution has the same half-gap estimate and needs no
commutation hypothesis. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_exponentialTrackingEnvelope_fastForcing_halfGap_right
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ μ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i) (hδpos : 0 < δ) (hδμ : δ ≤ μ)
    (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A : E →L[ℝ] E) (F U : ℝ → (E →L[ℝ] E))
    (F_lim : E →L[ℝ] E) (C : ℝ) (hC : 0 ≤ C) (hF : Continuous F)
    (hFC : ∀ s ∈ Set.Icc t₀ t,
      ‖F s - F_lim‖ ≤ C * Real.exp (-((s - t₀) * μ)))
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U (U r * (-orthonormalDiagonalOperator b a) + F r) r) :
    ‖U t - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim‖ ≤
      (‖A - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim‖ +
          2 * C / μ) *
        Real.exp (-((t - t₀) * (δ / 2))) := by
  have hμpos : 0 < μ := lt_of_lt_of_le hδpos hδμ
  simpa [min_eq_left hδμ, max_eq_right hδμ] using
    orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_exponentialTrackingEnvelope_uniform_halfMin_simplified_right
      b a δ μ hδ hδpos hμpos t₀ t ht A F U F_lim C hC hF hFC hU0 hU

end

end MathlibAnalytic
end MGAP4D