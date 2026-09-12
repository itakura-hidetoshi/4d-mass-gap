import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianSemigroupOperatorDuhamelAsymptoticallyConstantInputExponentialTrackingEnvelopeScalar

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Resonant left tracking is controlled by a single exponential with rate `δ / 2`. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_exponentialTrackingEnvelope_resonant_left
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E)
    (a : ι → ℝ)
    (δ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i)
    (hδpos : 0 < δ)
    (t₀ t : ℝ)
    (ht : t₀ ≤ t)
    (A : E →L[ℝ] E)
    (F U : ℝ → (E →L[ℝ] E))
    (F_lim : E →L[ℝ] E)
    (C : ℝ)
    (hC : 0 ≤ C)
    (hF : Continuous F)
    (hFC : ∀ s ∈ Set.Icc t₀ t,
      ‖F s - F_lim‖ ≤ C * Real.exp (-((s - t₀) * δ)))
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U ((-orthonormalDiagonalOperator b a) * U r + F r) r) :
    ‖U t - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim‖ ≤
      (‖A - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim‖ +
          2 * C / δ) *
        Real.exp (-((t - t₀) * (δ / 2))) := by
  let S := orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim
  have hclosed :=
    orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_exponentialTrackingRate_resonant_left
      b a δ hδ hδpos t₀ t ht A F U F_lim C hF hFC hU0 hU
  have hτ : 0 ≤ t - t₀ := sub_nonneg.mpr ht
  have hexp :
      Real.exp (-((t - t₀) * δ)) ≤
        Real.exp (-((t - t₀) * (δ / 2))) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hinitial :
      Real.exp (-((t - t₀) * δ)) * ‖A - S‖ ≤
        Real.exp (-((t - t₀) * (δ / 2))) * ‖A - S‖ :=
    mul_le_mul_of_nonneg_right hexp (norm_nonneg _)
  have hlinear :=
    mul_exp_tail_le_two_div_mul_exp_half_rate δ (t - t₀) hδpos hτ
  have hforcing :
      ((t - t₀) * Real.exp (-((t - t₀) * δ))) * C ≤
        ((2 / δ) * Real.exp (-((t - t₀) * (δ / 2)))) * C :=
    mul_le_mul_of_nonneg_right hlinear hC
  calc
    ‖U t - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim‖ ≤
        Real.exp (-((t - t₀) * δ)) *
            ‖A - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim‖ +
          ((t - t₀) * Real.exp (-((t - t₀) * δ))) * C := hclosed
    _ ≤ Real.exp (-((t - t₀) * (δ / 2))) * ‖A - S‖ +
          ((2 / δ) * Real.exp (-((t - t₀) * (δ / 2)))) * C := by
      simpa [S] using add_le_add hinitial hforcing
    _ = (‖A - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim‖ +
          2 * C / δ) * Real.exp (-((t - t₀) * (δ / 2))) := by
      simp [S]
      field_simp [hδpos.ne']

/-- Resonant right tracking has the same half-rate envelope. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_exponentialTrackingEnvelope_resonant_right
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E)
    (a : ι → ℝ)
    (δ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i)
    (hδpos : 0 < δ)
    (t₀ t : ℝ)
    (ht : t₀ ≤ t)
    (A : E →L[ℝ] E)
    (F U : ℝ → (E →L[ℝ] E))
    (F_lim : E →L[ℝ] E)
    (C : ℝ)
    (hC : 0 ≤ C)
    (hF : Continuous F)
    (hFC : ∀ s ∈ Set.Icc t₀ t,
      ‖F s - F_lim‖ ≤ C * Real.exp (-((s - t₀) * δ)))
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U (U r * (-orthonormalDiagonalOperator b a) + F r) r) :
    ‖U t - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim‖ ≤
      (‖A - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim‖ +
          2 * C / δ) *
        Real.exp (-((t - t₀) * (δ / 2))) := by
  let S := orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim
  have hclosed :=
    orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_exponentialTrackingRate_resonant_right
      b a δ hδ hδpos t₀ t ht A F U F_lim C hF hFC hU0 hU
  have hτ : 0 ≤ t - t₀ := sub_nonneg.mpr ht
  have hexp :
      Real.exp (-((t - t₀) * δ)) ≤
        Real.exp (-((t - t₀) * (δ / 2))) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hinitial :
      Real.exp (-((t - t₀) * δ)) * ‖A - S‖ ≤
        Real.exp (-((t - t₀) * (δ / 2))) * ‖A - S‖ :=
    mul_le_mul_of_nonneg_right hexp (norm_nonneg _)
  have hlinear :=
    mul_exp_tail_le_two_div_mul_exp_half_rate δ (t - t₀) hδpos hτ
  have hforcing :
      ((t - t₀) * Real.exp (-((t - t₀) * δ))) * C ≤
        ((2 / δ) * Real.exp (-((t - t₀) * (δ / 2)))) * C :=
    mul_le_mul_of_nonneg_right hlinear hC
  calc
    ‖U t - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim‖ ≤
        Real.exp (-((t - t₀) * δ)) *
            ‖A - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim‖ +
          ((t - t₀) * Real.exp (-((t - t₀) * δ))) * C := hclosed
    _ ≤ Real.exp (-((t - t₀) * (δ / 2))) * ‖A - S‖ +
          ((2 / δ) * Real.exp (-((t - t₀) * (δ / 2)))) * C := by
      simpa [S] using add_le_add hinitial hforcing
    _ = (‖A - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim‖ +
          2 * C / δ) * Real.exp (-((t - t₀) * (δ / 2))) := by
      simp [S]
      field_simp [hδpos.ne']

end

end MathlibAnalytic
end MGAP4D
