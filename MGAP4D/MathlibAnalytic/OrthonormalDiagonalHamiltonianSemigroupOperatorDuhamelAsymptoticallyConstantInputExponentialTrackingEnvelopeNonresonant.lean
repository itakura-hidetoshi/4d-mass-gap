import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianSemigroupOperatorDuhamelAsymptoticallyConstantInputExponentialTrackingEnvelopeScalar

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Non-resonant left tracking is controlled by one exponential with rate
`min δ μ`. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_exponentialTrackingEnvelope_nonresonant_left
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E)
    (a : ι → ℝ)
    (δ μ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i)
    (hδpos : 0 < δ)
    (hμpos : 0 < μ)
    (hδμ : δ ≠ μ)
    (t₀ t : ℝ)
    (ht : t₀ ≤ t)
    (A : E →L[ℝ] E)
    (F U : ℝ → (E →L[ℝ] E))
    (F_lim : E →L[ℝ] E)
    (C : ℝ)
    (hC : 0 ≤ C)
    (hF : Continuous F)
    (hFC : ∀ s ∈ Set.Icc t₀ t,
      ‖F s - F_lim‖ ≤ C * Real.exp (-((s - t₀) * μ)))
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U ((-orthonormalDiagonalOperator b a) * U r + F r) r) :
    ‖U t - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim‖ ≤
      (‖A - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim‖ +
          C / |δ - μ|) *
        Real.exp (-((t - t₀) * min δ μ)) := by
  let S := orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim
  have hclosed :=
    orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_exponentialTrackingRate_nonresonant_left
      b a δ μ hδ hδpos hδμ t₀ t ht A F U F_lim C hF hFC hU0 hU
  have hτ : 0 ≤ t - t₀ := sub_nonneg.mpr ht
  have hratepos : 0 < min δ μ := lt_min hδpos hμpos
  have hexp :
      Real.exp (-((t - t₀) * δ)) ≤
        Real.exp (-((t - t₀) * min δ μ)) := by
    apply Real.exp_le_exp.mpr
    have hmin : min δ μ ≤ δ := min_le_left _ _
    nlinarith [hratepos]
  have hinitial :
      Real.exp (-((t - t₀) * δ)) * ‖A - S‖ ≤
        Real.exp (-((t - t₀) * min δ μ)) * ‖A - S‖ :=
    mul_le_mul_of_nonneg_right hexp (norm_nonneg _)
  have hforcing :=
    exp_tail_difference_quotient_mul_le_single_rate
      δ μ C (t - t₀) hδμ hC
  calc
    ‖U t - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim‖ ≤
        Real.exp (-((t - t₀) * δ)) *
            ‖A - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim‖ +
          ((Real.exp (-((t - t₀) * μ)) -
              Real.exp (-((t - t₀) * δ))) / (δ - μ)) * C := hclosed
    _ ≤ Real.exp (-((t - t₀) * min δ μ)) * ‖A - S‖ +
          (C / |δ - μ|) * Real.exp (-((t - t₀) * min δ μ)) := by
      simpa [S] using add_le_add hinitial hforcing
    _ = (‖A - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim‖ +
          C / |δ - μ|) * Real.exp (-((t - t₀) * min δ μ)) := by
      simp [S]
      ring

/-- Non-resonant right tracking has the same single-rate envelope, without a
commutation hypothesis. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_exponentialTrackingEnvelope_nonresonant_right
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E)
    (a : ι → ℝ)
    (δ μ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i)
    (hδpos : 0 < δ)
    (hμpos : 0 < μ)
    (hδμ : δ ≠ μ)
    (t₀ t : ℝ)
    (ht : t₀ ≤ t)
    (A : E →L[ℝ] E)
    (F U : ℝ → (E →L[ℝ] E))
    (F_lim : E →L[ℝ] E)
    (C : ℝ)
    (hC : 0 ≤ C)
    (hF : Continuous F)
    (hFC : ∀ s ∈ Set.Icc t₀ t,
      ‖F s - F_lim‖ ≤ C * Real.exp (-((s - t₀) * μ)))
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U (U r * (-orthonormalDiagonalOperator b a) + F r) r) :
    ‖U t - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim‖ ≤
      (‖A - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim‖ +
          C / |δ - μ|) *
        Real.exp (-((t - t₀) * min δ μ)) := by
  let S := orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim
  have hclosed :=
    orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_exponentialTrackingRate_nonresonant_right
      b a δ μ hδ hδpos hδμ t₀ t ht A F U F_lim C hF hFC hU0 hU
  have hτ : 0 ≤ t - t₀ := sub_nonneg.mpr ht
  have hratepos : 0 < min δ μ := lt_min hδpos hμpos
  have hexp :
      Real.exp (-((t - t₀) * δ)) ≤
        Real.exp (-((t - t₀) * min δ μ)) := by
    apply Real.exp_le_exp.mpr
    have hmin : min δ μ ≤ δ := min_le_left _ _
    nlinarith [hratepos]
  have hinitial :
      Real.exp (-((t - t₀) * δ)) * ‖A - S‖ ≤
        Real.exp (-((t - t₀) * min δ μ)) * ‖A - S‖ :=
    mul_le_mul_of_nonneg_right hexp (norm_nonneg _)
  have hforcing :=
    exp_tail_difference_quotient_mul_le_single_rate
      δ μ C (t - t₀) hδμ hC
  calc
    ‖U t - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim‖ ≤
        Real.exp (-((t - t₀) * δ)) *
            ‖A - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim‖ +
          ((Real.exp (-((t - t₀) * μ)) -
              Real.exp (-((t - t₀) * δ))) / (δ - μ)) * C := hclosed
    _ ≤ Real.exp (-((t - t₀) * min δ μ)) * ‖A - S‖ +
          (C / |δ - μ|) * Real.exp (-((t - t₀) * min δ μ)) := by
      simpa [S] using add_le_add hinitial hforcing
    _ = (‖A - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim‖ +
          C / |δ - μ|) * Real.exp (-((t - t₀) * min δ μ)) := by
      simp [S]
      ring

end

end MathlibAnalytic
end MGAP4D
