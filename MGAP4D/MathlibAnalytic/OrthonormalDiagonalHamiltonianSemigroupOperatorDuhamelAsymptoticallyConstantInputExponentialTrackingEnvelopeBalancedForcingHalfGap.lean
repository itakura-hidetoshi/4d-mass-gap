import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianSemigroupOperatorDuhamelAsymptoticallyConstantInputExponentialTrackingEnvelopeFastForcingHalfGap

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- At the balanced forcing rate `μ = δ`, left tracking has half-gap decay and
forcing constant `2 * C / δ`. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_exponentialTrackingEnvelope_balancedForcing_halfGap_left
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i) (hδpos : 0 < δ)
    (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A : E →L[ℝ] E) (F U : ℝ → (E →L[ℝ] E))
    (F_lim : E →L[ℝ] E) (C : ℝ) (hC : 0 ≤ C) (hF : Continuous F)
    (hFC : ∀ s ∈ Set.Icc t₀ t,
      ‖F s - F_lim‖ ≤ C * Real.exp (-((s - t₀) * δ)))
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U ((-orthonormalDiagonalOperator b a) * U r + F r) r) :
    ‖U t - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim‖ ≤
      (‖A - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim‖ +
          2 * C / δ) *
        Real.exp (-((t - t₀) * (δ / 2))) := by
  simpa using
    orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_exponentialTrackingEnvelope_fastForcing_halfGap_left
      b a δ δ hδ hδpos le_rfl t₀ t ht A F U F_lim C hC hF hFC hU0 hU

/-- At the balanced forcing rate, the right evolution has the same estimate
without a commutation hypothesis. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_exponentialTrackingEnvelope_balancedForcing_halfGap_right
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i) (hδpos : 0 < δ)
    (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A : E →L[ℝ] E) (F U : ℝ → (E →L[ℝ] E))
    (F_lim : E →L[ℝ] E) (C : ℝ) (hC : 0 ≤ C) (hF : Continuous F)
    (hFC : ∀ s ∈ Set.Icc t₀ t,
      ‖F s - F_lim‖ ≤ C * Real.exp (-((s - t₀) * δ)))
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U (U r * (-orthonormalDiagonalOperator b a) + F r) r) :
    ‖U t - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim‖ ≤
      (‖A - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim‖ +
          2 * C / δ) *
        Real.exp (-((t - t₀) * (δ / 2))) := by
  simpa using
    orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_exponentialTrackingEnvelope_fastForcing_halfGap_right
      b a δ δ hδ hδpos le_rfl t₀ t ht A F U F_lim C hC hF hFC hU0 hU

end

end MathlibAnalytic
end MGAP4D
