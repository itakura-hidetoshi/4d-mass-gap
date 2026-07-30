import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianSemigroupOperatorConstantInputExponentialTrackingEnvelopeFullGap

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- With exactly constant input, the left tracking error acts pointwise with the
    full spectral-gap rate. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_constantInput_pointwise_exponentialTracking_fullGap_left
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i) (hδpos : 0 < δ)
    (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A : E →L[ℝ] E) (U : ℝ → (E →L[ℝ] E))
    (F_lim : E →L[ℝ] E) (y : E)
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U ((-orthonormalDiagonalOperator b a) * U r + F_lim) r) :
    ‖(U t - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim) y‖ ≤
      (‖A - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim‖ *
        Real.exp (-((t - t₀) * δ))) * ‖y‖ := by
  have henv :=
    orthonormalDiagonalHamiltonianSemigroup_operator_constantInput_exponentialTrackingEnvelope_fullGap_left
      b a δ hδ hδpos t₀ t ht A U F_lim hU0 hU
  calc
    ‖(U t - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim) y‖ ≤
        ‖U t - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim‖ * ‖y‖ :=
      (U t - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim).le_opNorm y
    _ ≤ (‖A - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim‖ *
          Real.exp (-((t - t₀) * δ))) * ‖y‖ :=
      mul_le_mul_of_nonneg_right henv (norm_nonneg y)

/-- With exactly constant input, the right tracking error has the same pointwise
    full-gap estimate and requires no commutation hypothesis. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_constantInput_pointwise_exponentialTracking_fullGap_right
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i) (hδpos : 0 < δ)
    (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A : E →L[ℝ] E) (U : ℝ → (E →L[ℝ] E))
    (F_lim : E →L[ℝ] E) (y : E)
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U (U r * (-orthonormalDiagonalOperator b a) + F_lim) r) :
    ‖(U t - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim) y‖ ≤
      (‖A - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim‖ *
        Real.exp (-((t - t₀) * δ))) * ‖y‖ := by
  have henv :=
    orthonormalDiagonalHamiltonianSemigroup_operator_constantInput_exponentialTrackingEnvelope_fullGap_right
      b a δ hδ hδpos t₀ t ht A U F_lim hU0 hU
  calc
    ‖(U t - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim) y‖ ≤
        ‖U t - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim‖ * ‖y‖ :=
      (U t - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim).le_opNorm y
    _ ≤ (‖A - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim‖ *
          Real.exp (-((t - t₀) * δ))) * ‖y‖ :=
      mul_le_mul_of_nonneg_right henv (norm_nonneg y)

end

end MathlibAnalytic
end MGAP4D
