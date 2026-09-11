import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedRealSpectralHamiltonianSemigroupOperatorDuhamelAsymptoticallyConstantInputExponentialTrackingEnvelopeBalancedForcingHalfGapSettlingTime
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapVacuumOrthogonalRealSpectralHamiltonianSemigroupOperatorDuhamelAsymptoticallyConstantInputExponentialTrackingEnvelopeBalancedForcingHalfGap
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapVacuumOrthogonalRealSpectralHamiltonianSemigroupOperatorDuhamelAsymptoticallyConstantInputExponentialTrackingEnvelopeFastForcingHalfGapSettlingTime

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- On `Ω⊥`, balanced-forcing left tracking has an explicit half-gap settling time. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_norm_sub_le_epsilon_after_exponentialTrackingEnvelope_balancedForcing_halfGap_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) (t₀ : ℝ)
    (A : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
    (F U : ℝ → (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
    (F_lim : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
    (C : ℝ) (hC : 0 ≤ C) (hF : Continuous F)
    (hFC : ∀ s : ℝ, t₀ ≤ s →
      ‖F s - F_lim‖ ≤ C * Real.exp (-((s - t₀) * exactGapValueReal)))
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U ((-LinearMap.toContinuousLinearMap
        (D.gapData.restrictedHamiltonian n)) * U r + F r) r)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ t : ℝ,
      t₀ + max 0
          (Real.log
            ((‖A - finiteWilsonVacuumOrthogonalHamiltonianLeftSteadyState D n F_lim‖ +
                2 * C / exactGapValueReal) / ε) / (exactGapValueReal / 2)) ≤ t →
        ‖U t - finiteWilsonVacuumOrthogonalHamiltonianLeftSteadyState D n F_lim‖ ≤ ε := by
  simpa using
    finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_norm_sub_le_epsilon_after_exponentialTrackingEnvelope_fastForcing_halfGap_left
      D n exactGapValueReal le_rfl t₀ A F U F_lim C hC hF hFC hU0 hU ε hε

/-- On `Ω⊥`, balanced-forcing right tracking has the identical explicit settling time. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_norm_sub_le_epsilon_after_exponentialTrackingEnvelope_balancedForcing_halfGap_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) (t₀ : ℝ)
    (A : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
    (F U : ℝ → (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
    (F_lim : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
    (C : ℝ) (hC : 0 ≤ C) (hF : Continuous F)
    (hFC : ∀ s : ℝ, t₀ ≤ s →
      ‖F s - F_lim‖ ≤ C * Real.exp (-((s - t₀) * exactGapValueReal)))
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U (U r * (-LinearMap.toContinuousLinearMap
        (D.gapData.restrictedHamiltonian n)) + F r) r)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ t : ℝ,
      t₀ + max 0
          (Real.log
            ((‖A - finiteWilsonVacuumOrthogonalHamiltonianRightSteadyState D n F_lim‖ +
                2 * C / exactGapValueReal) / ε) / (exactGapValueReal / 2)) ≤ t →
        ‖U t - finiteWilsonVacuumOrthogonalHamiltonianRightSteadyState D n F_lim‖ ≤ ε := by
  simpa using
    finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_norm_sub_le_epsilon_after_exponentialTrackingEnvelope_fastForcing_halfGap_right
      D n exactGapValueReal le_rfl t₀ A F U F_lim C hC hF hFC hU0 hU ε hε

end

end MathlibAnalytic
end MGAP4D
