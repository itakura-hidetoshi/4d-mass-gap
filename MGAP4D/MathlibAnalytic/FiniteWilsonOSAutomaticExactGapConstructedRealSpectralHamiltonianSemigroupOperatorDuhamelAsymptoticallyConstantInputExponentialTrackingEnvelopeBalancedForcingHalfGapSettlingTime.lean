import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedRealSpectralHamiltonianSemigroupOperatorDuhamelAsymptoticallyConstantInputExponentialTrackingEnvelopeBalancedForcingHalfGap
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedRealSpectralHamiltonianSemigroupOperatorDuhamelAsymptoticallyConstantInputExponentialTrackingEnvelopeFastForcingHalfGapSettlingTime

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Constructed finite Wilson balanced-forcing left tracking has an explicit
half-gap settling time. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_norm_sub_le_epsilon_after_exponentialTrackingEnvelope_balancedForcing_halfGap_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (t₀ : ℝ)
    (A : D.StateSpace →L[ℝ] D.StateSpace)
    (F U : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (F_lim : D.StateSpace →L[ℝ] D.StateSpace) (C : ℝ) (hC : 0 ≤ C)
    (hF : Continuous F)
    (hFC : ∀ s : ℝ, t₀ ≤ s →
      ‖F s - F_lim‖ ≤ C * Real.exp (-((s - t₀) * exactGapValueReal)))
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U
        ((-LinearMap.toContinuousLinearMap (D.hamiltonian n)) * U r + F r) r)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ t : ℝ,
      t₀ + max 0
          (Real.log
            ((‖A - finiteWilsonConstructedHamiltonianLeftSteadyState D n F_lim‖ +
                2 * C / exactGapValueReal) / ε) / (exactGapValueReal / 2)) ≤ t →
        ‖U t - finiteWilsonConstructedHamiltonianLeftSteadyState D n F_lim‖ ≤ ε := by
  simpa using
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_norm_sub_le_epsilon_after_exponentialTrackingEnvelope_fastForcing_halfGap_left
      D n exactGapValueReal le_rfl t₀ A F U F_lim C hC hF hFC hU0 hU ε hε

/-- Constructed finite Wilson balanced-forcing right tracking has the same
explicit settling time. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_norm_sub_le_epsilon_after_exponentialTrackingEnvelope_balancedForcing_halfGap_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (t₀ : ℝ)
    (A : D.StateSpace →L[ℝ] D.StateSpace)
    (F U : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (F_lim : D.StateSpace →L[ℝ] D.StateSpace) (C : ℝ) (hC : 0 ≤ C)
    (hF : Continuous F)
    (hFC : ∀ s : ℝ, t₀ ≤ s →
      ‖F s - F_lim‖ ≤ C * Real.exp (-((s - t₀) * exactGapValueReal)))
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U
        (U r * (-LinearMap.toContinuousLinearMap (D.hamiltonian n)) + F r) r)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ t : ℝ,
      t₀ + max 0
          (Real.log
            ((‖A - finiteWilsonConstructedHamiltonianRightSteadyState D n F_lim‖ +
                2 * C / exactGapValueReal) / ε) / (exactGapValueReal / 2)) ≤ t →
        ‖U t - finiteWilsonConstructedHamiltonianRightSteadyState D n F_lim‖ ≤ ε := by
  simpa using
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_norm_sub_le_epsilon_after_exponentialTrackingEnvelope_fastForcing_halfGap_right
      D n exactGapValueReal le_rfl t₀ A F U F_lim C hC hF hFC hU0 hU ε hε

end

end MathlibAnalytic
end MGAP4D
