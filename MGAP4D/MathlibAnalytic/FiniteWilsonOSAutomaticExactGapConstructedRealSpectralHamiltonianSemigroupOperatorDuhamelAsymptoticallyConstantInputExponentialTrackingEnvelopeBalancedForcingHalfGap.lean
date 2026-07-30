import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedRealSpectralHamiltonianSemigroupOperatorDuhamelAsymptoticallyConstantInputExponentialTrackingEnvelopeFastForcingHalfGap

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Constructed finite Wilson left tracking when the forcing decays exactly at
the spectral gap. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_exponentialTrackingEnvelope_balancedForcing_halfGap_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A : D.StateSpace →L[ℝ] D.StateSpace)
    (F U : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (F_lim : D.StateSpace →L[ℝ] D.StateSpace) (C : ℝ) (hC : 0 ≤ C)
    (hF : Continuous F)
    (hFC : ∀ s ∈ Set.Icc t₀ t,
      ‖F s - F_lim‖ ≤ C * Real.exp (-((s - t₀) * exactGapValueReal)))
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U
        ((-LinearMap.toContinuousLinearMap (D.hamiltonian n)) * U r + F r) r) :
    ‖U t - finiteWilsonConstructedHamiltonianLeftSteadyState D n F_lim‖ ≤
      (‖A - finiteWilsonConstructedHamiltonianLeftSteadyState D n F_lim‖ +
          2 * C / exactGapValueReal) *
        Real.exp (-((t - t₀) * (exactGapValueReal / 2))) := by
  simpa using
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_exponentialTrackingEnvelope_fastForcing_halfGap_left
      D n exactGapValueReal le_rfl t₀ t ht A F U F_lim C hC hF hFC hU0 hU

/-- Constructed finite Wilson right tracking has the same balanced-forcing estimate. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_exponentialTrackingEnvelope_balancedForcing_halfGap_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A : D.StateSpace →L[ℝ] D.StateSpace)
    (F U : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (F_lim : D.StateSpace →L[ℝ] D.StateSpace) (C : ℝ) (hC : 0 ≤ C)
    (hF : Continuous F)
    (hFC : ∀ s ∈ Set.Icc t₀ t,
      ‖F s - F_lim‖ ≤ C * Real.exp (-((s - t₀) * exactGapValueReal)))
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U
        (U r * (-LinearMap.toContinuousLinearMap (D.hamiltonian n)) + F r) r) :
    ‖U t - finiteWilsonConstructedHamiltonianRightSteadyState D n F_lim‖ ≤
      (‖A - finiteWilsonConstructedHamiltonianRightSteadyState D n F_lim‖ +
          2 * C / exactGapValueReal) *
        Real.exp (-((t - t₀) * (exactGapValueReal / 2))) := by
  simpa using
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_exponentialTrackingEnvelope_fastForcing_halfGap_right
      D n exactGapValueReal le_rfl t₀ t ht A F U F_lim C hC hF hFC hU0 hU

end

end MathlibAnalytic
end MGAP4D
