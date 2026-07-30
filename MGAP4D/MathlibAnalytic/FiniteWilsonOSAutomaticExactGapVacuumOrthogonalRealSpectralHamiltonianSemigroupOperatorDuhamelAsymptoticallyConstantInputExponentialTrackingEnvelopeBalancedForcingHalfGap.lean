import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedRealSpectralHamiltonianSemigroupOperatorDuhamelAsymptoticallyConstantInputExponentialTrackingEnvelopeBalancedForcingHalfGap
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapVacuumOrthogonalRealSpectralHamiltonianSemigroupOperatorDuhamelAsymptoticallyConstantInputExponentialTrackingEnvelopeFastForcingHalfGap

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- On `Ω⊥`, left tracking at a forcing rate equal to the exact gap has the
canonical half-gap estimate. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_exponentialTrackingEnvelope_balancedForcing_halfGap_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
    (F U : ℝ → (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
    (F_lim : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
    (C : ℝ) (hC : 0 ≤ C) (hF : Continuous F)
    (hFC : ∀ s ∈ Set.Icc t₀ t,
      ‖F s - F_lim‖ ≤ C * Real.exp (-((s - t₀) * exactGapValueReal)))
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U ((-LinearMap.toContinuousLinearMap
        (D.gapData.restrictedHamiltonian n)) * U r + F r) r) :
    ‖U t - finiteWilsonVacuumOrthogonalHamiltonianLeftSteadyState D n F_lim‖ ≤
      (‖A - finiteWilsonVacuumOrthogonalHamiltonianLeftSteadyState D n F_lim‖ +
          2 * C / exactGapValueReal) *
        Real.exp (-((t - t₀) * (exactGapValueReal / 2))) := by
  simpa using
    finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_exponentialTrackingEnvelope_fastForcing_halfGap_left
      D n exactGapValueReal le_rfl t₀ t ht A F U F_lim C hC hF hFC hU0 hU

/-- On `Ω⊥`, right tracking has the same balanced-forcing half-gap estimate. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_exponentialTrackingEnvelope_balancedForcing_halfGap_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
    (F U : ℝ → (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
    (F_lim : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
    (C : ℝ) (hC : 0 ≤ C) (hF : Continuous F)
    (hFC : ∀ s ∈ Set.Icc t₀ t,
      ‖F s - F_lim‖ ≤ C * Real.exp (-((s - t₀) * exactGapValueReal)))
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U (U r * (-LinearMap.toContinuousLinearMap
        (D.gapData.restrictedHamiltonian n)) + F r) r) :
    ‖U t - finiteWilsonVacuumOrthogonalHamiltonianRightSteadyState D n F_lim‖ ≤
      (‖A - finiteWilsonVacuumOrthogonalHamiltonianRightSteadyState D n F_lim‖ +
          2 * C / exactGapValueReal) *
        Real.exp (-((t - t₀) * (exactGapValueReal / 2))) := by
  simpa using
    finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_exponentialTrackingEnvelope_fastForcing_halfGap_right
      D n exactGapValueReal le_rfl t₀ t ht A F U F_lim C hC hF hFC hU0 hU

end

end MathlibAnalytic
end MGAP4D
