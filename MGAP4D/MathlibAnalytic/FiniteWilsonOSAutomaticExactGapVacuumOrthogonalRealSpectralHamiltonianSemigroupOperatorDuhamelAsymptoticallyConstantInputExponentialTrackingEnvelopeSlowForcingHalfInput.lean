import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedRealSpectralHamiltonianSemigroupOperatorDuhamelAsymptoticallyConstantInputExponentialTrackingEnvelopeSlowForcingHalfInput
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapVacuumOrthogonalRealSpectralHamiltonianSemigroupOperatorDuhamelAsymptoticallyConstantInputExponentialTrackingEnvelopeUniformHalfMinSimplified

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- On `Ω⊥`, slow forcing gives left tracking at half the forcing rate. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_exponentialTrackingEnvelope_slowForcing_halfInput_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) (μ : ℝ) (hμpos : 0 < μ) (hμgap : μ ≤ exactGapValueReal)
    (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
    (F U : ℝ → (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
    (F_lim : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
    (C : ℝ) (hC : 0 ≤ C) (hF : Continuous F)
    (hFC : ∀ s ∈ Set.Icc t₀ t,
      ‖F s - F_lim‖ ≤ C * Real.exp (-((s - t₀) * μ)))
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U ((-LinearMap.toContinuousLinearMap
        (D.gapData.restrictedHamiltonian n)) * U r + F r) r) :
    ‖U t - finiteWilsonVacuumOrthogonalHamiltonianLeftSteadyState D n F_lim‖ ≤
      (‖A - finiteWilsonVacuumOrthogonalHamiltonianLeftSteadyState D n F_lim‖ +
          2 * C / exactGapValueReal) *
        Real.exp (-((t - t₀) * (μ / 2))) := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_exponentialTrackingEnvelope_slowForcing_halfInput_left
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n μ hμpos hμgap t₀ t ht A F U F_lim C hC hF hFC hU0 hU

/-- On `Ω⊥`, right tracking has the same slow-forcing half-input estimate. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_exponentialTrackingEnvelope_slowForcing_halfInput_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) (μ : ℝ) (hμpos : 0 < μ) (hμgap : μ ≤ exactGapValueReal)
    (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
    (F U : ℝ → (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
    (F_lim : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
    (C : ℝ) (hC : 0 ≤ C) (hF : Continuous F)
    (hFC : ∀ s ∈ Set.Icc t₀ t,
      ‖F s - F_lim‖ ≤ C * Real.exp (-((s - t₀) * μ)))
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U (U r * (-LinearMap.toContinuousLinearMap
        (D.gapData.restrictedHamiltonian n)) + F r) r) :
    ‖U t - finiteWilsonVacuumOrthogonalHamiltonianRightSteadyState D n F_lim‖ ≤
      (‖A - finiteWilsonVacuumOrthogonalHamiltonianRightSteadyState D n F_lim‖ +
          2 * C / exactGapValueReal) *
        Real.exp (-((t - t₀) * (μ / 2))) := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_exponentialTrackingEnvelope_slowForcing_halfInput_right
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n μ hμpos hμgap t₀ t ht A F U F_lim C hC hF hFC hU0 hU

end

end MathlibAnalytic
end MGAP4D
