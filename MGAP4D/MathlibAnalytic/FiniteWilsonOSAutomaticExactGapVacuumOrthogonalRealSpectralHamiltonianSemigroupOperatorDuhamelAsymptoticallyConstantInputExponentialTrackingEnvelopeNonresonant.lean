import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedRealSpectralHamiltonianSemigroupOperatorDuhamelAsymptoticallyConstantInputExponentialTrackingEnvelope
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapVacuumOrthogonalRealSpectralHamiltonianSemigroupOperatorDuhamelAsymptoticallyConstantInputExponentialTrackingRate

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- On `Ω⊥`, the left evolution has the non-resonant single-rate envelope. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_exponentialTrackingEnvelope_nonresonant_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ)
    (μ : ℝ)
    (hμpos : 0 < μ)
    (hgapμ : exactGapValueReal ≠ μ)
    (t₀ t : ℝ)
    (ht : t₀ ≤ t)
    (A : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
    (F U : ℝ →
      (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
    (F_lim :
      D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
    (C : ℝ)
    (hC : 0 ≤ C)
    (hF : Continuous F)
    (hFC : ∀ s ∈ Set.Icc t₀ t,
      ‖F s - F_lim‖ ≤ C * Real.exp (-((s - t₀) * μ)))
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U
        ((-LinearMap.toContinuousLinearMap
          (D.gapData.restrictedHamiltonian n)) * U r + F r) r) :
    ‖U t - finiteWilsonVacuumOrthogonalHamiltonianLeftSteadyState D n F_lim‖ ≤
      (‖A - finiteWilsonVacuumOrthogonalHamiltonianLeftSteadyState D n F_lim‖ +
          C / |exactGapValueReal - μ|) *
        Real.exp (-((t - t₀) * min exactGapValueReal μ)) := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_exponentialTrackingEnvelope_nonresonant_left
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n μ hμpos hgapμ t₀ t ht A F U F_lim C hC hF hFC hU0 hU

/-- On `Ω⊥`, the right evolution has the same non-resonant single-rate envelope. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_exponentialTrackingEnvelope_nonresonant_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ)
    (μ : ℝ)
    (hμpos : 0 < μ)
    (hgapμ : exactGapValueReal ≠ μ)
    (t₀ t : ℝ)
    (ht : t₀ ≤ t)
    (A : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
    (F U : ℝ →
      (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
    (F_lim :
      D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
    (C : ℝ)
    (hC : 0 ≤ C)
    (hF : Continuous F)
    (hFC : ∀ s ∈ Set.Icc t₀ t,
      ‖F s - F_lim‖ ≤ C * Real.exp (-((s - t₀) * μ)))
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U
        (U r * (-LinearMap.toContinuousLinearMap
          (D.gapData.restrictedHamiltonian n)) + F r) r) :
    ‖U t - finiteWilsonVacuumOrthogonalHamiltonianRightSteadyState D n F_lim‖ ≤
      (‖A - finiteWilsonVacuumOrthogonalHamiltonianRightSteadyState D n F_lim‖ +
          C / |exactGapValueReal - μ|) *
        Real.exp (-((t - t₀) * min exactGapValueReal μ)) := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_exponentialTrackingEnvelope_nonresonant_right
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n μ hμpos hgapμ t₀ t ht A F U F_lim C hC hF hFC hU0 hU

end

end MathlibAnalytic
end MGAP4D
