import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedRealSpectralHamiltonianSemigroupOperatorDuhamelAsymptoticallyConstantInputExponentialTrackingEnvelopeUniformSubcriticalSettlingTime
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapVacuumOrthogonalRealSpectralHamiltonianSemigroupOperatorDuhamelAsymptoticallyConstantInputExponentialTrackingEnvelopeUniformSubcritical

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- On `Ω⊥`, the uniform subcritical left envelope yields an explicit settling
time. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_norm_sub_le_epsilon_after_exponentialTrackingEnvelope_uniform_subcritical_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) (μ ν : ℝ) (hνpos : 0 < ν)
    (hνgap : ν < exactGapValueReal) (hνμ : ν < μ)
    (t₀ : ℝ)
    (A : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
    (F U : ℝ → (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
    (F_lim : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
    (C : ℝ) (hC : 0 ≤ C) (hF : Continuous F)
    (hFC : ∀ s : ℝ, t₀ ≤ s →
      ‖F s - F_lim‖ ≤ C * Real.exp (-((s - t₀) * μ)))
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U
        ((-LinearMap.toContinuousLinearMap
          (D.gapData.restrictedHamiltonian n)) * U r + F r) r)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ t : ℝ,
      t₀ + max 0
          (Real.log
            ((‖A - finiteWilsonVacuumOrthogonalHamiltonianLeftSteadyState D n F_lim‖ +
                C / (max exactGapValueReal μ - ν)) / ε) / ν) ≤ t →
        ‖U t - finiteWilsonVacuumOrthogonalHamiltonianLeftSteadyState D n F_lim‖ ≤ ε := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_norm_sub_le_epsilon_after_exponentialTrackingEnvelope_uniform_subcritical_left
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n μ ν hνpos hνgap hνμ t₀ A F U F_lim C hC hF hFC hU0 hU ε hε

/-- On `Ω⊥`, the uniform subcritical right envelope yields the identical explicit
settling time. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_norm_sub_le_epsilon_after_exponentialTrackingEnvelope_uniform_subcritical_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) (μ ν : ℝ) (hνpos : 0 < ν)
    (hνgap : ν < exactGapValueReal) (hνμ : ν < μ)
    (t₀ : ℝ)
    (A : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
    (F U : ℝ → (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
    (F_lim : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
    (C : ℝ) (hC : 0 ≤ C) (hF : Continuous F)
    (hFC : ∀ s : ℝ, t₀ ≤ s →
      ‖F s - F_lim‖ ≤ C * Real.exp (-((s - t₀) * μ)))
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U
        (U r * (-LinearMap.toContinuousLinearMap
          (D.gapData.restrictedHamiltonian n)) + F r) r)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ t : ℝ,
      t₀ + max 0
          (Real.log
            ((‖A - finiteWilsonVacuumOrthogonalHamiltonianRightSteadyState D n F_lim‖ +
                C / (max exactGapValueReal μ - ν)) / ε) / ν) ≤ t →
        ‖U t - finiteWilsonVacuumOrthogonalHamiltonianRightSteadyState D n F_lim‖ ≤ ε := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_norm_sub_le_epsilon_after_exponentialTrackingEnvelope_uniform_subcritical_right
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n μ ν hνpos hνgap hνμ t₀ A F U F_lim C hC hF hFC hU0 hU ε hε

end

end MathlibAnalytic
end MGAP4D
