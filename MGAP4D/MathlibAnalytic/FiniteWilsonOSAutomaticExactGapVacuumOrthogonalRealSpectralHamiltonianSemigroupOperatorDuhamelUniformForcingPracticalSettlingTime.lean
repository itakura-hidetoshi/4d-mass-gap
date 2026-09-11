import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedRealSpectralHamiltonianSemigroupOperatorDuhamelUniformForcingPracticalSettlingTime
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapVacuumOrthogonalRealSpectralHamiltonianSemigroupOperatorDuhamelUniformForcingGain

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- On the physical excitation sector `Ω⊥`, left uniformly forced evolution
enters and remains in the explicit exact-gap ultimate ball after the practical
settling time. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_duhamel_uniformForcing_norm_le_ultimateBall_after_settlingTime_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ)
    (t₀ : ℝ)
    (A : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
    (F U : ℝ →
      (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
    (M : ℝ)
    (hM : 0 ≤ M)
    (hF : Continuous F)
    (hFM : ∀ s : ℝ, t₀ ≤ s → ‖F s‖ ≤ M)
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U
        ((-LinearMap.toContinuousLinearMap
          (D.gapData.restrictedHamiltonian n)) * U r + F r) r)
    (ε : ℝ)
    (hε : 0 < ε) :
    ∀ t : ℝ,
      t₀ + max 0 (Real.log (‖A‖ / ε) / exactGapValueReal) ≤ t →
        ‖U t‖ ≤ M / exactGapValueReal + ε := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_uniformForcing_norm_le_ultimateBall_after_settlingTime_left
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n t₀ A F U M hM hF hFM hU0 hU ε hε

/-- On `Ω⊥`, right uniformly forced evolution has the same practical
settling-time guarantee. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_duhamel_uniformForcing_norm_le_ultimateBall_after_settlingTime_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ)
    (t₀ : ℝ)
    (A : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
    (F U : ℝ →
      (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
    (M : ℝ)
    (hM : 0 ≤ M)
    (hF : Continuous F)
    (hFM : ∀ s : ℝ, t₀ ≤ s → ‖F s‖ ≤ M)
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U
        (U r * (-LinearMap.toContinuousLinearMap
          (D.gapData.restrictedHamiltonian n)) + F r) r)
    (ε : ℝ)
    (hε : 0 < ε) :
    ∀ t : ℝ,
      t₀ + max 0 (Real.log (‖A‖ / ε) / exactGapValueReal) ≤ t →
        ‖U t‖ ≤ M / exactGapValueReal + ε := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_uniformForcing_norm_le_ultimateBall_after_settlingTime_right
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n t₀ A F U M hM hF hFM hU0 hU ε hε

end

end MathlibAnalytic
end MGAP4D
