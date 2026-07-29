import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedRealSpectralHamiltonianSemigroupOperatorDuhamelZeroInputNormConvergence
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapVacuumOrthogonalRealSpectralHamiltonianSemigroupOperatorDuhamelUniformForcingGain

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Filter

/-- On the physical excitation sector `Ω⊥`, left zero-input restricted-Hamiltonian
evolution converges to zero in operator norm. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_duhamel_zeroInput_tendsto_norm_zero_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ)
    (t₀ : ℝ)
    (A : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
    (U : ℝ →
      (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U
        ((-LinearMap.toContinuousLinearMap
          (D.gapData.restrictedHamiltonian n)) * U r) r) :
    Tendsto (fun t : ℝ => ‖U t‖) atTop (nhds 0) := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_zeroInput_tendsto_norm_zero_left
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n t₀ A U hU0 hU

/-- On `Ω⊥`, right zero-input restricted-Hamiltonian evolution obeys the same
operator-norm convergence. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_duhamel_zeroInput_tendsto_norm_zero_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ)
    (t₀ : ℝ)
    (A : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
    (U : ℝ →
      (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U
        (U r * (-LinearMap.toContinuousLinearMap
          (D.gapData.restrictedHamiltonian n))) r) :
    Tendsto (fun t : ℝ => ‖U t‖) atTop (nhds 0) := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_zeroInput_tendsto_norm_zero_right
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n t₀ A U hU0 hU

end

end MathlibAnalytic
end MGAP4D
