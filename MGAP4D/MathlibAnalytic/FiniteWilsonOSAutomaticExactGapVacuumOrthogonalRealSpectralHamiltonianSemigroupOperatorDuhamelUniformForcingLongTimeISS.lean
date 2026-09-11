import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedRealSpectralHamiltonianSemigroupOperatorDuhamelUniformForcingLongTimeISS
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapVacuumOrthogonalRealSpectralHamiltonianSemigroupOperatorDuhamelUniformForcingGain

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Filter

/-- On the physical excitation sector `Ω⊥`, left restricted-Hamiltonian evolution
has long-time gain at most `M / exactGapValueReal`. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_duhamel_uniformForcing_limsup_norm_le_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ)
    (t₀ : ℝ)
    (A : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
    (F U : ℝ →
      (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
    (M : ℝ)
    (hF : Continuous F)
    (hFM : ∀ s : ℝ, t₀ ≤ s → ‖F s‖ ≤ M)
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U
        ((-LinearMap.toContinuousLinearMap
          (D.gapData.restrictedHamiltonian n)) * U r + F r) r) :
    Filter.limsup (fun t : ℝ => ‖U t‖) atTop ≤ M / exactGapValueReal := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_uniformForcing_limsup_norm_le_left
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n t₀ A F U M hF hFM hU0 hU

/-- On `Ω⊥`, right restricted-Hamiltonian evolution obeys the same long-time
input-to-state stability estimate. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_duhamel_uniformForcing_limsup_norm_le_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ)
    (t₀ : ℝ)
    (A : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
    (F U : ℝ →
      (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
    (M : ℝ)
    (hF : Continuous F)
    (hFM : ∀ s : ℝ, t₀ ≤ s → ‖F s‖ ≤ M)
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U
        (U r * (-LinearMap.toContinuousLinearMap
          (D.gapData.restrictedHamiltonian n)) + F r) r) :
    Filter.limsup (fun t : ℝ => ‖U t‖) atTop ≤ M / exactGapValueReal := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_uniformForcing_limsup_norm_le_right
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n t₀ A F U M hF hFM hU0 hU

end

end MathlibAnalytic
end MGAP4D
