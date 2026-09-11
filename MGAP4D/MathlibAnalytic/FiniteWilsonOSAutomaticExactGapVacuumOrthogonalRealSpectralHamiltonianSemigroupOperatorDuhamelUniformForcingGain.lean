import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedRealSpectralHamiltonianSemigroupOperatorDuhamelUniformForcingGain
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapVacuumOrthogonalRealSpectralHamiltonianSemigroupOperatorDuhamelMassGapBound

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- On `Ω⊥`, left restricted-Hamiltonian evolution has the exact finite-time
uniform-forcing gain. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_duhamel_uniformForcing_gain_bound_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ)
    (t₀ t : ℝ)
    (ht : t₀ ≤ t)
    (A : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
    (F U : ℝ →
      (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
    (M : ℝ)
    (hF : Continuous F)
    (hFM : ∀ s ∈ Set.Icc t₀ t, ‖F s‖ ≤ M)
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U
        ((-LinearMap.toContinuousLinearMap
          (D.gapData.restrictedHamiltonian n)) * U r + F r) r) :
    ‖U t‖ ≤
      Real.exp (-((t - t₀) * exactGapValueReal)) * ‖A‖ +
        ((1 - Real.exp (-((t - t₀) * exactGapValueReal))) /
          exactGapValueReal) * M := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_uniformForcing_gain_bound_left
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n t₀ t ht A F U M hF hFM hU0 hU

/-- On `Ω⊥`, right restricted-Hamiltonian evolution has the same exact
finite-time uniform-forcing gain. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_duhamel_uniformForcing_gain_bound_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ)
    (t₀ t : ℝ)
    (ht : t₀ ≤ t)
    (A : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
    (F U : ℝ →
      (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
    (M : ℝ)
    (hF : Continuous F)
    (hFM : ∀ s ∈ Set.Icc t₀ t, ‖F s‖ ≤ M)
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U
        (U r * (-LinearMap.toContinuousLinearMap
          (D.gapData.restrictedHamiltonian n)) + F r) r) :
    ‖U t‖ ≤
      Real.exp (-((t - t₀) * exactGapValueReal)) * ‖A‖ +
        ((1 - Real.exp (-((t - t₀) * exactGapValueReal))) /
          exactGapValueReal) * M := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_uniformForcing_gain_bound_right
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n t₀ t ht A F U M hF hFM hU0 hU

/-- On `Ω⊥`, left restricted-Hamiltonian evolution is bounded by its decaying
transient plus the static exact-gap input gain. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_duhamel_uniformForcing_ultimate_bound_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ)
    (t₀ t : ℝ)
    (ht : t₀ ≤ t)
    (A : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
    (F U : ℝ →
      (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
    (M : ℝ)
    (hM : 0 ≤ M)
    (hF : Continuous F)
    (hFM : ∀ s ∈ Set.Icc t₀ t, ‖F s‖ ≤ M)
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U
        ((-LinearMap.toContinuousLinearMap
          (D.gapData.restrictedHamiltonian n)) * U r + F r) r) :
    ‖U t‖ ≤
      Real.exp (-((t - t₀) * exactGapValueReal)) * ‖A‖ +
        M / exactGapValueReal := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_uniformForcing_ultimate_bound_left
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n t₀ t ht A F U M hM hF hFM hU0 hU

/-- On `Ω⊥`, right restricted-Hamiltonian evolution has the same static exact-gap
input gain. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_duhamel_uniformForcing_ultimate_bound_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ)
    (t₀ t : ℝ)
    (ht : t₀ ≤ t)
    (A : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
    (F U : ℝ →
      (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
    (M : ℝ)
    (hM : 0 ≤ M)
    (hF : Continuous F)
    (hFM : ∀ s ∈ Set.Icc t₀ t, ‖F s‖ ≤ M)
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U
        (U r * (-LinearMap.toContinuousLinearMap
          (D.gapData.restrictedHamiltonian n)) + F r) r) :
    ‖U t‖ ≤
      Real.exp (-((t - t₀) * exactGapValueReal)) * ‖A‖ +
        M / exactGapValueReal := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_uniformForcing_ultimate_bound_right
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n t₀ t ht A F U M hM hF hFM hU0 hU

end

end MathlibAnalytic
end MGAP4D
