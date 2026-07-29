import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedRealSpectralHamiltonianSemigroupOperatorDuhamelZeroInputSettlingTime
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapVacuumOrthogonalRealSpectralHamiltonianSemigroupOperatorDuhamelUniformForcingGain

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- On the physical excitation sector `Ω⊥`, left zero-input evolution obeys the
exact-gap exponential operator-norm rate. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_duhamel_zeroInput_norm_le_exp_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ)
    (t₀ t : ℝ)
    (ht : t₀ ≤ t)
    (A : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
    (U : ℝ →
      (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U
        ((-LinearMap.toContinuousLinearMap
          (D.gapData.restrictedHamiltonian n)) * U r) r) :
    ‖U t‖ ≤ Real.exp (-((t - t₀) * exactGapValueReal)) * ‖A‖ := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_zeroInput_norm_le_exp_left
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n t₀ t ht A U hU0 hU

/-- On `Ω⊥`, right zero-input evolution obeys the same exact-gap exponential
operator-norm rate. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_duhamel_zeroInput_norm_le_exp_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ)
    (t₀ t : ℝ)
    (ht : t₀ ≤ t)
    (A : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
    (U : ℝ →
      (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U
        (U r * (-LinearMap.toContinuousLinearMap
          (D.gapData.restrictedHamiltonian n))) r) :
    ‖U t‖ ≤ Real.exp (-((t - t₀) * exactGapValueReal)) * ‖A‖ := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_zeroInput_norm_le_exp_right
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n t₀ t ht A U hU0 hU

/-- On `Ω⊥`, left zero-input evolution enters any prescribed tolerance after the
explicit exact-gap settling time. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_duhamel_zeroInput_norm_le_epsilon_after_settlingTime_left
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
          (D.gapData.restrictedHamiltonian n)) * U r) r)
    (ε : ℝ)
    (hε : 0 < ε)
    (t : ℝ)
    (ht : t₀ + max 0 (Real.log (‖A‖ / ε) / exactGapValueReal) ≤ t) :
    ‖U t‖ ≤ ε := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_zeroInput_norm_le_epsilon_after_settlingTime_left
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n t₀ A U hU0 hU ε hε t ht

/-- On `Ω⊥`, right zero-input evolution has the same explicit exact-gap
settling-time guarantee. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_duhamel_zeroInput_norm_le_epsilon_after_settlingTime_right
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
          (D.gapData.restrictedHamiltonian n))) r)
    (ε : ℝ)
    (hε : 0 < ε)
    (t : ℝ)
    (ht : t₀ + max 0 (Real.log (‖A‖ / ε) / exactGapValueReal) ≤ t) :
    ‖U t‖ ≤ ε := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_zeroInput_norm_le_epsilon_after_settlingTime_right
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n t₀ A U hU0 hU ε hε t ht

end

end MathlibAnalytic
end MGAP4D
