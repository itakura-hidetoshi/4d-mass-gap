import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedRealSpectralHamiltonianSemigroupOperatorArbitraryInitialValueIVPUniqueness
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapVacuumOrthogonalRealSpectralHamiltonianSemigroupOperatorExp

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- On the physical excitation sector `Ω⊥`, an arbitrary initial operator `A` at
`t₀` evolves under the left restricted-Hamiltonian IVP as `S (t - t₀) A`. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_sub_mul_eq_of_hasDerivAt_operator_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ)
    (t₀ : ℝ)
    (A : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
    (U : ℝ → (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
    (hU0 : U t₀ = A)
    (hU : ∀ t : ℝ,
      HasDerivAt U
        ((-LinearMap.toContinuousLinearMap
          (D.gapData.restrictedHamiltonian n)) * U t) t) :
    U = fun t : ℝ =>
      D.vacuumOrthogonalRealSpectralHamiltonianSemigroup n (t - t₀) * A := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_sub_mul_eq_of_hasDerivAt_operator_left
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData n t₀ A U hU0 hU

/-- On the physical excitation sector `Ω⊥`, an arbitrary initial operator `A` at
`t₀` evolves under the right restricted-Hamiltonian IVP as `A S (t - t₀)`. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_mul_sub_eq_of_hasDerivAt_operator_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ)
    (t₀ : ℝ)
    (A : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
    (U : ℝ → (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
    (hU0 : U t₀ = A)
    (hU : ∀ t : ℝ,
      HasDerivAt U
        (U t * (-LinearMap.toContinuousLinearMap
          (D.gapData.restrictedHamiltonian n))) t) :
    U = fun t : ℝ =>
      A * D.vacuumOrthogonalRealSpectralHamiltonianSemigroup n (t - t₀) := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_mul_sub_eq_of_hasDerivAt_operator_right
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData n t₀ A U hU0 hU

end

end MathlibAnalytic
end MGAP4D
