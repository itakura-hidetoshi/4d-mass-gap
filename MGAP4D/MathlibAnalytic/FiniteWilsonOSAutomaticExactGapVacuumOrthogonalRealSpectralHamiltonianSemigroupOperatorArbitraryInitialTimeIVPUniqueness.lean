import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedRealSpectralHamiltonianSemigroupOperatorArbitraryInitialTimeIVPUniqueness
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapVacuumOrthogonalRealSpectralHamiltonianSemigroupOperatorExp

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- On the physical excitation sector `Ω⊥`, the real spectral semigroup based at
an arbitrary initial time `t₀` is the unique operator-norm solution of the left
restricted-Hamiltonian IVP. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_sub_eq_of_hasDerivAt_operator_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ)
    (t₀ : ℝ)
    (U : ℝ → (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
    (hU0 : U t₀ = 1)
    (hU : ∀ t : ℝ,
      HasDerivAt U
        ((-LinearMap.toContinuousLinearMap (D.gapData.restrictedHamiltonian n)) * U t) t) :
    U = fun t : ℝ => D.vacuumOrthogonalRealSpectralHamiltonianSemigroup n (t - t₀) := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_sub_eq_of_hasDerivAt_operator_left
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData n t₀ U hU0 hU

/-- On the physical excitation sector `Ω⊥`, the real spectral semigroup based at
an arbitrary initial time `t₀` is the unique operator-norm solution of the right
restricted-Hamiltonian IVP. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_sub_eq_of_hasDerivAt_operator_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ)
    (t₀ : ℝ)
    (U : ℝ → (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
    (hU0 : U t₀ = 1)
    (hU : ∀ t : ℝ,
      HasDerivAt U
        (U t * (-LinearMap.toContinuousLinearMap (D.gapData.restrictedHamiltonian n))) t) :
    U = fun t : ℝ => D.vacuumOrthogonalRealSpectralHamiltonianSemigroup n (t - t₀) := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_sub_eq_of_hasDerivAt_operator_right
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData n t₀ U hU0 hU

end

end MathlibAnalytic
end MGAP4D
