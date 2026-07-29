import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedRealSpectralHamiltonianSemigroupIVPUniqueness
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapVacuumOrthogonalRealSpectralHamiltonianSemigroupOperatorExp

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- On the physical excitation sector `Ω⊥`, the real spectral semigroup is the
unique operator-norm solution of the restricted-Hamiltonian initial-value
problem `U' = -H U`, `U 0 = 1`. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_eq_of_hasDerivAt_operator_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ)
    (U : ℝ → (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
    (hU0 : U 0 = 1)
    (hU : ∀ t : ℝ,
      HasDerivAt U
        ((-LinearMap.toContinuousLinearMap (D.gapData.restrictedHamiltonian n)) * U t) t) :
    U = D.vacuumOrthogonalRealSpectralHamiltonianSemigroup n := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_eq_of_hasDerivAt_operator_left
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData n U hU0 hU

end

end MathlibAnalytic
end MGAP4D
