import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedRealSpectralHamiltonianSemigroupOperatorDuhamel
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapVacuumOrthogonalRealSpectralHamiltonianSemigroupOperatorExp

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open MeasureTheory

/-- On the physical excitation sector `Ω⊥`, the left restricted-Hamiltonian
operator equation satisfies the Duhamel formula. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_duhamel_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ)
    (t₀ : ℝ)
    (A : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
    (F U : ℝ →
      (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
    (hF : Continuous F)
    (hU0 : U t₀ = A)
    (hU : ∀ t : ℝ,
      HasDerivAt U
        ((-LinearMap.toContinuousLinearMap
          (D.gapData.restrictedHamiltonian n)) * U t + F t) t) :
    U = fun t : ℝ =>
      D.vacuumOrthogonalRealSpectralHamiltonianSemigroup n (t - t₀) * A +
        ∫ s in t₀..t,
          D.vacuumOrthogonalRealSpectralHamiltonianSemigroup n (t - s) * F s := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_left
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n t₀ A F U hF hU0 hU

/-- On the physical excitation sector `Ω⊥`, the right restricted-Hamiltonian
operator equation satisfies the Duhamel formula. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_duhamel_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ)
    (t₀ : ℝ)
    (A : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
    (F U : ℝ →
      (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
    (hF : Continuous F)
    (hU0 : U t₀ = A)
    (hU : ∀ t : ℝ,
      HasDerivAt U
        (U t * (-LinearMap.toContinuousLinearMap
          (D.gapData.restrictedHamiltonian n)) + F t) t) :
    U = fun t : ℝ =>
      A * D.vacuumOrthogonalRealSpectralHamiltonianSemigroup n (t - t₀) +
        ∫ s in t₀..t,
          F s * D.vacuumOrthogonalRealSpectralHamiltonianSemigroup n (t - s) := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_right
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n t₀ A F U hF hU0 hU

end

end MathlibAnalytic
end MGAP4D
