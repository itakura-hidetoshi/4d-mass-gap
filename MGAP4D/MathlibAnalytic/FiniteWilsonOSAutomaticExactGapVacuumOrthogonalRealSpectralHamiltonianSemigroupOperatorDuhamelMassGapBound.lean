import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedRealSpectralHamiltonianSemigroupOperatorDuhamelMassGapBound
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapVacuumOrthogonalRealSpectralHamiltonianSemigroupOperatorDuhamel

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open MeasureTheory

/-- On the physical excitation sector `Ω⊥`, the left forced restricted-Hamiltonian
evolution obeys the exact mass-gap response estimate. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_duhamel_massGap_bound_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ)
    (t₀ t : ℝ)
    (ht : t₀ ≤ t)
    (A : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
    (F U : ℝ →
      (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
    (hF : Continuous F)
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U
        ((-LinearMap.toContinuousLinearMap
          (D.gapData.restrictedHamiltonian n)) * U r + F r) r) :
    ‖U t‖ ≤
      Real.exp (-((t - t₀) * exactGapValueReal)) * ‖A‖ +
        ∫ s in t₀..t,
          Real.exp (-((t - s) * exactGapValueReal)) * ‖F s‖ := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_massGap_bound_left
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n t₀ t ht A F U hF hU0 hU

/-- On the physical excitation sector `Ω⊥`, the right forced restricted-Hamiltonian
evolution obeys the same exact mass-gap response estimate. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_duhamel_massGap_bound_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ)
    (t₀ t : ℝ)
    (ht : t₀ ≤ t)
    (A : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
    (F U : ℝ →
      (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
    (hF : Continuous F)
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U
        (U r * (-LinearMap.toContinuousLinearMap
          (D.gapData.restrictedHamiltonian n)) + F r) r) :
    ‖U t‖ ≤
      Real.exp (-((t - t₀) * exactGapValueReal)) * ‖A‖ +
        ∫ s in t₀..t,
          Real.exp (-((t - s) * exactGapValueReal)) * ‖F s‖ := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_duhamel_massGap_bound_right
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n t₀ t ht A F U hF hU0 hU

end

end MathlibAnalytic
end MGAP4D
