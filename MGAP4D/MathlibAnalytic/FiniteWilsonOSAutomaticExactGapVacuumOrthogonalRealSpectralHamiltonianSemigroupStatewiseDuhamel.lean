import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedRealSpectralHamiltonianSemigroupStatewiseDuhamel
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapVacuumOrthogonalRealSpectralHamiltonianSemigroupOperatorExp

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open MeasureTheory

/-- On the physical excitation sector `Ω⊥`, the restricted real spectral
semigroup satisfies the statewise Duhamel / variation-of-constants formula for
continuous forcing. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_duhamel_eq_of_hasDerivAt
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ)
    (t₀ : ℝ)
    (x : D.gapData.ExcitedStateSpace)
    (f u : ℝ → D.gapData.ExcitedStateSpace)
    (hf : Continuous f)
    (hu0 : u t₀ = x)
    (hu : ∀ t : ℝ,
      HasDerivAt u
        (-((LinearMap.toContinuousLinearMap
          (D.gapData.restrictedHamiltonian n)) (u t)) + f t) t) :
    u = fun t : ℝ =>
      D.vacuumOrthogonalRealSpectralHamiltonianSemigroup n (t - t₀) x +
        ∫ s in t₀..t,
          D.vacuumOrthogonalRealSpectralHamiltonianSemigroup n (t - s) (f s) := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_duhamel_eq_of_hasDerivAt
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n t₀ x f u hf hu0 hu

end

end MathlibAnalytic
end MGAP4D
