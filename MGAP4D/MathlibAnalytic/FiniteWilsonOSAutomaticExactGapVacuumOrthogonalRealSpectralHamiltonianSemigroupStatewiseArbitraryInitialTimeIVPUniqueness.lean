import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedRealSpectralHamiltonianSemigroupStatewiseArbitraryInitialTimeIVPUniqueness
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapVacuumOrthogonalRealSpectralHamiltonianSemigroupOperatorExp

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- On the physical excitation sector `Ω⊥`, every statewise solution of the
restricted-Hamiltonian IVP based at an arbitrary initial time `t₀` is the
translated real spectral semigroup orbit through its initial state. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_apply_sub_eq_of_hasDerivAt
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ)
    (t₀ : ℝ)
    (x : D.gapData.ExcitedStateSpace)
    (u : ℝ → D.gapData.ExcitedStateSpace)
    (hu0 : u t₀ = x)
    (hu : ∀ t : ℝ,
      HasDerivAt u
        (-((LinearMap.toContinuousLinearMap
          (D.gapData.restrictedHamiltonian n)) (u t))) t) :
    u = fun t : ℝ =>
      D.vacuumOrthogonalRealSpectralHamiltonianSemigroup n (t - t₀) x := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_apply_sub_eq_of_hasDerivAt
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData n t₀ x u hu0 hu

end

end MathlibAnalytic
end MGAP4D
