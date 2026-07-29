import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedComplexSpectralHamiltonianSemigroup
import MGAP4D.MathlibAnalytic.OrthonormalComplexDiagonalHamiltonianSemigroupContinuity

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The constructed complex spectral Hamiltonian semigroup is smooth in operator norm. -/
theorem finite_wilson_constructed_complex_spectral_hamiltonianSemigroup_contDiff
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) :
    ContDiff ℝ ⊤ (D.complexSpectralHamiltonianSemigroup n) := by
  unfold FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData.complexSpectralHamiltonianSemigroup
  exact orthonormalComplexDiagonalHamiltonianSemigroup_contDiff
    D.complexSpectralBasis
    (fun i => (D.hamiltonianSymmetric n).eigenvalues D.stateFinrank i)

/-- The constructed complex spectral Hamiltonian semigroup is continuous in
operator norm. -/
theorem finite_wilson_constructed_complex_spectral_hamiltonianSemigroup_continuous
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) :
    Continuous (D.complexSpectralHamiltonianSemigroup n) :=
  (finite_wilson_constructed_complex_spectral_hamiltonianSemigroup_contDiff D n).continuous

/-- The constructed complex spectral Hamiltonian semigroup is strongly
continuous on every state vector. -/
theorem finite_wilson_constructed_complex_spectral_hamiltonianSemigroup_stronglyContinuous
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ)
    (x : D.complexSpectralStateSpace) :
    Continuous (fun t : ℝ => D.complexSpectralHamiltonianSemigroup n t x) := by
  unfold FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData.complexSpectralHamiltonianSemigroup
  exact orthonormalComplexDiagonalHamiltonianSemigroup_stronglyContinuous
    D.complexSpectralBasis
    (fun i => (D.hamiltonianSymmetric n).eigenvalues D.stateFinrank i)
    x

end

end MathlibAnalytic
end MGAP4D
