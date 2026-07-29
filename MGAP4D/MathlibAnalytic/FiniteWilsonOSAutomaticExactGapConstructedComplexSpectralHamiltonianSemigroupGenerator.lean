import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedComplexSpectralHamiltonianSemigroupContinuity
import MGAP4D.MathlibAnalytic.OrthonormalComplexDiagonalHamiltonianSemigroupGenerator
import Mathlib.LinearAlgebra.Complex.Module

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- On every constructed complex spectral state, the strong derivative at time
zero is the negative explicit Hamiltonian action. -/
theorem finite_wilson_constructed_complex_spectral_hamiltonianSemigroup_hasDerivAt_zero
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ)
    (x : D.complexSpectralStateSpace) :
    HasDerivAt
      (fun t : ℝ => D.complexSpectralHamiltonianSemigroup n t x)
      (-(D.complexSpectralHamiltonian n x)) 0 := by
  unfold FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData.complexSpectralHamiltonianSemigroup
  unfold FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData.complexSpectralHamiltonian
  exact orthonormalComplexDiagonalHamiltonianSemigroup_hasDerivAt_zero
    D.complexSpectralBasis
    (fun i => (D.hamiltonianSymmetric n).eigenvalues D.stateFinrank i)
    x

/-- The constructed semigroup generator is the negative canonical logarithmic
Hamiltonian on every complex spectral state. -/
theorem finite_wilson_constructed_complex_spectral_hamiltonianSemigroup_hasDerivAt_zero_logHamiltonian
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ)
    (x : D.complexSpectralStateSpace) :
    HasDerivAt
      (fun t : ℝ => D.complexSpectralHamiltonianSemigroup n t x)
      (-(D.complexSpectralLogHamiltonian n x)) 0 := by
  rw [finite_wilson_constructed_complex_spectral_logHamiltonian_eq_hamiltonian D n]
  exact finite_wilson_constructed_complex_spectral_hamiltonianSemigroup_hasDerivAt_zero
    D n x

/-- Ordinary derivative form of the constructed generator identity. -/
theorem finite_wilson_constructed_complex_spectral_hamiltonianSemigroup_deriv_zero
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ)
    (x : D.complexSpectralStateSpace) :
    deriv (fun t : ℝ => D.complexSpectralHamiltonianSemigroup n t x) 0 =
      -(D.complexSpectralLogHamiltonian n x) :=
  (finite_wilson_constructed_complex_spectral_hamiltonianSemigroup_hasDerivAt_zero_logHamiltonian
    D n x).deriv

end

end MathlibAnalytic
end MGAP4D
