import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedComplexSpectralHamiltonianSemigroupGenerator
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapVacuumOrthogonalComplexSpectralHamiltonianSemigroupContinuity
import Mathlib.Analysis.Normed.Module.RCLike.Basic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

local instance vacuumOrthogonalComplexSpectralNormedSpaceReal
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W} :
    NormedSpace ℝ D.vacuumOrthogonalComplexSpectralStateSpace :=
  NormedSpace.restrictScalars ℝ ℂ D.vacuumOrthogonalComplexSpectralStateSpace

/-- On every vacuum-orthogonal complex spectral excitation state, the strong
derivative at time zero is the negative explicit Hamiltonian action. -/
theorem finite_wilson_vacuum_orthogonal_complex_spectral_hamiltonianSemigroup_hasDerivAt_zero
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ)
    (x : D.vacuumOrthogonalComplexSpectralStateSpace) :
    HasDerivAt
      (fun t : ℝ => D.vacuumOrthogonalComplexSpectralHamiltonianSemigroup n t x)
      (-(D.vacuumOrthogonalComplexSpectralHamiltonian n x)) 0 :=
  finite_wilson_constructed_complex_spectral_hamiltonianSemigroup_hasDerivAt_zero
    D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData n x

/-- The vacuum-orthogonal complex spectral semigroup generator is the negative
canonical logarithmic Hamiltonian, with no new assumption on the vacuum line. -/
theorem finite_wilson_vacuum_orthogonal_complex_spectral_hamiltonianSemigroup_hasDerivAt_zero_logHamiltonian
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ)
    (x : D.vacuumOrthogonalComplexSpectralStateSpace) :
    HasDerivAt
      (fun t : ℝ => D.vacuumOrthogonalComplexSpectralHamiltonianSemigroup n t x)
      (-(D.vacuumOrthogonalComplexSpectralLogHamiltonian n x)) 0 :=
  finite_wilson_constructed_complex_spectral_hamiltonianSemigroup_hasDerivAt_zero_logHamiltonian
    D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData n x

/-- Ordinary derivative form of the physical excitation-sector generator
identity. -/
theorem finite_wilson_vacuum_orthogonal_complex_spectral_hamiltonianSemigroup_deriv_zero
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ)
    (x : D.vacuumOrthogonalComplexSpectralStateSpace) :
    deriv
        (fun t : ℝ => D.vacuumOrthogonalComplexSpectralHamiltonianSemigroup n t x)
        0 =
      -(D.vacuumOrthogonalComplexSpectralLogHamiltonian n x) :=
  (finite_wilson_vacuum_orthogonal_complex_spectral_hamiltonianSemigroup_hasDerivAt_zero_logHamiltonian
    D n x).deriv

end

end MathlibAnalytic
end MGAP4D
