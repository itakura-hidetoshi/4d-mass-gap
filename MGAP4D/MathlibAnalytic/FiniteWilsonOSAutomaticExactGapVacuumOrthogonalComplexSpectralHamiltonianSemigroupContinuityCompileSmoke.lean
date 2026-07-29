import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapVacuumOrthogonalComplexSpectralHamiltonianSemigroupGenerator
import Mathlib.Analysis.Normed.Module.RCLike.Basic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

variable {W : FiniteWilsonOSAutomaticApproximationFamily}
variable
  (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
variable (n : ℕ)

local instance vacuumOrthogonalComplexSpectralCompileSmokeNormedSpaceReal
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W} :
    NormedSpace ℝ D.vacuumOrthogonalComplexSpectralStateSpace :=
  NormedSpace.restrictScalars ℝ ℂ D.vacuumOrthogonalComplexSpectralStateSpace

example :
    ContDiff ℝ ⊤ (D.vacuumOrthogonalComplexSpectralHamiltonianSemigroup n) :=
  finite_wilson_vacuum_orthogonal_complex_spectral_hamiltonianSemigroup_contDiff D n

example :
    Continuous (D.vacuumOrthogonalComplexSpectralHamiltonianSemigroup n) :=
  finite_wilson_vacuum_orthogonal_complex_spectral_hamiltonianSemigroup_continuous D n

example (x : D.vacuumOrthogonalComplexSpectralStateSpace) :
    Continuous (fun t : ℝ =>
      D.vacuumOrthogonalComplexSpectralHamiltonianSemigroup n t x) :=
  finite_wilson_vacuum_orthogonal_complex_spectral_hamiltonianSemigroup_stronglyContinuous
    D n x

example (x : D.vacuumOrthogonalComplexSpectralStateSpace) :
    HasDerivAt
      (fun t : ℝ => D.vacuumOrthogonalComplexSpectralHamiltonianSemigroup n t x)
      (-(D.vacuumOrthogonalComplexSpectralLogHamiltonian n x)) 0 :=
  finite_wilson_vacuum_orthogonal_complex_spectral_hamiltonianSemigroup_hasDerivAt_zero_logHamiltonian
    D n x

example (x : D.vacuumOrthogonalComplexSpectralStateSpace) :
    deriv
        (fun t : ℝ => D.vacuumOrthogonalComplexSpectralHamiltonianSemigroup n t x)
        0 =
      -(D.vacuumOrthogonalComplexSpectralLogHamiltonian n x) :=
  finite_wilson_vacuum_orthogonal_complex_spectral_hamiltonianSemigroup_deriv_zero
    D n x

end

end MathlibAnalytic
end MGAP4D
