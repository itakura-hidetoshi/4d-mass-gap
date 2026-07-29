import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapVacuumOrthogonalComplexSpectralHamiltonianSemigroupContinuity

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

variable {W : FiniteWilsonOSAutomaticApproximationFamily}
variable
  (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
variable (n : ℕ)

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

end

end MathlibAnalytic
end MGAP4D
