import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapVacuumOrthogonalRealSpectralHamiltonianSemigroupGenerator

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

variable {W : FiniteWilsonOSAutomaticApproximationFamily}
variable
  (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
variable (n : ℕ)

example :
    ContDiff ℝ ⊤ (D.vacuumOrthogonalRealSpectralHamiltonianSemigroup n) :=
  finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_contDiff D n

example (x : D.gapData.ExcitedStateSpace) :
    Continuous (fun t : ℝ =>
      D.vacuumOrthogonalRealSpectralHamiltonianSemigroup n t x) :=
  finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_stronglyContinuous
    D n x

example :
    HasDerivAt
      (D.vacuumOrthogonalRealSpectralHamiltonianSemigroup n)
      (-LinearMap.toContinuousLinearMap (D.gapData.restrictedHamiltonian n)) 0 :=
  finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_hasDerivAt_zero_operator
    D n

example (x : D.gapData.ExcitedStateSpace) :
    HasDerivAt
      (fun t : ℝ =>
        D.vacuumOrthogonalRealSpectralHamiltonianSemigroup n t x)
      (-(D.gapData.restrictedHamiltonian n x)) 0 :=
  finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_hasDerivAt_zero
    D n x

example (y : D.vacuumOrthogonalComplexScalarExtensionStateSpace) :
    HasDerivAt
      (fun t : ℝ =>
        D.vacuumOrthogonalComplexSpectralHamiltonianSemigroup n t
          (D.vacuumOrthogonalComplexSpectralScalarExtensionEquiv n y))
      (D.vacuumOrthogonalComplexSpectralScalarExtensionEquiv n
        (-((D.gapData.restrictedHamiltonian n).baseChange ℂ y))) 0 :=
  finite_wilson_vacuum_orthogonal_complex_scalarExtension_generator_compatible
    D n y

example (y : D.vacuumOrthogonalComplexScalarExtensionStateSpace) :
    HasDerivAt
      (fun t : ℝ =>
        D.vacuumOrthogonalComplexSpectralHamiltonianSemigroup n t
          (D.vacuumOrthogonalComplexSpectralScalarExtensionEquiv n y))
      (-(D.vacuumOrthogonalComplexSpectralLogHamiltonian n
        (D.vacuumOrthogonalComplexSpectralScalarExtensionEquiv n y))) 0 :=
  finite_wilson_vacuum_orthogonal_complex_scalarExtension_logGenerator_compatible
    D n y

end

end MathlibAnalytic
end MGAP4D
