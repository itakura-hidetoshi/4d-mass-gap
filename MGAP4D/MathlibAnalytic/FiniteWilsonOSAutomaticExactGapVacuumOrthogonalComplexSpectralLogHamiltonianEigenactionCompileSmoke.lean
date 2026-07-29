import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapVacuumOrthogonalComplexSpectralLogHamiltonianEigenaction

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

variable {W : FiniteWilsonOSAutomaticApproximationFamily}
variable
  (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
variable (n : ℕ)

example :
    (D.vacuumOrthogonalComplexSpectralHamiltonian n).IsPositive :=
  finite_wilson_vacuum_orthogonal_complex_spectral_hamiltonian_isPositive D n

example :
    NormedSpace.exp (-D.vacuumOrthogonalComplexSpectralHamiltonian n) =
      D.vacuumOrthogonalComplexSpectralTransferOperator n :=
  finite_wilson_vacuum_orthogonal_complex_spectral_exp_neg_hamiltonian D n

example :
    D.vacuumOrthogonalComplexSpectralLogHamiltonian n =
      D.vacuumOrthogonalComplexSpectralHamiltonian n :=
  finite_wilson_vacuum_orthogonal_complex_spectral_logHamiltonian_eq_hamiltonian D n

example (i : Fin D.gapData.ExcitedDimension) :
    D.vacuumOrthogonalComplexSpectralLogHamiltonian n
        (D.vacuumOrthogonalComplexSpectralBasis i) =
      ((finite_wilson_vacuum_orthogonal_restricted_hamiltonian_symmetric
          D.gapData n).eigenvalues D.gapData.excitedFinrank i : ℂ) •
        D.vacuumOrthogonalComplexSpectralBasis i :=
  finite_wilson_vacuum_orthogonal_complex_spectral_logHamiltonian_on_basis D n i

end

end MathlibAnalytic
end MGAP4D
